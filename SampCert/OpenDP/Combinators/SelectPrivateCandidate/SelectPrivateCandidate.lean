/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate, GitHub Copilot
-/
import SampCert.SLang
import SampCert.Foundations.Monad
import SampCert.Foundations.Until
import SampCert.Samplers.Geometric.Code
import SampCert.Samplers.Geometric.Properties
import SampCert.DifferentialPrivacy.Pure.DP

/-!
# Select private candidate

This file formalizes ``make_select_private_candidate`` using SampCert's ``Mechanism`` and
pure DP definition. The implementation mirrors the Rust/pseudocode semantics:
- Sample a geometric number of iterations when ``stop_probability > 0``.
- Otherwise loop until the score exceeds ``threshold`` (modeled via ``probUntil``).
- Return ``none`` if the geometric budget is exhausted without meeting the threshold.

The privacy bound is stated as a theorem parameterized by the paper's Theorem 3.1 bound.
-/

noncomputable section

open Classical Real ENNReal

namespace SLang

variable {T TO : Type}

/-
Bernoulli distribution with real parameter ``p`` in ``[0, 1]``.
-/
def bernoulliReal (p : ℝ) : SLang Bool :=
  fun b => if b then ENNReal.ofReal p else (1 - ENNReal.ofReal p)

lemma bernoulliReal_sum (p : ℝ) (hp1 : p ≤ 1) :
    bernoulliReal p false + bernoulliReal p true = 1 := by
  have hp1' : ENNReal.ofReal p ≤ 1 := (ENNReal.ofReal_le_one).2 hp1
  simpa [bernoulliReal, add_comm] using (tsub_add_cancel_of_le hp1')

lemma bernoulliReal_true_lt_one (p : ℝ) (hp1 : p < 1) :
    bernoulliReal p true < 1 := by
  simp [bernoulliReal, ENNReal.ofReal_lt_one, hp1]

def scoreAbove (threshold : ℝ) (v : ℝ × TO) : Bool :=
  decide (v.1 >= threshold)

def runFixed
    (measurement : Mechanism T (ℝ × TO)) (threshold : ℝ)
    : Nat → List T → PMF (Option (ℝ × TO))
  | 0, _ => PMF.pure none
  | (Nat.succ n), l => do
      let v ← measurement l
      if scoreAbove threshold v then
        return some v
      else
        runFixed measurement threshold n l

lemma probUntil_hasSum
    (body : SLang α) (cond : α → Bool)
    (norm : ∑' x : α, body x = 1)
    (hpos : 0 < ∑' x : α, if cond x then body x else 0) :
    HasSum (probUntil body cond) 1 := by
  have hne : (∑' x : α, if cond x then body x else 0) ≠ 0 := by
    exact ne_of_gt hpos
  have hle : (∑' x : α, if cond x then body x else 0) ≤ 1 := by
    have A : ∀ x : α, (if cond x then body x else 0) ≤ body x := by
      intro x
      split <;> simp
    have B := ENNReal.tsum_le_tsum A
    simpa [norm] using B
  have hne_top : (∑' x : α, if cond x then body x else 0) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  have htsum : ∑' x : α, probUntil body cond x = 1 := by
    set S : ENNReal := ∑' x : α, if cond x then body x else 0
    have S_eq : (∑' x : α, if cond x = true then body x else 0) = S := by
      refine (tsum_congr ?_)
      intro x
      by_cases h : cond x <;> simp [h, S]
    have hrewrite : ∑' x : α, probUntil body cond x
        = ∑' x : α, (if cond x then body x else 0) * S⁻¹ := by
      refine tsum_congr ?_
      intro x
      have hx := probUntil_apply_norm (body := body) (cond := cond) (x := x) norm
      simpa [S] using hx
    calc
      ∑' x : α, probUntil body cond x
          = ∑' x : α, (if cond x then body x else 0) * S⁻¹ := hrewrite
      _ = ∑' x : α, if cond x = true then body x * S⁻¹ else 0 := by
        refine tsum_congr ?_
        intro x
        by_cases h : cond x <;> simp [h]
      _ = (∑' x : α, if cond x = true then body x else 0) * S⁻¹ := by
          have hmul : (∑' x : α, if cond x = true then body x * S⁻¹ else 0)
              = ∑' x : α, (if cond x = true then body x else 0) * S⁻¹ := by
            refine tsum_congr ?_
            intro x
            by_cases h : cond x <;> simp [h]
          rw [hmul, ENNReal.tsum_mul_right]
      _ = S * S⁻¹ := by
        simp [S_eq]
      _ = 1 := by
          simp [S, ENNReal.mul_inv_cancel hne hne_top]
  exact (Summable.hasSum_iff ENNReal.summable).2 htsum

def probUntilPMF
    (body : SLang α) (cond : α → Bool)
    (norm : ∑' x : α, body x = 1)
    (hpos : 0 < ∑' x : α, if cond x then body x else 0) : PMF α :=
  SLang.toPMF (probUntil body cond) (probUntil_hasSum body cond norm hpos)

def geomIterations
    (stop_probability : ℝ) (hpos : 0 < stop_probability) (h1 : stop_probability < 1) : PMF ℕ :=
  let trial := bernoulliReal (1 - stop_probability)
  have trial_spec : trial false + trial true = 1 := by
    have hp1 : (1 - stop_probability) ≤ 1 := by linarith
    simpa [trial] using bernoulliReal_sum (1 - stop_probability) hp1
  have trial_spec' : trial true < 1 := by
    have hp1 : (1 - stop_probability) < 1 := by linarith [h1]
    simpa [trial] using bernoulliReal_true_lt_one (1 - stop_probability) hp1
  have hsum : HasSum (probGeometric trial) 1 :=
    (Summable.hasSum_iff ENNReal.summable).2 (probGeometric_normalizes trial trial_spec trial_spec')
  SLang.toPMF (probGeometric trial) hsum

/-
Semantics of ``make_select_private_candidate``.

``termination`` supplies a normalization witness when ``stop_probability = 0``.
-/
def make_select_private_candidate
    (measurement : Mechanism T (ℝ × TO))
    (stop_probability : ℝ) (threshold : ℝ)
    (hsp0 : 0 ≤ stop_probability) (hsp1 : stop_probability < 1)
    (termination : ∀ l : List T,
      stop_probability = 0 → 0 < ∑' v : ℝ × TO, if scoreAbove threshold v then measurement l v else 0)
    : Mechanism T (Option (ℝ × TO)) :=
  fun l =>
    if hzero : stop_probability = 0 then
      let body : SLang (ℝ × TO) := measurement l
      let cond := scoreAbove threshold
      let pmf := probUntilPMF body cond
        (PMF.tsum_coe (measurement l))
        (termination l hzero)
      do
        let v ← pmf
        return some v
    else
      let hpos : 0 < stop_probability := lt_of_le_of_ne hsp0 (Ne.symm hzero)
      let geom := geomIterations stop_probability hpos hsp1
      do
        let n ← geom
        runFixed measurement threshold n l

/-
Paper-level privacy bound for ``make_select_private_candidate``.

This structure captures Theorem 3.1 of Liu and Talwar (STOC 2019) as a reusable assumption.
-/
structure SelectPrivateCandidatePaperBound (T TO : Type) where
  bound : ∀ (measurement : Mechanism T (ℝ × TO))
    (stop_probability : ℝ) (threshold : ℝ)
    (hsp0 : 0 ≤ stop_probability) (hsp1 : stop_probability < 1)
    (termination : ∀ l : List T,
      stop_probability = 0 → 0 < ∑' v : ℝ × TO, if scoreAbove threshold v then measurement l v else 0)
    (ε : NNReal),
    DP measurement ε →
    DP (make_select_private_candidate measurement stop_probability threshold hsp0 hsp1 termination) (2 * ε)

theorem make_select_private_candidate_valid
    (paper : SelectPrivateCandidatePaperBound T TO)
    (measurement : Mechanism T (ℝ × TO))
    (stop_probability : ℝ) (threshold : ℝ)
    (hsp0 : 0 ≤ stop_probability) (hsp1 : stop_probability < 1)
    (termination : ∀ l : List T,
      stop_probability = 0 → 0 < ∑' v : ℝ × TO, if scoreAbove threshold v then measurement l v else 0)
    (ε : NNReal) (hmeasurement : DP measurement ε) :
    DP (make_select_private_candidate measurement stop_probability threshold hsp0 hsp1 termination) (2 * ε) :=
  paper.bound measurement stop_probability threshold hsp0 hsp1 termination ε hmeasurement

end SLang
