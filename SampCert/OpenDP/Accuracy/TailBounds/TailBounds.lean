import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

open Real BigOperators

-- /// Computes the probability of sampling a value greater than `t` from the discrete laplace distribution.
-- ///
-- /// Arithmetic is controlled such that the resulting probability can only ever be slightly over-estimated due to numerical inaccuracy.
-- ///
-- /// # Proof definition
-- /// Returns `Ok(out)`, where `out` does not underestimate $\Pr[X > t]$
-- /// for $X \sim \mathcal{L}_\mathbb{Z}(0, scale)$, assuming $t > 0$,
-- /// or `Err(e)` if any numerical computation overflows.
-- ///
-- /// $\mathcal{L}_\mathbb{Z}(0, scale)$ is distributed as follows:
-- /// ```math
-- /// \forall x \in \mathbb{Z}, \quad
-- /// P[X = x] = \frac{e^{-1/scale} - 1}{e^{-1/scale} + 1} e^{-|x|/scale}, \quad
-- /// \text{where } X \sim \mathcal{L}_\mathbb{Z}(0, scale)
-- /// ```
def conservative_discrete_laplacian_tail_to_alpha (scale : ℝ) (tail : ℕ) : ℝ :=
  Real.exp (-((tail : ℝ) / scale)) / (Real.exp (-1 / scale) + 1)

def discrete_laplace_pmf (scale : ℝ) (x : ℤ) : ℝ :=
  let q := Real.exp (-1 / scale)
  (1 - q) / (1 + q) * q ^ (Int.natAbs x)

def discrete_laplace_tail_prob (scale : ℝ) (tail : ℕ) : ℝ :=
  ∑' n : ℕ, discrete_laplace_pmf scale (Int.ofNat (n + tail.succ))

theorem discrete_laplace_tail_prob_eq (scale : ℝ) (tail : ℕ) (hscale : 0 < scale) :
    discrete_laplace_tail_prob scale tail =
      Real.exp (-((tail.succ : ℝ) / scale)) / (Real.exp (-1 / scale) + 1) := by
  let q := Real.exp (-1 / scale)
  have hq0 : 0 ≤ q := le_of_lt (Real.exp_pos _)
  have hq1 : q < 1 := by
    have hpos : 0 < (1 / scale : ℝ) := one_div_pos.mpr hscale
    have hneg : (-1 / scale : ℝ) < 0 := by
      simpa [neg_div] using (neg_neg_iff_pos).2 hpos
    simpa [q] using (Real.exp_lt_one_iff.mpr hneg)
  have htsum : (∑' n : ℕ, q ^ n) = 1 / (1 - q) := by
    simpa using (tsum_geometric_of_lt_one hq0 hq1)
  have hshift : (∑' n : ℕ, q ^ (n + tail.succ)) = q ^ tail.succ * ∑' n : ℕ, q ^ n := by
    calc
      (∑' n : ℕ, q ^ (n + tail.succ)) = (∑' n : ℕ, q ^ tail.succ * q ^ n) := by
        refine tsum_congr ?_;
        intro n
        simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
      _ = q ^ tail.succ * ∑' n : ℕ, q ^ n := by
        simpa using (tsum_mul_left (a := q ^ tail.succ) (f := fun n : ℕ => q ^ n))
  have h1q : (1 - q) ≠ 0 := by nlinarith [hq1]
  have h1q' : (1 + q) ≠ 0 := by nlinarith [hq0]
  have hpow : q ^ tail.succ = Real.exp (-((tail.succ : ℝ) / scale)) := by
    have hpow' : Real.exp ((tail.succ : ℝ) * (-1 / scale)) = q ^ tail.succ := by
      simpa [q] using (Real.exp_nat_mul (-1 / scale) tail.succ)
    have hmul : (tail.succ : ℝ) * (-1 / scale) = -((tail.succ : ℝ) / scale) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    calc
      q ^ tail.succ = Real.exp ((tail.succ : ℝ) * (-1 / scale)) := by
        simpa using hpow'.symm
      _ = Real.exp (-((tail.succ : ℝ) / scale)) := by
        rw [hmul]
  calc
    discrete_laplace_tail_prob scale tail
        = (1 - q) / (1 + q) * ∑' n : ℕ, q ^ (n + tail.succ) := by
          have hsum : (∑' n : ℕ, (1 - q) / (1 + q) * q ^ (n + tail.succ))
              = (1 - q) / (1 + q) * ∑' n : ℕ, q ^ (n + tail.succ) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (tsum_mul_left (a := (1 - q) / (1 + q)) (f := fun n : ℕ => q ^ (n + tail.succ)))
          simpa [discrete_laplace_tail_prob, discrete_laplace_pmf, q, Int.natAbs_ofNat,
            mul_comm, mul_left_comm, mul_assoc] using hsum
    _ = (1 - q) / (1 + q) * (q ^ tail.succ * ∑' n : ℕ, q ^ n) := by
          simp [hshift]
    _ = (1 - q) / (1 + q) * (q ^ tail.succ * (1 / (1 - q))) := by
          simp [htsum]
    _ = q ^ tail.succ / (1 + q) := by
          field_simp [h1q, h1q']
          ring
    _ = Real.exp (-((tail.succ : ℝ) / scale)) / (Real.exp (-1 / scale) + 1) := by
          simp [q, hpow, add_comm]

theorem conservative_discrete_laplacian_tail_to_alpha_spec (scale : ℝ) (tail : ℕ)
    (hscale : 0 < scale) :
    discrete_laplace_tail_prob scale tail ≤
      conservative_discrete_laplacian_tail_to_alpha scale tail := by
  have hden : 0 ≤ Real.exp (-1 / scale) + 1 := by
    have hpos : 0 < Real.exp (-1 / scale) := Real.exp_pos _
    nlinarith
  have hle_nat : (tail : ℝ) ≤ (tail.succ : ℝ) := by
    exact_mod_cast (Nat.le_succ tail)
  have hdiv : (tail : ℝ) / scale ≤ (tail.succ : ℝ) / scale := by
    exact div_le_div_of_nonneg_right hle_nat hscale.le
  have hneg : -((tail.succ : ℝ) / scale) ≤ -((tail : ℝ) / scale) := by
    exact neg_le_neg hdiv
  have hnum : Real.exp (-((tail.succ : ℝ) / scale)) ≤ Real.exp (-((tail : ℝ) / scale)) := by
    exact Real.exp_le_exp_of_le hneg
  calc
    discrete_laplace_tail_prob scale tail
        = Real.exp (-((tail.succ : ℝ) / scale)) / (Real.exp (-1 / scale) + 1) :=
          discrete_laplace_tail_prob_eq scale tail hscale
    _ ≤ Real.exp (-((tail : ℝ) / scale)) / (Real.exp (-1 / scale) + 1) := by
          exact div_le_div_of_nonneg_right hnum hden
    _ = conservative_discrete_laplacian_tail_to_alpha scale tail := by
          simp [conservative_discrete_laplacian_tail_to_alpha]
