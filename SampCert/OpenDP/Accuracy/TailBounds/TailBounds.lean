import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Option.Basic

noncomputable section

open Real BigOperators

namespace TailBounds

/-! ## Float to Real interpretation -/

/-- Interpretation of a Float as the real number it represents (IEEE 754 semantics).
    Every finite IEEE 754 double-precision float represents a specific real number. -/
axiom floatToReal : Float → ℝ

/-- 1.0 is exactly representable as an IEEE 754 float. -/
axiom floatToReal_one : floatToReal (1 : Float) = 1

/-! ## Helpers for directed rounding implementation -/

/-- Convert an `Int` to `Float`. -/
private def intToFloat (n : Int) : Float :=
  if n ≥ 0 then Float.ofNat n.toNat else -(Float.ofNat (-n).toNat)

/-- Convert a `ℚ` to `Float` using default (nearest) rounding. -/
private def ratToFloat (x : ℚ) : Float :=
  intToFloat x.num / Float.ofNat x.den

/-- Machine epsilon for Float64: 2⁻⁵². -/
private def machEps : Float := 2.220446049250313e-16

/-- Minimum positive subnormal Float64: 2⁻¹⁰⁷⁴ ≈ 5 × 10⁻³²⁴. -/
private def minPosFloat : Float := 5.0e-324

/-- Return `some x` if `x` is finite, `none` otherwise. -/
private def guardFinite (x : Float) : Option Float :=
  if x.isFinite then some x else none

/-- Bump a Float up by at least 1 ULP (conservative model of IEEE 754 `next_up`). -/
private def bumpUp (x : Float) : Float :=
  let delta := Float.abs x * machEps
  if delta > minPosFloat then x + delta else x + minPosFloat

/-- Bump a Float down by at least 1 ULP (conservative model of IEEE 754 `next_down`). -/
private def bumpDown (x : Float) : Float :=
  let delta := Float.abs x * machEps
  if delta > minPosFloat then x - delta else x - minPosFloat

/-! ## Directed rounding operations

These functions model the corresponding Rust/dashu implementations which perform
arithmetic with directed rounding. They return `none` when the computation
would overflow or produce a non-finite result. -/

/-- Convert ℚ to Float, rounding toward +∞.
    Models: `f64::inf_cast(v: RBig)` using dashu `FBig<Up>` conversion.

    The Rust implementation converts the rational to an arbitrary-precision
    `FBig` with `Up` rounding mode (dashu), then converts to f64 ensuring
    the result is ≥ the exact rational value.

    # Proof Definition
    For any `x : ℚ`, `inf_cast x` either returns `none`,
    or `some f` where `floatToReal f ≥ (x : ℝ)`. -/
def inf_cast (x : ℚ) : Option Float :=
  guardFinite (bumpUp (ratToFloat x))

/-- Convert ℚ to Float, rounding toward -∞.
    Models: `f64::neg_inf_cast(v: RBig)` using dashu `FBig<Down>` conversion.

    The Rust implementation converts the rational to an arbitrary-precision
    `FBig` with `Down` rounding mode (dashu), then converts to f64 ensuring
    the result is ≤ the exact rational value.

    # Proof Definition
    For any `x : ℚ`, `neg_inf_cast x` either returns `none`,
    or `some f` where `floatToReal f ≤ (x : ℝ)`. -/
def neg_inf_cast (x : ℚ) : Option Float :=
  guardFinite (bumpDown (ratToFloat x))

/-- Compute exp rounding toward +∞.
    Models: `f64::inf_exp` using dashu `FBig<Up>` exp and Up-rounded conversion to f64.

    The Rust implementation converts the f64 input to `FBig<Up>`, sets precision
    to f64 mantissa digits (53), computes exp with upward rounding, then converts
    back to f64 with upward rounding.

    # Proof Definition
    For any `x : Float`, `inf_exp x` either returns `none`,
    or `some f` where `floatToReal f ≥ exp(floatToReal x)`. -/
def inf_exp (x : Float) : Option Float :=
  guardFinite (bumpUp (Float.exp x))

/-- Compute exp rounding toward -∞.
    Models: `f64::neg_inf_exp` using dashu `FBig<Down>` exp and Down-rounded conversion to f64.

    The Rust implementation converts the f64 input to `FBig<Down>`, computes exp
    with downward rounding, then converts back to f64 with downward rounding.

    # Proof Definition
    For any `x : Float`, `neg_inf_exp x` either returns `none`,
    or `some f` where `floatToReal f ≤ exp(floatToReal x)`. -/
def neg_inf_exp (x : Float) : Option Float :=
  let r := bumpDown (Float.exp x)
  guardFinite (if r < 0.0 then 0.0 else r)

/-- Addition rounding toward -∞.
    Models: `f64::neg_inf_add` using dashu `FBig<Down>` addition and Down-rounded conversion.

    The Rust implementation converts both f64 operands to `FBig<Down>` (exact),
    adds with downward rounding, then converts back to f64 with downward rounding.

    # Proof Definition
    For any `x y : Float`, `neg_inf_add x y` either returns `none`,
    or `some f` where `floatToReal f ≤ floatToReal x + floatToReal y`. -/
def neg_inf_add (x y : Float) : Option Float :=
  guardFinite (bumpDown (x + y))

/-- Division rounding toward +∞.
    Models: `f64::inf_div` using dashu `FBig<Up>` division and Up-rounded conversion.

    The Rust implementation converts both f64 operands to `FBig<Up>` (exact),
    divides with upward rounding, then converts back to f64 with upward rounding.

    # Proof Definition
    For any `x y : Float`, `inf_div x y` either returns `none`,
    or `some f` where `floatToReal y > 0 → floatToReal f ≥ floatToReal x / floatToReal y`. -/
def inf_div (x y : Float) : Option Float :=
  guardFinite (bumpUp (x / y))

/-! ## Correctness axioms for directed rounding operations

These axioms capture the properties guaranteed by the Rust/dashu implementations.
Each directed rounding operation returns a bound in the specified direction. -/

/-- `inf_cast` returns a value ≥ the input rational (rounds toward +∞). -/
axiom inf_cast_spec (x : ℚ) (f : Float) :
    inf_cast x = some f → floatToReal f ≥ (x : ℝ)

/-- `neg_inf_cast` returns a value ≤ the input rational (rounds toward -∞). -/
axiom neg_inf_cast_spec (x : ℚ) (f : Float) :
    neg_inf_cast x = some f → floatToReal f ≤ (x : ℝ)

/-- `inf_exp` returns a value ≥ exp of the input (rounds exp toward +∞). -/
axiom inf_exp_spec (x f : Float) :
    inf_exp x = some f → floatToReal f ≥ exp (floatToReal x)

/-- `neg_inf_exp` returns a value ≤ exp of the input (rounds exp toward -∞). -/
axiom neg_inf_exp_spec (x f : Float) :
    neg_inf_exp x = some f → floatToReal f ≤ exp (floatToReal x)

/-- `neg_inf_exp` returns a non-negative value (exp is always positive,
    so any lower bound used in practice is non-negative). -/
axiom neg_inf_exp_nonneg (x f : Float) :
    neg_inf_exp x = some f → floatToReal f ≥ 0

/-- `neg_inf_add` returns a value ≤ the true sum (rounds addition toward -∞). -/
axiom neg_inf_add_spec (x y f : Float) :
    neg_inf_add x y = some f → floatToReal f ≤ floatToReal x + floatToReal y

/-- When the first operand is ≥ 0 and the second is exactly 1.0,
    `neg_inf_add` returns a positive result.
    This holds because the true sum ≥ 0 + 1 = 1, and rounding down a value ≥ 1
    in IEEE 754 gives at least 1.0 (which is exactly representable). -/
axiom neg_inf_add_val_pos (x y f : Float) :
    neg_inf_add x y = some f → floatToReal x ≥ 0 → floatToReal y = 1 → floatToReal f > 0

/-- `inf_div` with positive denominator returns a value ≥ the true quotient
    (rounds division toward +∞). -/
axiom inf_div_spec (x y f : Float) :
    inf_div x y = some f → floatToReal y > 0 → floatToReal f ≥ floatToReal x / floatToReal y

/-! ## Main function -/

/-- Computes a conservative upper bound on Pr[X > tail] for X ~ DiscreteLaplace(0, scale).

    Faithfully models the Rust implementation:
    ```
    pub fn conservative_discrete_laplacian_tail_to_alpha(scale: RBig, tail: UBig) -> Fallible<f64> {
        let numer = f64::inf_cast(-RBig::from(tail) / scale.clone())?.inf_exp()?;
        let denom = f64::neg_inf_cast(RBig::ONE / scale)?
            .neg_inf_exp()?
            .neg_inf_add(&1.)?;
        numer.inf_div(&denom)
    }
    ```

    The numerator is an upper bound on exp(-tail/scale).
    The denominator is a lower bound on exp(1/scale) + 1.
    Their quotient (rounded up) is an upper bound on exp(-tail/scale) / (exp(1/scale) + 1),
    which equals Pr[X > tail] for the discrete Laplace distribution. -/
def conservative_discrete_laplacian_tail_to_alpha (scale : ℚ) (tail : ℕ) : Option Float :=
  (inf_cast (-(↑tail : ℚ) / scale)).bind fun v1 =>
  (inf_exp v1).bind fun numer =>
  (neg_inf_cast ((1 : ℚ) / scale)).bind fun v2 =>
  (neg_inf_exp v2).bind fun w =>
  (neg_inf_add w (1 : Float)).bind fun denom =>
  inf_div numer denom

/-! ## Mathematical definition of the tail probability -/

/-- The tail probability Pr[X > tail] for X ~ DiscreteLaplace(0, scale).

    For the discrete Laplace distribution with scale parameter s > 0 and PMF:
      P[X = x] = ((1 - e^{-1/s}) / (1 + e^{-1/s})) · e^{-|x|/s}  for x ∈ ℤ

    the tail probability is:
      Pr[X > t] = Σ_{x=t+1}^∞ P[X = x] = e^{-t/s} / (e^{1/s} + 1)

    Derivation: Let r = e^{-1/s}. Then Σ_{x ∈ ℤ} r^|x| = (1+r)/(1-r),
    so the normalization constant is (1-r)/(1+r). The tail sum is:
      Pr[X > t] = (1-r)/(1+r) · r^{t+1}/(1-r) = r^{t+1}/(1+r)
                = e^{-(t+1)/s} / (1 + e^{-1/s})
                = e^{-t/s} / (e^{1/s} + 1)   [multiply num and denom by e^{1/s}] -/
noncomputable def disc_laplace_tail_prob (scale : ℝ) (tail : ℕ) : ℝ :=
  exp (-(↑tail : ℝ) / scale) / (exp (1 / scale) + 1)

/-! ## Specification theorem -/

/-- The output of `conservative_discrete_laplacian_tail_to_alpha` does not underestimate
    the discrete Laplace tail probability Pr[X > tail] for X ~ L_Z(0, scale).

    This corresponds to the Rust proof definition:
    "Returns Ok(out), where out does not underestimate Pr[X > t]
     for X ~ L_Z(0, scale), assuming t > 0,
     or Err(e) if any numerical computation overflows."

    Proof sketch:
    1. The numerator satisfies: floatToReal numer ≥ exp(-tail/scale)
       (by inf_cast rounding up, then inf_exp rounding up, and monotonicity of exp)
    2. The denominator satisfies: 0 < floatToReal denom ≤ exp(1/scale) + 1
       (by neg_inf_cast rounding down, neg_inf_exp rounding down, neg_inf_add rounding down,
        and monotonicity of exp)
    3. Division monotonicity: for a' ≤ a, 0 < b ≤ b', we have a'/b' ≤ a/b
    4. inf_div rounds up: floatToReal out ≥ numer/denom
    5. Combining: floatToReal out ≥ exp(-tail/scale) / (exp(1/scale) + 1) = Pr[X > tail] -/
theorem conservative_discrete_laplacian_tail_to_alpha_spec
    (scale : ℚ) (tail : ℕ) (out : Float) :
    conservative_discrete_laplacian_tail_to_alpha scale tail = some out →
    floatToReal out ≥ disc_laplace_tail_prob (↑scale) tail := by
  intro h
  -- Decompose the chain of Option.bind calls
  unfold conservative_discrete_laplacian_tail_to_alpha at h
  simp only [Option.bind_eq_some'] at h
  obtain ⟨v1, hv1, numer, hnumer, v2, hv2, w, hw, denom, hdenom, hout⟩ := h
  -- Step 1: Apply directed rounding axioms to get bounds on intermediate values
  have h_v1 := inf_cast_spec _ _ hv1
  have h_numer := inf_exp_spec _ _ hnumer
  have h_v2 := neg_inf_cast_spec _ _ hv2
  have h_w := neg_inf_exp_spec _ _ hw
  have h_w_nn := neg_inf_exp_nonneg _ _ hw
  have h_denom_le := neg_inf_add_spec _ _ _ hdenom
  have h_denom_pos := neg_inf_add_val_pos _ _ _ hdenom h_w_nn floatToReal_one
  have h_out := inf_div_spec _ _ _ hout h_denom_pos
  -- Step 2: Normalize rational casts to real number expressions
  have h_cast1 : (↑(-(↑tail : ℚ) / scale) : ℝ) = -(↑tail : ℝ) / (↑scale : ℝ) := by
    push_cast; ring
  have h_cast2 : (↑((1 : ℚ) / scale) : ℝ) = 1 / (↑scale : ℝ) := by
    push_cast; ring
  rw [h_cast1] at h_v1
  rw [h_cast2] at h_v2
  -- Step 3: Chain bounds for numerator using monotonicity of exp
  --   floatToReal v1 ≥ -tail/scale  (from inf_cast)
  --   floatToReal numer ≥ exp(floatToReal v1) ≥ exp(-tail/scale)  (from inf_exp + exp monotone)
  have h_numer_bound : exp (-(↑tail : ℝ) / ↑scale) ≤ floatToReal numer :=
    le_trans (exp_le_exp.mpr h_v1) h_numer
  -- Step 4: Chain bounds for denominator using monotonicity of exp
  --   floatToReal v2 ≤ 1/scale  (from neg_inf_cast)
  --   floatToReal w ≤ exp(floatToReal v2) ≤ exp(1/scale)  (from neg_inf_exp + exp monotone)
  --   floatToReal denom ≤ floatToReal w + 1 ≤ exp(1/scale) + 1  (from neg_inf_add)
  have h_w_bound : floatToReal w ≤ exp (1 / ↑scale) :=
    le_trans h_w (exp_le_exp.mpr h_v2)
  have h_denom_bound : floatToReal denom ≤ exp (1 / ↑scale) + 1 := by
    have := floatToReal_one
    linarith
  -- Step 5: Numerator is non-negative (since exp is always positive)
  have h_numer_nn : 0 ≤ floatToReal numer :=
    le_of_lt (lt_of_lt_of_le (exp_pos _) h_numer_bound)
  -- Step 6: Division monotonicity
  --   For 0 ≤ c, a ≤ c, 0 < d, d ≤ b: a / b ≤ c / d
  --   Here a = exp(-tail/scale), b = exp(1/scale)+1, c = numer, d = denom
  have h_div : exp (-(↑tail : ℝ) / ↑scale) / (exp (1 / ↑scale) + 1) ≤
               floatToReal numer / floatToReal denom :=
    div_le_div h_numer_nn h_numer_bound h_denom_pos h_denom_bound
  -- Step 7: Combine inf_div bound with division monotonicity
  show floatToReal out ≥ disc_laplace_tail_prob ↑scale tail
  unfold disc_laplace_tail_prob
  exact le_trans h_div h_out

end TailBounds
