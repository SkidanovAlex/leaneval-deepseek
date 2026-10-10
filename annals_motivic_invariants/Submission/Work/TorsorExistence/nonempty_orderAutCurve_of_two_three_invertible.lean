import Mathlib
import Submission.Work.Arithmetic.Aut_orderOf_dvd_of_short
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

/-- `2 ^ k * 3 ^ l` is nonzero in a field in which `2` and `3` are invertible. -/
private lemma pow_two_mul_pow_three_ne_zero {𝕜 : Type} [Field 𝕜]
    (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) (k l : ℕ) :
    (2 : 𝕜) ^ k * (3 : 𝕜) ^ l ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-- The short Weierstrass model `y² = x³ + a₄x + a₆` has
`Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2)`; for the model `y² = x³ + 1` this is `-432`. -/
private lemma Δ_of_short_one {𝕜 : Type} [Field 𝕜] :
    (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve 𝕜).Δ = -432 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num

/-- For the short Weierstrass model `y² = x³ + 1` the invariant `c₄` vanishes, hence `j = 0`. -/
private lemma c₄_of_short_one {𝕜 : Type} [Field 𝕜] :
    (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve 𝕜).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  norm_num

/-- `y² = x³ + 1` is an elliptic curve over a field in which `2` and `3` are invertible. -/
private lemma isElliptic_short_one {𝕜 : Type} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) :
    (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve 𝕜).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Δ_of_short_one (𝕜 := 𝕜)]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (by
    have h : (432 : 𝕜) = (2 : 𝕜) ^ 4 * (3 : 𝕜) ^ 3 := by norm_num
    rw [h]
    exact pow_two_mul_pow_three_ne_zero h2 h3 4 3))

/-- Over a field in which `2` and `3` are invertible there is an elliptic curve with
`j ≠ 1728` and with every automorphism of order dividing `2` or `6` (Silverman, *AEC*,
Proposition A.1.2).  (Route: take `E : y² = x³ + 1`, i.e. the short Weierstrass curve
`⟨0, 0, 0, 0, 1⟩`; then `Δ = -16 * 27 = -432 ≠ 0` and `c₄ = 0`, so `j = 0 ≠ 1728`, and
`Work.Arithmetic.Aut_orderOf_dvd_of_short 0 1 h2 h3` with `a₄ = 0`, `a₆ = 1` gives the
automorphism statement — here every automorphism has order dividing `6`.) -/
theorem nonempty_orderAutCurve_of_two_three_invertible {𝕜 : Type} [Field 𝕜]
    (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) : Nonempty (OrderAutCurve 𝕜) := by
  -- the curve `E : y² = x³ + 1` is a short Weierstrass model with `a₄ = 0`, `a₆ = 1`;
  -- `a₄ = 0` already satisfies `4 * 0 ^ 3 + 27 = 27 ≠ 0`, so no genericity is needed
  have hEll : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve 𝕜).IsElliptic := isElliptic_short_one h2 h3
  haveI := hEll
  refine ⟨{ E := ⟨0, 0, 0, 0, 1⟩, isElliptic := hEll, j_ne := ?_, order_aut := ?_ }⟩
  · -- `j(E) = Δ⁻¹ * c₄ ^ 3 = Δ⁻¹ * 0 = 0 ≠ 1728` since `1728 = 2 ^ 6 * 3 ^ 3 ≠ 0`
    rw [WeierstrassCurve.j, c₄_of_short_one]
    simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero]
    intro h
    exact (by
      have h' : (1728 : 𝕜) = (2 : 𝕜) ^ 6 * (3 : 𝕜) ^ 3 := by norm_num
      rw [h'] at h
      exact pow_two_mul_pow_three_ne_zero h2 h3 6 3 h.symm)
  · -- every automorphism of a short Weierstrass model in characteristic `≠ 2, 3` has order
    -- dividing `2` or `6` (Silverman, *AEC*, Proposition A.1.2)
    intro σ
    exact Work.Arithmetic.Aut_orderOf_dvd_of_short 0 1 h2 h3 (Or.inr one_ne_zero)
      (by simp) σ

end Work.TorsorExistence
