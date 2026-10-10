import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, node V4: the `t`-adic valuation and the exponent-rigidity vocabulary

This file holds the vocabulary for `Work.MotV.exponent_rigidity` (node V4, the count of the
exponents of the element `h * (α h)^k ∈ 𝕜(t)`, `h = t(t-1)`).

* `vT 𝕜` is the `t`-adic valuation of `𝕜(t)` (`t = RatFunc.X`), i.e. the order of vanishing at
  `t = 0`, as a `ℤᵐ⁰`-valued valuation: it is the `(X)`-adic valuation of `𝕜[X]`.
  Its value on `RatFunc.X` is `exp (-1)`, so it is normalized (its value group is all of `ℤ`).

The basic evaluation facts are proved outright at the end of the file.
-/

set_option autoImplicit false

open scoped WithZero
open Polynomial WithZero Multiplicative

namespace Work.MotV
noncomputable section

/-- The `t`-adic valuation on `𝕜(t)` (`t = RatFunc.X`), as a `ℤᵐ⁰`-valued valuation: this is
`ord_0` of the paper (the order of vanishing at the point `t = 0`), normalized so that
`vT 𝕜 RatFunc.X = exp (-1)`. -/
abbrev vT (𝕜 : Type*) [Field 𝕜] : Valuation (RatFunc 𝕜) ℤᵐ⁰ :=
  (Polynomial.idealX 𝕜).valuation (RatFunc 𝕜)

/-- `vT 𝕜` is trivial on the constants. -/
theorem vT_trivOn (𝕜 : Type*) [Field 𝕜] : TrivOn 𝕜 (vT 𝕜) := by
  intro c hc
  rw [vT]
  rw [show algebraMap 𝕜 (RatFunc 𝕜) c
      = algebraMap 𝕜[X] (RatFunc 𝕜) (Polynomial.C c) from rfl]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp only [Polynomial.idealX_span, Ideal.mem_span_singleton]
  intro h
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_C_zero] at h
  exact hc h

/-- `TrivOn` is Mathlib's `Valuation.IsTrivialOn`. -/
theorem trivOn_iff_isTrivialOn {𝕜 F Γ₀ : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    TrivOn 𝕜 v ↔ v.IsTrivialOn 𝕜 :=
  ⟨fun h => ⟨h⟩, fun h => h.eq_one⟩

/-- The `t`-adic valuation of `t` is `exp (-1)`. -/
theorem vT_X (𝕜 : Type*) [Field 𝕜] : vT 𝕜 RatFunc.X = exp (-1 : ℤ) :=
  Polynomial.valuation_X_eq_neg_one 𝕜

/-- The `t`-adic valuation of `t - 1` is `1` (the point `t = 1` is not the point `t = 0`). -/
theorem vT_X_sub_one (𝕜 : Type*) [Field 𝕜] : vT 𝕜 (RatFunc.X - 1) = 1 := by
  have h1 : (RatFunc.X - 1 : RatFunc 𝕜)
      = algebraMap 𝕜[X] (RatFunc 𝕜) (Polynomial.X - Polynomial.C 1) := by simp
  rw [vT, h1, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp only [Polynomial.idealX_span, Ideal.mem_span_singleton]
  intro h
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C] at h
  norm_num at h

/-- The `t`-adic valuation of the Kummer parameter `hT 𝕜 = t(t-1)` is `exp (-1)`. -/
theorem vT_hT (𝕜 : Type*) [Field 𝕜] : vT 𝕜 (hT 𝕜) = exp (-1 : ℤ) := by
  rw [hT, map_mul, vT_X, vT_X_sub_one, mul_one]

end
end Work.MotV
