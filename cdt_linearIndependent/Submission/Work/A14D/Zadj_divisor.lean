import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.A14D.Zadj_bounds
import Submission.Commons.FieldTheory.RatFunc.exists_dvd_of_ordAt_bounds

/-!
# `Work.A14D.Zadj_divisor` — the divisor bound for the adjoint Zagier equation

Let `β ∈ ℂ(x)` solve `LZf β = RhsZ c`, where `LZf = P·β'' + P'·β' + R·β` is Zagier's operator in
self-adjoint form (`P = x − 10x² + 9x³ = x(1−x)(1−9x)`, `P' = 1 − 20x + 27x²`, `R = −3 + 9x`) and
the right hand side `Σ_{i<3} c_i·y^{−i}·y'` (`y = x²/(x−1)`) has poles of order at most `3` at
`x = 0` and `2` at `x = 1`.

`Work.A14D.Zadj_bounds` (built on the local indicial analysis `Zadj_generic` / `Zadj_singular`)
then says that `β` has a pole of order at most `2` at `x = 0`, at most `1` at `x = 1`, and no pole
whatsoever away from `{0, 1}`.  Consequently the product `DZ·β` of `β` with the *universal
denominator* `DZ = x²(x−1)` has nonnegative order of vanishing at every point of `ℂ`, hence — `ℂ`
being algebraically closed — is the image of a polynomial `W` under the inclusion
`ℂ[x] ↪ ℂ(x)` (`Commons.FieldTheory.RatFunc.exists_eq_algebraMap_of_forall_nonneg_ordAt`).

The two ingredients of the computation are
* the multiplicativity of `ordAt` in the product `DZ·β` (`ordAt_mul`), and
* `rootMultiplicity α DZ = 2` at `α = 0`, `1` at `α = 1` and `0` elsewhere, and
  `ordAt α (algebraMap DZ) = rootMultiplicity α DZ` (`ordAt_algebraMap`).

This is the A-side analogue of `Work.C17adj.beta_Dadj_is_poly`.
-/

open Polynomial

noncomputable section
namespace Work.A14D

/-- The `rootMultiplicity` of the square of `X`: `2` at the origin and `0` elsewhere. -/
private lemma rootMult_X_sq (α : ℂ) :
    ((X : Polynomial ℂ) ^ 2).rootMultiplicity α = if α = 0 then 2 else 0 := by
  by_cases h : α = 0
  · subst h
    rw [show (X : Polynomial ℂ) ^ 2 = (X - C (0 : ℂ)) ^ 2 by simp,
      Polynomial.rootMultiplicity_X_sub_C_pow, if_pos rfl]
  · rw [if_neg h, Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    have h2 : α ^ 2 = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at hroot
      exact hroot
    exact h ((pow_eq_zero_iff (by norm_num)).mp h2)

/-- The `rootMultiplicity` of the linear factor `X − 1`. -/
private lemma rootMult_X_sub_one (α : ℂ) :
    (X - C (1 : ℂ) : Polynomial ℂ).rootMultiplicity α = if α = 1 then 1 else 0 :=
  Polynomial.rootMultiplicity_X_sub_C

/-- The root multiplicity of the universal denominator `DZ = x²(x−1)`. -/
private lemma rootMult_DZ (α : ℂ) :
    DZ.rootMultiplicity α = if α = 0 then 2 else if α = 1 then 1 else 0 := by
  rw [show DZ = (X : Polynomial ℂ) ^ 2 * (X - C (1 : ℂ)) by rw [DZ, Polynomial.C_1],
    Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
      (Polynomial.X_sub_C_ne_zero (1 : ℂ))),
    rootMult_X_sq, rootMult_X_sub_one]
  by_cases h1 : α = 1
  · subst h1; simp
  · by_cases h0 : α = 0
    · subst h0; simp [h1]
    · simp [h1, h0]

/-- The same root multiplicity, as an integer, in the shape needed for `ordAt`. -/
private lemma rootMult_DZ_int (α : ℂ) :
    (DZ.rootMultiplicity α : ℤ) = if α = 0 then (2 : ℤ) else if α = 1 then 1 else 0 := by
  rw [rootMult_DZ]
  by_cases h0 : α = 0
  · subst h0; simp
  · by_cases h1 : α = 1
    · subst h1; simp [h0]
    · simp [h0, h1]

/-- **The divisor bound.**  A solution `β ∈ ℂ(x)` of the adjoint Zagier equation
`LZf β = RhsZ c` with `RhsZ c` having poles of order at most `3` at `0` and `2` at `1` satisfies
`DZ·β = W` for a polynomial `W`, `DZ = x²(x−1)`. -/
theorem Zadj_divisor {β : RatFunc ℂ} {c : Fin 3 → ℂ} (h : LZf β = RhsZ c)
    (hrhs : ∀ α : ℂ, (if α = 0 then (-3 : ℤ) else if α = 1 then (-2 : ℤ) else 0)
      ≤ Commons.FieldTheory.RatFunc.ordAtT α (RhsZ c)) :
    ∃ W : Polynomial ℂ, algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ * β := by
  rcases eq_or_ne β 0 with hβ0 | hβ
  · subst hβ0
    exact ⟨0, by simp⟩
  obtain ⟨hb0, hb1, hbgen⟩ := Zadj_bounds hβ h hrhs
  have hprod : ∀ α : ℂ,
      (0 : ℤ) ≤ Commons.FieldTheory.RatFunc.ordAt α
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ * β) := by
    intro α
    rw [Commons.FieldTheory.RatFunc.ordAt_mul α
        (RatFunc.algebraMap_ne_zero DZ_ne_zero) hβ,
      Commons.FieldTheory.RatFunc.ordAt_algebraMap, rootMult_DZ_int]
    split_ifs with h0 h1
    · subst h0; omega
    · subst h1; omega
    · have := hbgen α h0 h1; omega
  obtain ⟨W, hW⟩ :=
    Commons.FieldTheory.RatFunc.exists_eq_algebraMap_of_forall_nonneg_ordAt
      (x := algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ * β) hprod
  exact ⟨W, hW.symm⟩


namespace Work.A14D

/-- The same statement under the doubled-namespace name
`Work.A14D.Work.A14D.Zadj_divisor`, the name under which the seeded file declared it. -/
theorem Zadj_divisor {β : RatFunc ℂ} {c : Fin 3 → ℂ} (h : Work.A14D.LZf β = Work.A14D.RhsZ c)
    (hrhs : ∀ α : ℂ, (if α = 0 then (-3 : ℤ) else if α = 1 then (-2 : ℤ) else 0)
      ≤ Commons.FieldTheory.RatFunc.ordAtT α (Work.A14D.RhsZ c)) :
    ∃ W : Polynomial ℂ, algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.A14D.DZ * β :=
  _root_.Work.A14D.Zadj_divisor h hrhs

end Work.A14D
end Work.A14D

end
