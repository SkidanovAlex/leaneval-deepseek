import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Zeros of the completed Dirichlet L-function lie in the critical strip

For a *primitive*, *non-trivial* Dirichlet character `χ mod N`, every zero of the
completed L-function `Λ(s, χ) = completedLFunction χ s` satisfies `0 < Re s < 1`.

This is the standard "zeros in the critical strip" fact.  It follows from two inputs:

1. **No zeros on `Re s ≥ 1`**: for any non-trivial character, the ordinary L-function
   `L(s, χ)` does not vanish on the closed half-plane `Re s ≥ 1`
   (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`, Mathlib).  Since
   `L(s, χ) = Λ(s, χ) / gammaFactor(s)` almost everywhere, a zero of `Λ` on
   `Re s ≥ 1` would force a zero of `L`.

2. **No zeros on `Re s ≤ 0`**: the functional equation for primitive characters
   (`Commons...completedLFunction_eq`, a rearrangement of Mathlib's
   `IsPrimitive.completedLFunction_one_sub`) gives
   `Λ(s, χ) = N^(1/2 - s) · ε(χ) · Λ(1 - s, χ⁻¹)`.
   A zero at `s` with `Re s ≤ 0` reflects to a zero of `Λ(·, χ⁻¹)` at `1 - s`
   with `Re(1 - s) ≥ 1`, contradicting (1) applied to the non-trivial character `χ⁻¹`.
   (The prefactor is non-zero: `N ≠ 0` and `|ε(χ)| = 1` by
   `Commons...rootNumber_norm_eq_one`.)
-/

/-- The completed L-function of a non-trivial Dirichlet character does not vanish on the
closed half-plane `Re s ≥ 1`. -/
private lemma zerosInStrip_aux_one_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro hz
  -- `Re s ≥ 1` implies `s ≠ 0`, so the L-function is the quotient of the completed
  -- L-function by the Gamma-factor at `s`.
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  have hL : DirichletCharacter.LFunction χ s = 0 := by
    rw [hdiv, hz]
    simp
  -- but `L(s, χ) ≠ 0` on `Re s ≥ 1` for non-trivial `χ`.
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs) hL

/-- The inverse of a non-trivial Dirichlet character is non-trivial. -/
private lemma zerosInStrip_aux_inv_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc
    χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

/-- The completed L-function of a primitive non-trivial Dirichlet character does not vanish on
the closed half-plane `Re s ≤ 0`.  This is deduced from the case `Re s ≥ 1` by the functional
equation `Λ(s, χ) = N^(1/2 - s) · ε(χ) · Λ(1 - s, χ⁻¹)`. -/
private lemma zerosInStrip_aux_re_le_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro hz
  -- The reflected point `1 - s` has `Re ≥ 1`.
  have h1s : 1 ≤ (1 - s : ℂ).re := by
    have hre : (1 - s : ℂ).re = 1 - s.re := by simp
    rw [hre]
    linarith
  -- `χ⁻¹` is non-trivial, so `Λ(·, χ⁻¹)` has no zero at `1 - s`:
  have hχinv : χ⁻¹ ≠ 1 := zerosInStrip_aux_inv_ne_one hχ
  have hC : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 :=
    zerosInStrip_aux_one_le_re (χ := χ⁻¹) hχinv h1s
  -- The prefactor in the functional equation is non-zero: `N ≠ 0` and `|ε(χ)| = 1`.
  have hA : (N : ℂ) ^ (1 / 2 - s) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast (NeZero.ne N : N ≠ 0))
  have hB : χ.rootNumber ≠ 0 := by
    intro h
    have hnorm : ‖χ.rootNumber‖ = 1 := rootNumber_norm_eq_one χ hχprim
    rw [h] at hnorm
    norm_num at hnorm
  -- Hence the right-hand side of the functional equation at `s` is non-zero,
  -- contradicting the assumed zero of `Λ(·, χ)` at `s`.
  have hprod_ne : (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA hB) hC
  have hprod : (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) = 0 := by
    rw [← completedLFunction_eq χ hχprim s, hz]
  exact hprod_ne hprod

/-- **Zeros in the critical strip.**  Every zero of the completed L-function of a primitive
non-trivial Dirichlet character lies in the open strip `0 < Re s < 1`. -/
theorem zerosInStrip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∀ s : ℂ, DirichletCharacter.completedLFunction χ s = 0 →
      0 < s.re ∧ s.re < 1 := by
  intro s hs
  constructor
  · -- `0 < s.re`: otherwise `s.re ≤ 0` and the reflection argument applies.
    by_contra hnot
    exact zerosInStrip_aux_re_le_zero χ hχ hχprim (le_of_not_gt hnot) hs
  · -- `s.re < 1`: otherwise `1 ≤ s.re` contradicts non-vanishing on `Re s ≥ 1`.
    by_contra hnot
    exact zerosInStrip_aux_one_le_re χ hχ (not_lt.mp hnot) hs

end Commons.NumberTheory.DirichletCharacter
