/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR, layer 3: multiplication of adèles by a rational function

`mulAdele C f` is the `k`-linear endomorphism of the adèle space given by componentwise
multiplication by `f ∈ K(C)`.  It is the tool that makes the adèle space a `K`-module: it
carries `A(D + div f)` to `A(D)` and fixes the diagonal copy of `K` setwise, hence acts on the
quotients `H1 C D = A_K/(K + A(D))` by `i(D + div f) = i(D)` (the index of speciality depends
only on the divisor class).
-/
import Submission.Work.RiemannRoch.Pole

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- Multiplication of adèles by a rational function, componentwise. -/
def mulAdele (C : Curve k) (f : C.functionField) : Adeles C →ₗ[k] Adeles C where
  toFun a := ⟨fun Q => f * (a : C.Place → C.functionField) Q, by
    refine Set.Finite.subset ((C.finite_support_ordAt f).union a.2) ?_
    intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    simp only [Set.mem_setOf_eq, not_lt] at hcon
    obtain ⟨hf, ha⟩ := hcon
    rcases eq_or_ne f 0 with h0 | h0
    · rw [h0, zero_mul] at hQ
      exact absurd hQ (not_lt_of_ge (ordAt_zero C Q).ge)
    rcases eq_or_ne ((a : C.Place → C.functionField) Q) 0 with ha0 | ha0
    · rw [ha0, mul_zero] at hQ
      exact absurd hQ (not_lt_of_ge (ordAt_zero C Q).ge)
    · have hf0 : C.ordAt f Q = 0 := not_not.mp hf
      rw [Work.CurveBasics.Curve.ordAt_mul C h0 ha0 Q, hf0] at hQ
      linarith
    ⟩
  map_add' a b := by
    ext Q
    simp [mul_add]
  map_smul' c a := by
    ext Q
    simp [mul_comm, mul_assoc, Algebra.smul_def]

@[simp]
theorem mulAdele_apply (C : Curve k) (f : C.functionField) (a : Adeles C) (Q : C.Place) :
    ((mulAdele C f a : Adeles C) : C.Place → C.functionField) Q =
      f * (a : C.Place → C.functionField) Q := rfl

theorem mulAdele_one (C : Curve k) : mulAdele C (1 : C.functionField) = LinearMap.id := by
  ext a Q
  simp

theorem mulAdele_mul_apply (C : Curve k) (f g : C.functionField) (a : Adeles C) :
    mulAdele C f (mulAdele C g a) = mulAdele C (f * g) a := by
  ext Q
  simp [mul_assoc]

theorem mulAdele_comp (C : Curve k) (f g : C.functionField) :
    (mulAdele C f).comp (mulAdele C g) = mulAdele C (f * g) := by
  ext a Q
  simp [mul_assoc]

theorem mulAdele_inv_comp (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    (mulAdele C f).comp (mulAdele C f⁻¹) = LinearMap.id := by
  rw [mulAdele_comp, mul_inv_cancel₀ hf, mulAdele_one]

theorem mulAdele_inv_comp' (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    (mulAdele C f⁻¹).comp (mulAdele C f) = LinearMap.id := by
  rw [mulAdele_comp, inv_mul_cancel₀ hf, mulAdele_one]

/-- Multiplication by a nonzero function injects the adèles. -/
theorem mulAdele_injective (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    Function.Injective (mulAdele C f) := by
  intro a b hab
  have h := congrArg (mulAdele C f⁻¹) hab
  rw [mulAdele_mul_apply, mulAdele_mul_apply, inv_mul_cancel₀ hf] at h
  simpa [mulAdele_one] using h

/-- Multiplication by a nonzero function is surjective on the adèles (with inverse
multiplication by `f⁻¹`). -/
theorem mulAdele_surjective (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    Function.Surjective (mulAdele C f) := by
  intro a
  refine ⟨mulAdele C f⁻¹ a, ?_⟩
  rw [mulAdele_mul_apply, mul_inv_cancel₀ hf]
  simp [mulAdele_one]

/-- Multiplication by `f` carries `A(D + div f)` into `A(D)`. -/
theorem mulAdele_mem_Asub (C : Curve k) (D : C.Div) (f : C.functionField) {a : Adeles C}
    (ha : a ∈ Asub C (D + C.div f)) : mulAdele C f a ∈ Asub C D := by
  rw [mem_Asub]
  apply mem_A.mpr
  intro Q
  have hq := mem_A.mp (mem_Asub.mp ha) Q
  by_cases h0 : f = 0
  · rw [mulAdele_apply, h0, zero_mul]
    exact Or.inl rfl
  rcases eq_or_ne ((a : C.Place → C.functionField) Q) 0 with ha0 | ha0
  · rw [mulAdele_apply, ha0, mul_zero]
    exact Or.inl rfl
  by_cases hf0 : f * (a : C.Place → C.functionField) Q = 0
  · rw [mulAdele_apply, hf0]
    exact Or.inl rfl
  · refine Or.inr ?_
    rw [mulAdele_apply, Work.CurveBasics.Curve.ordAt_mul C h0 ha0 Q]
    rcases hq with h' | h'
    · exact absurd h' ha0
    · simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply] at h'
      linarith

/-- The local form of `comap_mulAdele_Asub`: multiplication by `f ≠ 0` shifts the index of
the local lattice `I_Q(n) = m_Q^{-n}` by `ord_Q f`. -/
theorem mul_mem_localIdeal_iff (C : Curve k) (Q : C.Place) {f : C.functionField} (hf : f ≠ 0)
    (n : ℤ) (y : C.functionField) :
    f * y ∈ localIdeal C Q n ↔ y ∈ localIdeal C Q (n + C.ordAt f Q) := by
  rw [mem_localIdeal, mem_localIdeal]
  constructor
  · rintro (h0 | h)
    · exact Or.inl ((mul_eq_zero.mp h0).resolve_left hf)
    · by_cases hy : y = 0
      · exact Or.inl hy
      · refine Or.inr ?_
        rw [Work.CurveBasics.Curve.ordAt_mul C hf hy Q] at h
        linarith
  · rintro (h0 | h)
    · rw [h0, mul_zero]; exact Or.inl rfl
    · by_cases hy : y = 0
      · rw [hy, mul_zero]; exact Or.inl rfl
      · refine Or.inr ?_
        rw [Work.CurveBasics.Curve.ordAt_mul C hf hy Q]
        linarith

/-- The preimage under multiplication by `f ≠ 0` of `A(D)` is `A(D + div f)`. -/
theorem comap_mulAdele_Asub (C : Curve k) {f : C.functionField} (hf : f ≠ 0) (D : C.Div) :
    (Asub C D).comap (mulAdele C f) = Asub C (D + C.div f) := by
  ext a
  rw [Submodule.mem_comap, mem_Asub, mem_Asub]
  constructor
  · intro ha
    apply mem_A.mpr
    intro Q
    have h := mem_A.mp ha Q
    simp only [mulAdele_apply, Work.CurveBasics.Curve.div_apply, Finsupp.add_apply] at h
    exact (mul_mem_localIdeal_iff C Q hf (D Q) ((a : C.Place → C.functionField) Q)).mp h
  · intro ha
    apply mem_A.mpr
    intro Q
    have h := mem_A.mp ha Q
    simp only [mulAdele_apply, Work.CurveBasics.Curve.div_apply, Finsupp.add_apply]
    exact (mul_mem_localIdeal_iff C Q hf (D Q) ((a : C.Place → C.functionField) Q)).mpr h

/-- Multiplication by `f` maps the diagonal copy of `K` onto itself. -/
theorem map_diagK_mulAdele (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    (diagK C).map (mulAdele C f) = diagK C := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨h, rfl⟩ := mem_diagK.mp hy
    exact mem_diagK.mpr ⟨f * h, by ext Q; simp [mul_comm]⟩
  · intro x hx
    obtain ⟨h, rfl⟩ := mem_diagK.mp hx
    refine Submodule.mem_map.mpr ⟨diag C (f⁻¹ * h), ?_, ?_⟩
    · exact mem_diagK.mpr ⟨f⁻¹ * h, rfl⟩
    · ext Q
      simp only [mulAdele_apply, diag_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

theorem comap_diagK_mulAdele (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    (diagK C).comap (mulAdele C f) = diagK C := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_comap] at hx
    obtain ⟨h, hh⟩ := mem_diagK.mp hx
    refine mem_diagK.mpr ⟨f⁻¹ * h, ?_⟩
    have hcomp : mulAdele C f⁻¹ (mulAdele C f x) = x := by
      rw [mulAdele_mul_apply, inv_mul_cancel₀ hf]
      simp [mulAdele_one]
    rw [← hcomp, ← hh]
    ext Q
    simp only [mulAdele_apply, diag_apply]
  · intro x hx
    rw [Submodule.mem_comap]
    obtain ⟨h, rfl⟩ := mem_diagK.mp hx
    exact mem_diagK.mpr ⟨f * h, rfl⟩

end

end Curve

end Work.RiemannRoch
