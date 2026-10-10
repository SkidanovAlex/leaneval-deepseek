/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.CylinderChart` — affine charts of integral `𝕜`-schemes

Auxiliary definitions and lemmas for `Work.CrauderKatz.cylinderField_resAlgEquiv_prod`.

For an integral scheme `D` over `Spec 𝕜` and an *affine chart* `z : Z ⟶ D` (an open immersion
whose source `Z` is affine), the global sections `Γ(Z,⊤)` form a fraction ring of the function
field `κ(D)`, with the structure map induced by `z`; and when `z` is a morphism over `Spec 𝕜`
encoded by a ring map `ψ : 𝕜 →+* Γ(Z,⊤)`, this structure map is the `𝕜`-structure map of `D`.

The geometric input for the cylinder theorem is that the canonical morphism
`Spec (Γ(X,U)[t]) ⟶ X ×_𝕜 𝔸¹` (attached to an affine chart `Spec Γ(X,U) ⊆ X`) is such a chart.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz

noncomputable section

variable {D Z : AlgebraicGeometry.Scheme.{0}}

/-- **Transfer of `IsLocalization` along a ring isomorphism.**  If `S` is the localization of `R`
at `M` and `e : R ≃+* R'` identifies `M` with `M'` (and the two structure maps), then `S` is also
the localization of `R'` at `M'`. -/
theorem isLocalization_of_ringEquiv {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    (e : R ≃+* R') (M : Submonoid R) (M' : Submonoid R') [Algebra R S] [Algebra R' S]
    (hM' : ∀ y : R', y ∈ M' ↔ e.symm y ∈ M) (h : ∀ x : R, algebraMap R' S (e x) = algebraMap R S x)
    [IsLocalization M S] : IsLocalization M' S where
  map_units y := by
    have hy : e.symm y.1 ∈ M := (hM' y.1).mp y.2
    rw [← e.apply_symm_apply y.1, h]
    exact IsLocalization.map_units S ⟨e.symm y.1, hy⟩
  surj z := by
    obtain ⟨⟨x, m⟩, hm⟩ := IsLocalization.surj M z
    refine ⟨⟨e x, ⟨e m, ?_⟩⟩, ?_⟩
    · rw [hM']; simp
    · rw [h, h]; exact hm
  exists_of_eq {x y} hxy := by
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, h, h] at hxy
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    refine ⟨⟨e c, ?_⟩, ?_⟩
    · rw [hM']; simp
    · have h2 : e (↑c * e.symm x) = e (↑c * e.symm y) := by rw [hc]
      rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h2
      simpa using h2

/-- The canonical identification of the global sections of the open image of a chart immersion
with the global sections of the chart. -/
def chartIso (z : Z ⟶ D) [IsOpenImmersion z] : Γ(D, Hom.opensRange z) ≅ Γ(Z,⊤) :=
  (CategoryTheory.eqToIso (by rw [Scheme.Hom.image_top_eq_opensRange])).symm ≪≫
    (Scheme.Hom.appIso z ⊤)

/-- The structure map `Γ(Z,⊤) ⟶ κ(D)` induced by an affine chart `z : Z ⟶ D`. -/
def chartHom [IrreducibleSpace D] (z : Z ⟶ D) [IsOpenImmersion z] [Nonempty Z] :
    Γ(Z, ⊤) →+* (D.functionField : Type) :=
  letI : Nonempty (Hom.opensRange z) := ⟨⟨z (Classical.arbitrary Z), ⟨Classical.arbitrary Z, rfl⟩⟩⟩
  ((chartIso z).symm.hom ≫ D.germToFunctionField (Hom.opensRange z)).hom

/-- **Chart lemma.**  For an integral scheme `D` and an affine nonempty chart `z : Z ⟶ D` given
by an open immersion, the global sections `Γ(Z,⊤)` form a fraction ring of the function field of
`D`, with the structure map induced by `z`. -/
theorem isFractionRing_functionField_of_chart [IrreducibleSpace D] [IsIntegral D]
    [IsAffine Z] [Nonempty Z] [IsIntegral Z] (z : Z ⟶ D) [IsOpenImmersion z] :
    letI : Algebra Γ(Z,⊤) (D.functionField : Type) := (chartHom z).toAlgebra
    IsFractionRing Γ(Z,⊤) (D.functionField : Type) := by
  letI : Nonempty (Hom.opensRange z) := ⟨⟨z (Classical.arbitrary Z), ⟨Classical.arbitrary Z, rfl⟩⟩⟩
  letI : Algebra Γ(Z,⊤) (D.functionField : Type) := (chartHom z).toAlgebra
  have hAff : IsAffineOpen (Hom.opensRange z) := isAffineOpen_opensRange z
  haveI : IsFractionRing Γ(D, Hom.opensRange z) (D.functionField : Type) :=
    functionField_isFractionRing_of_isAffineOpen D _ hAff
  refine isLocalization_of_ringEquiv (M := nonZeroDivisors Γ(D, Hom.opensRange z))
    (M' := nonZeroDivisors Γ(Z,⊤)) (Iso.commRingCatIsoToRingEquiv (chartIso z)) ?_ ?_
  · intro y
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact (Iff.not (RingEquiv.map_eq_zero_iff (f := _) (x := y))).symm
  · intro x
    simp only [RingHom.algebraMap_toAlgebra, chartHom, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    refine congrArg _ ?_
    show (chartIso z).inv ((chartIso z).hom x) = x
    exact Iso.hom_inv_id_apply (chartIso z) x

end

end Work.CrauderKatz
