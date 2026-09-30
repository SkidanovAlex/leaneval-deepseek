import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.ATools

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Isomorphisms of bundles: the induced homeomorphism of the Thom pairs

A bundle isomorphism `e : BundleIso Z Z'` (`Submission/Work/Thom/Iso.lean`) carries the zero section
to the zero section, hence the complement `E∖0` of the zero section of `Z` into the complement of the
zero section of `Z'`.  This module records that:

* `Work.Thom.BundleIso.punctMap` — the induced map `↥(zeroComplementCore Z) → ↥(zeroComplementCore Z')`;
* `Work.Thom.BundleIso.punctHomeomorph` — the induced homeomorphism of the punctured total spaces;
* `Work.Thom.BundleIso.relCohMap_punct_bijective` — the induced map on the relative cohomology of
  the **Thom pairs**, `H^n(E', E'∖0) → H^n(E, E∖0)`, is bijective
  (`Work.Thom.bijective_relCohMap_of_homeomorphA`).

This is the transfer tool that an isomorphism-invariance statement for the Thom class (and therefore
for the characteristic classes of this chapter) has to be built on; see `README.md` ADDENDUM 23.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {B : Type} [TopologicalSpace B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι ι' : Type}

/-- The complement of the zero section of a vector bundle over an arbitrary field (the
`Work.Thom.zeroComplement` of `Submission/Work/Thom/Basic.lean`, for an arbitrary field of
scalars). -/
def zeroComplementCore (Z : VectorBundleCore 𝕜 B F ι) : Set Z.TotalSpace := {p | p.2 ≠ 0}

/-- For a real bundle, `Work.Thom.zeroComplementCore` is `Work.Thom.zeroComplement`. -/
theorem zeroComplementCore_eq_zeroComplement {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type} [TopologicalSpace B] {ι : Type} (Z : RealBundle B F ι) :
    zeroComplementCore Z = zeroComplement Z := rfl

namespace BundleIso

variable {Z : VectorBundleCore 𝕜 B F ι} {Z' : VectorBundleCore 𝕜 B F ι'}

/-- **The map of punctured total spaces induced by a bundle isomorphism.** -/
def punctMap (e : BundleIso Z Z') : ↥(zeroComplementCore Z) → ↥(zeroComplementCore Z') :=
  fun p => ⟨e.toTotalSpace p.1, e.hom_ne_zero p.2⟩

@[simp] theorem punctMap_apply (e : BundleIso Z Z') (p : ↥(zeroComplementCore Z)) :
    ((e.punctMap p : ↥(zeroComplementCore Z')) : Z'.TotalSpace) = e.toTotalSpace p.1 := rfl

theorem continuous_punctMap (e : BundleIso Z Z') : Continuous e.punctMap :=
  Continuous.subtype_mk (e.continuous_hom.comp continuous_subtype_val) _

/-- **The homeomorphism of the punctured total spaces induced by a bundle isomorphism.** -/
def punctHomeomorph (e : BundleIso Z Z') : ↥(zeroComplementCore Z) ≃ₜ ↥(zeroComplementCore Z') where
  toFun := e.punctMap
  invFun := e.symm.punctMap
  left_inv p := by
    apply Subtype.ext
    show e.invTotalSpace (e.toTotalSpace p.1) = p.1
    exact e.toTotalSpace_left_inv p.1
  right_inv p := by
    apply Subtype.ext
    show e.toTotalSpace (e.invTotalSpace p.1) = p.1
    exact e.toTotalSpace_right_inv p.1
  continuous_toFun := e.continuous_punctMap
  continuous_invFun := e.symm.continuous_punctMap

@[simp] theorem punctHomeomorph_apply (e : BundleIso Z Z') (p : ↥(zeroComplementCore Z)) :
    e.punctHomeomorph p = e.punctMap p := rfl

/-- **The induced map on the relative cohomology of the Thom pairs is bijective.** -/
theorem relCohMap_punct_bijective (e : BundleIso Z Z') (R : Type) [CommRing R] (n : ℕ) :
    Function.Bijective (relCohMap (e.toHomeomorph : C(Z.TotalSpace, Z'.TotalSpace))
      (zeroComplementCore Z) (zeroComplementCore Z')
      (fun x hx => by
        show (e.toTotalSpace x).2 ≠ 0
        exact e.hom_ne_zero hx) R n).hom :=
  bijective_relCohMap_of_homeomorphA (zeroComplementCore Z) (zeroComplementCore Z')
    e.toHomeomorph
    (fun x => ⟨fun hx => by
        show (e.toTotalSpace x).2 ≠ 0
        exact e.hom_ne_zero hx,
      fun hx h0 => hx (by
        have h1 : (e.toTotalSpace x).2 = 0 := by
          show e.hom x.1 x.2 = 0
          rw [h0, hom_zero]
        exact h1)⟩) R n

end BundleIso

end

end Work.Thom
