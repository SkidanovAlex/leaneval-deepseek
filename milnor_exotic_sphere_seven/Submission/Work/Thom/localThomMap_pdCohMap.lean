import Mathlib
import Submission.Work.Thom.thomClass_of_cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Thom

open Work.TangentClasses CategoryTheory CategoryTheory.Limits
open Work.Cohomology

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Restriction-naturality of the local Thom map for an arbitrary piece class.**  This is
`Work.Thom.localThomMap_restrict` (in `Submission/Work/Thom/thomClass_of_cover.lean`) with the
global class `τ : OpenThom Z n` replaced by an arbitrary piece class `τ : PieceCoh Z U n` (which
need *not* be the restriction of a global class).  The proof is the same computation: expand both
sides with `Work.Thom.localThomMap_apply` and apply `Work.Thom.mixedCupC_pairNatural` for the
restriction map `Work.Cohomology.pdIncl U W hWU`.  In this generality the auxiliary identity `h2`
of `localThomMap_restrict` becomes `rfl` (the restriction of the piece class is
`pdCohMap ... τ` by definition). -/
theorem localThomMap_pdCohMap (Z : RealBundle B F ι) (n : ℕ) {U W : Set B} (hWU : W ⊆ U)
    (τ : Work.Thom.PieceCoh Z U n) (k : ℕ) :
    Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) U W hWU)) ℤ k
        ≫ ModuleCat.ofHom (Work.Thom.localThomMap Z n W
            ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n).hom τ) k)
      = ModuleCat.ofHom (Work.Thom.localThomMap Z n U τ k)
        ≫ Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) (k + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  simp only [LinearMap.comp_apply]
  rw [localThomMap_apply, localThomMap_apply]
  set AW : Set ↥(Z.proj ⁻¹' W) :=
    (Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z
  set AU : Set ↥(Z.proj ⁻¹' U) :=
    (Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹' zeroComplement Z
  set f : C(↥(Z.proj ⁻¹' W), ↥(Z.proj ⁻¹' U)) :=
    TopCat.Hom.hom (pdIncl (M := TopCat.of Z.TotalSpace)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU))
  set inclC : C(↥W, ↥U) := TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)
  rw [show (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
      (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n)
      = relCohMap f AW AU (fun y hy => hy) ℤ n from rfl]
  rw [show (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
      (Z.proj ⁻¹' W) (Set.preimage_mono hWU) (k + n))
      = relCohMap f AW AU (fun y hy => hy) ℤ (k + n) from rfl]
  have h1 : (CohMap f ℤ k).hom ((CohMap (pieceProj Z U) ℤ k).hom x)
      = (CohMap (pieceProj Z W) ℤ k).hom ((CohMap inclC ℤ k).hom x) := by
    have hm : (CohMap (pieceProj Z U) ℤ k ≫ CohMap f ℤ k)
        = (CohMap inclC ℤ k ≫ CohMap (pieceProj Z W) ℤ k) := by
      rw [← CohMap_comp f (pieceProj Z U) ℤ k, ← CohMap_comp (pieceProj Z W) inclC ℤ k]
      congr 1
    have hx := congrArg (fun m => (ModuleCat.Hom.hom m) x) hm
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx
  rw [← h1]
  exact (mixedCupC_pairNatural f AW AU (fun y hy => hy) k n
    ((CohMap (pieceProj Z U) ℤ k).hom x) τ).symm

end Work.Thom
