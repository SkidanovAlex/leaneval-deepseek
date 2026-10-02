import Mathlib
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.ATools
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.localThomOfComplexCover_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the canonical Thom class, from the naturality of the cover data

`Work.Thom.thomClassOf hm Z` is the unique `ThomClass` of the realified bundle whose class restricts,
along the identification of the piece over `Set.univ` with the total space, to the local data
`Work.Thom.localThomOfComplexCover hm Z` (`Work.Thom.thomClassOf_spec`,
`Work.Thom.exists_unique_thomClassOfLocalThomUniv`).  Consequently, once the *local data* is natural
(`Work.Thom.localThomOfComplexCover_comap`), so is the Thom class: the pullback of `Z`'s class has
the pullback's prescribed restriction, and the restriction map is injective
(`Work.Thom.bijective_relCohMap_of_homeomorphA`).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Naturality of the canonical Thom class of the realification**, deduced from the naturality of
the local cover data. -/
theorem thomClassOf_comap_via_cover {m : ℕ} {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} [Fintype ι] (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    (relCohMap (totalMapR Z f)
      (zeroComplement (realification (bundleComap Z f)))
      (zeroComplement (realification Z))
      (fun _ hp => hp) ℤ (2 * m)).hom (thomClassOf hm Z).τ
      = (thomClassOf hm (bundleComap Z f)).τ := by
  let pi : C(↥((realification Z).proj ⁻¹' (Set.univ : Set B)), (realification Z).TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let pi' : C(↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')),
      (realification (bundleComap Z f)).TotalSpace) := ⟨Subtype.val, continuous_subtype_val⟩
  let Bs : Set ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) :=
    pieceZero (realification Z) Set.univ
  let Bs' : Set ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')) :=
    pieceZero (realification (bundleComap Z f)) Set.univ
  let pm := pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)
  have hZspec : (relCohMap pi Bs (zeroComplement (realification Z))
        (fun y hy => hy) ℤ (2*m)).hom (thomClassOf hm Z).τ
      = (localThomOfComplexCover hm Z).τ :=
    thomClassOf_spec (hm := hm) Z
  have hXspec : (relCohMap pi' Bs' (zeroComplement (realification (bundleComap Z f)))
        (fun y hy => hy) ℤ (2*m)).hom (thomClassOf hm (bundleComap Z f)).τ
      = (localThomOfComplexCover hm (bundleComap Z f)).τ :=
    thomClassOf_spec (hm := hm) (bundleComap Z f)
  have hcov' : (relCohMap pm Bs' Bs (pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ)
        (fun _ _ => trivial)) ℤ (2*m)).hom (localThomOfComplexCover hm Z).τ
      = (localThomOfComplexCover hm (bundleComap Z f)).τ :=
    localThomOfComplexCover_comap hm Z f
  have hbij' : Function.Bijective (relCohMap pi' Bs'
      (zeroComplement (realification (bundleComap Z f))) (fun y hy => hy) ℤ (2*m)).hom := by
    let e : ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')) ≃ₜ
        (realification (bundleComap Z f)).TotalSpace :=
      { toFun := Subtype.val
        invFun := fun p => ⟨p, Set.mem_univ p⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun p => rfl
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
    exact bijective_relCohMap_of_homeomorphA Bs'
      (zeroComplement (realification (bundleComap Z f))) e (fun y => Iff.rfl) ℤ (2*m)
  have hmap : (totalMapR Z f).comp pi' = pi.comp pm := by
    apply ContinuousMap.ext; intro q
    rfl
  have hkey : (relCohMap pi' Bs' (zeroComplement (realification (bundleComap Z f)))
        (fun y hy => hy) ℤ (2*m)).hom
        ((relCohMap (totalMapR Z f) (zeroComplement (realification (bundleComap Z f)))
          (zeroComplement (realification Z)) (fun _ hp => hp) ℤ (2*m)).hom
            (thomClassOf hm Z).τ)
      = (relCohMap pi' Bs' (zeroComplement (realification (bundleComap Z f)))
          (fun y hy => hy) ℤ (2*m)).hom (thomClassOf hm (bundleComap Z f)).τ := by
    rw [hXspec]
    rw [relCohMap_compA_apply Bs' (zeroComplement (realification (bundleComap Z f)))
          (zeroComplement (realification Z)) pi' (totalMapR Z f) (fun y hy => hy)
          (fun _ hp => hp) (fun _ hp => hp) ℤ (2*m) (thomClassOf hm Z).τ]
    rw [relCohMap_congrA Bs' (zeroComplement (realification Z)) hmap
          (fun _ hp => hp) (fun _ hp => hp) ℤ (2*m)]
    rw [← relCohMap_compA_apply Bs' Bs (zeroComplement (realification Z)) pm pi
          (pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial))
          (fun _ hp => hp) (fun _ hp => hp) ℤ (2*m) (thomClassOf hm Z).τ]
    rw [hZspec]
    exact hcov'
  exact hbij'.1 hkey

end

end Work.Thom
