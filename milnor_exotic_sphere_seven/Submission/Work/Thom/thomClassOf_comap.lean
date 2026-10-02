import Mathlib
import Submission.Work.Thom.CovComap
import Submission.Work.Thom.exists_unique_thomClassOfLocalThomUniv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Naturality of the canonical Thom class under pullback.** -/
theorem thomClassOf_comap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    (Work.Thom.relCohMap (Work.Thom.totalMapR Z f)
      (Work.Thom.zeroComplement (Work.Thom.realification (Work.Thom.bundleComap Z f)))
      (Work.Thom.zeroComplement (Work.Thom.realification Z))
      (fun _ hp => hp) ℤ (2 * m)).hom (Work.Thom.thomClassOf hm Z).τ
      = (Work.Thom.thomClassOf hm (Work.Thom.bundleComap Z f)).τ := by
  let AZ : Set (realification Z).TotalSpace := zeroComplement (realification Z)
  let AX : Set (realification (bundleComap Z f)).TotalSpace :=
    zeroComplement (realification (bundleComap Z f))
  let pzZ : Set ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) :=
    pieceZero (realification Z) (Set.univ : Set B)
  let pzX : Set ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')) :=
    pieceZero (realification (bundleComap Z f)) (Set.univ : Set B')
  let univZ : C(↥((realification Z).proj ⁻¹' (Set.univ : Set B)), (realification Z).TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let univX : C(↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')),
      (realification (bundleComap Z f)).TotalSpace) := ⟨Subtype.val, continuous_subtype_val⟩
  let pmR : C(↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')),
      ↥((realification Z).proj ⁻¹' (Set.univ : Set B))) :=
    pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)
  let tZ : RelCoh ℤ (2 * m) (realification Z).TotalSpace (zeroComplement (realification Z)) :=
    (thomClassOf hm Z).τ
  let tX : RelCoh ℤ (2 * m) (realification (bundleComap Z f)).TotalSpace
      (zeroComplement (realification (bundleComap Z f))) :=
    (thomClassOf hm (bundleComap Z f)).τ
  let TP : PieceCoh (realification Z) (Set.univ : Set B) (2 * m) :=
    (localThomOfComplexCover hm Z).τ
  let TP' : PieceCoh (realification (bundleComap Z f)) (Set.univ : Set B') (2 * m) :=
    (localThomOfComplexCover hm (bundleComap Z f)).τ
  let T : RelCoh ℤ (2 * m) ↥((realification Z).proj ⁻¹' (Set.univ : Set B))
      (pieceZero (realification Z) (Set.univ : Set B)) := TP
  let T' : RelCoh ℤ (2 * m) ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B'))
      (pieceZero (realification (bundleComap Z f)) (Set.univ : Set B')) := TP'
  have hmemR : ∀ x ∈ pzX, pmR x ∈ pzZ :=
    pieceMapR_mem Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial)
  have hmemX : ∀ x ∈ pzX, univX x ∈ AX := fun _ hx => hx
  have hmemZ : ∀ x ∈ pzZ, univZ x ∈ AZ := fun _ hx => hx
  have hmemT : ∀ x ∈ AX, (totalMapR Z f) x ∈ AZ := fun _ hx => hx
  have hspecZ := thomClassOf_spec hm Z
  have hspecX := thomClassOf_spec hm (bundleComap Z f)
  have hcast := pieceMapR_cast_comm Z f (covHfUnion Z f) (covHcover Z)
    (covHcover (bundleComap Z f)) (covWitness hm Z)
  have hcompmap : (totalMapR Z f).comp univX = univZ.comp pmR := by
    apply ContinuousMap.ext
    intro q
    show (totalMapR Z f) (univX q) = univZ (pmR q)
    rw [show univZ (pmR q)
        = (pieceMapR Z f (W := Set.univ) (W' := Set.univ) (fun _ _ => trivial) q
            : (realification Z).TotalSpace) from rfl]
    rw [totalMapR_apply, pieceMapR_apply]
    rfl
  have hanat : (relCohMap pmR pzX pzZ hmemR ℤ (2 * m)).hom T = T' := by
    have h2 := congrArg (fun z => (covHcover (bundleComap Z f) ▸ z :
        RelCoh ℤ (2 * m) ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B'))
          (pieceZero (realification (bundleComap Z f)) (Set.univ : Set B'))))
      (covWitness_comap hm Z f)
    have h3 : ((covHcover (bundleComap Z f) ▸ covWitness hm (bundleComap Z f) :
        RelCoh ℤ (2 * m) ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B'))
          (pieceZero (realification (bundleComap Z f)) (Set.univ : Set B')))) = T' := rfl
    exact hcast.trans (h2.trans h3)
  let eX : ↥((realification (bundleComap Z f)).proj ⁻¹' (Set.univ : Set B')) ≃ₜ
      (realification (bundleComap Z f)).TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  have hbij := bijective_relCohMap_of_homeomorphA pzX AX eX (fun y => Iff.rfl) ℤ (2 * m)
  change (relCohMap (totalMapR Z f) AX AZ hmemT ℤ (2 * m)).hom tZ = tX
  refine hbij.1 ?_
  calc (relCohMap univX pzX AX hmemX ℤ (2 * m)).hom
        ((relCohMap (totalMapR Z f) AX AZ hmemT ℤ (2 * m)).hom tZ)
      = (relCohMap ((totalMapR Z f).comp univX) pzX AZ (fun _ hp => hp) ℤ (2 * m)).hom tZ :=
        relCohMap_compA_apply pzX AX AZ univX (totalMapR Z f) hmemX hmemT (fun _ hp => hp)
          ℤ (2 * m) tZ
    _ = (relCohMap (univZ.comp pmR) pzX AZ (fun _ hp => hp) ℤ (2 * m)).hom tZ :=
        congrArg (fun φ => φ.hom tZ)
          (relCohMap_congrA pzX AZ hcompmap (fun _ hp => hp) (fun _ hp => hp) ℤ (2 * m))
    _ = (relCohMap pmR pzX pzZ hmemR ℤ (2 * m)).hom
          ((relCohMap univZ pzZ AZ hmemZ ℤ (2 * m)).hom tZ) :=
        (relCohMap_compA_apply pzX pzZ AZ pmR univZ hmemR hmemZ (fun _ hp => hp)
          ℤ (2 * m) tZ).symm
    _ = (relCohMap pmR pzX pzZ hmemR ℤ (2 * m)).hom T :=
        congrArg (fun z => (relCohMap pmR pzX pzZ hmemR ℤ (2 * m)).hom z) hspecZ
    _ = (relCohMap univX pzX AX hmemX ℤ (2 * m)).hom tX := hanat.trans hspecX.symm

end

end Work.Thom
