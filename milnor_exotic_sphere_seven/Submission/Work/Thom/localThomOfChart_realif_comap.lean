import Mathlib
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.Mpun_natural_map

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the chart local Thom data, on the realification side

The chart local Thom data `Work.Thom.localThomOfChart Z n e i W hW` is the pullback of the punctured
model class `Work.Thom.Mpun n ↥W` along the chart homeomorphism.  Here we prove its naturality under
a pullback `realification (bundleComap Z f)` (the presentation the Chern recursion sees: the
pullback of the *complex* bundle, realified), for an arbitrary pair of sets `W ⊆ B`, `W' ⊆ B'` with
`f '' W' ⊆ W`.

The only input is the naturality of the punctured model class in the base,
`Work.Thom.Mpun_natural_map`, together with the commutativity of the diagram

  `chartHomeo_Z ∘ pieceMapR = baseMap (f|W') ∘ chartHomeo_{f^*Z}`,

which is a computation in the transition functions (`bundleComap_coordChange`,
`realification_coordChange`).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Naturality of `Work.Thom.localThomOfChart` on the realification side.** -/
theorem localThomOfChart_realif_comap {m n : ℕ} {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (e : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι)
    {W : Set B} {W' : Set B'} (hW : W ⊆ (realification Z).baseSet i)
    (hW' : W' ⊆ (realification (bundleComap Z f)).baseSet i) (hWf : ∀ x ∈ W', f x ∈ W) :
    (relCohMap (pieceMapR Z f hWf)
      (pieceZero (realification (bundleComap Z f)) W') (pieceZero (realification Z) W)
      (pieceMapR_mem Z f hWf) ℤ n).hom
        (localThomOfChart (realification Z) n e i W hW).τ
      = (localThomOfChart (realification (bundleComap Z f)) n e i W' hW').τ := by
  rw [localThomOfChart_tau, localThomOfChart_tau]
  let g : C(↥W', ↥W) :=
    ⟨fun x => ⟨f x.1, hWf x.1 x.2⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk (fun x => hWf x.1 x.2)⟩
  have hg : ∀ x : ↥W', (g x : B) = f x.1 := fun x => rfl
  have hcomp : (chartHomeo (realification Z) n e i W hW :
        C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))).comp
          (pieceMapR Z f hWf)
      = (baseMap g n).comp (chartHomeo (realification (bundleComap Z f)) n e i W' hW') := by
    apply ContinuousMap.ext; intro q
    apply Prod.ext
    · apply Subtype.ext
      show (realification Z).proj ((pieceMapR Z f hWf q) : (realification Z).TotalSpace)
        = (g ((chartHomeo (realification (bundleComap Z f)) n e i W' hW') q).1 : B)
      rw [pieceMapR_apply, hg]
      rfl
    · show e ((realification Z).coordChange ((realification Z).indexAt
            ((pieceMapR Z f hWf q) : (realification Z).TotalSpace).1) i
            ((pieceMapR Z f hWf q) : (realification Z).TotalSpace).1
            ((pieceMapR Z f hWf q) : (realification Z).TotalSpace).2)
        = e ((realification (bundleComap Z f)).coordChange
            ((realification (bundleComap Z f)).indexAt (q.1.1)) i (q.1.1) (q.1.2))
      rw [pieceMapR_apply]
      simp only [realification_coordChange, realification_indexAt, bundleComap_coordChange,
        bundleComap_indexAt]
  set A := pieceZero (realification (bundleComap Z f)) W' with hA
  set Bs := pieceZero (realification Z) W with hBs
  set C := Punct ↥W n with hC
  set Bp := Punct ↥W' n with hBp
  rw [relCohMap_compA_apply A Bs C
        (pieceMapR Z f hWf) (chartHomeo (realification Z) n e i W hW)
        (pieceMapR_mem Z f hWf) (chartHomeo_mem (realification Z) n e i W hW)
        (fun p hp => chartHomeo_mem (realification Z) n e i W hW (pieceMapR Z f hWf p)
          (pieceMapR_mem Z f hWf p hp)) ℤ n (Mpun n ↥W)]
  rw [relCohMap_congrA A C hcomp
        (fun p hp => chartHomeo_mem (realification Z) n e i W hW (pieceMapR Z f hWf p)
          (pieceMapR_mem Z f hWf p hp))
        (fun p hp => chartHomeo_mem (realification (bundleComap Z f)) n e i W' hW' p hp) ℤ n]
  rw [← relCohMap_compA_apply A Bp C
        (chartHomeo (realification (bundleComap Z f)) n e i W' hW') (baseMap g n)
        (chartHomeo_mem (realification (bundleComap Z f)) n e i W' hW')
        (fun p hp => hp)
        (fun p hp => chartHomeo_mem (realification (bundleComap Z f)) n e i W' hW' p hp) ℤ n
        (Mpun n ↥W)]
  rw [show (relCohMap (baseMap g n) Bp C (fun p hp => hp) ℤ n).hom
        (Mpun n ↥W) = Mpun n ↥W' from Mpun_natural_map g]

end

end Work.Thom
