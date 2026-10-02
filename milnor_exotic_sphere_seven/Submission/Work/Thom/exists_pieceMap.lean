import Mathlib
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Basic
import Submission.Work.Thom.exists_punctMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The restricted total-space map of a bundle morphism over `f`

Given a real vector bundle `Z` over `B` (gluing data) and a continuous map `f : C(B', B)`,
the pullback bundle `bundleComap Z f` maps to `Z` by `⟨x, v⟩ ↦ ⟨f x, v⟩`, and this map is
continuous (`Work.Thom.continuous_totalSpaceMap`).  If `W' ⊆ B'` is carried by `f` into `W ⊆ B`,
then that map restricts to a continuous map
`(bundleComap Z f).proj ⁻¹' W' → Z.proj ⁻¹' W`, which is what this module records
(`Work.Thom.exists_pieceMap`).
-/

namespace Work.Thom

open Bundle

noncomputable section

theorem exists_pieceMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (f : C(B', B)) {W : Set B} {W' : Set B'} (hWf : ∀ x ∈ W', f x ∈ W) :
    ∃ Fm : C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'), ↥(Z.proj ⁻¹' W)),
      ∀ p : ↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
        (Fm p : Z.TotalSpace) = (⟨f p.1.1, p.1.2⟩ : Z.TotalSpace) := by
  have hbase : ∀ i : ι, (bundleComap Z f).baseSet i = f ⁻¹' Z.baseSet i :=
    fun i => bundleComap_baseSet Z f i
  have hcoord : ∀ (x : B') (i : ι),
      (bundleComap Z f).coordChange ((bundleComap Z f).indexAt x) i x
        = Z.coordChange (Z.indexAt (f x)) i (f x) := by
    intro x i
    rw [bundleComap_coordChange, bundleComap_indexAt]
  have hg : Continuous (fun p : (bundleComap Z f).TotalSpace =>
      (⟨f p.1, p.2⟩ : Z.TotalSpace)) :=
    continuous_totalSpaceMap _ _ f hbase hcoord
  have hmem : ∀ q : ↥((bundleComap Z f).proj ⁻¹' W'),
      (⟨f q.1.1, q.1.2⟩ : Z.TotalSpace) ∈ Z.proj ⁻¹' W := by
    intro q
    exact hWf q.1.1 q.2
  refine ⟨⟨fun q => ⟨(⟨f q.1.1, q.1.2⟩ : Z.TotalSpace), hmem q⟩, ?_⟩, ?_⟩
  · exact (hg.comp continuous_subtype_val).subtype_mk hmem
  · intro q
    rfl

end

end Work.Thom
