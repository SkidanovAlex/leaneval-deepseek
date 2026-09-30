import Mathlib
import Submission.Work.Serre.ThomCylDefs

/-!
# The restriction of a Serre fibration to the preimage of a subset

`Work.Serre.restrictFibre q S : C(↥(q ⁻¹' S), ↥S)` is the map induced by `q` on the preimage of a
subset `S` of the base (see `Submission/Work/Serre/ThomCylDefs.lean`).  Here we prove that it is a
Serre fibration whenever `q` is.

This is the pullback (base change) of `q` along the inclusion `S ↪ Γ`, read in the equivalent
"preimage" form: the fibre product `{x : X × ↥S // q x.1 = ↑x.2}` is homeomorphic to `q ⁻¹' S`
(the second coordinate is determined).  Direct proof: given a homotopy `H` in `↥S` and a lift `f`
of its initial map to `q ⁻¹' S`, compose both with the inclusions `↥S ↪ Γ`, `q ⁻¹' S ↪ X` and apply
the homotopy lifting property of `q`; the resulting lift `H''` lands in `q ⁻¹' S` at every time
because `q (H'' (t,z)) = ↑(H (t,z)) ∈ S`.
-/

open scoped Topology unitInterval

namespace Work.Serre

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

theorem isSerreFibration_restrictFibre {X : Type} [TopologicalSpace X] {Γ : Type}
    [TopologicalSpace Γ] (q : C(X, Γ)) (hq : Work.StemsB.IsSerreFibration q) (S : Set Γ) :
    Work.StemsB.IsSerreFibration (Work.Serre.restrictFibre q S) := by
  intro n f b H
  obtain ⟨g', H'', heq⟩ :=
    hq n ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(q ⁻¹' S), X)).comp f)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, Γ)).comp b)
      { toContinuousMap := (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, Γ)).comp H.toContinuousMap
        map_zero_left := fun z => by
          show Subtype.val (H.toContinuousMap (0, z)) =
            q (((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(q ⁻¹' S), X)).comp f) z)
          have h : H.toContinuousMap (0, z) = ((restrictFibre q S).comp f) z := H.map_zero_left z
          rw [h]
          rfl
        map_one_left := fun z => by
          show Subtype.val (H.toContinuousMap (1, z)) =
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, Γ)).comp b) z
          have h : H.toContinuousMap (1, z) = b z := H.map_one_left z
          rw [h]
          rfl }
  have hkey : ∀ zt : ↑I × (Fin n → I), q (H''.toContinuousMap zt) = H.toContinuousMap zt :=
    fun zt => ContinuousMap.congr_fun heq zt
  have hmem : ∀ zt : ↑I × (Fin n → I), q (H''.toContinuousMap zt) ∈ S := by
    intro zt
    have h3 : q (H''.toContinuousMap zt) = H.toContinuousMap zt := hkey zt
    change q (H''.toContinuousMap zt) ∈ S
    rw [h3]
    exact (H.toContinuousMap zt).2
  have hz0 : ∀ z : Fin n → I, q (g' z) ∈ S := by
    intro z
    have h1 : H''.toContinuousMap (1, z) = g' z := H''.map_one_left z
    have h3 : q (H''.toContinuousMap (1, z)) = H.toContinuousMap (1, z) := hkey (1, z)
    have h2 : H.toContinuousMap (1, z) = b z := H.map_one_left z
    change q (g' z) ∈ S
    rw [← h1, h3, h2]
    exact (b z).2
  refine ⟨⟨fun z => ⟨g' z, hz0 z⟩, Continuous.subtype_mk g'.continuous hz0⟩,
    ⟨⟨fun zt => ⟨H''.toContinuousMap zt, hmem zt⟩, Continuous.subtype_mk H''.continuous hmem⟩,
      ?_, ?_⟩, ?_⟩
  · intro z
    refine Subtype.ext ?_
    change H''.toContinuousMap (0, z) = (f z).1
    have h1 : H''.toContinuousMap (0, z) =
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(q ⁻¹' S), X)).comp f) z := H''.map_zero_left z
    rw [h1]
    rfl
  · intro z
    refine Subtype.ext ?_
    change H''.toContinuousMap (1, z) = (g' z)
    have h1 : H''.toContinuousMap (1, z) = g' z := H''.map_one_left z
    rw [h1]
  · ext zt
    exact hkey zt

end Work.Serre
