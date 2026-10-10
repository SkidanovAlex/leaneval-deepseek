import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructureDeep.Degree.zhat_existsUnique_compHomZMod_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Degree

noncomputable section

/-- **The comparison map of `Ẑ` with the product of its finite quotients**, sending `z` to the
family of all its components `compHomZMod d hd z`. -/
def zhatCompMap (z : NK.LocalAnabelian.Zhat) :
    ∀ d : {d : ℕ // d ≠ 0}, Multiplicative (ZMod d) :=
  fun d => compHomZMod d.1 d.2 z

/-- The comparison map is continuous: it is the product of the continuous component maps. -/
theorem continuous_zhatCompMap : Continuous zhatCompMap :=
  continuous_pi fun d => continuous_compHomZMod d.1 d.2

/-- The comparison map is injective: the components separate the points of `Ẑ`. -/
theorem injective_zhatCompMap : Function.Injective zhatCompMap :=
  fun _ _ hz => eq_of_compHomZMod_eq _ _ fun d hd => congrFun hz ⟨d, hd⟩

/-- **The topology of `Ẑ` is the topology induced by its components.**  The comparison map is a
closed embedding, because `Ẑ` is compact, the product of the finite quotients `ℤ ⧸ dℤ` is
Hausdorff, and the comparison map is a continuous injection. -/
theorem isClosedEmbedding_zhatCompMap : Topology.IsClosedEmbedding zhatCompMap :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_zhatCompMap
    injective_zhatCompMap continuous_zhatCompMap.isClosedMap

/-- The topology of `Ẑ` is induced by its components. -/
theorem isInducing_zhatCompMap : Topology.IsInducing zhatCompMap :=
  isClosedEmbedding_zhatCompMap.isInducing

/-- **Continuity into `Ẑ` is tested on the components.**  A map `f : X → Ẑ` is continuous as
soon as every composite `x ↦ compHomZMod d hd (f x)` (`d ≠ 0`) is continuous. -/
theorem continuous_of_continuous_compHomZMod
    {X : Type*} [TopologicalSpace X]
    (f : X → NK.LocalAnabelian.Zhat)
    (h : ∀ (d : ℕ) (hd : d ≠ 0),
      Continuous (fun x => NK.TameStructureDeep.Degree.compHomZMod d hd (f x))) :
    Continuous f := by
  rw [isInducing_zhatCompMap.continuous_iff]
  show Continuous fun x => fun d : {d : ℕ // d ≠ 0} =>
    NK.TameStructureDeep.Degree.compHomZMod d.1 d.2 (f x)
  exact continuous_pi fun d => h d.1 d.2

end

end NK.TameStructureDeep.Degree
