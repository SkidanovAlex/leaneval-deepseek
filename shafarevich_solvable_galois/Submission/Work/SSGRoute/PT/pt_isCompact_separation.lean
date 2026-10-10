import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Connected.Separation
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.Work.SSGRoute.PT.pt_restrictedPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped RestrictedProduct

/-- In a product of topological spaces, an open neighbourhood of a point contains a "finite
cylinder" around that point: there are finitely many coordinates such that every point agreeing
with `f` on those coordinates still lies in the neighbourhood. -/
lemma exists_finset_pi_singleton_subset {ι : Type*} {A : ι → Type*}
    [∀ i, TopologicalSpace (A i)] {s : Set (∀ i, A i)} (hs : IsOpen s) {f : ∀ i, A i}
    (hf : f ∈ s) :
    ∃ I : Finset ι, (I : Set ι).pi (fun i => {f i}) ⊆ s := by
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hs f hf
  exact ⟨I, (Set.pi_mono fun i hi => by
    rw [Set.singleton_subset_iff]; exact (hu i hi).2).trans hIu⟩

/-- **A compact subset of a restricted product is separated from an outside point by finitely many
coordinates.**  If `B ⊆ Πʳ i, [Y i, U' i]` is compact (restricted-product topology; the `Y i` are
discrete) and `y ∉ B`, then there is a finite set `F` of indices such that no `b ∈ B` agrees with
`y` on all of `F`.  Equivalently `y` is not in the closure of `B` for the coarser topology induced
from the full product `∏ i, Y i`. -/
theorem pt_isCompact_separation
    (p : ℕ) [Fact p.Prime] {ι : Type*} {Y : ι → Type*}
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)]
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)]
    (U' : ∀ i, Submodule (ZMod p) (Y i))
    {B : Set (Πʳ i, [Y i, U' i])} (hB : IsCompact B)
    {y : Πʳ i, [Y i, U' i]} (hy : y ∉ B) :
    ∃ F : Finset ι, ∀ b ∈ B, ∃ i ∈ F, (b i : Y i) ≠ y i := by
  classical
  -- The continuous projection of the restricted product onto the full product.  Compactness of `B`
  -- in the (finer) restricted-product topology makes its image in the (Hausdorff) full product
  -- compact, hence closed, so `B` is separated from `y` by a finite cylinder.
  have hf : Continuous (DFunLike.coe : (Πʳ i, [Y i, U' i]) → Π i, Y i) :=
    RestrictedProduct.continuous_coe
  have hBimg : IsCompact (DFunLike.coe '' B) := hB.image hf
  have hyimg : (DFunLike.coe y) ∉ DFunLike.coe '' B := by
    rintro ⟨b, hb, hby⟩
    exact hy (DFunLike.coe_injective hby ▸ hb)
  obtain ⟨F, hF⟩ := exists_finset_pi_singleton_subset hBimg.isClosed.isOpen_compl hyimg
  refine ⟨F, fun b hb => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : DFunLike.coe b ∈ DFunLike.coe '' B := ⟨b, hb, rfl⟩
  have hnot : DFunLike.coe b ∈ (DFunLike.coe '' B)ᶜ := by
    apply hF
    rw [Set.mem_pi]
    intro i hi
    rw [Set.mem_singleton_iff]
    exact hcon i (Finset.mem_coe.mp hi)
  exact hnot hmem

end Work.SSGRoute.PT
