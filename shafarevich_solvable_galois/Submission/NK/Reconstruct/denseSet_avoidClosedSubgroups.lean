import Mathlib
import Submission.NK.Reconstruct.exists_notMem_iUnion_closedSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A dense set meets the complement of a finite union of non-open closed subgroups

This file isolates the purely topological half of the measure argument of Shimizu's
Proposition 4f.3 (arXiv:2009.10431, §4): if `H_i ≤ G` are finitely many closed subgroups of a
compact Hausdorff topological group which are *not open*, then the union `⋃ H_i` has empty interior
(it is a finite union of closed sets with empty interior), hence its complement is a non-empty open
set, hence meets every dense subset of `G`.

The engine of the union statement is `NK.Reconstruct.exists_notMem_iUnion_closedSubgroup` (a
Baire-category argument, already proved in this area).

In Shimizu's argument one takes `G = Γ_L`, `H_τ = ker(φ_τ)` for the finitely many
`τ ∈ G(L/ℚ)` (finitely many because `L/ℚ` is finite), and for the dense set the image of the
Frobenius elements of `Gal(Ω/L)` in `Γ_L`; the conclusion is a prime `𝔭` whose Frobenius element
avoids all the kernels, which is the contradiction producing the `τ` of Proposition 4f.3.
-/

namespace NK.Reconstruct

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G]

/-- **A dense subset of a compact Hausdorff group meets the complement of a finite union of
non-open closed subgroups.** -/
theorem exists_mem_dense_notMem_iUnion_closedSubgroup {ι : Type*} [Finite ι]
    (H : ι → Subgroup G) (hcl : ∀ i, IsClosed (H i : Set G))
    (h : ∀ i, ¬ IsOpen (H i : Set G)) {D : Set G} (hD : Dense D) :
    ∃ d ∈ D, ∀ i, d ∉ H i := by
  obtain ⟨g, hg⟩ := exists_notMem_iUnion_closedSubgroup H hcl h
  have hnotmem : g ∉ ⋃ i, (H i : Set G) := by
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact hg i hi
  have hopen : IsOpen (⋃ i, (H i : Set G))ᶜ := (isClosed_iUnion_of_finite hcl).isOpen_compl
  obtain ⟨d, hdD, hd⟩ := hD.exists_mem_open hopen ⟨g, hnotmem⟩
  exact ⟨d, hdD, fun i hdi => hd (Set.mem_iUnion.mpr ⟨i, hdi⟩)⟩

/-- The version for a finite family of closed subgroups indexed by a `Finset` of an arbitrary
index type: this is the form in which Shimizu's Proposition 4f.3 uses it (the finitely many
`τ ∈ G(L/ℚ)`). -/
theorem exists_mem_dense_notMem_finset_iUnion_closedSubgroup {ι : Type*} (s : Finset ι)
    (H : ι → Subgroup G) (hcl : ∀ i, IsClosed (H i : Set G))
    (h : ∀ i, ¬ IsOpen (H i : Set G)) {D : Set G} (hD : Dense D) :
    ∃ d ∈ D, ∀ i ∈ s, d ∉ H i := by
  classical
  haveI : Finite {i // i ∈ s} := s.finite_toSet
  obtain ⟨d, hdD, hd⟩ := exists_mem_dense_notMem_iUnion_closedSubgroup
    (fun i : {i // i ∈ s} => H i.1) (fun i => hcl i.1) (fun i => h i.1) hD
  exact ⟨d, hdD, fun i hi => hd ⟨i, hi⟩⟩

namespace Subgroup

/-- **The kernel form.**  For finitely many group homomorphisms out of a compact Hausdorff group
whose kernels are all non-open and closed, a dense subset contains an element avoiding all the
kernels. -/
theorem exists_mem_dense_notMem_iUnion_ker {ι : Type*} [Finite ι] {G H' : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [Group H'] (φ : ι → G →* H') (hcl : ∀ i, IsClosed ((φ i).ker : Set G))
    (h : ∀ i, ¬ IsOpen ((φ i).ker : Set G)) {D : Set G} (hD : Dense D) :
    ∃ d ∈ D, ∀ i, φ i d ≠ 1 := by
  obtain ⟨d, hdD, hd⟩ := exists_mem_dense_notMem_iUnion_closedSubgroup
    (fun i => (φ i).ker) hcl h hD
  exact ⟨d, hdD, fun i => by simpa using hd i⟩

end Subgroup

end NK.Reconstruct
