import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- Given `2 ≤ r ≤ Fintype.card ι` and `ℤ`-linearly independent vectors `x, y : ι → ℤ`, there is a
rank-`r` sublattice of `ℤ^ι` containing both `x` and `y`.

Route (Smith normal form; concrete). Let `N := Submodule.span ℤ ({x, y} : Set (ι → ℤ))`, of rank `2`
(`Module.Basis.span` applied to the `ℤ`-independent family `![x, y]`, plus
`Module.finrank_eq_card_basis`). Apply `Submodule.smithNormalForm (Pi.basisFun ℤ ι) N`, which
provides a basis `bM` of `ℤ^ι`, a basis `bN` of `N`, an embedding `f : Fin n ↪ ι` with `n = 2`
(use `Module.finrank_eq_card_basis bN` and `rk N = 2`) and nonzero `a : Fin n → ℤ` such that
`(bN i : ι → ℤ) = a i • bM (f i)`.

Since `Fintype.card ι ≥ r` and `Set.range f` has `2 ≤ r` elements, choose a Finset
`s ⊆ Finset.univ \ Set.range f` with `s.card = r - 2` (e.g. by `Finset.exists_subset_card_eq`), and
set `S := s ∪ {f 0, f 1}` (a Finset of cardinality `r`). Put
`L := Submodule.span ℤ (Set.range fun j : {j // j ∈ S} => (bM j.1 : ι → ℤ))`.
The family `bM ∘ (↑)` is `ℤ`-independent (subfamily of a basis), so `Module.Basis.span` exhibits a
basis of `L` indexed by `{j // j ∈ S}`, and `Module.finrank_eq_card_basis` gives
`rk L = Fintype.card {j // j ∈ S} = S.card = r`. Finally `x, y ∈ L`: both lie in
`N = span{bN 0, bN 1} ⊆ span{bM (f 0), bM (f 1)} ⊆ L` (each `bN i` is a nonzero multiple of
`bM (f i)`), and `f 0, f 1 ∈ S`.

An alternative route is to work in the `ℚ`-vector space `ι → ℚ`, extend `{x, y}` (`ℚ`-independent by
`linearIndependent_algebraMap_comp_iff`) to a basis with `LinearIndepOn.extend`/`Module.Basis.extend`,
take any `r - 2` further basis elements, clear denominators to land in `ℤ^ι`, and use that the
resulting `ℤ`-independent family of integer vectors spans a rank-`r` lattice
(`Module.Basis.span`); to descend from `ℚ`- to `ℤ`-independence use that `Pi.algebraMap ι ℤ ℚ` is
`ℤ`-linear (`LinearIndependent.of_comp`) and `LinearIndependent.restrict_scalars' ℤ`. -/
theorem exists_sub_lat_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (x y : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) (hr : 2 ≤ r) (hrN : r ≤ Fintype.card ι) :
    ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ x ∈ L ∧ y ∈ L := by
  classical
  let z : Fin 2 → (ι → ℤ) := ![x, y]
  have hz : LinearIndependent ℤ z := hxy
  let N : Submodule ℤ (ι → ℤ) := Submodule.span ℤ (Set.range z)
  have hfinN : Module.finrank ℤ N = 2 := by
    have := Module.finrank_eq_card_basis (Module.Basis.span hz)
    simpa [N] using this
  obtain ⟨n, snf⟩ := N.smithNormalForm (Pi.basisFun ℤ ι)
  have hn : n = 2 := by
    have h1 : Module.finrank ℤ N = n := by
      have := Module.finrank_eq_card_basis snf.bN
      simpa using this
    omega
  let A : Finset ι := Finset.univ.image snf.f
  have hA : A.card = 2 := by
    rw [Finset.card_image_of_injective Finset.univ snf.f.injective, Finset.card_univ]
    simp [hn]
  let U : Finset ι := Finset.univ \ A
  have hU : r - 2 ≤ U.card := by
    change r - 2 ≤ (Finset.univ \ A).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]
    omega
  obtain ⟨s, hsU, hscard⟩ := Finset.exists_subset_card_eq hU
  let S : Finset ι := A ∪ s
  have hdisj : Disjoint A s := by
    rw [Finset.disjoint_left]
    intro a ha has
    exact (Finset.mem_sdiff.mp (hsU has)).2 ha
  have hScard : S.card = r := by
    change (A ∪ s).card = r
    rw [Finset.card_union_of_disjoint hdisj, hA, hscard]
    omega
  have hfS : ∀ i : Fin n, snf.f i ∈ S := fun i =>
    Finset.mem_union_left s (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let v : ↥S → (ι → ℤ) := fun j => (snf.bM j.1 : ι → ℤ)
  have hv : LinearIndependent ℤ v :=
    snf.bM.linearIndependent.comp Subtype.val Subtype.val_injective
  let L : Submodule ℤ (ι → ℤ) := Submodule.span ℤ (Set.range v)
  have hLrank : rk L = r := by
    rw [rk]
    change Module.finrank ℤ ↥(Submodule.span ℤ (Set.range v)) = r
    rw [Module.finrank_eq_card_basis (Module.Basis.span hv), Fintype.card_coe, hScard]
  have hgen : ∀ i : Fin n, (snf.bN i : ι → ℤ) ∈ L := by
    intro i
    have hmem : snf.bM (snf.f i) ∈ L := by
      apply Submodule.subset_span
      exact Set.mem_range_self (⟨snf.f i, hfS i⟩ : ↥S)
    rw [snf.snf i]
    exact Submodule.smul_mem _ _ hmem
  have hN_eq : N = Submodule.span ℤ (Set.range fun i : Fin n => (snf.bN i : ι → ℤ)) := by
    conv_lhs => rw [← Submodule.map_subtype_top N]
    rw [← Module.Basis.span_eq snf.bN, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      rcases hc with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨snf.bN i, ⟨i, rfl⟩, rfl⟩
  have hN_le_L : N ≤ L := by
    rw [hN_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hxN : x ∈ N := by
    apply Submodule.subset_span
    exact Set.mem_range_self 0
  have hyN : y ∈ N := by
    apply Submodule.subset_span
    exact Set.mem_range_self 1
  exact ⟨L, hLrank, hN_le_L hxN, hN_le_L hyN⟩

end Work.HP
