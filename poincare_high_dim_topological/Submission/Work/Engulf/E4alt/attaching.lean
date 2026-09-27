import Mathlib
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic

namespace Work.Engulf.E4alt

/-- **Attaching lemma for the `E4` shelling.**

Given the shelling data `ord` of `Γ₁` (each `ord[j]` a face of `Γ₁`, all of the common
cardinality `(τ₀ ∪ τ₁).card`) together with the splitting hypothesis `hsplit` expressing the
intersection of `simp (ord[i])` with the already shelled part
`floorOf τ₀ τ₁ ∪ ⋃_{j<i} simp (ord[j])` as a union of facets of `ord[i]`, each such facet is
contained in the region already engulfed after `i` steps, namely `K` together with the union of
the boundaries `⋃_{w'} simp (ord[j].erase w')` of the previous shelling simplices.

The point is that this is *not* immediate from `hsplit`: a point of one of the attaching facets
lies either in `floorOf τ₀ τ₁ = K ∩ simp (τ₀ ∪ τ₁)` (by `H7.meetK`), hence in `K`, or in some
`simp (ord[j])` with `j < i`.  In the second case, the intersection with the facet
`simp (ord[i].erase w)` is, by `Work.Engulf.simp_inter`, the simplex on the vertex set
`(ord[i].erase w) ∩ ord[j]`; that vertex set is a *proper* subset of `ord[j]` (the equal
cardinalities `hord2` forbid equality, since `w ∈ ord[i] \ (ord[i].erase w)`), so the simplex
lies in a facet `simp (ord[j].erase v)` of `ord[j]`, i.e. in the boundary of the previous
simplex. -/
theorem attaching {n p q : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {N : ℕ}
    {Γ : PL.Cx N} {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)}
    {ψ : PL.CubeChart n M} {ε : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (ord : List (Finset (PL.E N)))
    (hord1 : ∀ t ∈ ord, t ∈ ND.Γ₁.faces)
    (hord2 : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card)
    (hsplit : ∀ i (hi : i < ord.length), ∃ fl : Finset (PL.E N), fl.Nonempty ∧ fl ⊂ ord[i] ∧
        PL.simp (ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
          ⋃ j ∈ Finset.range i, ⋃ (_ : j < ord.length), PL.simp (ord[j])) =
        ⋃ w ∈ fl, PL.simp (ord[i].erase w))
    {i : ℕ} (hi : i < ord.length) :
    ∃ fl : Finset (PL.E N), fl.Nonempty ∧ fl ⊂ ord[i] ∧
      (∀ w ∈ fl, PL.simp (ord[i].erase w) ⊆ K ∪
        ⋃ j ∈ Finset.range i, ⋃ (_ : j < ord.length),
          ⋃ w' ∈ ord[j], PL.simp (ord[j].erase w')) := by
  obtain ⟨fl, hflne, hflsub, hflsplit⟩ := hsplit i hi
  refine ⟨fl, hflne, hflsub, ?_⟩
  intro w hw
  have hwi : w ∈ ord[i] := hflsub.1 hw
  have hiface : ord[i] ∈ ND.Γ₁.faces := hord1 _ (List.getElem_mem hi)
  have hneerase : (ord[i].erase w).Nonempty :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hwi, hord2 _ (List.getElem_mem hi), H7.card]
      omega)
  have hfaceerase : ord[i].erase w ∈ ND.Γ₁.faces :=
    ND.Γ₁.down_closed hiface (Finset.erase_subset w ord[i]) hneerase
  intro x hx
  -- the point lies in the attaching region described by `hsplit`
  have hxmem : x ∈ PL.simp (ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
      ⋃ j ∈ Finset.range i, ⋃ (_ : j < ord.length), PL.simp (ord[j])) := by
    rw [hflsplit]
    exact Set.mem_iUnion₂.mpr ⟨w, hw, hx⟩
  rw [Set.mem_inter_iff] at hxmem
  rcases hxmem with ⟨_hxsi, hxrest⟩
  rcases hxrest with hxfl | hxW
  · -- in the floor: `floorOf τ₀ τ₁ = K ∩ simp (τ₀ ∪ τ₁)`
    left
    have hxK : x ∈ K ∩ PL.simp (τ₀ ∪ τ₁) := H7.meetK.symm ▸ hxfl
    exact hxK.1
  · -- in a previously shelled simplex `simp (ord[j])`
    right
    obtain ⟨j, hjmem, hxW'⟩ := Set.mem_iUnion₂.mp hxW
    have hjlti : j < i := Finset.mem_range.mp hjmem
    obtain ⟨hjlen, hxj⟩ := Set.mem_iUnion.mp hxW'
    have hjface : ord[j] ∈ ND.Γ₁.faces := hord1 _ (List.getElem_mem hjlen)
    have hxinter : x ∈ PL.simp ((ord[i].erase w) ∩ ord[j]) := by
      rw [← Work.Engulf.simp_inter hfaceerase hjface]
      exact ⟨hx, hxj⟩
    have hρsub : (ord[i].erase w) ∩ ord[j] ⊆ ord[j] := Finset.inter_subset_right
    have hρne : (ord[i].erase w) ∩ ord[j] ≠ ord[j] := by
      intro h
      have hsub : ord[j] ⊆ ord[i].erase w := by rw [← h]; exact Finset.inter_subset_left
      have hcardle : ord[j].card ≤ (ord[i].erase w).card := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hwi, hord2 _ (List.getElem_mem hjlen),
        hord2 _ (List.getElem_mem hi), H7.card] at hcardle
      omega
    have hssub : (ord[i].erase w) ∩ ord[j] ⊂ ord[j] :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hρsub, hρne⟩
    obtain ⟨v, hvj, hvρ⟩ := Finset.exists_of_ssubset hssub
    have hsubev : (ord[i].erase w) ∩ ord[j] ⊆ ord[j].erase v :=
      Finset.subset_erase.mpr ⟨hρsub, hvρ⟩
    have hxv : x ∈ PL.simp (ord[j].erase v) := (Work.Engulf.simp_mono hsubev) hxinter
    exact Set.mem_biUnion hjmem (Set.mem_iUnion.mpr ⟨hjlen, Set.mem_biUnion hvj hxv⟩)

end Work.Engulf.E4alt
