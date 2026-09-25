import Mathlib
import Submission.Work.CFT.MaxProP.ContCohomology.Burnside.exists_openNormalSubgroup_sup_ne_top

namespace Work.CFTLib.ProP

/-- If `G` is a profinite group (compact, Hausdorff, totally disconnected) and `Φ ≤ G` is a closed
normal subgroup such that every open normal subgroup `N` containing `Φ` has bounded index
`N.index ≤ M`, then the quotient `G ⧸ Φ` is finite.

The proof picks an open normal subgroup `N₀ ⊇ Φ` of maximal index `m`; for any open normal `N ⊇ Φ`
the intersection `N ⊓ N₀` again has index `m`, which forces `N₀ ≤ N`. Since open normal subgroups
of a profinite group separate points (a closed subgroup is the intersection of the open subgroups
containing it), this yields `N₀ ≤ Φ`, hence `Φ = N₀` has finite index and `G ⧸ Φ` is finite. -/
theorem finite_quotient_of_forall_index_le (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (Φ : Subgroup G) [Φ.Normal] (hΦ : IsClosed (Φ : Set G)) (M : ℕ)
    (h : ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → Φ ≤ N → N.index ≤ M) :
    Finite (G ⧸ Φ) := by
  rw [← Subgroup.index_ne_zero_iff_finite]
  -- The family of open normal subgroups containing `Φ`.
  let fam : Set (Subgroup G) := {N | N.Normal ∧ IsOpen (N : Set G) ∧ Φ ≤ N}
  have htop : (⊤ : Subgroup G) ∈ fam := by
    refine ⟨Subgroup.normal_top, ?_, ?_⟩ <;> simp
  -- The set of indices of members of `fam` is finite (bounded by `M`).
  have hfin : (Subgroup.index '' fam).Finite := by
    refine Set.Finite.subset (Set.finite_Iic M) ?_
    rintro n ⟨N, hN, rfl⟩
    exact h N hN.1 hN.2.1 hN.2.2
  -- Choose `N₀ ∈ fam` of maximal index.
  obtain ⟨N₀, hmem, hmax⟩ := Set.Finite.exists_maximalFor' Subgroup.index fam hfin ⟨⊤, htop⟩
  have hN₀norm : N₀.Normal := hmem.1
  have hN₀open : IsOpen (N₀ : Set G) := hmem.2.1
  have hΦN₀ : Φ ≤ N₀ := hmem.2.2
  have hN₀idx : N₀.index ≠ 0 :=
    Subgroup.index_ne_zero_iff_finite.mpr (Subgroup.quotient_finite_of_isOpen N₀ hN₀open)
  have hmax' : ∀ N, N ∈ fam → N.index ≤ N₀.index := by
    intro N hN
    rcases le_total N₀.index N.index with hle | hle
    · exact hmax hN hle
    · exact hle
  -- `N₀` is contained in every other member of `fam`.
  have hle_all : ∀ N, N ∈ fam → N₀ ≤ N := by
    intro N hN
    have hopen : IsOpen ((N ⊓ N₀ : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]; exact hN.2.1.inter hN₀open
    have hmem' : N ⊓ N₀ ∈ fam :=
      ⟨@Subgroup.normal_inf_normal G _ N N₀ hN.1 hN₀norm, hopen, le_inf hN.2.2 hΦN₀⟩
    have h1 : (N ⊓ N₀).index ≤ N₀.index := hmax' (N ⊓ N₀) hmem'
    have hinfidx : (N ⊓ N₀).index ≠ 0 :=
      Subgroup.index_ne_zero_iff_finite.mpr (Subgroup.quotient_finite_of_isOpen (N ⊓ N₀) hopen)
    have hrel : (N ⊓ N₀).relIndex N₀ * N₀.index = (N ⊓ N₀).index :=
      Subgroup.relIndex_mul_index inf_le_right
    have hrelpos : 0 < (N ⊓ N₀).relIndex N₀ := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hinfidx (by rw [← hrel, h0, zero_mul])
    have h2 : N₀.index ≤ (N ⊓ N₀).index := by
      rw [← hrel]
      exact Nat.le_mul_of_pos_left _ hrelpos
    have heq : (N ⊓ N₀).index = N₀.index := le_antisymm h1 h2
    have hrelone : (N ⊓ N₀).relIndex N₀ = 1 := by
      have hh : (N ⊓ N₀).relIndex N₀ * N₀.index = 1 * N₀.index := by
        rw [hrel, heq, one_mul]
      exact mul_right_cancel₀ hN₀idx hh
    exact (le_inf_iff.mp ((Subgroup.relIndex_eq_one).mp hrelone)).1
  -- Open normal subgroups separate points, so `N₀ ⊆ Φ`.
  have hN₀leΦ : N₀ ≤ Φ := by
    intro x hx
    by_contra hxΦ
    obtain ⟨N, hNx⟩ :=
      Work.CFT.MaxProP.ContCohomology.Burnside.exists_openNormalSubgroup_sup_ne_top hΦ hxΦ
    have hmemN : (Φ ⊔ (N.toOpenSubgroup : Subgroup G)) ∈ fam := by
      refine ⟨Subgroup.sup_normal Φ (N.toOpenSubgroup : Subgroup G), ?_, le_sup_left⟩
      exact Subgroup.isOpen_mono le_sup_right N.toOpenSubgroup.isOpen
    exact hNx (hle_all _ hmemN hx)
  have hN₀eq : N₀ = Φ := le_antisymm hN₀leΦ hΦN₀
  rw [← hN₀eq]
  exact hN₀idx

end Work.CFTLib.ProP
