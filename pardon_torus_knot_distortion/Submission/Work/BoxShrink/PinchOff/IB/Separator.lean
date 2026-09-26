import Mathlib
import Submission.Work.Smooth.JordanSeparation.exists_continuum_separating
import Submission.Work.Smooth.JordanSeparation.ComplHelpers
import Submission.Work.BoxShrink.Pinch.isPreconnected_frontier_of_compl_preconnected

/-!
# At most one unbounded complementary domain

If `Z ⊆ ℂ` is closed and every connected component of `Z` is compact, then `Zᶜ` has at most one
unbounded component.  This is proved by the Phragmén–Brouwer argument (via the minimal closed
preconnected separator `separator_of_closed`): two points of distinct unbounded components would
be separated by a closed preconnected `C ⊆ Z`; `C` lies in a component of `Z`, hence is compact,
so points of `Zᶜ` far away lie in one component of `Cᶜ`, and the two components would meet.
-/

open Set Metric
open scoped Topology

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The irreducible preconnected separator.**  If a closed set `K` separates `p` from `q`, then
`K` contains a closed preconnected subset that still separates them.

(This is `Work.JordanSeparation.exists_preconnected_separator_of_closed`, reproduced here because
the module containing it imports a source file which is no longer present in this workspace.) -/
theorem separator_of_closed {K : Set ℂ} (hK : IsClosed K) {p q : ℂ}
    (hp : p ∉ K) (hq : q ∉ K) (hsep : q ∉ connectedComponentIn Kᶜ p) :
    ∃ C : Set ℂ, C ⊆ K ∧ IsClosed C ∧ IsPreconnected C ∧ p ∉ C ∧ q ∉ C ∧
      q ∉ connectedComponentIn Cᶜ p := by
  set SS : Set (Set ℂ) := {L | L ⊆ K ∧ IsClosed L ∧ q ∉ connectedComponentIn Lᶜ p} with hSS
  have hKmem : K ∈ SS := ⟨subset_rfl, hK, hsep⟩
  have hchain : ∀ c ⊆ SS, IsChain (fun x1 x2 : Set ℂ => x1 ⊆ x2) c →
      ∃ lb ∈ SS, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hneC
    · exact ⟨K, hKmem, by simp⟩
    · obtain ⟨s0, hs0⟩ := hneC
      have hs0SS : s0 ∈ SS := hc hs0
      exact ⟨⋂₀ c, ⟨(sInter_subset_of_mem hs0).trans hs0SS.1,
        isClosed_sInter (fun s hs => (hc hs).2.1),
        Work.Smooth.JordanSeparation.sInter_sep hch (fun s hs => (hc hs).2.1)
          (fun s hs h => hp ((hc hs).1 h)) (fun s hs => (hc hs).2.2) ⟨s0, hs0⟩⟩,
        fun s hs => sInter_subset_of_mem hs⟩
  obtain ⟨L, hLmin⟩ := zorn_superset SS hchain
  have hLK : L ⊆ K := hLmin.1.1
  have hLclosed : IsClosed L := hLmin.1.2.1
  have hLsep : q ∉ connectedComponentIn Lᶜ p := hLmin.1.2.2
  refine ⟨L, hLK, hLclosed, ?_, fun h => hp (hLK h), fun h => hq (hLK h), hLsep⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hnu, hnv⟩ := hc
  have hAc : IsClosed (L ∩ u) := hLclosed.inter hu
  have hBc : IsClosed (L ∩ v) := hLclosed.inter hv
  have hUnion : (L ∩ u) ∪ (L ∩ v) = L := by
    apply Subset.antisymm
    · rintro z (hz | hz) <;> exact hz.1
    · intro z hz
      rcases huv hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hAB : Disjoint (L ∩ u) (L ∩ v) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hz1.1, hz1.2, hz2.2⟩
  have hAne : (L ∩ u).Nonempty := by
    obtain ⟨z, hzL, hzv⟩ := not_subset.mp hnv
    exact ⟨z, hzL, by rcases huv hzL with h | h; exacts [h, absurd h hzv]⟩
  have hBne : (L ∩ v).Nonempty := by
    obtain ⟨z, hzL, hzu⟩ := not_subset.mp hnu
    exact ⟨z, hzL, by rcases huv hzL with h | h; exacts [absurd h hzu, h]⟩
  have hAproper : L ∩ u ≠ L := by
    intro h
    obtain ⟨z, hzB⟩ := hBne
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z
      ⟨hzB.1, (h.symm ▸ hzB.1 : z ∈ L ∩ u).2, hzB.2⟩
  have hBproper : L ∩ v ≠ L := by
    intro h
    obtain ⟨z, hzA⟩ := hAne
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z
      ⟨hzA.1, hzA.2, (h.symm ▸ hzA.1 : z ∈ L ∩ v).2⟩
  have hAsep : q ∈ connectedComponentIn (L ∩ u)ᶜ p := by
    by_contra h
    exact hAproper (Subset.antisymm (fun z hz => hz.1) (hLmin.2
      ⟨fun z hz => hLK hz.1, hAc, h⟩ (fun z hz => hz.1)))
  have hBsep : q ∈ connectedComponentIn (L ∩ v)ᶜ p := by
    by_contra h
    exact hBproper (Subset.antisymm (fun z hz => hz.1) (hLmin.2
      ⟨fun z hz => hLK hz.1, hBc, h⟩ (fun z hz => hz.1)))
  have hpAB : p ∉ (L ∩ u) ∪ (L ∩ v) := by
    rintro (hz | hz); exacts [hp (hLK hz.1), hp (hLK hz.1)]
  have hcontra := Work.BoxShrink.Pinch.phragmenBrouwer_isClosed hAc hBc hAB hpAB
  have hqmem : q ∈ connectedComponentIn (L ∩ u)ᶜ p ∩ connectedComponentIn (L ∩ v)ᶜ p :=
    ⟨hAsep, hBsep⟩
  rw [hcontra, hUnion] at hqmem
  exact hLsep hqmem

/-- **At most one unbounded complementary domain.**  If `Z ⊆ ℂ` is closed and every connected
component of `Z` is compact, then any two unbounded components of `Zᶜ` are equal. -/
theorem unbounded_component_unique {Z : Set ℂ} (hZ : IsClosed Z)
    (hcomp : ∀ z ∈ Z, IsCompact (connectedComponentIn Z z))
    {x y : ℂ} (hx : x ∉ Z) (hy : y ∉ Z)
    (hbx : ∀ R : ℝ, ∃ w ∈ connectedComponentIn Zᶜ x, R ≤ ‖w‖)
    (hby : ∀ R : ℝ, ∃ w ∈ connectedComponentIn Zᶜ y, R ≤ ‖w‖) :
    connectedComponentIn Zᶜ x = connectedComponentIn Zᶜ y := by
  by_contra hne
  have hsep : y ∉ connectedComponentIn Zᶜ x := fun h => hne (connectedComponentIn_eq h)
  obtain ⟨C, hCZ, hCcl, hCpre, hxC, hyC, hCsep⟩ := separator_of_closed hZ hx hy hsep
  -- `C` lies in a component of `Z`, hence is compact
  have hCne : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with h | h
    · exfalso
      apply hCsep
      rw [h, compl_empty]
      exact (isPreconnected_univ).subset_connectedComponentIn (Set.mem_univ x)
        (by simp) (Set.mem_univ y)
    · exact h
  obtain ⟨c, hcC⟩ := hCne
  have hCcomp : IsCompact C :=
    (hcomp c (hCZ hcC)).of_isClosed_subset hCcl (hCpre.subset_connectedComponentIn hcC hCZ)
  obtain ⟨r, hr⟩ := hCcomp.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨x', hx'mem, hx'far⟩ := hbx (max r 0 + 1)
  obtain ⟨y', hy'mem, hy'far⟩ := hby (max r 0 + 1)
  have hx'Z : x' ∉ Z := connectedComponentIn_subset Zᶜ x hx'mem
  have hy'Z : y' ∉ Z := connectedComponentIn_subset Zᶜ y hy'mem
  have hx'notC : x' ∉ C := fun h => hx'Z (hCZ h)
  have hy'notC : y' ∉ C := fun h => hy'Z (hCZ h)
  -- both far points lie in the exterior of a ball containing `C`
  have hx'gap : max r 0 < ‖x'‖ := by linarith [hx'far]
  have hy'gap : max r 0 < ‖y'‖ := by linarith [hy'far]
  have hpre : IsPreconnected {z : ℂ | max r 0 < ‖z‖} :=
    Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl (max r 0) (le_max_right r 0)
  have hsub : {z : ℂ | max r 0 < ‖z‖} ⊆ Cᶜ := by
    intro z hz
    simp only [Set.mem_ofPred_eq, mem_compl_iff] at hz ⊢
    intro hzC
    have h1 : ‖z‖ ≤ r := by
      have h2 := hr hzC
      rwa [mem_closedBall, dist_zero_right] at h2
    have h3 : r ≤ max r 0 := le_max_left r 0
    linarith
  have hx'C : x' ∈ connectedComponentIn Cᶜ x :=
    connectedComponentIn_mono x (compl_subset_compl.mpr hCZ) hx'mem
  have hy'C : y' ∈ connectedComponentIn Cᶜ y :=
    connectedComponentIn_mono y (compl_subset_compl.mpr hCZ) hy'mem
  have hsame : connectedComponentIn Cᶜ x' = connectedComponentIn Cᶜ y' := by
    have h := hpre.subset_connectedComponentIn (show x' ∈ {z : ℂ | max r 0 < ‖z‖} from hx'gap)
      hsub (show y' ∈ {z : ℂ | max r 0 < ‖z‖} from hy'gap)
    exact connectedComponentIn_eq h
  have hxy' : connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ y' := by
    rw [connectedComponentIn_eq hx'C, hsame]
  have hyin : y ∈ connectedComponentIn Cᶜ x := by
    have h1 : y ∈ connectedComponentIn Cᶜ y' := by
      rw [← connectedComponentIn_eq hy'C]
      exact mem_connectedComponentIn hyC
    rwa [← hxy'] at h1
  exact hCsep hyin

end

end Work.BoxShrink.PinchOff
