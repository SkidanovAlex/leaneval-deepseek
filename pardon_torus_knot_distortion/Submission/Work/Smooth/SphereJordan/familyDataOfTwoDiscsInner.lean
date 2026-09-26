import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscs
import Submission.Work.Topology.SphereSlicing.exists_rank_of_strict_order

/-!
# `familyDataOfTwoDiscsInner`

The family of `Submission/Work/Smooth/SphereJordan/familyDataOfTwoDiscs.lean` can be chosen so
that the *first* disc of the curve `i` is the one **not** containing the base point `x₀`: this is
the form in which the standard position of a finite family of pairwise disjoint simple closed
curves on the Riemann sphere is consumed downstream (the "inner" disc of each curve).

The proof repeats the construction of `familyDataOfTwoDiscs`, with `e := fun i => (h i).inner x₀`,
so that the identity `F.e i = (h i).inner x₀` holds on the nose.
-/

open Set
open Filter

namespace Work.Smooth.SphereJordan

noncomputable section

open Work.Topology.SphereSlicing

theorem familyDataOfTwoDiscsInner {ι : Type} [Fintype ι] {c : ι → ℝ → RiemannSphere}
    (hs : ∀ i, IsSimpleClosedCurve (c i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j)))
    (h : ∀ i, TwoDiscs (c i)) (x₀ : RiemannSphere) (hx₀ : ∀ i, x₀ ∉ Set.range (c i)) :
    ∃ F : FamilyData c, ∀ i, F.e i = (h i).inner x₀ := by
  classical
  let inn : ι → C(Disc, RiemannSphere) := fun i => (h i).inner x₀
  let out : ι → C(Disc, RiemannSphere) := fun i => (h i).outer x₀
  let U : ι → Set RiemannSphere := fun i => (h i).inSide x₀
  let V : ι → Set RiemannSphere := fun i => (h i).outSide x₀
  let K : ι → Set RiemannSphere := fun i => Set.range (c i)
  have hUopen : ∀ i, IsOpen (U i) := fun i => TwoDiscs.isOpen_inSide (h i) x₀
  have hVopen : ∀ i, IsOpen (V i) := fun i => TwoDiscs.isOpen_outSide (h i) x₀
  have hUdisjK : ∀ i, Disjoint (U i) (K i) := fun i => TwoDiscs.disjoint_inSide_range (h i) x₀
  have hVdisjK : ∀ i, Disjoint (V i) (K i) := fun i => TwoDiscs.disjoint_outSide_range (h i) x₀
  have hUVdisj : ∀ i, Disjoint (U i) (V i) := fun i => TwoDiscs.disjoint_inSide_outSide (h i) x₀
  have hUKV : ∀ i, U i ∪ K i ∪ V i = Set.univ :=
    fun i => TwoDiscs.inSide_union_range_union_outSide (h i) x₀
  have hmem_split : ∀ i x, x ∈ U i ∨ x ∈ K i ∨ x ∈ V i := fun i x =>
    TwoDiscs.inSide_or_range_or_outSide (h i) x₀ x
  have hx0V : ∀ i, x₀ ∈ V i := fun i => TwoDiscs.mem_outSide_self (h i) x₀ (hx₀ i)
  have hVpre : ∀ i, IsPreconnected (V i) := fun i => TwoDiscs.outSide_preconnected (h i) x₀
  have hKpre : ∀ i, IsPreconnected (K i) :=
    fun i => (isConnected_range (hs i).continuous).isPreconnected
  have hKne : ∀ i, (K i).Nonempty := fun i => ⟨c i 0, ⟨0, rfl⟩⟩
  have hfrontier : ∀ i, frontier (V i) = K i := fun i => TwoDiscs.frontier_outSide (h i) x₀
  have hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ K i → x ∈ K j → False :=
    fun i j hij x hx hy => (Set.disjoint_left.mp (hd hij)) hx hy
  have hdisjV : ∀ i x, x ∈ U i → x ∈ V i → False :=
    fun i x hu hv => (Set.disjoint_left.mp (hUVdisj i)) hu hv
  let R : ι → ι → Prop := fun i j => ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ inn i z ∈ K j
  have hirr : ∀ i, ¬ R i i := by
    intro i hRi
    obtain ⟨z, hz, hzK⟩ := hRi
    exact (Set.disjoint_left.mp (hUdisjK i)) ⟨z, hz, rfl⟩ hzK
  -- a curve meeting the inner disc of `i` lies wholly in it
  have hKsub : ∀ i j, R i j → K j ⊆ U i := by
    intro i j hij
    have hijne : i ≠ j := fun h => hirr i (h.symm ▸ hij)
    refine IsPreconnected.subset_left_of_subset_union (hUopen i) (hVopen i)
      (hUVdisj i) ?_ ?_ (hKpre j)
    · intro x hx
      rcases hmem_split i x with h1 | h1 | h1
      · exact Or.inl h1
      · exact (hdisj i j hijne x h1 hx).elim
      · exact Or.inr h1
    · obtain ⟨z, hz, hzK⟩ := hij
      exact ⟨inn i z, hzK, ⟨z, hz, rfl⟩⟩
  -- the key geometric lemma
  have hM : ∀ i j, K j ⊆ U i → V i ⊆ V j := by
    intro i j hKj
    refine IsPreconnected.subset_left_of_subset_union (hVopen j) (hUopen j)
      (hUVdisj j).symm ?_ ?_ (hVpre i)
    · intro x hx
      rcases hmem_split j x with h1 | h1 | h1
      · exact Or.inr h1
      · exact (hdisjV i x (hKj h1) hx).elim
      · exact Or.inl h1
    · exact ⟨x₀, hx0V i, hx0V j⟩
  -- mutual nesting is impossible
  have hanti : ∀ i j, R i j → R j i → False := by
    intro i j hij hji
    have hijne : i ≠ j := fun h => hirr i (h.symm ▸ hij)
    have hKj : K j ⊆ U i := hKsub i j hij
    have hKi : K i ⊆ U j := hKsub j i hji
    have hVij : V i ⊆ V j := hM i j hKj
    have hVji : V j ⊆ V i := hM j i hKi
    have hVeq : V i = V j := Set.Subset.antisymm hVij hVji
    have hKiKj : K i = K j := by rw [← hfrontier i, ← hfrontier j, hVeq]
    obtain ⟨x, hxK⟩ := hKne i
    have hxj : x ∈ K j := by rw [← hKiKj]; exact hxK
    exact hdisj i j hijne x hxK hxj
  have htrans : ∀ i j k, R i j → R j k → R i k := by
    intro i j k hij hjk
    by_cases hik : i = k
    · rw [← hik] at hjk ⊢
      exact (hanti i j hij hjk).elim
    · have hKj : K j ⊆ U i := hKsub i j hij
      have hKk : K k ⊆ U j := hKsub j k hjk
      have hVij : V i ⊆ V j := hM i j hKj
      have step : K k ⊆ U i ∪ K i := by
        intro x hx
        have hxnotVi : x ∉ V i := fun hv => hdisjV j x (hKk hx) (hVij hv)
        rcases hmem_split i x with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 hxnotVi
      have hKkU : K k ⊆ U i := by
        intro x hx
        rcases step hx with h1 | h1
        · exact h1
        · exact (hdisj i k hik x h1 hx).elim
      obtain ⟨x, hxK⟩ := hKne k
      obtain ⟨z, hz, hzx⟩ := hKkU hxK
      exact ⟨z, hz, by rw [hzx]; exact hxK⟩
  obtain ⟨rank, hrank⟩ := exists_rank_of_strict_order R hirr htrans
  exact ⟨{
    e := inn
    e' := out
    rank := rank
    inj := fun i => TwoDiscs.inner_injective (h i) x₀
    inj' := fun i => TwoDiscs.outer_injective (h i) x₀
    boundary := fun i θ => TwoDiscs.inner_boundary (h i) x₀ θ
    boundary' := fun i θ => TwoDiscs.outer_boundary (h i) x₀ θ
    open_interior := fun i => TwoDiscs.isOpen_inSide (h i) x₀
    open_interior' := fun i => TwoDiscs.isOpen_outSide (h i) x₀
    cover := fun i => TwoDiscs.cover_range (h i) x₀
    meet := fun i => TwoDiscs.meet_range (h i) x₀
    nested := fun i j hmem => hrank i j hmem }, fun i => rfl⟩

end

end Work.Smooth.SphereJordan
