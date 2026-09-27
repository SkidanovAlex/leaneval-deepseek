import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.ray_of_pieces_with_germs
import Submission.Work.Noncompact.CompressionTube.line_of_two_oneSided_rays

/-!
# Two lanes of pieces assemble into a proper immersed line

The remaining geometric input of `Work.Noncompact.CompressionTube.exists_disjoint_immersed_lines`
is, for a corridor chain `h : CorridorChain b W`, a proper embedded *immersed* line through `b`
inside `W`.  This module isolates the *assembly* of such a line out of two "lanes" of pieces,
so that the geometric work (the recursion producing the pieces) is separated from the bookkeeping.

A `Lane` is exactly the hypothesis list of the proved lemma
`Work.Noncompact.CompressionTube.ray_of_pieces_with_germs`: a family of pieces `P i : ℝ → M`,
each `C^∞`, an immersion and injective on `[0,1]`, joined at the junctions (`P i 1 = P (i+1) 0`),
with matching straight germs at every junction, pairwise separated up to the junctions, and
escaping every compact set — plus the data of the initial germ at the base of the lane.

`TwoLanes` is a pair of lanes based at the same point `b`, with opposite initial germs, images
meeting only at `b`, and both contained in `W`.  The two rays produced by
`ray_of_pieces_with_germs` are then glued by `line_of_two_oneSided_rays` into the required line.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **A lane of pieces.**  The exact hypothesis list of `ray_of_pieces_with_germs`, bundled. -/
structure Lane (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] where
  /-- the pieces -/
  P : ℕ → ℝ → M
  /-- each piece is `C^∞` -/
  hsm : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (P i)
  /-- each piece is an immersion on `[0,1]` -/
  himm : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
    Function.Injective (mfderiv MCreal (MC n) (P i) t)
  /-- each piece is injective on `[0,1]` -/
  hinj : ∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1)
  /-- consecutive pieces meet at a junction -/
  hjun : ∀ i : ℕ, P i 1 = P (i + 1) 0
  /-- matching straight germs at every junction -/
  hgerm : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (u : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      0 < e ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P i 1 ∈ c.source ∧
      (∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P i t = c.symm (c (P i 1) + (t - 1) • u)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → P (i + 1) t = c.symm (c (P (i + 1) 0) + t • u))
  /-- pieces meet only at the junctions -/
  hsep : ∀ i j : ℕ, i < j → P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1}
  /-- the pieces escape every compact set -/
  hesc : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i → P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅
  /-- the chart of the initial germ -/
  c₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- the direction of the initial germ -/
  u₀ : EuclideanSpace ℝ (Fin n)
  /-- the length of the initial germ -/
  e₀ : ℝ
  he₀ : 0 < e₀
  he₀1 : e₀ ≤ 1
  hu₀ : u₀ ≠ 0
  hc₀ : c₀ ∈ IsManifold.maximalAtlas (MC n) smoothOrder M
  hsrc₀ : P 0 0 ∈ c₀.source
  hgerm₀ : ∀ t : ℝ, 0 ≤ t → t ≤ e₀ → P 0 t = c₀.symm (c₀ (P 0 0) + t • u₀)

/-- **Two lanes at a common base point.**  The two lanes have the same initial chart and opposite
initial directions, their piece images meet only at the base point, and both lie in `W`. -/
structure TwoLanes (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (b : M) (W : Set M) where
  /-- the positive lane -/
  Lp : Lane n M
  /-- the negative lane -/
  Lm : Lane n M
  hb : b ∈ W
  hbasep : Lp.P 0 0 = b
  hbasem : Lm.P 0 0 = b
  hchart : Lm.c₀ = Lp.c₀
  hdir : Lm.u₀ = - Lp.u₀
  hsubWp : ∀ i : ℕ, Lp.P i '' Set.Icc (0:ℝ) 1 ⊆ W
  hsubWm : ∀ i : ℕ, Lm.P i '' Set.Icc (0:ℝ) 1 ⊆ W
  /-- the two lanes' images meet only at the base point -/
  hcross : (⋃ i, Lp.P i '' Set.Icc (0:ℝ) 1) ∩
    (⋃ j, Lm.P j '' Set.Icc (0:ℝ) 1) ⊆ {b}

/-- **The assembly: two lanes give the immersed proper line.** -/
theorem exists_immersedProperLine_of_twoLanes {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {b : M} {W : Set M} (T : TwoLanes n M b W) :
    ∃ γ : ℝ → M, ContMDiff MCreal (MC n) smoothOrder γ ∧ Function.Injective γ ∧
      IsProperMap γ ∧ (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧
      γ 1 = b ∧ Set.range γ ⊆ W := by
  obtain ⟨rp, hrple, hrpsm, hrpinj, hrpprop, hrpimm, hrpmem, hrpgerm⟩ :=
    ray_of_pieces_with_germs (n := n) hn T.Lp.P T.Lp.hsm T.Lp.himm T.Lp.hinj T.Lp.hjun
      T.Lp.hgerm T.Lp.hsep T.Lp.hesc T.Lp.he₀ T.Lp.he₀1 T.Lp.hu₀ T.Lp.hc₀ T.Lp.hsrc₀ T.Lp.hgerm₀
  obtain ⟨rm, _hrmle, hrmsm, hrminj, hrmprop, hrmimm, hrmmem, hrmgerm⟩ :=
    ray_of_pieces_with_germs (n := n) hn T.Lm.P T.Lm.hsm T.Lm.himm T.Lm.hinj T.Lm.hjun
      T.Lm.hgerm T.Lm.hsep T.Lm.hesc T.Lm.he₀ T.Lm.he₀1 T.Lm.hu₀ T.Lm.hc₀ T.Lm.hsrc₀ T.Lm.hgerm₀
  -- the base points
  have hrp0 : rp 0 = b := by
    have h := hrpgerm 0 le_rfl T.Lp.he₀.le
    rw [zero_smul, add_zero] at h
    rw [h, T.Lp.c₀.left_inv T.Lp.hsrc₀, T.hbasep]
  have hrm0 : rm 0 = b := by
    have h := hrmgerm 0 le_rfl T.Lm.he₀.le
    rw [zero_smul, add_zero] at h
    rw [h, T.Lm.c₀.left_inv T.Lm.hsrc₀, T.hbasem]
  -- the two rays meet only at `b`
  have hmeet : ∀ x : M, x ∈ rp '' Set.Ici (0:ℝ) → x ∈ rm '' Set.Ici (0:ℝ) → x = b := by
    intro x hx hx'
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, hst⟩ := hx'
    have hp : rp s = b ∨ rp s ∈ ⋃ i, T.Lp.P i '' Set.Icc (0:ℝ) 1 := by
      rcases hrpmem s hs with h | h
      · exact Or.inl (by rw [Set.mem_singleton_iff] at h; rw [h, T.hbasep])
      · exact Or.inr h
    have hm : rp s = b ∨ rp s ∈ ⋃ j, T.Lm.P j '' Set.Icc (0:ℝ) 1 := by
      have h2 : rp s ∈ ({T.Lm.P 0 0} ∪ ⋃ j, T.Lm.P j '' Set.Icc (0:ℝ) 1) := by
        rw [← hst]; exact hrmmem t ht
      rcases h2 with h | h
      · exact Or.inl (by rw [Set.mem_singleton_iff] at h; rw [h, T.hbasem])
      · exact Or.inr h
    rcases hp with h | h <;> rcases hm with h' | h'
    · exact h
    · exact h
    · exact h'
    · exact Set.mem_singleton_iff.mp (T.hcross ⟨h, h'⟩)
  -- the common straight germ at `b`
  have hger : ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ b ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → rp t = c.symm (c b + t • w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → rm t = c.symm (c b + t • (-w))) := by
    refine ⟨T.Lp.c₀, T.Lp.u₀, min T.Lp.e₀ T.Lm.e₀, lt_min T.Lp.he₀ T.Lm.he₀, T.Lp.hu₀,
      T.Lp.hc₀, ?_, ?_, ?_⟩
    · simpa only [T.hbasep] using T.Lp.hsrc₀
    · intro t ht hte
      rw [hrpgerm t ht (le_trans hte (min_le_left _ _)), T.hbasep]
    · intro t ht hte
      rw [hrmgerm t ht (le_trans hte (min_le_right _ _)), T.hchart, T.hdir, T.hbasem]
  obtain ⟨γ, hγsm, hγinj, hγprop, hγimm, hγ1, hγrange⟩ :=
    line_of_two_oneSided_rays (n := n) hrpsm hrmsm hrp0 hrm0 hrpinj hrminj hmeet
      hrpprop hrmprop hrpimm hrmimm hger
  refine ⟨γ, hγsm, hγinj, hγprop, hγimm, hγ1, ?_⟩
  refine Set.Subset.trans hγrange ?_
  rintro x (h | h)
  · obtain ⟨s, hs, rfl⟩ := h
    rcases hrpmem s hs with h' | h'
    · rw [Set.mem_singleton_iff] at h'; rw [h', T.hbasep]; exact T.hb
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h'
      exact T.hsubWp i hi
  · obtain ⟨t, ht, rfl⟩ := h
    have h2 : rm t ∈ ({T.Lm.P 0 0} ∪ ⋃ j, T.Lm.P j '' Set.Icc (0:ℝ) 1) := hrmmem t ht
    rcases h2 with h' | h'
    · rw [Set.mem_singleton_iff] at h'; rw [h', T.hbasem]; exact T.hb
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h'
      exact T.hsubWm j hj

end

end Work.Noncompact.CompressionTube
