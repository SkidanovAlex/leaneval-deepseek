import Mathlib
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Plane.exists_polyPath
import Submission.Work.BoxShrink.Bubble.Plane.segment_interior_eq_empty
import Submission.Work.BoxShrink.Bubble.Plane.interior_iUnion_fin_eq_empty

/-!
# `Work.BoxShrink.Bubble.Plane.thinPath`

Replacement of a continuous path in an open subset `Ω ⊆ ℝ²` by a *thin* path: same endpoints,
image in `Ω`, closed image with empty interior, and uniformly separated from the complement of `Ω`.

The construction is the polygonal approximation of `p`: `Ω` is open and `[0,1]` is compact, so
`range p` is a compact subset of `Ω`, hence has a positive distance `δ₀` from `Ωᶜ`; splitting
`[0,1]` into `N` equal pieces fine enough for the uniform continuity of `p` with tolerance
`δ₀ / 2`, the polygonal path through the points `p (i/N)` runs inside the balls
`B (p (i/N)) (δ₀/2) ⊆ Ω`.  Its image is contained in the finite union of the consecutive segments,
which is closed with empty interior, and its distance to `Ωᶜ` is positive.

The two ingredients about the polyline and about finite unions of thin closed sets are proved in
the sibling modules imported below.
-/

namespace Work.BoxShrink.Bubble.Plane

open Set Metric

theorem thinPath {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (hp : ∀ t : Set.Icc (0 : ℝ) 1, p t ∈ Ω) :
    ∃ p' : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      p' ⟨0, by norm_num⟩ = p ⟨0, by norm_num⟩ ∧
      p' ⟨1, by norm_num⟩ = p ⟨1, by norm_num⟩ ∧
      (∀ t : Set.Icc (0 : ℝ) 1, p' t ∈ Ω) ∧
      IsClosed (Set.range p') ∧
      interior (Set.range p') = ∅ ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ × ℝ, ‖v‖ < δ → ∀ t : Set.Icc (0 : ℝ) 1, p' t + v ∈ Ω := by
  -- `range p` is a compact subset of the open set `Ω`, hence has a positive distance from `Ωᶜ`.
  have hK : IsCompact (Set.range p) := isCompact_range p.continuous
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ :=
    hK.exists_thickening_subset_open hΩ (by rintro x ⟨t, rfl⟩; exact hp t)
  -- Uniform continuity of `p` on `[0,1]` with tolerance `δ₀/2`.
  have huc : UniformContinuous p := CompactSpace.uniformContinuous_of_continuous p.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨η, hηpos, hη⟩ := huc (δ₀ / 2) (by linarith)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hηpos
  set N : ℕ := m + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos m
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1N : 1 / (N : ℝ) < η := by rw [hN]; simpa using hm
  -- The vertices `p (i/N)`, as elements of the parametrising interval.
  let sN : Fin (N + 1) → Set.Icc (0 : ℝ) 1 := fun i => ⟨(i : ℝ) / N, by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNposR]
    have hi : (i : ℕ) ≤ N := by have := i.isLt; omega
    exact_mod_cast hi⟩
  let v : Fin (N + 1) → ℝ × ℝ := fun i => p (sN i)
  have hsNval : ∀ i : Fin (N + 1), ((sN i : Set.Icc (0 : ℝ) 1) : ℝ) = (i : ℝ) / N :=
    fun i => rfl
  -- Consecutive parameters are at distance `1/N < η`.
  have hparam_close : ∀ i : Fin N, dist (sN i.succ) (sN i.castSucc) < η := by
    intro i
    rw [Subtype.dist_eq]
    have hsucc : ((sN i.succ : Set.Icc (0 : ℝ) 1) : ℝ) =
        ((sN i.castSucc : Set.Icc (0 : ℝ) 1) : ℝ) + 1 / N := by
      rw [hsNval, hsNval]
      have h1 : ((i.succ : Fin (N + 1)) : ℝ) = ((i.castSucc : Fin (N + 1)) : ℝ) + 1 := by
        have h2 : ((i.succ : Fin (N + 1)) : ℕ) = ((i.castSucc : Fin (N + 1)) : ℕ) + 1 := by
          rw [Fin.val_succ]; rfl
        exact_mod_cast h2
      rw [h1]; ring
    rw [Real.dist_eq, hsucc, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    exact h1N
  have hsN0 : sN 0 = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) :=
    Subtype.ext (by rw [hsNval]; simp)
  have hsNlast : sN (Fin.last N) = (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) :=
    Subtype.ext (by rw [hsNval, Fin.val_last]; exact div_self (ne_of_gt hNposR))
  have hv0 : v 0 = p ⟨0, by norm_num⟩ := by
    show p (sN 0) = p ⟨0, by norm_num⟩
    rw [hsN0]
  have hvlast : v (Fin.last N) = p ⟨1, by norm_num⟩ := by
    show p (sN (Fin.last N)) = p ⟨1, by norm_num⟩
    rw [hsNlast]
  -- Consecutive vertices lie in the ball `B (v i.castSucc) (δ₀/2)`, which is convex and in `Ω`.
  have hcover : ∀ i : Fin N, ∃ C : Set (ℝ × ℝ), Convex ℝ C ∧ C ⊆ Ω ∧
      v i.castSucc ∈ C ∧ v i.succ ∈ C := by
    intro i
    refine ⟨ball (v i.castSucc) (δ₀ / 2), convex_ball _ _, ?_,
      Metric.mem_ball_self (by positivity), ?_⟩
    · intro x hx
      apply hδ₀sub
      rw [Metric.mem_thickening_iff]
      exact ⟨v i.castSucc, ⟨sN i.castSucc, rfl⟩,
        lt_of_lt_of_le (Metric.mem_ball.mp hx) (by linarith)⟩
    · show dist (p (sN i.succ)) (p (sN i.castSucc)) < δ₀ / 2
      exact hη (hparam_close i)
  -- The polygonal path through the vertices.
  obtain ⟨q, hq0, hq1, hqseg⟩ := exists_polyPath N hNpos v
  have hq0' : q ⟨0, by norm_num⟩ = p ⟨0, by norm_num⟩ := by rw [hq0, hv0]
  have hq1' : q ⟨1, by norm_num⟩ = p ⟨1, by norm_num⟩ := by rw [hq1, hvlast]
  have hqΩ : ∀ t : Set.Icc (0 : ℝ) 1, q t ∈ Ω := by
    intro t
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hqseg t)
    obtain ⟨C, hCconv, hCΩ, hC1, hC2⟩ := hcover i
    exact hCΩ (hCconv.segment_subset hC1 hC2 hi)
  have hrange : Set.range q ⊆ ⋃ i : Fin N, segment ℝ (v i.castSucc) (v i.succ) := by
    rintro x ⟨t, rfl⟩
    exact hqseg t
  have hcompact_seg : ∀ x y : ℝ × ℝ, IsCompact (segment ℝ x y) := by
    intro x y
    rw [segment_eq_image]
    exact isCompact_Icc.image (by continuity)
  have hclosed : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
  have hinterior : interior (Set.range q) = ∅ := by
    have hcl : ∀ i : Fin N, IsClosed (segment ℝ (v i.castSucc) (v i.succ)) :=
      fun i => (hcompact_seg _ _).isClosed
    have hd : ∀ i : Fin N, interior (segment ℝ (v i.castSucc) (v i.succ)) = ∅ :=
      fun i => segment_interior_eq_empty _ _
    refine subset_empty_iff.mp (subset_trans (interior_mono hrange) ?_)
    rw [interior_iUnion_fin_eq_empty hcl hd]
  -- The whole `δ`-neighbourhood of the image of `q` is still inside `Ω`.
  obtain ⟨δ, hδpos, hδsub⟩ := (isCompact_range q.continuous).exists_thickening_subset_open hΩ
    (range_subset_iff.mpr hqΩ)
  exact ⟨q, hq0', hq1', hqΩ, hclosed, hinterior, δ, hδpos, fun w hw t => hδsub (by
    rw [Metric.mem_thickening_iff]
    exact ⟨q t, ⟨t, rfl⟩, by rw [dist_eq_norm, add_sub_cancel_left]; exact hw⟩)⟩

end Work.BoxShrink.Bubble.Plane
