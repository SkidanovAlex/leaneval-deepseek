import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Geometry.Convex.Hadwiger

open scoped Pointwise
open Metric

theorem polytope_dense
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (X : ConvexBody V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : ConvexBody V, ∃ u : Finset V,
      (P : Set V) = convexHull ℝ (u : Set V) ∧ dist P X < δ := by
  classical
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρδ : ρ < δ := by
    dsimp [ρ]
    linarith
  -- Cover the compact convex body X by finitely many open balls of radius ρ
  -- centered at points of X, and take their centers as the vertex set u.
  let c : {x : V // x ∈ (X : Set V)} → Set V := fun i => ball (i : V) ρ
  have hcov : (X : Set V) ⊆ ⋃ i : {x : V // x ∈ (X : Set V)}, c i := by
    intro x hx
    rw [Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, Metric.mem_ball_self hρ⟩
  rcases (X.isCompact.elim_finite_subcover c (fun i => Metric.isOpen_ball) hcov) with ⟨t, ht⟩
  let e : {x : V // x ∈ (X : Set V)} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let u : Finset V := t.map e
  -- Every point of X lies within distance ρ of some vertex in u.
  have hnet : ∀ x ∈ (X : Set V), ∃ y ∈ u, dist x y < ρ := by
    intro x hx
    have hx' : x ∈ ⋃ i ∈ t, ball (i : V) ρ := by
      simpa [c] using ht hx
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨i, hi⟩
    rw [Set.mem_iUnion] at hi
    rcases hi with ⟨hit, hix⟩
    refine ⟨(i : V), ?_, ?_⟩
    · dsimp [u]
      exact Finset.mem_map.mpr ⟨i, Finset.mem_coe.mp hit, rfl⟩
    · exact Metric.mem_ball.mp hix
  -- P = convexHull of u is a convex body: nonempty since X is nonempty.
  obtain ⟨x₀, hx₀⟩ := X.nonempty
  have hu_nonempty : (u : Set V).Nonempty := by
    rcases hnet x₀ hx₀ with ⟨y, hyu, _⟩
    exact Finset.coe_nonempty.mpr ⟨y, hyu⟩
  let P : ConvexBody V := ⟨convexHull ℝ (u : Set V),
      convex_convexHull ℝ (u : Set V),
      Set.Finite.isCompact_convexHull ℝ (Finset.finite_toSet u),
      convexHull_nonempty_iff.mpr hu_nonempty⟩
  -- P is inscribed in X, so the one-sided Hausdorff excess of X over P is all
  -- that remains; it is < ρ by the net property.
  have hsubP : (P : Set V) ⊆ (X : Set V) := by
    dsimp [P]
    apply convexHull_min
    · intro y hy
      have hy' : y ∈ u := by simpa using hy
      rcases Finset.mem_map.mp hy' with ⟨a, hat, ha⟩
      dsimp [e] at ha
      simpa [ha] using a.2
    · exact X.convex
  have hdist : Metric.hausdorffDist (P : Set V) (X : Set V) ≤ ρ := by
    refine Metric.hausdorffDist_le_of_mem_dist (le_of_lt hρ) ?_ ?_
    · intro x hx
      refine ⟨x, hsubP hx, ?_⟩
      rw [dist_self]
      exact le_of_lt hρ
    · intro y hyX
      rcases hnet y hyX with ⟨z, hzu, hzy⟩
      refine ⟨z, ?_, le_of_lt hzy⟩
      dsimp [P]
      exact subset_convexHull ℝ (u : Set V) (by simpa using hzu)
  refine ⟨P, u, ?_, ?_⟩
  · rfl
  · have hd : Metric.hausdorffDist (P : Set V) (X : Set V) < δ := lt_of_le_of_lt hdist hρδ
    simpa [ConvexBody.hausdorffDist_coe] using hd

end Commons.Geometry.Convex.Hadwiger