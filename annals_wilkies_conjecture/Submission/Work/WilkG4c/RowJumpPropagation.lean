import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilkG4c

open Filter

open scoped Topology

noncomputable section

/-- The open cube is open. -/
theorem isOpen_openCube (n : ℕ) : IsOpen (WilkiesDesign.openCube n) := by
  have heq : WilkiesDesign.openCube n = Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) 1) := by
    ext t; simp [WilkiesDesign.openCube, Set.mem_pi]
  rw [heq]
  exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)

/-- Tail is 1-Lipschitz with respect to the sup-distance. -/
theorem dist_tail_le {n : ℕ} (y : Fin (n + 1) → ℝ) (x : ℝ) (u : Fin n → ℝ) :
    dist (Fin.tail y) u ≤ dist y (Fin.cons x u) := by
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  exact dist_le_pi_dist y (Fin.cons x u) i.succ

/-- A four-point triangle inequality. -/
theorem abs_triple (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  have h1 : |a - d| ≤ |a - b + (b - c)| + |c - d| := by
    have h : a - d = (a - b + (b - c)) + (c - d) := by ring
    rw [h]; exact abs_add_le _ _
  have h2 : |a - b + (b - c)| ≤ |a - b| + |b - c| := abs_add_le _ _
  linarith

theorem RowJumpPropagation {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (hu : ∀ (x : ℝ) (u u' : Fin n → ℝ), u ∈ WilkiesDesign.openCube n →
      u' ∈ WilkiesDesign.openCube n →
      |g (Fin.cons x u) - g (Fin.cons x u')| ≤ dist u u')
    {x : ℝ} {u₀ : Fin n → ℝ} (hu₀ : u₀ ∈ WilkiesDesign.openCube n)
    (h : ¬ ContinuousAt g (Fin.cons x u₀)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin n → ℝ, q ∈ WilkiesDesign.openCube n →
      dist q u₀ ≤ ε / 4 → ¬ ContinuousAt (fun t : ℝ => g (Fin.cons t q)) x := by
  -- Step 1: extract a quantitative witness of the discontinuity at `Fin.cons x u₀`.
  obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ y : Fin (n + 1) → ℝ, dist y (Fin.cons x u₀) < δ ∧
        ε₀ ≤ dist (g y) (g (Fin.cons x u₀)) := by
    by_contra hcon
    push Not at hcon
    exact h (Metric.continuousAt_iff.mpr hcon)
  -- Step 2: a radius keeping the tail inside the cube.
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.isOpen_iff.mp (isOpen_openCube n) u₀ hu₀
  have hcube : ∀ y : Fin (n + 1) → ℝ, dist y (Fin.cons x u₀) < δ₀ →
      Fin.tail y ∈ WilkiesDesign.openCube n := fun y hy =>
    hδ₀ (Metric.mem_ball.mpr (lt_of_le_of_lt (dist_tail_le y x u₀) hy))
  -- Step 3: build the sequence of witnesses, shrinking the radius.
  let δ : ℕ → ℝ := fun k => min δ₀ (1 / ((k : ℝ) + 1))
  have hδpos : ∀ k, 0 < δ k := fun k => lt_min hδ₀pos (by positivity)
  choose y hy using fun k => hε₀ (δ k) (hδpos k)
  have hytend : Tendsto (fun k => dist (y k) (Fin.cons x u₀)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => dist_nonneg)
    · intro k
      exact le_trans (le_of_lt (hy k).1) (min_le_right _ _)
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have huk_mem : ∀ k, Fin.tail (y k) ∈ WilkiesDesign.openCube n :=
    fun k => hcube (y k) (lt_of_lt_of_le (hy k).1 (min_le_left _ _))
  have huk_tend : Tendsto (fun k => Fin.tail (y k)) atTop (𝓝 u₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) (fun k => dist_tail_le (y k) x u₀) hytend
  have hxk_tend : Tendsto (fun k => y k 0) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun k => dist_nonneg)
    · intro k
      exact dist_le_pi_dist (y k) (Fin.cons x u₀) (0 : Fin (n + 1))
    · exact hytend
  -- Step 4: the propagation.
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro q hq hqdist hcont
  have hftend : Tendsto (fun k => g (Fin.cons (y k 0) q)) atTop (𝓝 (g (Fin.cons x q))) :=
    hcont.tendsto.comp hxk_tend
  have hdist_tend : Tendsto (fun k => dist (g (Fin.cons (y k 0) q)) (g (Fin.cons x q)))
      atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hftend
  have habs_tend : Tendsto (fun k => |g (Fin.cons (y k 0) q) - g (Fin.cons x q)|)
      atTop (𝓝 0) := by
    simpa only [Real.dist_eq] using hdist_tend
  have hB_tend : Tendsto
      (fun k => dist (Fin.tail (y k)) q + |g (Fin.cons (y k 0) q) - g (Fin.cons x q)|
        + dist q u₀) atTop (𝓝 (2 * dist q u₀)) := by
    have hf1 : Tendsto (fun k => dist (Fin.tail (y k)) q) atTop (𝓝 (dist u₀ q)) :=
      huk_tend.dist tendsto_const_nhds
    have h3t : Tendsto (fun _ : ℕ => dist q u₀) atTop (𝓝 (dist q u₀)) := tendsto_const_nhds
    have hsum := (hf1.add habs_tend).add h3t
    have hlim : dist u₀ q + 0 + dist q u₀ = 2 * dist q u₀ := by
      rw [dist_comm u₀ q]; ring
    rw [hlim] at hsum
    exact hsum
  have hB_ge : ∀ k, ε₀ ≤ dist (Fin.tail (y k)) q
      + |g (Fin.cons (y k 0) q) - g (Fin.cons x q)| + dist q u₀ := by
    intro k
    have h1 : |g (y k) - g (Fin.cons (y k 0) q)| ≤ dist (Fin.tail (y k)) q := by
      have hh := hu (y k 0) (Fin.tail (y k)) q (huk_mem k) hq
      rwa [Fin.cons_self_tail (y k)] at hh
    have h2 : |g (Fin.cons x q) - g (Fin.cons x u₀)| ≤ dist q u₀ := hu x q u₀ hq hu₀
    have h3 : ε₀ ≤ |g (y k) - g (Fin.cons x u₀)| := by
      have hh := (hy k).2
      rwa [Real.dist_eq] at hh
    have htri : |g (y k) - g (Fin.cons x u₀)| ≤
        |g (y k) - g (Fin.cons (y k 0) q)| + |g (Fin.cons (y k 0) q) - g (Fin.cons x q)|
          + |g (Fin.cons x q) - g (Fin.cons x u₀)| :=
      abs_triple _ _ _ _
    linarith [h1, h2, h3, htri]
  have hε₀_le : ε₀ ≤ 2 * dist q u₀ :=
    Set.mem_Ici.mp (isClosed_Ici.mem_of_tendsto hB_tend (Filter.Eventually.of_forall hB_ge))
  linarith

end

end Work.WilkG4c
