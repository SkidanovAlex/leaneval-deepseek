import Mathlib

namespace Work.WilG1.Cell

theorem isNowhereDense_graph {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f C) :
    IsNowhereDense {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  -- Write `G` for the graph of `f` over `C`.
  set G : Set (Fin (n + 1) → ℝ) :=
      {z | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} with hGdef
  change IsNowhereDense G
  rw [IsNowhereDense]
  -- Continuity of `f` on `C` forces the closure of the graph to meet each vertical fibre
  -- over a point of `C` in at most one point.
  have fiber : ∀ x ∈ C, ∀ y ∈ closure G, Fin.init y = x → y (Fin.last n) = f x := by
    intro x hxC y hycl hyinit
    refine eq_of_forall_dist_le (fun ε hε => le_of_lt ?_)
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hf x hxC)) (ε / 2) (by positivity)
    obtain ⟨w, hwG, hyw⟩ :=
      Metric.mem_closure_iff.mp hycl (min δ (ε / 2)) (lt_min hδpos (by positivity))
    obtain ⟨hwC, hwlast⟩ := hwG
    have hdx : dist (Fin.init w) x < δ := by
      have h1 : dist (Fin.init w) (Fin.init y) ≤ dist w y := by
        rw [dist_pi_le_iff dist_nonneg]
        intro i
        exact dist_le_pi_dist w y i.castSucc
      rw [hyinit] at h1
      rw [dist_comm w y] at h1
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hyw (min_le_left _ _))
    have hfw : dist (f (Fin.init w)) (f x) < ε / 2 := hδ hwC hdx
    have hyw' : dist (y (Fin.last n)) (f (Fin.init w)) < ε / 2 := by
      have h2 : dist (y (Fin.last n)) (w (Fin.last n)) ≤ dist y w :=
        dist_le_pi_dist y w (Fin.last n)
      rw [hwlast] at h2
      exact lt_of_le_of_lt h2 (lt_of_lt_of_le hyw (min_le_right _ _))
    calc dist (y (Fin.last n)) (f x)
        ≤ dist (y (Fin.last n)) (f (Fin.init w)) + dist (f (Fin.init w)) (f x) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hyw' hfw
      _ = ε := by ring
  by_contra hne
  obtain ⟨z, hz⟩ : (interior (closure G)).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hmemnhds : closure G ∈ nhds z := mem_interior_iff_mem_nhds.mp hz
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hmemnhds
  have hzcl : z ∈ closure G := interior_subset hz
  obtain ⟨w, hwG, hzw⟩ := Metric.mem_closure_iff.mp hzcl (ε / 2) (by positivity)
  obtain ⟨hwC, hwlast⟩ := hwG
  -- Two points sharing their first `n` coordinates with `w` and lying in the ball of `z`
  -- that is contained in the closure of the graph.
  set p : Fin (n + 1) → ℝ := Fin.snoc (Fin.init w) (z (Fin.last n)) with hpdef
  set q : Fin (n + 1) → ℝ := Fin.snoc (Fin.init w) (z (Fin.last n) + ε / 2) with hqdef
  have hpinit : Fin.init p = Fin.init w := by rw [hpdef]; exact Fin.init_snoc _ _
  have hqinit : Fin.init q = Fin.init w := by rw [hqdef]; exact Fin.init_snoc _ _
  have hplast : p (Fin.last n) = z (Fin.last n) := by rw [hpdef]; exact Fin.snoc_last _ _
  have hqlast : q (Fin.last n) = z (Fin.last n) + ε / 2 := by rw [hqdef]; exact Fin.snoc_last _ _
  have hdp : dist z p < ε := by
    rw [hpdef]
    have h1 : dist z (Fin.snoc (Fin.init w) (z (Fin.last n))) ≤ dist z w := by
      rw [dist_pi_le_iff dist_nonneg]
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact dist_le_pi_dist z w j.castSucc
      · rw [Fin.snoc_last]
        simp
    exact lt_of_le_of_lt h1 (by linarith [hzw, hεpos])
  have hdq : dist z q < ε := by
    rw [hqdef, dist_pi_lt_iff hεpos]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      have h2 : dist (z j.castSucc) (Fin.init w j) ≤ dist z w :=
        dist_le_pi_dist z w j.castSucc
      linarith [h2, hzw, hεpos]
    · rw [Fin.snoc_last]
      have h3 : dist (z (Fin.last n)) (z (Fin.last n) + ε / 2) = ε / 2 := by
        rw [Real.dist_eq]
        rw [show z (Fin.last n) - (z (Fin.last n) + ε / 2) = -(ε / 2) by ring]
        rw [abs_neg, abs_of_nonneg (by linarith)]
      rw [h3]
      linarith [hεpos]
  have hpfl : p (Fin.last n) = f (Fin.init w) :=
    fiber (Fin.init w) hwC p (hεball (Metric.mem_ball.mpr (dist_comm z p ▸ hdp))) hpinit
  have hqfl : q (Fin.last n) = f (Fin.init w) :=
    fiber (Fin.init w) hwC q (hεball (Metric.mem_ball.mpr (dist_comm z q ▸ hdq))) hqinit
  rw [hplast] at hpfl
  rw [hqlast] at hqfl
  linarith [hεpos]

end Work.WilG1.Cell
