import Submission.Work.Drive.ChartBridge

/-!
# Globalization of the charted difference map

`Work.Drive.exists_chartDiff_extension`: at a point `x` of the chart region of the chart at `p`, the
charted difference map `chartDiff p D N` agrees on a neighbourhood of `x` with a *globally* `C^∞`
map `F : ℝ⁵ → ℝ⁴`.

Such a globalization is needed to apply `Work.Drive.exists_local_normalForm` (which requires global
smoothness) to the charted difference map; the construction is the standard one: multiply the
charted difference map by a smooth bump which is `1` on a neighbourhood of `x` and whose support is
contained in the open chart region (`Work.Drive.isOpen_chartRegion`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

theorem exists_chartDiff_extension (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) :
    ∃ (F : Amb 4 → Tgt 4) (U : Set (Amb 4)), IsOpen U ∧ x ∈ U ∧ U ⊆ chartRegion p D N ∧
      ContDiff ℝ Ctop F ∧ Set.EqOn F (chartDiff p D N) U := by
  have hregion : IsOpen (chartRegion p D N) :=
    isOpen_chartRegion p D N hD.continuous hN.continuous
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hregion x hx
  set χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hχ
  have hχ1 : ∀ y ∈ Metric.ball x (r / 4), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχ0 : ∀ y, r / 2 ≤ dist y x → χ y = 0 := by
    intro y hy
    refine χ.zero_of_le_dist ?_
    rw [hχ]
    show r / 2 ≤ dist y x
    exact hy
  have hsupp : ∀ y, ¬ (dist y x ≤ r / 2) → ∀ᶠ z in 𝓝 y, χ z = 0 := by
    intro y hy
    have hy' : r / 2 < dist y x := not_le.mp hy
    refine Filter.eventually_of_mem
      (Metric.ball_mem_nhds y (sub_pos.mpr hy')) ?_
    intro z hz
    refine hχ0 z (le_of_lt ?_)
    have hz' : dist z y < dist y x - r / 2 := Metric.mem_ball.mp hz
    have h1 : dist y x ≤ dist z y + dist z x := by
      simpa [dist_comm] using dist_triangle y z x
    linarith
  refine ⟨fun y => χ y • chartDiff p D N y, Metric.ball x (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), ?_, ?_, ?_⟩
  · intro y hy
    exact hsub (Metric.ball_subset_ball (by linarith) hy)
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ chartRegion p D N
    · have h1 : ContDiffAt ℝ Ctop (fun y : Amb 4 => χ y) y := χ.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ Ctop (chartDiff p D N) y :=
        (contDiffOn_chartDiff p D N hD hN).contDiffAt (hregion.mem_nhds hy)
      exact h1.smul h2
    · have hdist : ¬ (dist y x ≤ r / 2) := by
        intro hcon
        refine hy (hsub (Metric.mem_ball.mpr ?_))
        linarith
      refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [hsupp y hdist] with z hz
      simp [hz]
  · intro y hy
    change χ y • chartDiff p D N y = chartDiff p D N y
    rw [hχ1 y hy, one_smul]

end

end Work.Drive
