import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xc_deep_bound
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup
import Submission.Work.PertCrux.exists_orbit_nhd
import Submission.Work.PertCrux.QLeft_sub_real
import Submission.Work.PertCrux.exists_translate_mem_QLeft
import Submission.Work.PertCrux.phi_norm_le_of_far

/-!
# A uniform neighbourhood of the backward orbit `φ₀ (w - m)`

For a parabolic germ `f₀` on `D₀` with §4.1 (Fatou coordinate) data `d : ParabData f₀ D₀` and a
compact `K' ⊆ d.Dφ`, the points `d.φ (w - m)` (`w ∈ K'`, `m ≥ 1`) have a *uniform* `D₀`-ball
around them.  (`ParabData.succ_iff` only gives the pointwise statement `d.φ (w - m) ∈ D₀`.)

The proof splits the index `m` at a threshold `M`:

* `m ≤ M` is a finite range, and `Work.PertCrux.exists_orbit_nhd` (compactness of the finite union
  of the compact images `d.φ '' (K' - m)`, all contained in the open set `D₀`) gives one radius.
* `m ≥ M`: the uniform translate `w - Nq` of `K'` lies in the repelling sector
  `QLeft ξ₀` (`Work.PertCrux.exists_translate_mem_QLeft`), and the sector is closed under further
  leftward translations (`Work.PertCrux.QLeft_sub_real`), so `w - m ∈ QLeft ξ₀`; since
  `‖w - m‖ → ∞` uniformly in `w ∈ K'`, the asymptotic expansion `ParabData.φ_asymp` gives
  `‖d.φ (w - m)‖ ≤ ε/2` (`Work.PertCrux.phi_norm_le_of_far`), i.e. a fixed ball inside the ball
  `ball 0 ε ⊆ D₀` supplied by openness of `D₀` at `0`.
-/

namespace Work.PertCrux

open Set Metric
open scoped Topology

theorem orbit_nhd_uniform {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ K', ∀ m : ℕ, 1 ≤ m →
      Metric.closedBall (d.φ (w - (m : ℂ))) r ⊆ D₀ := by
  have hD0open : IsOpen D₀ := hd.1
  have h0D0 : (0 : ℂ) ∈ D₀ := hd.2.1
  -- a `D₀`-neighbourhood of `0`
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hD0open.mem_nhds h0D0)
  -- uniform translate that lands in the petal sector
  obtain ⟨Nq, hNq⟩ := exists_translate_mem_QLeft d hK'c hK'
  -- `φ` is small far out in the sector
  obtain ⟨Rφ, hRφpos, hRφ⟩ := phi_norm_le_of_far d (c := ε / 2) (by linarith)
  -- `K'` is bounded
  obtain ⟨RK, hRK⟩ := hK'c.isBounded.exists_norm_le
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge (Rφ + RK)
  set M : ℕ := max Nq M₀ with hMdef
  have hMNq : Nq ≤ M := le_max_left _ _
  have hMM₀ : M₀ ≤ M := le_max_right _ _
  -- the tail `m ≥ M`
  have htail : ∀ w ∈ K', ∀ m : ℕ, M ≤ m →
      Metric.closedBall (d.φ (w - (m : ℂ))) (ε / 4) ⊆ D₀ := by
    intro w hw m hm
    have hmcast : Rφ + RK ≤ (m : ℝ) := by
      have h1 : (M₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans hMM₀ hm
      linarith
    have hmem : w - (m : ℂ) ∈ MandelDim.QLeft d.ξ₀ := by
      have h1 : w - (Nq : ℂ) ∈ MandelDim.QLeft d.ξ₀ := hNq w hw
      have h2 : w - (m : ℂ) = (w - (Nq : ℂ)) - (((m - Nq : ℕ) : ℝ) : ℂ) := by
        rw [Nat.cast_sub (le_trans hMNq hm)]
        push_cast
        ring
      rw [h2]
      exact QLeft_sub_real h1 (t := ((m - Nq : ℕ) : ℝ)) (Nat.cast_nonneg _)
    have hnorm : Rφ ≤ ‖w - (m : ℂ)‖ := by
      have hwRK : ‖w‖ ≤ RK := hRK w hw
      have h1 : (m : ℝ) - ‖w‖ ≤ ‖w - (m : ℂ)‖ := by
        have h2 := abs_norm_sub_norm_le (m : ℂ) w
        rw [Complex.norm_natCast, norm_sub_rev] at h2
        have h3 : (m : ℝ) - ‖w‖ ≤ |(m : ℝ) - ‖w‖| := le_abs_self _
        linarith
      linarith
    have hφ : ‖d.φ (w - (m : ℂ))‖ ≤ ε / 2 := hRφ _ hmem hnorm
    intro z hz
    have hzε : ‖z - d.φ (w - (m : ℂ))‖ ≤ ε / 4 := by
      have h := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    apply hεsub
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖z‖ ≤ ‖z - d.φ (w - (m : ℂ))‖ + ‖d.φ (w - (m : ℂ))‖ := by
          have h := norm_add_le (z - d.φ (w - (m : ℂ))) (d.φ (w - (m : ℂ)))
          rwa [sub_add_cancel] at h
      _ ≤ ε / 4 + ε / 2 := add_le_add hzε hφ
      _ < ε := by linarith
  -- the finite part `m ≤ M`
  obtain ⟨V, _hVc, hVD, R, hRpos, _Lf, _hLf, _hLip, hball⟩ :=
    exists_orbit_nhd hd d hK'c hK' M
  refine ⟨min R (ε / 4), lt_min hRpos (by linarith), ?_⟩
  intro w hw m hm1
  rcases lt_or_ge m M with hm | hm
  · exact subset_trans (Metric.closedBall_subset_closedBall (min_le_left _ _))
      (subset_trans (hball w hw m hm1 hm.le) hVD)
  · exact subset_trans (Metric.closedBall_subset_closedBall (min_le_right _ _))
      (htail w hw m hm)

end Work.PertCrux
