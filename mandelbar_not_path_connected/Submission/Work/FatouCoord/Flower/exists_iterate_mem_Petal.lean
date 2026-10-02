import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.widePetal_growth
import Submission.Work.FatouCoord.Flower.enters_widePetal
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

open Work.FatouCoord

/-- If `z ≠ 0` and `M < Re (chart z)`, then `z` lies in the petal `Petal r M` as soon as
`1 / r < M` (and `r > 0`, `M > 0`).  Indeed `M < Re (-1/z)` forces `M ‖z‖² < -Re z ≤ ‖z‖`,
hence `‖z‖ < 1/M < r`; and the same inequality is exactly `Re z < -M ‖z‖²`. -/
theorem mem_Petal_of_lt_re_chart {z : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M) (hMr : 1 / r < M)
    (hz : z ≠ 0) (h : M < (chart z).re) : z ∈ Petal r M := by
  have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [re_chart hz] at h
  have h1 : M * Complex.normSq z < -z.re := by
    rw [lt_div_iff₀ hns] at h
    linarith
  rw [mem_Petal]
  refine ⟨?_, ?_⟩
  · have h2 : -z.re ≤ ‖z‖ := by
      have h3 := Complex.abs_re_le_norm z
      rw [abs_le] at h3
      linarith [h3.1]
    have h1c := h1
    rw [Complex.normSq_eq_norm_sq] at h1c
    have h3 : M * ‖z‖ < 1 := by nlinarith
    have h4 : 1 / M < r := by
      rw [div_lt_iff₀ hM]
      rw [div_lt_iff₀ hr] at hMr
      linarith
    have h5 : ‖z‖ < 1 / M := by
      rw [lt_div_iff₀ hM]
      linarith
    linarith
  · linarith

theorem exists_iterate_mem_Petal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    {Ms M : ℝ} (hMs : 1 ≤ Ms) (hMsr : 1 / r < Ms)
    (hgr : ∀ W : ℂ, Ms < Work.FatouCoord.Flower.sgauge W → Ms < Work.FatouCoord.Flower.sgauge (Work.FatouCoord.wMap f W) ∧ (Work.FatouCoord.wMap f W).re ≥ W.re + 1 / 2)
    (hM : 1 ≤ M) (hMr : 1 / r < M) :
    ∀ u : ℂ, Filter.Tendsto (fun n : ℕ => f^[n] u) Filter.atTop (nhds 0) → (∀ n : ℕ, f^[n] u ≠ 0) →
      ∃ n : ℕ, f^[n] u ∈ Work.FatouCoord.Petal r M := by
  intro u ht hne
  -- first get an iterate inside the wide petal at level `Ms`
  obtain ⟨n₀, hn₀⟩ := enters_widePetal hb hMs hMsr hgr u ht hne
  rw [mem_WidePetal] at hn₀
  -- the chart iterates `W k = chart (f^[n₀ + k] u)`
  set W : ℕ → ℂ := fun k => chart (f^[n₀ + k] u) with hW
  have h0 : Ms < sgauge (W 0) := by
    rw [hW]
    simpa [chart] using hn₀.2
  -- the chart iterates follow the chart dynamics
  have hstep : ∀ k : ℕ, W (k + 1) = wMap f (W k) := by
    intro k
    have hk : f^[n₀ + k] u ≠ 0 := hne _
    rw [hW]
    show chart (f^[(n₀ + k) + 1] u) = wMap f (chart (f^[n₀ + k] u))
    rw [Function.iterate_succ_apply']
    simp only [wMap]
    rw [chart_chart hk]
  -- the wide sector is forward invariant, and the real part grows by `1/2` each step
  have hsg : ∀ k : ℕ, Ms < sgauge (W k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
        rw [hstep k]
        exact (hgr (W k) ih).1
  have hre : ∀ k : ℕ, (W 0).re + (k : ℝ) / 2 ≤ (W k).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h2 : (W k).re + 1 / 2 ≤ (W (k + 1)).re := by
          have h2' := (hgr (W k) (hsg k)).2
          rw [← hstep k] at h2'
          exact h2'
        have hcast : ((k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 / 2 := by push_cast; ring
        rw [hcast]
        linarith
  -- choose `k` with `Re (W k) > M`, then `f^[n₀ + k] u` lies in `Petal r M`
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (M - (W 0).re))
  refine ⟨n₀ + k, ?_⟩
  have hMpos : 0 < M := by linarith
  have hWk : W k = chart (f^[n₀ + k] u) := by rw [hW]
  have hMlt : M < (chart (f^[n₀ + k] u)).re := by
    have h1 := hre k
    rw [hWk] at h1
    have h2 : M - (W 0).re < (k : ℝ) / 2 := by linarith
    linarith
  exact mem_Petal_of_lt_re_chart hb.hr hMpos hMr (hne (n₀ + k)) hMlt

end Work.FatouCoord.Flower
