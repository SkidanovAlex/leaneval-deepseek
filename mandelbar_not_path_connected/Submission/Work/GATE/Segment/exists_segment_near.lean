import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Segment

theorem exists_segment_near {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm)
    (hfront : c₀ ∈ frontier Nm) {r : ℝ} (hr : 0 < r) :
    ∃ y p : ℂ, y ∈ Nm ∩ Metric.ball c₀ (r / 4) ∧ p ∉ Nm ∧ 0 < dist y p ∧
      (∀ z : ℂ, dist y z < dist y p → z ∈ Nm) ∧
      p ∈ Metric.ball c₀ (r / 2) ∧
      (∀ μ ∈ Set.Icc (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Metric.ball c₀ (r / 2)) ∧
      (∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm) := by
  -- `c₀` lies on the boundary of the open set `Nm`: it is in `closure Nm` but not in `Nm`.
  have hfront' : c₀ ∈ closure Nm \ Nm := by
    rwa [hOpen.frontier_eq] at hfront
  have hc0_notmem : c₀ ∉ Nm := hfront'.2
  have hc0_closure : c₀ ∈ closure Nm := hfront'.1
  -- a point `y` of `Nm` within `r/4` of `c₀`
  rw [Metric.mem_closure_iff] at hc0_closure
  obtain ⟨y, hyNm, hyc0⟩ := hc0_closure (r / 4) (by linarith)
  have hyc0' : dist y c₀ < r / 4 := by rw [dist_comm]; exact hyc0
  -- the nearest point `p` of the complement of `Nm`
  have hne : (Nmᶜ).Nonempty := ⟨c₀, by simpa [Set.mem_compl_iff] using hc0_notmem⟩
  have hclosed : IsClosed Nmᶜ := hOpen.isClosed_compl
  obtain ⟨p, hpnotmem, hpd⟩ := hclosed.exists_infDist_eq_dist hne y
  have hpNm : p ∉ Nm := by simpa [Set.mem_compl_iff] using hpnotmem
  have hy_notmem : y ∉ Nmᶜ := by simpa [Set.mem_compl_iff] using hyNm
  -- the distance from `y` to the complement is positive
  have hpos : 0 < dist y p := by
    rw [← hpd]
    have hne0 : Metric.infDist y Nmᶜ ≠ 0 := by
      intro h0
      have hmem : y ∈ closure Nmᶜ := (Metric.mem_closure_iff_infDist_zero hne).mpr h0
      rw [hclosed.closure_eq] at hmem
      exact hy_notmem hmem
    exact lt_of_le_of_ne (Metric.infDist_nonneg (x := y) (s := Nmᶜ)) (Ne.symm hne0)
  -- the open ball about `y` of radius `dist y p` is contained in `Nm`
  have hball : ∀ z : ℂ, dist y z < dist y p → z ∈ Nm := by
    intro z hz
    by_contra hzn
    have hzm : z ∈ Nmᶜ := by simpa [Set.mem_compl_iff] using hzn
    have hle : Metric.infDist y Nmᶜ ≤ dist y z := Metric.infDist_le_dist_of_mem hzm
    rw [hpd] at hle
    linarith
  -- `p` is within `r/2` of `c₀`
  have hpball : p ∈ Metric.ball c₀ (r / 2) := by
    rw [Metric.mem_ball]
    have h3 : dist y p ≤ dist y c₀ := by
      rw [← hpd]
      exact Metric.infDist_le_dist_of_mem (by simpa [Set.mem_compl_iff] using hc0_notmem)
    calc dist p c₀ ≤ dist p y + dist y c₀ := dist_triangle _ _ _
      _ = dist y p + dist y c₀ := by rw [dist_comm]
      _ ≤ dist y c₀ + dist y c₀ := by linarith
      _ < r / 2 := by linarith
  refine ⟨y, p, ⟨hyNm, by rw [Metric.mem_ball]; exact hyc0'⟩, hpNm, hpos, hball, hpball, ?_, ?_⟩
  · -- the closed segment from `y` to `p` stays in the ball, by convexity of the ball
    intro μ hμ
    have hconv := convex_ball c₀ (r / 2)
    have hyball : y ∈ Metric.ball c₀ (r / 2) := by rw [Metric.mem_ball]; linarith [hyc0']
    have hyplus : y + (p - y) ∈ Metric.ball c₀ (r / 2) := by
      convert hpball using 1; ring
    have := hconv.add_smul_mem hyball hyplus hμ
    simpa [Complex.real_smul] using this
  · -- the segment minus its endpoint is in `Nm` (it lies in the ball about `y`)
    intro μ hμ
    have hμ0 : 0 ≤ μ := hμ.1
    have hμ1 : μ < 1 := hμ.2
    apply hball
    have hd : dist y (y + ((μ : ℝ) : ℂ) * (p - y)) = μ * dist y p := by
      have h1 : dist y (y + ((μ : ℝ) : ℂ) * (p - y)) = ‖((μ : ℝ) : ℂ) * (p - y)‖ := by
        rw [dist_eq_norm']; congr 1; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ0,
        dist_comm y p, dist_eq_norm]
    rw [hd]
    have := mul_lt_mul_of_pos_right hμ1 hpos
    simpa using this

end Work.GATE.Segment
