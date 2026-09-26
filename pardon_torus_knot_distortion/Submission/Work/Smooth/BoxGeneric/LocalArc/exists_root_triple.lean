import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair

namespace Work.Smooth.BoxGeneric.LocalArc

open Set

/-- A function continuous at the origin with value `0` there is bounded by `R` on a symmetric
neighbourhood of the origin. -/
private lemma exists_abs_le_of_continuousAt_zero {ψ : ℝ → ℝ} {R : ℝ}
    (hcont : ContinuousAt ψ 0) (h0 : ψ 0 = 0) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| ≤ δ → |ψ y| ≤ R := by
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₀, hδ₀pos, hδ₀spec⟩ := hcont R hR
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro y hy
  have hy' : dist y 0 < δ₀ := by rw [Real.dist_eq, sub_zero]; linarith
  have h := hδ₀spec hy'
  rw [Real.dist_eq, h0, sub_zero] at h
  exact h.le

/-- For a single `C¹` function with `f 0 = 0` and `∂f/∂x (0) > 0`: there is a rectangle around
the origin on which the zero set is a graph over the second coordinate. -/
private theorem exists_root_single' {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (ha : 0 < (fderiv ℝ f 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧
      ContinuousOn ψ (Ioo (-Ry) Ry) ∧
      (∀ y, |y| ≤ Ry → |ψ y| ≤ Rx ∧ f (ψ y, y) = 0) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) = 0 ↔ x = ψ y)) := by
  obtain ⟨Rx, Ry, hRx, hRy, ψ, φ, hψ0, _hφ0, hψc, _hφc, hroot, hsign, hzero⟩ :=
    exists_root_pair hf hf hf0 hf0 rfl ha
  exact ⟨Rx, Ry, hRx, hRy, ψ, hψ0, hψc,
    fun y hy => ⟨(hroot y hy).1, (hroot y hy).2.2.1⟩,
    fun x y hx hy => (hsign x y hx hy).1,
    fun x y hx hy => (hzero x y hx hy).1⟩

theorem exists_root_triple {F G H : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hH : ContDiff ℝ 1 H) (hF0 : F 0 = 0) (hG0 : G 0 = 0) (hH0 : H 0 = 0)
    (haF : 0 < (fderiv ℝ F 0) (1, 0)) (haG : 0 < (fderiv ℝ G 0) (1, 0))
    (haH : 0 < (fderiv ℝ H 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ φ χ : ℝ → ℝ,
      ψ 0 = 0 ∧ φ 0 = 0 ∧ χ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧ ContinuousOn φ (Set.Ioo (-Ry) Ry) ∧
      ContinuousOn χ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ |φ y| ≤ Rx ∧ |χ y| ≤ Rx ∧
        F (ψ y, y) = 0 ∧ G (φ y, y) = 0 ∧ H (χ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y) ∧
        (G (x, y) ≤ 0 ↔ x ≤ φ y) ∧ (H (x, y) ≤ 0 ↔ x ≤ χ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y) ∧
        (G (x, y) = 0 ↔ x = φ y) ∧ (H (x, y) = 0 ↔ x = χ y)) := by
  obtain ⟨RxF, RyF, hRxF, hRyF, ψ, hψ0, hψc, hψroot, hψsign, hψzero⟩ :=
    exists_root_single' hF hF0 haF
  obtain ⟨RxG, RyG, hRxG, hRyG, φ, hφ0, hφc, hφroot, hφsign, hφzero⟩ :=
    exists_root_single' hG hG0 haG
  obtain ⟨RxH, RyH, hRxH, hRyH, χ, hχ0, hχc, hχroot, hχsign, hχzero⟩ :=
    exists_root_single' hH hH0 haH
  -- a common half-width in the first coordinate
  set Rx : ℝ := min (min RxF RxG) RxH with hRxdef
  have hRxpos : 0 < Rx := by rw [hRxdef]; exact lt_min (lt_min hRxF hRxG) hRxH
  have hRxF' : Rx ≤ RxF := by
    rw [hRxdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRxG' : Rx ≤ RxG := by
    rw [hRxdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hRxH' : Rx ≤ RxH := by rw [hRxdef]; exact min_le_right _ _
  -- continuity of the three roots at the origin
  have hψc0 : ContinuousAt ψ 0 :=
    hψc.continuousAt (isOpen_Ioo.mem_nhds (by rw [Set.mem_Ioo]; exact ⟨by linarith, hRyF⟩))
  have hφc0 : ContinuousAt φ 0 :=
    hφc.continuousAt (isOpen_Ioo.mem_nhds (by rw [Set.mem_Ioo]; exact ⟨by linarith, hRyG⟩))
  have hχc0 : ContinuousAt χ 0 :=
    hχc.continuousAt (isOpen_Ioo.mem_nhds (by rw [Set.mem_Ioo]; exact ⟨by linarith, hRyH⟩))
  obtain ⟨δψ, hδψpos, hδψ⟩ := exists_abs_le_of_continuousAt_zero hψc0 hψ0 hRxpos
  obtain ⟨δφ, hδφpos, hδφ⟩ := exists_abs_le_of_continuousAt_zero hφc0 hφ0 hRxpos
  obtain ⟨δχ, hδχpos, hδχ⟩ := exists_abs_le_of_continuousAt_zero hχc0 hχ0 hRxpos
  -- shrink the second coordinate so that the roots stay in `[-Rx, Rx]`
  set Ry : ℝ := min δψ (min δφ (min δχ (min RyF (min RyG RyH)))) with hRydef
  have hRypos : 0 < Ry := by
    rw [hRydef]
    exact lt_min hδψpos (lt_min hδφpos (lt_min hδχpos (lt_min hRyF (lt_min hRyG hRyH))))
  have hRy1 : Ry ≤ min δφ (min δχ (min RyF (min RyG RyH))) := by
    rw [hRydef]; exact min_le_right _ _
  have hRy2 : min δφ (min δχ (min RyF (min RyG RyH)))
      ≤ min δχ (min RyF (min RyG RyH)) := min_le_right _ _
  have hRy3 : min δχ (min RyF (min RyG RyH)) ≤ min RyF (min RyG RyH) := min_le_right _ _
  have hRy4 : min RyF (min RyG RyH) ≤ min RyG RyH := min_le_right _ _
  have hRyδψ : Ry ≤ δψ := by rw [hRydef]; exact min_le_left _ _
  have hRyδφ : Ry ≤ δφ := le_trans hRy1 (min_le_left _ _)
  have hRyδχ : Ry ≤ δχ := le_trans (le_trans hRy1 hRy2) (min_le_left _ _)
  have hRyF' : Ry ≤ RyF := le_trans (le_trans (le_trans hRy1 hRy2) hRy3) (min_le_left _ _)
  have hRyG' : Ry ≤ RyG :=
    le_trans (le_trans (le_trans (le_trans hRy1 hRy2) hRy3) hRy4) (min_le_left _ _)
  have hRyH' : Ry ≤ RyH :=
    le_trans (le_trans (le_trans (le_trans hRy1 hRy2) hRy3) hRy4) (min_le_right _ _)
  refine ⟨Rx, Ry, hRxpos, hRypos, ψ, φ, χ, hψ0, hφ0, hχ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hψc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyF'], by linarith [hy.2, hRyF']⟩
  · refine hφc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyG'], by linarith [hy.2, hRyG']⟩
  · refine hχc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyH'], by linarith [hy.2, hRyH']⟩
  · intro y hy
    exact ⟨hδψ y (le_trans hy hRyδψ), hδφ y (le_trans hy hRyδφ), hδχ y (le_trans hy hRyδχ),
      (hψroot y (le_trans hy hRyF')).2, (hφroot y (le_trans hy hRyG')).2,
      (hχroot y (le_trans hy hRyH')).2⟩
  · intro x y hx hy
    exact ⟨hψsign x y (le_trans hx hRxF') (le_trans hy hRyF'),
      hφsign x y (le_trans hx hRxG') (le_trans hy hRyG'),
      hχsign x y (le_trans hx hRxH') (le_trans hy hRyH')⟩
  · intro x y hx hy
    exact ⟨hψzero x y (le_trans hx hRxF') (le_trans hy hRyF'),
      hφzero x y (le_trans hx hRxG') (le_trans hy hRyG'),
      hχzero x y (le_trans hx hRxH') (le_trans hy hRyH')⟩

end Work.Smooth.BoxGeneric.LocalArc
