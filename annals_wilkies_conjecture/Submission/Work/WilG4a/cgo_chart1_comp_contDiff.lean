import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

namespace Work.WilG4a

theorem cgo_chart1_comp_contDiff {p : ℕ} (f g : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (l : Fin p → ℝ)
    (hcts : ContinuousOn (Work.WilG4a.chart1 f κ l) Work.WilG4a.I)
    (hmaps : ∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.fibre κ l)
    (hd : ∀ t ∈ Work.WilG4a.I, HasDerivAt (Work.WilG4a.chart1 f κ l)
      ((Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) /
        deriv (f l) (Work.WilG4a.chart1 f κ l t)) t)
    (hgd : ∀ y ∈ Work.WilG4a.fibre κ l, HasDerivAt (g l) (deriv (g l) y) y)
    (hfd : ∀ y ∈ Work.WilG4a.fibre κ l, HasDerivAt (f l) (deriv (f l) y) y)
    (hgc : ContinuousOn (deriv (g l)) (Work.WilG4a.fibre κ l))
    (hfc : ContinuousOn (deriv (f l)) (Work.WilG4a.fibre κ l))
    (hfne : ∀ y ∈ Work.WilG4a.fibre κ l, deriv (f l) y ≠ 0)
    (hdom : ∀ y ∈ Work.WilG4a.fibre κ l, |deriv (g l) y| ≤ |deriv (f l) y|)
    (hAB : |Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l| ≤ 1) :
    ContDiffOn ℝ 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) Work.WilG4a.I ∧
    ∀ t ∈ Work.WilG4a.I,
      |iteratedDeriv 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) t| ≤ 1 := by
  set K : ℝ := Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l with hK
  set h : ℝ → ℝ := fun t => deriv (g l) (Work.WilG4a.chart1 f κ l t) *
    (K / deriv (f l) (Work.WilG4a.chart1 f κ l t)) with hh
  -- The chain rule gives the derivative of the composite at every point of `I`.
  have hderiv : ∀ t ∈ Work.WilG4a.I,
      HasDerivAt (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) (h t) t := by
    intro t ht
    have h2 : HasDerivAt (g l) (deriv (g l) (Work.WilG4a.chart1 f κ l t))
        (Work.WilG4a.chart1 f κ l t) := hgd _ (hmaps t ht)
    have h3 := h2.comp t (hd t ht)
    have heq : deriv (g l) (Work.WilG4a.chart1 f κ l t) *
        ((Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) /
          deriv (f l) (Work.WilG4a.chart1 f κ l t)) = h t := by
      simp only [hh, hK]
    rw [heq] at h3
    exact h3
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t))
      Work.WilG4a.I :=
    fun t ht => ((hderiv t ht).differentiableAt).differentiableWithinAt
  have hgc' : ContinuousOn (fun t : ℝ => deriv (g l) (Work.WilG4a.chart1 f κ l t))
      Work.WilG4a.I := hgc.comp hcts hmaps
  have hfc' : ContinuousOn (fun t : ℝ => deriv (f l) (Work.WilG4a.chart1 f κ l t))
      Work.WilG4a.I := hfc.comp hcts hmaps
  have hdiv : ContinuousOn (fun t : ℝ => K / deriv (f l) (Work.WilG4a.chart1 f κ l t))
      Work.WilG4a.I :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => K) Work.WilG4a.I).div hfc'
      (fun t ht => hfne _ (hmaps t ht))
  have hcont_deriv : ContinuousOn h Work.WilG4a.I := by
    rw [hh]
    exact hgc'.mul hdiv
  have hcontWithin : ContinuousOn
      (derivWithin (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) Work.WilG4a.I)
      Work.WilG4a.I := by
    refine hcont_deriv.congr (fun t ht => ?_)
    rw [derivWithin_of_isOpen (isOpen_Ioo (a := (0:ℝ)) (b := 1)) ht, (hderiv t ht).deriv]
  have hcd : ContDiffOn ℝ 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t))
      Work.WilG4a.I :=
    (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo 0 1)).2 ⟨hdiff, hcontWithin⟩
  refine ⟨hcd, fun t ht => ?_⟩
  rw [iteratedDeriv_one, (hderiv t ht).deriv]
  simp only [hh]
  have hy : Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.fibre κ l := hmaps t ht
  have hbpos : 0 < |deriv (f l) (Work.WilG4a.chart1 f κ l t)| := abs_pos.mpr (hfne _ hy)
  have ha : |deriv (g l) (Work.WilG4a.chart1 f κ l t)| ≤
      |deriv (f l) (Work.WilG4a.chart1 f κ l t)| := hdom _ hy
  have hK1 : |K| ≤ 1 := by rw [hK]; exact hAB
  calc |deriv (g l) (Work.WilG4a.chart1 f κ l t) *
        (K / deriv (f l) (Work.WilG4a.chart1 f κ l t))|
      = |deriv (g l) (Work.WilG4a.chart1 f κ l t)| * |K| /
          |deriv (f l) (Work.WilG4a.chart1 f κ l t)| := by
        rw [abs_mul, abs_div, mul_div_assoc]
    _ ≤ |deriv (f l) (Work.WilG4a.chart1 f κ l t)| * |K| /
          |deriv (f l) (Work.WilG4a.chart1 f κ l t)| := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hbpos)
        exact mul_le_mul_of_nonneg_right ha (abs_nonneg K)
    _ = |K| := by
        rw [mul_div_cancel_left₀ |K| (abs_ne_zero.mpr (hfne _ hy))]
    _ ≤ 1 := hK1

end Work.WilG4a
