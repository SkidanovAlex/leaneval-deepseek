import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem hasDerivAt_of_hasDerivWithinAt_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {c : ℝ → E} {T t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (hg : ContinuousOn g (Set.Icc 0 T))
    (hc : ContinuousOn c (Set.Ico 0 T))
    (hderiv : ∀ s ∈ Set.Ico 0 T, HasDerivWithinAt g (c s) (Set.Ici s) s) :
    HasDerivAt g (c t) t := by
  obtain ⟨ht0, htT⟩ := ht
  -- Work on a closed interval `[a, b] ⊆ (0, T)` containing `t` in its interior.
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have hat : a < t := by dsimp only [a]; linarith
  have htb : t < b := by dsimp only [b]; linarith
  have hbT : b < T := by dsimp only [b]; linarith
  -- The primitive of `c`, which is differentiable on `(0, T)` with derivative `c`.
  let P : ℝ → E := fun s => ∫ u in (0 : ℝ)..s, c u
  have hcIoo : ContinuousOn c (Set.Ioo 0 T) := hc.mono fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hcAt : ∀ x ∈ Set.Ioo 0 T, ContinuousAt c x :=
    fun x hx => isOpen_Ioo.continuousOn_iff.mp hcIoo hx
  have hPderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt P (c x) x := by
    intro x hx
    have hint : IntervalIntegrable c MeasureTheory.volume (0 : ℝ) x :=
      ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hx.1)
        (hc.mono fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hx.2⟩)
    have hmeas : StronglyMeasurableAtFilter c (nhds x) MeasureTheory.volume :=
      (hcIoo.stronglyMeasurableAtFilter isOpen_Ioo) x hx
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hcAt x hx)
  -- Hence `g - P` has vanishing right derivative on `[a, b)`.
  have hFderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt (g - P) 0 (Set.Ici x) x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 T :=
      ⟨lt_of_lt_of_le ha0 hx.1, lt_of_lt_of_le hx.2 (le_of_lt hbT)⟩
    have hgx : HasDerivWithinAt g (c x) (Set.Ici x) x :=
      hderiv x ⟨le_of_lt (lt_of_lt_of_le ha0 hx.1), lt_of_lt_of_le hx.2 (le_of_lt hbT)⟩
    have hPx : HasDerivWithinAt P (c x) (Set.Ici x) x := (hPderiv x hxIoo).hasDerivWithinAt
    simpa only [sub_self] using hgx.sub hPx
  have hPcont : ContinuousOn P (Set.Icc a b) := by
    intro x hx
    exact ((hPderiv x ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hbT⟩).continuousAt).continuousWithinAt
  have hFcont : ContinuousOn (g - P) (Set.Icc a b) :=
    (hg.mono fun x hx => ⟨le_trans (le_of_lt ha0) hx.1, le_trans hx.2 (le_of_lt hbT)⟩).sub hPcont
  -- So `g - P` is constant on `[a, b]`.
  have hseg : ∀ x ∈ Set.Icc a b, ‖(g - P) x - (g - P) a‖ ≤ 0 * (x - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hFcont hFderiv (fun x hx => by simp)
  have hconst : ∀ x ∈ Set.Icc a b, g x - P x = g a - P a := by
    intro x hx
    have h := hseg x hx
    simp only [Pi.sub_apply, zero_mul] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  -- Near `t`, `g` is a translate of `P`, hence differentiable with derivative `c t`.
  have hPt : HasDerivAt P (c t) t := hPderiv t ⟨ht0, htT⟩
  have hmain : HasDerivAt (fun x => (g a - P a) + P x) (c t) t := hPt.const_add (g a - P a)
  refine hmain.congr_of_eventuallyEq ?_
  have hmem : Set.Ioo a b ∈ nhds t := IsOpen.mem_nhds isOpen_Ioo ⟨hat, htb⟩
  filter_upwards [hmem] with x hx
  exact sub_eq_iff_eq_add.mp (hconst x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

end Work.FTS.PressureOn.Connect
