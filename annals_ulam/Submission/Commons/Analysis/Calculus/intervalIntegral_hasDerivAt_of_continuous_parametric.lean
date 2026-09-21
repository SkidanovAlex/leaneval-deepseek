import Mathlib
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_upper_piece_of_continuous

namespace Commons.Analysis.Calculus

open Filter MeasureTheory
open scoped Topology Interval

lemma intervalIntegral_hasDerivAt_of_continuous_parametric
    {F F' : ℝ → ℝ → ℝ} {x y : ℝ → ℝ} {x' y' : ℝ} {s : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u)
    (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s)
    (hx_cont : ContinuousAt x s) (hy_cont : ContinuousAt y s) :
    HasDerivAt (fun u : ℝ => ∫ t in (-x u)..(y u), F u t)
      (F s (y s) * y' - F s (-x s) * (-x') + ∫ t in (-x s)..(y s), F' s t) s := by
  have hupper : HasDerivAt (fun u : ℝ => ∫ t in 0..(y u), F u t)
      ((∫ t in 0..(y s), F' s t) + F s (y s) * y') s :=
    intervalIntegral_hasDerivAt_upper_piece_of_continuous (c := 0) (y := y) (y' := y')
      hF_cont hF'_cont hF'_isDeriv hy hy_cont
  have ha_deriv : HasDerivAt (fun u : ℝ => -x u) (-x') s := hx.neg
  have ha_cont : ContinuousAt (fun u : ℝ => -x u) s := hx_cont.neg
  have hlower0 : HasDerivAt (fun u : ℝ => ∫ t in 0..(-x u), F u t)
      ((∫ t in 0..(-x s), F' s t) + F s (-x s) * (-x')) s :=
    intervalIntegral_hasDerivAt_upper_piece_of_continuous (c := 0) (y := fun u : ℝ => -x u)
      (y' := -x') hF_cont hF'_cont hF'_isDeriv ha_deriv ha_cont
  have hlower : HasDerivAt (fun u : ℝ => -∫ t in 0..(-x u), F u t)
      (-((∫ t in 0..(-x s), F' s t) + F s (-x s) * (-x'))) s :=
    hlower0.neg
  have hsum : HasDerivAt
      (fun u : ℝ => (∫ t in 0..(y u), F u t) + (-∫ t in 0..(-x u), F u t))
      (((∫ t in 0..(y s), F' s t) + F s (y s) * y')
        + (-((∫ t in 0..(-x s), F' s t) + F s (-x s) * (-x')))) s :=
    hupper.add hlower
  have hderiv_eq :
      ((∫ t in 0..(y s), F' s t) + F s (y s) * y')
        + (-((∫ t in 0..(-x s), F' s t) + F s (-x s) * (-x')))
        = F s (y s) * y' - F s (-x s) * (-x') + ∫ t in (-x s)..(y s), F' s t := by
    have hF'_cont_s : Continuous (fun t : ℝ => F' s t) := by
      exact hF'_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (s, t)))
    have hint0a : IntervalIntegrable (fun t : ℝ => F' s t) volume 0 (-x s) :=
      hF'_cont_s.intervalIntegrable _ _
    have hint0b : IntervalIntegrable (fun t : ℝ => F' s t) volume 0 (y s) :=
      hF'_cont_s.intervalIntegrable _ _
    have hint_a0 : IntervalIntegrable (fun t : ℝ => F' s t) volume (-x s) 0 :=
      hF'_cont_s.intervalIntegrable _ _
    have hadj : (∫ t in (-x s)..0, F' s t) + ∫ t in 0..(y s), F' s t
        = ∫ t in (-x s)..(y s), F' s t :=
      intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (f := fun t : ℝ => F' s t) (a := -x s) (b := 0) (c := y s) hint_a0 hint0b
    have hsym : (∫ t in (-x s)..0, F' s t) = -∫ t in 0..(-x s), F' s t :=
      intervalIntegral.integral_symm 0 (-x s)
    have hint_eq : ∫ t in (-x s)..(y s), F' s t
        = (∫ t in 0..(y s), F' s t) - (∫ t in 0..(-x s), F' s t) := by
      rw [← hadj, hsym]
      ring
    rw [hint_eq]
    ring
  have hsum' : HasDerivAt
      (fun u : ℝ => (∫ t in 0..(y u), F u t) + (-∫ t in 0..(-x u), F u t))
      (F s (y s) * y' - F s (-x s) * (-x') + ∫ t in (-x s)..(y s), F' s t) s :=
    hsum.congr_deriv hderiv_eq
  have hfun : (fun u : ℝ => ∫ t in (-x u)..(y u), F u t)
      = fun u : ℝ => (∫ t in 0..(y u), F u t) + (-∫ t in 0..(-x u), F u t) := by
    funext u
    have hcontF : Continuous (fun t : ℝ => F u t) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (u, t)))
    have hint1 : IntervalIntegrable (fun t : ℝ => F u t) volume (-x u) 0 :=
      hcontF.intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t : ℝ => F u t) volume 0 (y u) :=
      hcontF.intervalIntegrable _ _
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F u t) (a := -x u) (b := 0) (c := y u) hint1 hint2
    -- hadj : ∫ in a..0 + ∫ in 0..c = ∫ in a..c
    calc
      ∫ t in (-x u)..(y u), F u t = (∫ t in (-x u)..0, F u t) + ∫ t in 0..(y u), F u t := by
        rw [← hadj]
      _ = (∫ t in 0..(y u), F u t) + (-∫ t in 0..(-x u), F u t) := by
        rw [intervalIntegral.integral_symm 0 (-x u)]
        ring
  have hfinal := hsum'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => by exact congrFun hfun u))
  exact hfinal
