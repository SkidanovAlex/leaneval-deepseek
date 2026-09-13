import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Measure.LpSeminorm

open MeasureTheory
open scoped ENNReal

theorem norm_le_toReal_eLpNorm_top {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin 4) → F} {s : Set (EuclideanSpace ℝ (Fin 4))} (hs : IsOpen s)
    (hcont : ContinuousOn f s)
    (hfin : MeasureTheory.eLpNorm f (⊤ : ENNReal) (MeasureTheory.volume.restrict s) < ⊤)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ s) :
    ‖f x‖ ≤ (MeasureTheory.eLpNorm f (⊤ : ENNReal) (MeasureTheory.volume.restrict s)).toReal := by
  let c : ℝ≥0∞ := eLpNorm f ⊤ (volume.restrict s)
  let M : ℝ := c.toReal
  change ‖f x‖ ≤ M
  have hcne : c ≠ ⊤ := ne_of_lt hfin
  have h1 : ∀ᵐ y ∂(volume.restrict s), ‖f y‖ₑ ≤ c := by
    have h := ae_le_eLpNormEssSup (f := f) (μ := volume.restrict s)
    simpa [c, eLpNorm_exponent_top] using h
  have hae : ∀ᵐ y ∂(volume.restrict s), ‖f y‖ ≤ M := by
    filter_upwards [h1] with y hy
    have h2 := ENNReal.toReal_mono hcne hy
    rwa [toReal_enorm] at h2
  have hmin_eq : (fun y => min (‖f y‖) M) =ᵐ[volume.restrict s] (fun y => ‖f y‖) := by
    filter_upwards [hae] with y hy
    exact min_eq_left hy
  have hnormcont : ContinuousOn (fun y => ‖f y‖) s := hcont.norm
  have hmincont : ContinuousOn (fun y => min (‖f y‖) M) s :=
    continuous_min.comp_continuousOn (hnormcont.prodMk continuousOn_const)
  have heq : Set.EqOn (fun y => min (‖f y‖) M) (fun y => ‖f y‖) s :=
    Measure.eqOn_open_of_ae_eq hmin_eq hs hmincont hnormcont
  have hx' : min (‖f x‖) M = ‖f x‖ := heq hx
  exact min_eq_left_iff.mp hx'

end Commons.Measure.LpSeminorm