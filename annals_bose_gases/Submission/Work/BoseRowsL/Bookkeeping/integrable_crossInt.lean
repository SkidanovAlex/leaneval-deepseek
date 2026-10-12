import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.cross_chat_coulomb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Bookkeeping

open MeasureTheory

/-- **Pointwise AM–GM domination of the cross Coulomb integrand by the two diagonal ones.**

For arbitrary (not necessarily integrable, nonnegative or even) `f g` and any `p`,

  `|Ŷf(p)·Ŷg(p)/(2‖p‖²)| ≤ Ŷf(p)²/(2‖p‖²) + Ŷg(p)²/(2‖p‖²)`,

where `Ŷ = Work.BoseFixR.chat`.  Both sides are `0` at `p = 0` (division by zero), so no
side condition on `p` is needed.  The inequality is the elementary `|ab| ≤ a² + b²`
(hence `≤ (a²+b²)/2·2`) divided by the common positive denominator `2‖p‖²`. -/
private lemma abs_crossInt_le (f g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat f p * Work.BoseFixR.chat g p / (2 * ‖p‖ ^ 2)|
      ≤ Work.BoseFixR.chat f p ^ 2 / (2 * ‖p‖ ^ 2)
        + Work.BoseFixR.chat g p ^ 2 / (2 * ‖p‖ ^ 2) := by
  rcases eq_or_lt_of_le (norm_nonneg p) with h | h
  · rw [← h]; simp
  · have hr : (0 : ℝ) < 2 * ‖p‖ ^ 2 := by positivity
    have h1 : |Work.BoseFixR.chat f p| * |Work.BoseFixR.chat g p|
        ≤ Work.BoseFixR.chat f p ^ 2 + Work.BoseFixR.chat g p ^ 2 := by
      nlinarith [sq_nonneg (|Work.BoseFixR.chat f p| - |Work.BoseFixR.chat g p|),
        sq_abs (Work.BoseFixR.chat f p), sq_abs (Work.BoseFixR.chat g p),
        abs_nonneg (Work.BoseFixR.chat f p), abs_nonneg (Work.BoseFixR.chat g p)]
    rw [abs_div, abs_mul, abs_of_pos hr, ← add_div]
    exact div_le_div_of_nonneg_right h1 hr.le

theorem integrable_crossInt {W U : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hU : MeasureTheory.Integrable U)
    (hWnn : ∀ᵐ x, 0 ≤ W x) (hUnn : ∀ᵐ x, 0 ≤ U x)
    (hWe : ∀ x, W (-x) = W x) (hUe : ∀ x, U (-x) = U x)
    (hP : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤)
    (hR2 : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (U x * U y / ‖x - y‖)) ≠ ⊤)
    (hX : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W x * U y / ‖x - y‖)) ≠ ⊤) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.chat W p * Work.BoseFixR.chat U p / (2 * ‖p‖ ^ 2)) := by
  -- ## Pointwise nonnegative, even representatives of the a.e. classes of `W` and `U`
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => max (W x) 0 with hfdef
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => max (U x) 0 with hgdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => by rw [hfdef]; exact le_max_right _ _
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hgdef]; exact le_max_right _ _
  have hfe : ∀ x, f (-x) = f x := fun x => by rw [hfdef]; simp only [hWe x]
  have hge : ∀ x, g (-x) = g x := fun x => by rw [hgdef]; simp only [hUe x]
  have haef : f =ᵐ[volume] W :=
    hWnn.mono (fun x hx => by rw [hfdef]; exact max_eq_left hx)
  have haeg : g =ᵐ[volume] U :=
    hUnn.mono (fun x hx => by rw [hgdef]; exact max_eq_left hx)
  have hfI : MeasureTheory.Integrable f := hW.congr haef.symm
  have hgI : MeasureTheory.Integrable g := hU.congr haeg.symm
  -- ## Finiteness of the two diagonal Coulomb doubles, transported along the a.e. classes
  have hPf : Work.BoseRowsFS.X2 f f ≠ ⊤ := by
    rw [Work.BoseRowsFS.x2_congr_ae haef haef]; exact hP
  have hPg : Work.BoseRowsFS.X2 g g ≠ ⊤ := by
    rw [Work.BoseRowsFS.x2_congr_ae haeg haeg]; exact hR2
  -- ## Integrability of the two diagonal momentum integrands (Fourier–Coulomb identity)
  have hIf : MeasureTheory.Integrable (Work.BoseRowsFS.diagInt f) :=
    Work.BoseRowsFS.diagInt_integrable hfI hf0 hfe hPf
  have hIg : MeasureTheory.Integrable (Work.BoseRowsFS.diagInt g) :=
    Work.BoseRowsFS.diagInt_integrable hgI hg0 hge hPg
  -- ## `chat` only sees the a.e. classes, so the target integrand is that of `(f, g)`
  have hfun : (fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.chat W p * Work.BoseFixR.chat U p / (2 * ‖p‖ ^ 2))
      = fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.chat f p * Work.BoseFixR.chat g p / (2 * ‖p‖ ^ 2) := by
    funext p
    rw [Work.BoseB7AK.C3Q.chat_congr_ae haef p, Work.BoseB7AK.C3Q.chat_congr_ae haeg p]
  rw [hfun]
  -- ## Domination by the sum of the two integrable diagonal integrands
  refine MeasureTheory.Integrable.mono' (hIf.add hIg) ?_ ?_
  · have hcf : Continuous (Work.BoseFixR.chat f) := Work.BoseBogFS.continuous_chat f hfI
    have hcg : Continuous (Work.BoseFixR.chat g) := Work.BoseBogFS.continuous_chat g hgI
    have hden : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => 2 * ‖p‖ ^ 2) := by fun_prop
    exact ((hcf.mul hcg).measurable.div hden.measurable).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_crossInt_le f g p

end Work.BoseRowsL.Bookkeeping
