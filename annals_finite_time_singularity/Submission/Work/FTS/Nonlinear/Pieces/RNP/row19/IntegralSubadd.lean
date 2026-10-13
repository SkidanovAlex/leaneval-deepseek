/-
# Subadditivity of the Bochner integral for nonnegative functions

For `f g : α → ℝ` that are nonnegative a.e. (and a.e.-measurable), the Bochner integral is
subadditive:

  `∫ x, (f x + g x) ∂μ ≤ ∫ x, f x ∂μ + ∫ x, g x ∂μ`.

The point is that this needs *no* integrability hypothesis: if `f + g` is not integrable then
Lean's Bochner integral gives the value `0` on the left, while the right-hand side is `≥ 0`
(each of `∫ f`, `∫ g` is `0` — the junk value — or an honest nonnegative number).  Without this
lemma one cannot bound `∫ (A + B)` by `∫ A + ∫ B` when one of the two summands is not
integrable, which is precisely the situation of the row-19 junk term.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open MeasureTheory

theorem integral_add_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    ∫ x, (f x + g x) ∂μ ≤ (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := by
  by_cases h : Integrable (fun x => f x + g x) μ
  · have hff : Integrable f μ :=
      h.mono' hfm.aestronglyMeasurable (by
        filter_upwards [hf, hg] with x hfx hgx
        simp only [Pi.zero_apply] at hfx hgx
        rw [Real.norm_eq_abs, abs_of_nonneg hfx]
        linarith)
    have hgg : Integrable g μ :=
      h.mono' hgm.aestronglyMeasurable (by
        filter_upwards [hf, hg] with x hfx hgx
        simp only [Pi.zero_apply] at hfx hgx
        rw [Real.norm_eq_abs, abs_of_nonneg hgx]
        linarith)
    rw [integral_add hff hgg]
  · rw [integral_undef h]
    have h1 : 0 ≤ ∫ x, f x ∂μ := by
      by_cases hi : Integrable f μ
      · exact integral_nonneg_of_ae hf
      · rw [integral_undef hi]
    have h2 : 0 ≤ ∫ x, g x ∂μ := by
      by_cases hi : Integrable g μ
      · exact integral_nonneg_of_ae hg
      · rw [integral_undef hi]
    linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
