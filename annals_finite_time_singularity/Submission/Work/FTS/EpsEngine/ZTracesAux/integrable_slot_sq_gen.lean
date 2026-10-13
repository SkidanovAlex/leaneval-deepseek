import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The `θ`-slice of the square of a mixed slot is integrable on `Iθ` once its `w`-weighted
square is dominated by the `ℋ^m`-integrand, whose `θ`-slice is integrable by `HkMem`.

The only analytic input is a.e. strong measurability of the slice, supplied by the continuity
hypothesis on the open interval `(0,π/2)` (which agrees with `Iθ` up to the null set of the
two endpoints). -/
theorem integrable_slot_sq_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (b a : ℕ) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun σ => Work.Spaces.mixed b a f s σ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α m f s σ) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b a f s σ) ^ 2) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (Work.FTS_RegExport.RXT.Slots.aesm_Iθ_of_continuousOn_Ioo_aux (hcont.pow 2)) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hwne : (Work.Spaces.w s) ^ 2 ≠ 0 := by
    have h := Work.FTS_RegExport.RXT.Slots.w_pos_aux hs
    positivity
  have hkey : (Work.Spaces.mixed b a f s σ) ^ 2
      = (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 / (Work.Spaces.w s) ^ 2 := by
    rw [mul_pow, eq_div_iff hwne]
  rw [hkey]
  exact div_le_div_of_nonneg_right (hpoint σ hσ) (sq_nonneg _)

end Work.FTS.EpsEngine.ZTracesAux
