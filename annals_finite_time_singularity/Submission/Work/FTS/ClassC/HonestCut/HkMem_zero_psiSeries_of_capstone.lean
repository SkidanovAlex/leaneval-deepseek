import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral
import Submission.Work.FTS.ClassC.HonestCut.integrableOn_slice_psiSeries_zero
import Submission.Work.FTS.PhiStar.Series.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

/-!
# `HkMem α 0 (psiSeries α F)` from the capstone's finiteness data

The `H^k`-honesty of the mode series at level `0` is the conjunction of

* `∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 0 Ψ z θ) Iθ` (`Iz = [0,∞)`), and
* `IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α 0 Ψ z θ) Iz`.

The capstone supplies the *iterated `lintegral`* bound (`hfin`, with the two measurability
inputs `hslmeas`, `hmeas`), which by `HkMemAe_of_lintegral` yields the *almost everywhere*
version of both assertions, with the outer integral taken over `(0,∞)` only (the `lintegral`
in `hfin` is over `Set.Ioi 0`).  The two gaps are closed as follows.

* The point `z = 0` (the difference between `Iz = [0,∞)` and `(0,∞)`) is trivial: the radial
  weight vanishes there, `w 0 = 0`, which kills `HkIntegrand` identically
  (`HkIntegrand_zero_at_zero`).  Likewise `{0}` is null, so integrability over `(0,∞)`
  upgrades to integrability over `[0,∞)` (`MeasureTheory.restrict_Ioi_eq_restrict_Ici`).
* The `θ`-slice at a fixed `z > 0` is integrable *everywhere*, not merely a.e., by the
  self-contained `integrableOn_slice_psiSeries_zero`, whose only input is the weighted
  summability `hcoef` of the radial coefficients (available for every `z > 0`).
-/

/-- At `z = 0` the radial weight `w` vanishes, so the whole `H^0`-integrand vanishes. -/
lemma HkIntegrand_zero_at_zero (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 Ψ 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, hw, zero_div, mul_zero]
  simp

theorem HkMem_zero_psiSeries_of_capstone {α : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    Work.Spaces.HkMem α 0 (Work.FTS.PhiStar.Series.psiSeries α F) := by
  obtain ⟨-, hout⟩ := HkMemAe_of_lintegral (α := α)
    (Ψ := Work.FTS.PhiStar.Series.psiSeries α F) hC hslmeas hfin hmeas
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes, so the slice integrand is identically zero.
      rw [← hz0]
      rw [show (fun θ => Work.Spaces.HkIntegrand α 0
              (Work.FTS.PhiStar.Series.psiSeries α F) 0 θ) = fun _ => (0 : ℝ) from
            funext fun θ => HkIntegrand_zero_at_zero α _ θ]
      exact integrableOn_zero
    · -- `z > 0`: the slice is integrable by the weighted summability of the coefficients.
      exact integrableOn_slice_psiSeries_zero z hzpos (hcoef z hzpos)
  · -- `{0}` is null, so the outer integrability over `(0,∞)` upgrades to `[0,∞)`.
    rw [Work.Spaces.Iz]
    change Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ)
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (μ := volume) (a := (0 : ℝ))]
    exact hout

end Work.FTS.ClassC.HonestCut
