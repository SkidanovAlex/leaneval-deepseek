import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The radial mode coefficients of a general-source modal solution are a.e. measurable on
`Iz = [0,∞)`.**

`acoeff α m F = radGreen α m (cmode m F)`; for a source which is `C^∞` on the open quadrant and
honest at levels `0` and `1`, `cmode m F` is continuous on `(0,∞)`
(`Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one`) and `(cmode m F)² ∈ L¹(0,∞)`
(`Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable`, whose two halves are `c²/t⁴` on
`(0,1)` and `c²` on `(1,∞)`), so `z ↦ radGreen α m (cmode m F) z` is continuous on `(0,∞)` by
`Work.FTS.H2.ModalSolR.radGreenContinuousOn`; the missing point `z = 0` is null, and
`volume.restrict Iz` is `volume.restrict (Ioi 0)` up to that null set.

This is the `hacm` input of the measurability bundle of the level-`0` honesty of
`psiSeries α F`.  (The sibling `Work.FTS.ClassCHon.CmpSupp.acoeff_aemeasurable` proves the same
for a *compactly supported* source, where continuity comes from the compact support of
`cmode m F` instead.) -/
theorem aemeasurable_acoeff_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (hF1 : Work.Spaces.HkMem α 1 F) :
    ∀ m : ℕ, AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro m
  have hα1 : α ≤ 1 := by linarith
  -- continuity of the mode coefficient `cmode m F` on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z) (Set.Ioi 0) :=
    Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one m hsm hF1
  -- square integrability of `cmode m F` on `(0,∞)`, from the two halves of the mode energy
  have hsq : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := by
    obtain ⟨hnear, hfar⟩ :=
      Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable (α := α) m hsm hF0
    -- near `0`: `c² ≤ c²/t⁴` on `(0,1)`
    have hn1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioo 0 1) := by
      refine MeasureTheory.Integrable.mono' hnear ?_ ?_
      · have hmeas : MeasureTheory.AEStronglyMeasurable
            (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
          ((hcont.aestronglyMeasurable measurableSet_Ioi).mono_set
            (fun t ht => ht.1)).pow 2
        simpa only [Pi.pow_apply] using hmeas
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht.1 4
        have hle : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
        rw [Real.norm_of_nonneg (sq_nonneg _), le_div_iff₀ ht4]
        have hmul : (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * t ^ 4
            ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        simpa using hmul
    -- far out: `(1,∞)` versus `[1,∞)` differ by the null set `{1}`
    have hn2 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ici 1) :=
      hfar.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
    have hun : Set.Ioi (0 : ℝ) = Set.Ioo 0 1 ∪ Set.Ici 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
      constructor
      · intro ht
        rcases lt_or_ge t 1 with h | h
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr h
      · rintro (⟨h1, _⟩ | h1)
        · exact h1
        · linarith
    rw [hun]
    exact hn1.union hn2
  -- a.e. strong measurability of `cmode m F` on `(0,∞)`
  have hcm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  -- continuity of the modal radial Green function on `(0,∞)`
  have hrg : ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => Work.FTS.PhiStar.Series.cmode m F t)) (Set.Ioi 0) :=
    Work.FTS.H2.ModalSolR.radGreenContinuousOn hα hα1 m hsq hcm
  have hae : AEMeasurable (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => Work.FTS.PhiStar.Series.cmode m F t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hrg.aemeasurable measurableSet_Ioi
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hIz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rw [hIz]
  simpa only [Work.FTS.PhiStar.Series.acoeff] using hae

end Work.FTS.ClassCHon
