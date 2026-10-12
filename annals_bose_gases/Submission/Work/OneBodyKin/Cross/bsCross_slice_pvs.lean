import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.CrossDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open Submission.BoseGases

namespace Work.OneBodyKin.Cross

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

lemma bsCross_slice_pvs {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.OneBodyKin.bsLf ℓ F z.1 z.2.1 * ψ (ℓ • (z.2.1 + u)) * ψ (ℓ • (u + z.2.2)))
      (MeasureTheory.volume.prod (MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1)))) := by
  -- `ψ` is bounded, say by `Cψ ≥ 0`
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  -- `χ` is integrable (`Cχ := ∫|χ|`)
  set Cχ : ℝ := ∫ z : ℝ³, |chi z| with hCχ
  have hchi_int : Integrable (fun z : ℝ³ => |chi z|) :=
    (chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport).abs
  -- `volume↾acube 1` is a finite measure, so constants are integrable on it
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top 1 (by norm_num)⟩
  have hχ2 : Integrable (fun w : ℝ³ × ℝ³ => |chi w.1|)
      (volume.prod ((volume : Measure ℝ³).restrict (acube 1))) := by
    simpa using hchi_int.mul_prod (integrable_const (1 : ℝ))
  -- the `p`-factor is `L¹`
  have hF1 : Integrable (fun p : ℝ³ => |F ‖p‖|) := by
    simpa [Real.norm_eq_abs] using hFi.norm
  -- the dominating function is a product of two `L¹` functions of separate variables
  have hpair : Integrable (fun z : ℝ³ × (ℝ³ × ℝ³) => |F ‖z.1‖| * |chi z.2.1|)
      (volume.prod (volume.prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
    hF1.mul_prod hχ2
  have hmaj : Integrable
      (fun z : ℝ³ × (ℝ³ × ℝ³) => (Cχ * Cψ ^ 2) * (|F ‖z.1‖| * |chi z.2.1|))
      (volume.prod (volume.prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
    hpair.const_mul _
  refine hmaj.mono' ?_ ?_
  · -- a.e. strong measurability of the integrand
    have hFmeas : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) => F ‖z.1‖)
        (volume.prod (volume.prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
      hFi.aestronglyMeasurable.comp_fst
    have h1 : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) => profHat (ℓ • z.1)) :=
      continuous_profHat.comp ((continuous_const_smul ℓ).comp continuous_fst)
    have h2 : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) => chi z.2.1) :=
      chi_continuous.comp (continuous_fst.comp continuous_snd)
    have h3 : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) => Real.cos (inner ℝ (ℓ • z.1) z.2.1)) :=
      Real.continuous_cos.comp
        (((continuous_const_smul ℓ).comp continuous_fst).inner
          (continuous_fst.comp continuous_snd))
    have h4 : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) => ψ (ℓ • (z.2.1 + u))) :=
      hψ.continuous.comp (((continuous_const_smul ℓ).comp
        ((continuous_fst.comp continuous_snd).add continuous_const)))
    have h5 : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) => ψ (ℓ • (u + z.2.2))) :=
      hψ.continuous.comp (((continuous_const_smul ℓ).comp
        (continuous_const.add (continuous_snd.comp continuous_snd))))
    have hsm : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) =>
        profHat (ℓ • z.1) * chi z.2.1 * Real.cos (inner ℝ (ℓ • z.1) z.2.1) *
          ψ (ℓ • (z.2.1 + u)) * ψ (ℓ • (u + z.2.2)))
        (volume.prod (volume.prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
      ((((h1.mul h2).mul h3).mul h4).mul h5).aestronglyMeasurable
    refine (hFmeas.mul hsm).congr ?_
    filter_upwards with z
    simp only [Work.OneBodyKin.bsLf, Pi.mul_apply]
    ring
  · -- the pointwise domination
    filter_upwards with z
    obtain ⟨p, w⟩ := z
    obtain ⟨v, s⟩ := w
    have h1 : |Work.OneBodyKin.bsLf ℓ F p v| ≤ Cχ * |F ‖p‖| * |chi v| := by
      rw [hCχ]; exact abs_bsLf_le ℓ F p v
    have h2 : |ψ (ℓ • (v + u))| ≤ Cψ := hCψ _
    have h3 : |ψ (ℓ • (u + s))| ≤ Cψ := hCψ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Work.OneBodyKin.bsLf ℓ F p v| * |ψ (ℓ • (v + u))| * |ψ (ℓ • (u + s))|
        ≤ (Cχ * |F ‖p‖| * |chi v|) * Cψ * Cψ := by gcongr
      _ = (Cχ * Cψ ^ 2) * (|F ‖p‖| * |chi v|) := by ring_nf

end Work.OneBodyKin.Cross
