import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

/-- The `y`-integral over the analysis cube of `|g₀(z−y)|·χ_{B(u)}(y)` is bounded by `Bv` times the
full mass `∫ χ_{B(u)}`, using `|g₀| ≤ |v| ≤ Bv` a.e. (which the chosen scattering solution
provides) and `χ_{B(u)} ≥ 0`.  The pointwise sup bound on `χ_{B(u)}` used for the integrability of
the majorant is `chiSupAbs · chiSmallDecay M` (the `ℓ`-scale factor is the corpus bump `chiScale L`,
bounded by `chiSupAbs`; the `(ℓd)`-scale factor by `chiSmallDecay M`). -/
theorem integral_abs_g0_shift_mul_chiSmallB_le {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R0 Bv : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv)
    {M : ℕ} (hM : 1 ≤ M) {d : ℕ} (hd : (0 : ℝ) < (d : ℝ))
    {L : ℝ} (hL : 1 ≤ L) (u z : EuclideanSpace ℝ (Fin 3)) :
    ∫ y in Submission.BoseGases.acube L, |Submission.BoseGases.g0 v h (z - y)| *
        Submission.BoseGases.chiSmallB M L (d : ℝ) u y ≤
      Bv * ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L (d : ℝ) u y := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hBv : 0 ≤ Bv := le_trans (abs_nonneg (v 0)) (hvb 0)
  set χ : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.chiSmallB M L (d : ℝ) u with hχ
  have hχnn : ∀ y, 0 ≤ χ y := by
    intro y
    rw [hχ]
    exact mul_nonneg (Submission.BoseGases.chiScale_nonneg L y)
      (Submission.BoseGases.chiSmall_nonneg M _)
  have hχint : Integrable χ := by
    rw [hχ]
    exact (Submission.BoseGases.chiSmallB_continuous hM hLpos hd u).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM hLpos u)
  have hg0bound : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h x| ≤ Bv := by
    have h1 := Submission.BoseGases.g0_abs_le_v_ae hR0 hv hvrad hv_supp h
    filter_upwards [h1] with x hx
    exact le_trans hx (le_trans (le_abs_self (v x)) (hvb x))
  have hshift : ∀ᵐ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (z - y)| ≤ Bv :=
    (MeasureTheory.Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hg0bound
  have hg0_int : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hshift_int :
      Integrable (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (z - y)|) :=
    (hg0_int.abs).comp_sub_left z
  have hχbound : ∀ y, χ y ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro y
    rw [hχ]
    have h1 : Submission.BoseGases.chiScale L y ≤ Submission.BoseGases.chiSupAbs :=
      le_trans (le_abs_self _) (Submission.BoseGases.chiScale_abs_le_sup L y)
    have h2 : Submission.BoseGases.chiSmall M ((L * (d : ℝ))⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M :=
      le_trans (le_abs_self _) (Submission.BoseGases.chiSmall_decay_coord_le_decay hM _)
    exact mul_le_mul h1 h2 (Submission.BoseGases.chiSmall_nonneg M _)
      Submission.BoseGases.chiSupAbs_nonneg
  have hF_aesm :
      AEStronglyMeasurable (fun y => |Submission.BoseGases.g0 v h (z - y)| * χ y) volume :=
    hshift_int.aestronglyMeasurable.mul hχint.aestronglyMeasurable
  have hF_int : Integrable (fun y => |Submission.BoseGases.g0 v h (z - y)| * χ y) := by
    refine Integrable.mono'
      (hshift_int.const_mul (Submission.BoseGases.chiSupAbs *
        Submission.BoseGases.chiSmallDecay M)) hF_aesm ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    have hnn : 0 ≤ |Submission.BoseGases.g0 v h (z - y)| * χ y :=
      mul_nonneg (abs_nonneg _) (hχnn y)
    rw [abs_of_nonneg hnn]
    calc |Submission.BoseGases.g0 v h (z - y)| * χ y
        ≤ |Submission.BoseGases.g0 v h (z - y)| *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
          mul_le_mul_of_nonneg_left (hχbound y) (abs_nonneg _)
      _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
            |Submission.BoseGases.g0 v h (z - y)| := by ring
  have hG_int : Integrable (fun y => Bv * χ y) := hχint.const_mul Bv
  have step1 : ∫ y in Submission.BoseGases.acube L, |Submission.BoseGases.g0 v h (z - y)| * χ y
      ≤ ∫ y in Submission.BoseGases.acube L, Bv * χ y := by
    refine MeasureTheory.setIntegral_mono_ae_restrict hF_int.restrict hG_int.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hshift] with y hy
    exact mul_le_mul_of_nonneg_right hy (hχnn y)
  have step2 : ∫ y in Submission.BoseGases.acube L, Bv * χ y
      = Bv * ∫ y in Submission.BoseGases.acube L, χ y := by
    rw [MeasureTheory.integral_const_mul]
  have step3 : ∫ y in Submission.BoseGases.acube L, χ y ≤ ∫ y, χ y :=
    MeasureTheory.setIntegral_le_integral hχint (Filter.Eventually.of_forall hχnn)
  calc ∫ y in Submission.BoseGases.acube L, |Submission.BoseGases.g0 v h (z - y)| * χ y
      ≤ ∫ y in Submission.BoseGases.acube L, Bv * χ y := step1
    _ = Bv * ∫ y in Submission.BoseGases.acube L, χ y := step2
    _ ≤ Bv * ∫ y, χ y := mul_le_mul_of_nonneg_left step3 hBv

end Work.UBBInputs8.A
