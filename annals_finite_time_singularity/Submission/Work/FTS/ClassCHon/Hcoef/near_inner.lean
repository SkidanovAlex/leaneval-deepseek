import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgL2Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

theorem near_inner {q L a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    {c : ℝ → ℝ} (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (hc : ∀ t ∈ Set.Icc a b, |c t| ≤ L) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc a b) ∧
      |∫ t in Set.Ioc a b, c t * t ^ (q - 1)| ≤ L * b ^ q / q := by
  -- The pure power `t ↦ t ^ (q - 1)` is integrable on `Ioc a b` (`a > 0`, `q > 0`),
  -- and its integral is `(b ^ q - a ^ q) / q`.
  have hpow_int : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hpow_val : ∫ t in Set.Ioc a b, t ^ (q - 1) = (b ^ q - a ^ q) / q := by
    rw [← intervalIntegral.integral_of_le hab, integral_rpow (Or.inl (by linarith))]
    have : q - 1 + 1 = q := by ring
    rw [this]
  have hdom_int : MeasureTheory.IntegrableOn (fun t : ℝ => L * t ^ (q - 1)) (Set.Ioc a b) :=
    hpow_int.const_mul L
  -- Pointwise domination on `Ioc a b`.
  have hnorm : ∀ t ∈ Set.Ioc a b, ‖c t * t ^ (q - 1)‖ ≤ L * t ^ (q - 1) := by
    intro t ht
    have htpos : 0 < t := lt_trans ha ht.1
    have hle : 0 ≤ t ^ (q - 1) := Real.rpow_nonneg htpos.le _
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hle]
    exact mul_le_mul_of_nonneg_right (hc t htIcc) hle
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      ‖c t * t ^ (q - 1)‖ ≤ L * t ^ (q - 1) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun t ht => hnorm t ht)
  have hprod_int : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc a b) := by
    refine MeasureTheory.Integrable.mono' hdom_int ?_ hbound
    have haesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (q - 1))
        (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
      (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_trans ha hx.1)))).aestronglyMeasurable measurableSet_Ioc
    exact hcm.mul haesm
  refine ⟨hprod_int, ?_⟩
  have h1 : |∫ t in Set.Ioc a b, c t * t ^ (q - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) := by
    calc |∫ t in Set.Ioc a b, c t * t ^ (q - 1)|
        = ‖∫ t in Set.Ioc a b, c t * t ^ (q - 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t in Set.Ioc a b, ‖c t * t ^ (q - 1)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) :=
          MeasureTheory.integral_mono_ae hprod_int.norm hdom_int hbound
  have h2 : ∫ t in Set.Ioc a b, L * t ^ (q - 1) = L * ((b ^ q - a ^ q) / q) := by
    rw [MeasureTheory.integral_const_mul, hpow_val]
  have h3 : L * ((b ^ q - a ^ q) / q) ≤ L * b ^ q / q := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hq.le) hL
    have haq : 0 ≤ a ^ q := Real.rpow_nonneg ha.le q
    linarith
  calc |∫ t in Set.Ioc a b, c t * t ^ (q - 1)| ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) := h1
    _ = L * ((b ^ q - a ^ q) / q) := h2
    _ ≤ L * b ^ q / q := h3

end Work.FTS.ClassCHon.Hcoef
