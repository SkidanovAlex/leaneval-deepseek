import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.inner_integral_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function
open scoped ENNReal Topology

namespace Work.MRMT.Found

/-! ## Elementary lemmas about the `ℝ≥0∞`-valued Cauchy kernel -/

/-- `‖a / b‖ₑ` in terms of the Cauchy kernel `ℝ≥0∞`-valued factor `ofReal (‖b‖⁻¹)`.

Unlike `enorm_inv` this holds at `b = 0` too, because `ofReal (‖0‖⁻¹) = 0` is the correct
value there (the `ℝ≥0∞`-inverse of `0` is `⊤`, which is *not* what the kernel integral needs). -/
lemma enorm_div_eq_mul_ofReal_inv (a b : ℂ) :
    ‖a / b‖ₑ = ‖a‖ₑ * ENNReal.ofReal (‖b‖⁻¹) := by
  rw [div_eq_mul_inv, enorm_mul]
  congr 1
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; simp
  · rw [enorm_inv hb, ← ofReal_norm]
    exact (ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hb)).symm

/-- The algebraic identity behind Cauchy–Schwarz with the Cauchy kernel: splitting
`a * k = (a²k)^{1/2} k^{1/2}`. -/
lemma rpow_half_mul_rpow_half (a k : ℝ≥0∞) :
    (a ^ 2 * k) ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ) = a * k := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [show a ^ 2 * k * k = (a * k) ^ 2 by ring]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- `(a b)² = a² b²` for `ℝ≥0∞`. -/
lemma mul_sq (a b : ℝ≥0∞) : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  rw [← ENNReal.rpow_two, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.rpow_two, ENNReal.rpow_two]

/-- `eLpNorm f 2 μ` as the square root of `∫⁻ ‖f‖²`. -/
lemma eLpNorm_two (f : ℂ → ℂ) (μ : Measure ℂ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, one_div]
  congr 1
  exact lintegral_congr fun z => ENNReal.rpow_two (‖f z‖ₑ)

/-- `(A^{1/2} B^{1/2})² = AB`, the "squaring" half of the same identity. -/
lemma sq_rpow_half_mul (A B : ℝ≥0∞) :
    (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 = A * B := by
  rw [← ENNReal.rpow_two, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

/-- Uniform bound for the `lintegral` of the Cauchy kernel in the `z`-variable. -/
lemma lintegral_cauchyKernel_le (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    ∫⁻ ζ in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹)
      ≤ ENNReal.ofReal (8 * Real.pi * R) := by
  rw [show (∫⁻ ζ in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹))
      = (∫⁻ ζ in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖z - ζ‖⁻¹)) from
    lintegral_congr fun ζ => by rw [norm_sub_rev]]
  exact Work.MRMT.Cauchy.inner_integral_bound (Metric.ball (0 : ℂ) R) R hR subset_rfl z

/-- The same uniform bound, in the orientation where the second variable is integrated. -/
lemma lintegral_cauchyKernel_le' (R : ℝ) (hR : 0 ≤ R) (ζ : ℂ) :
    ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹)
      ≤ ENNReal.ofReal (8 * Real.pi * R) :=
  Work.MRMT.Cauchy.inner_integral_bound (Metric.ball (0 : ℂ) R) R hR subset_rfl ζ


/-! ## The Schur/Tonelli bound for the Cauchy kernel on balls -/

/-- **`L²` bound for the Cauchy kernel integral.** For any `f : ℂ → ℂ` and radii `R, R' ≥ 0`,
`∫⁻ z in ball 0 R', (∫⁻ ζ in ball 0 R, ‖f ζ‖ ⟶⁻¹ ‖ζ-z‖⁻¹)² ≤ 8πR · 8πR' · ∫⁻ ζ in ball 0 R, ‖f ζ‖²`.

The proof is Cauchy–Schwarz in the `ζ`-variable *pointwise in `z`*, using the uniform bounds
`∫⁻ ζ in ball 0 R, ‖ζ-z‖⁻¹ ≤ 8πR` and `∫⁻ z in ball 0 R', ‖ζ-z‖⁻¹ ≤ 8πR'`, followed by Tonelli. -/
theorem lintegral_sq_cauchyKernel_le (f : ℂ → ℂ) {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hf : AEMeasurable f (volume : Measure ℂ)) :
    ∫⁻ z in Metric.ball (0 : ℂ) R',
        (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2
      ≤ ENNReal.ofReal (8 * Real.pi * R) * ENNReal.ofReal (8 * Real.pi * R')
          * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 := by
  classical
  have hKm : ∀ z : ℂ, Measurable (fun ζ : ℂ => ENNReal.ofReal (‖ζ - z‖⁻¹)) := fun z =>
    ENNReal.measurable_ofReal.comp (((continuous_id.sub continuous_const).norm).measurable.inv)
  have hzm : ∀ ζ : ℂ, Measurable (fun z : ℂ => ENNReal.ofReal (‖ζ - z‖⁻¹)) := fun ζ =>
    ENNReal.measurable_ofReal.comp (((continuous_const.sub continuous_id).norm).measurable.inv)
  -- Pointwise Cauchy–Schwarz in `ζ`.
  have hcs : ∀ z : ℂ,
      (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2
        ≤ ENNReal.ofReal (8 * Real.pi * R)
            * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
    intro z
    set F : ℂ → ℝ≥0∞ := fun ζ => ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) with hF
    set G : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (‖ζ - z‖⁻¹) with hG
    have hFm : AEMeasurable F (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      rw [hF]
      exact (hf.restrict.enorm.pow_const 2).mul ((hKm z).aemeasurable)
    have hGm : AEMeasurable G (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      rw [hG]; exact (hKm z).aemeasurable
    have hold := ENNReal.lintegral_mul_norm_pow_le hFm hGm (p := 1 / 2) (q := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    have hL : ∫⁻ ζ in Metric.ball (0 : ℂ) R, F ζ ^ (1 / 2 : ℝ) * G ζ ^ (1 / 2 : ℝ)
        = ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro ζ _
      rw [hF, hG]
      exact rpow_half_mul_rpow_half (‖f ζ‖ₑ) _
    have hGs : ∫⁻ ζ in Metric.ball (0 : ℂ) R, G ζ ≤ ENNReal.ofReal (8 * Real.pi * R) := by
      rw [hG]; exact lintegral_cauchyKernel_le R hR z
    calc (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2
        = (∫⁻ ζ in Metric.ball (0 : ℂ) R, F ζ ^ (1 / 2 : ℝ) * G ζ ^ (1 / 2 : ℝ)) ^ 2 := by rw [hL]
      _ ≤ ((∫⁻ ζ in Metric.ball (0 : ℂ) R, F ζ) ^ (1 / 2 : ℝ)
              * (∫⁻ ζ in Metric.ball (0 : ℂ) R, G ζ) ^ (1 / 2 : ℝ)) ^ 2 :=
            ENNReal.pow_le_pow_left hold
      _ = (∫⁻ ζ in Metric.ball (0 : ℂ) R, F ζ) * (∫⁻ ζ in Metric.ball (0 : ℂ) R, G ζ) :=
            sq_rpow_half_mul _ _
      _ ≤ (∫⁻ ζ in Metric.ball (0 : ℂ) R, F ζ) * ENNReal.ofReal (8 * Real.pi * R) :=
            mul_le_mul_right hGs _
      _ = ENNReal.ofReal (8 * Real.pi * R)
            * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
            rw [hF, mul_comm]
  have hjoint : AEMeasurable (Function.uncurry
      (fun z ζ : ℂ => ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹)))
      ((volume.restrict (Metric.ball (0 : ℂ) R')).prod (volume.restrict (Metric.ball (0 : ℂ) R))) := by
    have h1 : AEMeasurable (fun p : ℂ × ℂ => ‖f p.2‖ₑ ^ 2)
        ((volume.restrict (Metric.ball (0 : ℂ) R')).prod (volume.restrict (Metric.ball (0 : ℂ) R))) :=
      (((hf.restrict (s := Metric.ball (0 : ℂ) R)).enorm).comp_snd
        (μ := volume.restrict (Metric.ball (0 : ℂ) R'))).pow_const 2
    have h2 : AEMeasurable (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.2 - p.1‖⁻¹))
        ((volume.restrict (Metric.ball (0 : ℂ) R')).prod (volume.restrict (Metric.ball (0 : ℂ) R))) :=
      (ENNReal.measurable_ofReal.comp
        (((continuous_snd.sub continuous_fst).norm).measurable.inv)).aemeasurable
    exact h1.mul h2
  calc ∫⁻ z in Metric.ball (0 : ℂ) R',
          (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : ℂ) R', ENNReal.ofReal (8 * Real.pi * R)
          * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) :=
        lintegral_mono_ae (Filter.Eventually.of_forall hcs)
    _ = ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ z in Metric.ball (0 : ℂ) R',
          ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ ζ in Metric.ball (0 : ℂ) R,
          ∫⁻ z in Metric.ball (0 : ℂ) R', ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
        rw [lintegral_lintegral_swap hjoint]
    _ = ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ ζ in Metric.ball (0 : ℂ) R,
          ‖f ζ‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R', ENNReal.ofReal (‖ζ - z‖⁻¹) := by
        congr 1
        apply setLIntegral_congr_fun measurableSet_ball
        intro ζ _
        exact lintegral_const_mul _ (hzm ζ)
    _ ≤ ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ ζ in Metric.ball (0 : ℂ) R,
          ‖f ζ‖ₑ ^ 2 * ENNReal.ofReal (8 * Real.pi * R') := by
        refine mul_le_mul_right ?_ _
        exact lintegral_mono fun ζ => mul_le_mul_right (lintegral_cauchyKernel_le' R' hR' ζ) _
    _ = ENNReal.ofReal (8 * Real.pi * R) * ENNReal.ofReal (8 * Real.pi * R')
          * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖f ζ‖ₑ ^ 2 := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        ring

theorem cauchyTransform_memLp_ball {h : ℂ → ℂ} {R R' : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hh : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : Function.support h ⊆ Metric.ball 0 R) :
    MeasureTheory.MemLp (cauchyTransform h) 2
        (MeasureTheory.volume.restrict (Metric.ball 0 R')) ∧
      ∃ c : ℝ, 0 ≤ c ∧
        MeasureTheory.eLpNorm (cauchyTransform h) 2
            (MeasureTheory.volume.restrict (Metric.ball 0 R')) ≤
          ENNReal.ofReal c * MeasureTheory.eLpNorm h 2
            (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  classical
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hR'0 : (0 : ℝ) ≤ R' := hR'.le
  have hsm : AEStronglyMeasurable h (volume : Measure ℂ) := hh.aestronglyMeasurable
  -- `h` vanishes off `ball 0 R` (pointwise, not just a.e.).
  have hvanish : ∀ ζ : ℂ, ζ ∉ Metric.ball (0 : ℂ) R → h ζ = 0 := fun ζ hζ =>
    by_contra fun hne => hζ (hs (by simpa [Function.mem_support] using hne))
  ---------------------------------------------------------------------------------------
  -- Step 1: measurability of the Cauchy transform.
  ---------------------------------------------------------------------------------------
  have hch_sm : AEStronglyMeasurable (cauchyTransform h) (volume : Measure ℂ) := by
    have hF : AEStronglyMeasurable (fun p : ℂ × ℂ => h p.2 * (p.2 - p.1)⁻¹)
        ((volume : Measure ℂ).prod volume) :=
      (hsm.comp_snd).mul (((measurable_snd.sub measurable_fst).inv).aestronglyMeasurable)
    exact (MeasureTheory.AEStronglyMeasurable.integral_prod_right' hF).const_mul cauchyConst
  ---------------------------------------------------------------------------------------
  -- Step 2: pointwise (in `z`) bound by the Cauchy-kernel integral.
  ---------------------------------------------------------------------------------------
  have hpt : ∀ z : ℂ, ‖cauchyTransform h z‖ₑ ≤ ‖cauchyConst‖ₑ *
      ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
    intro z
    have hzero : ∀ ζ ∉ Metric.ball (0 : ℂ) R, h ζ / (ζ - z) = 0 := by
      intro ζ hζ
      rw [hvanish ζ hζ, zero_div]
    have h1 : (∫ ζ, h ζ / (ζ - z)) = ∫ ζ in Metric.ball (0 : ℂ) R, h ζ / (ζ - z) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    calc ‖cauchyTransform h z‖ₑ
        = ‖cauchyConst‖ₑ * ‖∫ ζ, h ζ / (ζ - z)‖ₑ := by
          rw [cauchyTransform, enorm_mul]
      _ = ‖cauchyConst‖ₑ * ‖∫ ζ in Metric.ball (0 : ℂ) R, h ζ / (ζ - z)‖ₑ := by rw [h1]
      _ ≤ ‖cauchyConst‖ₑ * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ / (ζ - z)‖ₑ :=
          mul_le_mul_right (enorm_integral_le_lintegral_enorm (fun ζ => h ζ / (ζ - z))) _
      _ = ‖cauchyConst‖ₑ * ∫⁻ ζ in Metric.ball (0 : ℂ) R,
            ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
          congr 1
          apply setLIntegral_congr_fun measurableSet_ball
          intro ζ _
          exact enorm_div_eq_mul_ofReal_inv (h ζ) (ζ - z)
  ---------------------------------------------------------------------------------------
  -- Step 3: the `L²` bound on `ball 0 R'` for the kernel integral.
  ---------------------------------------------------------------------------------------
  have hsupp : ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ ^ 2 = ∫⁻ ζ, ‖h ζ‖ₑ ^ 2 := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun ζ => ?_
    rw [Set.indicator_apply]
    by_cases hζ : ζ ∈ Metric.ball (0 : ℂ) R
    · rw [ite_eq_left hζ]
    · rw [ite_eq_right hζ, hvanish ζ hζ]; simp
  have hschur := lintegral_sq_cauchyKernel_le h hR0 hR'0 hsm.aemeasurable
  have hcc : ‖cauchyConst‖ₑ = ENNReal.ofReal Real.pi⁻¹ := by
    have hpi : ‖((Real.pi : ℂ))‖ = Real.pi := by norm_num
    rw [cauchyConst, enorm_neg, enorm_inv (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)),
      ← ofReal_norm, hpi]
    exact (ENNReal.ofReal_inv_of_pos Real.pi_pos).symm
  have hCBB : ‖cauchyConst‖ₑ ^ 2
        * (ENNReal.ofReal (8 * Real.pi * R) * ENNReal.ofReal (8 * Real.pi * R'))
      = ENNReal.ofReal (64 * R * R') := by
    rw [hcc, ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ Real.pi⁻¹),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi * R),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi⁻¹ ^ 2)]
    congr 1
    rw [show Real.pi⁻¹ ^ 2 * (8 * Real.pi * R * (8 * Real.pi * R')) = 64 * R * R' from by
      field_simp
      ring]
  have hkey : ∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2
      ≤ ENNReal.ofReal (64 * R * R') * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2 := by
    have h1 : ∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2
        ≤ ‖cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R',
            (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := by
      calc ∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2
          ≤ ∫⁻ z in Metric.ball (0 : ℂ) R',
              (‖cauchyConst‖ₑ
                * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 :=
            lintegral_mono fun z => ENNReal.pow_le_pow_left (hpt z)
        _ = ∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyConst‖ₑ ^ 2
              * (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := by
            apply setLIntegral_congr_fun measurableSet_ball
            intro z _
            exact mul_sq _ _
        _ = ‖cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R',
              (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 :=
            lintegral_const_mul' _ _ (by rw [hcc]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    calc ∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2
        ≤ ‖cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R',
            (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := h1
      _ ≤ ‖cauchyConst‖ₑ ^ 2 * (ENNReal.ofReal (8 * Real.pi * R)
            * ENNReal.ofReal (8 * Real.pi * R') * ∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖h ζ‖ₑ ^ 2) :=
          mul_le_mul_right hschur _
      _ = ‖cauchyConst‖ₑ ^ 2 * (ENNReal.ofReal (8 * Real.pi * R)
            * ENNReal.ofReal (8 * Real.pi * R') * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2) := by rw [hsupp]
      _ = (‖cauchyConst‖ₑ ^ 2
            * (ENNReal.ofReal (8 * Real.pi * R) * ENNReal.ofReal (8 * Real.pi * R')))
            * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2 := by ring
      _ = ENNReal.ofReal (64 * R * R') * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2 := by rw [hCBB]
  ---------------------------------------------------------------------------------------
  -- Step 4: pass to `eLpNorm`.
  ---------------------------------------------------------------------------------------
  have hL2ch : eLpNorm (cauchyTransform h) 2 (volume.restrict (Metric.ball (0 : ℂ) R'))
      = (∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_two _ _ hch_sm.restrict]
  have hL2h : eLpNorm h 2 (volume : Measure ℂ) = (∫⁻ ζ, ‖h ζ‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
    eLpNorm_two h volume hsm
  have hsqrt : (64 * R * R') ^ (1 / 2 : ℝ) = 8 * Real.sqrt (R * R') := by
    rw [← Real.sqrt_eq_rpow, show 64 * R * R' = 64 * (R * R') by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64) (R * R')]
    norm_num
  have hfinal : eLpNorm (cauchyTransform h) 2 (volume.restrict (Metric.ball (0 : ℂ) R'))
      ≤ ENNReal.ofReal (8 * Real.sqrt (R * R')) * eLpNorm h 2 (volume : Measure ℂ) := by
    rw [hL2ch, hL2h]
    calc (∫⁻ z in Metric.ball (0 : ℂ) R', ‖cauchyTransform h z‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (64 * R * R') * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hkey (by norm_num)
      _ = (ENNReal.ofReal (64 * R * R')) ^ (1 / 2 : ℝ)
            * (∫⁻ ζ, ‖h ζ‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal ((64 * R * R') ^ (1 / 2 : ℝ)) * (∫⁻ ζ, ‖h ζ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      _ = ENNReal.ofReal (8 * Real.sqrt (R * R')) * (∫⁻ ζ, ‖h ζ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [hsqrt]
  refine ⟨?_, 8 * Real.sqrt (R * R'), by positivity, hfinal⟩
  rw [MeasureTheory.memLp_iff]
  exact lt_of_le_of_lt hfinal
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (MeasureTheory.memLp_iff.mp hh))

end Work.MRMT.Found
