import Submission.FUP.Friedrichs
import Submission.Commons.MeasureTheory.volume_absolutelyContinuous_withDensity_ofReal_pos
import Submission.Commons.MeasureTheory.eventuallyEq_volume_of_ae_withDensity_ofReal_pos
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.FUP

noncomputable section

variable {d : ℕ}

lemma hasCompactSupport_partialZbar_toC {χ : FormDu d → ℝ} (hχ : HasCompactSupport χ)
    (j : Fin d) : HasCompactSupport (fun z => partialZbar j (toC χ) z) := by
  have hχc : HasCompactSupport (toC χ) :=
    hχ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have ha : HasCompactSupport (fun z => (fderiv ℝ (toC χ) z) (Pi.single j (1 : ℂ))) :=
    hχc.fderiv_apply ℝ (Pi.single j (1 : ℂ))
  have hb : HasCompactSupport (fun z => (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) :=
    hχc.fderiv_apply ℝ (Pi.single j Complex.I)
  have hb' : HasCompactSupport
      (fun z => Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) :=
    hb.mul_left (f := fun _ : FormDu d => Complex.I)
  have hnum : HasCompactSupport
      ((fun z : FormDu d => (fderiv ℝ (toC χ) z) (Pi.single j (1 : ℂ)))
        + (fun z : FormDu d => Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I))) :=
    ha.add hb'
  refine hnum.mono' ?_
  intro z hz
  refine subset_tsupport _ (Function.mem_support.mpr fun h0 => hz ?_)
  have hsplit : partialZbar j (toC χ) z
      = ((fderiv ℝ (toC χ) z) (Pi.single j 1)
          + Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) / 2 := rfl
  dsimp only
  simp only [Pi.add_apply] at h0
  rw [hsplit, h0, zero_div]

lemma hasCompactSupport_partialZ_toC {χ : FormDu d → ℝ} (hχ : HasCompactSupport χ)
    (j : Fin d) : HasCompactSupport (fun z => partialZ j (toC χ) z) := by
  have hχc : HasCompactSupport (toC χ) :=
    hχ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have ha : HasCompactSupport (fun z => (fderiv ℝ (toC χ) z) (Pi.single j (1 : ℂ))) :=
    hχc.fderiv_apply ℝ (Pi.single j (1 : ℂ))
  have hb : HasCompactSupport (fun z => (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) :=
    hχc.fderiv_apply ℝ (Pi.single j Complex.I)
  have hb' : HasCompactSupport
      (fun z => Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) :=
    hb.mul_left (f := fun _ : FormDu d => Complex.I)
  have hnum : HasCompactSupport
      ((fun z : FormDu d => (fderiv ℝ (toC χ) z) (Pi.single j (1 : ℂ)))
        - (fun z : FormDu d => Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I))) :=
    ha.sub hb'
  refine hnum.mono' ?_
  intro z hz
  refine subset_tsupport _ (Function.mem_support.mpr fun h0 => hz ?_)
  have hsplit : partialZ j (toC χ) z
      = ((fderiv ℝ (toC χ) z) (Pi.single j 1)
          - Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)) / 2 := rfl
  dsimp only
  simp only [Pi.sub_apply] at h0
  rw [hsplit, h0, zero_div]

lemma hasCompactSupport_cutErr2 {R : ℝ} (hR : 0 < R) (X : FormDu d → FormSpace d) :
    HasCompactSupport (cutErr2 d R X) := by
  classical
  have hS : IsCompact (⋃ j : Fin d, tsupport (fun z => partialZbar j (toC (cutFn d R)) z)) :=
    isCompact_iUnion fun j => hasCompactSupport_partialZbar_toC (hasCompactSupport_cutFn hR) j
  refine HasCompactSupport.of_support_subset_isCompact hS ?_
  intro w hw
  by_contra hnot
  rw [Set.mem_iUnion] at hnot
  push Not at hnot
  refine hw ?_
  funext i
  have h1 : partialZbar i.1 (toC (cutFn d R)) w = 0 :=
    image_eq_zero_of_notMem_tsupport (hnot i.1)
  have h2 : partialZbar i.2 (toC (cutFn d R)) w = 0 :=
    image_eq_zero_of_notMem_tsupport (hnot i.2)
  show X w i.1 * partialZbar i.2 (toC (cutFn d R)) w
      - X w i.2 * partialZbar i.1 (toC (cutFn d R)) w = 0
  rw [h1, h2]
  ring

lemma hasCompactSupport_cutErr1 {R : ℝ} (hR : 0 < R) (X : FormDu d → FormSpace d) :
    HasCompactSupport (cutErr1 d R X) := by
  classical
  have hS : IsCompact (⋃ j : Fin d, tsupport (fun z => partialZ j (toC (cutFn d R)) z)) :=
    isCompact_iUnion fun j => hasCompactSupport_partialZ_toC (hasCompactSupport_cutFn hR) j
  refine HasCompactSupport.of_support_subset_isCompact hS ?_
  intro w hw
  by_contra hnot
  rw [Set.mem_iUnion] at hnot
  push Not at hnot
  refine hw ?_
  show (∑ j : Fin d, partialZ j (toC (cutFn d R)) w * X w j) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [image_eq_zero_of_notMem_tsupport (hnot j), zero_mul]

variable {φ : FormDu d → ℝ}

lemma hasCompactSupport_cutX (R : ℝ) (x : H2 φ) :
    HasCompactSupport (cutX (φ := φ) R x) := by
  refine HasCompactSupport.of_support_subset_isCompact (hasCompactSupport_cutFamily d R).isCompact ?_
  intro w hw
  rw [Function.mem_support] at hw
  exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hw (by
    show toC (cutFamily d R) w • (x : FormDu d → FormSpace d) w = 0
    simp only [toC_apply, h0, Complex.ofReal_zero, zero_smul]))

lemma hasCompactSupport_cutZeta (R : ℝ) (z : H3 φ) :
    HasCompactSupport (cutZeta (φ := φ) R z) := by
  refine HasCompactSupport.of_support_subset_isCompact (hasCompactSupport_cutFamily d R).isCompact ?_
  intro w hw
  rw [Function.mem_support] at hw
  exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hw (by
    show toC (cutFamily d R) w • (z : FormDu d → FormSpace2 d) w = 0
    simp only [toC_apply, h0, Complex.ofReal_zero, zero_smul]))

lemma hasCompactSupport_cutZc (R : ℝ) (z : H1 φ) :
    HasCompactSupport (cutZc (φ := φ) R z) := by
  refine HasCompactSupport.of_support_subset_isCompact (hasCompactSupport_cutFamily d R).isCompact ?_
  intro w hw
  rw [Function.mem_support] at hw
  exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hw (by
    show toC (cutFamily d R) w * (z : FormDu d → ℂ) w = 0
    simp only [toC_apply, h0, Complex.ofReal_zero, zero_mul]))

lemma hasCompactSupport_cutE2 (R : ℝ) (x : H2 φ) :
    HasCompactSupport (liftForm2 (cutE2 (φ := φ) R x)) :=
  hasCompactSupport_liftForm2 (hasCompactSupport_cutErr2
    (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) (x : FormDu d → FormSpace d))

lemma hasCompactSupport_cutE1 (R : ℝ) (x : H2 φ) :
    HasCompactSupport (cutE1 (φ := φ) R x) :=
  hasCompactSupport_cutErr1 (lt_of_lt_of_le zero_lt_one (le_max_right R 1))
    (x : FormDu d → FormSpace d)

theorem memLp_toFormFun {X : FormDu d → FormSpace d}
    (h : MemLp X 2 (volume : Measure (FormDu d))) :
    MemLp (toFormFun X) 2 (volume : Measure (FormDu d)) := by
  have he : toFormFun X = fun z => (X z).ofLp := rfl
  rw [he]
  refine MemLp.of_le h ?_ (Eventually.of_forall fun z => ?_)
  · obtain ⟨g, hg, hge⟩ := h.aestronglyMeasurable
    exact ⟨fun z => (g z).ofLp,
      ((WithLp.measurable_ofLp 2 (Fin d → ℂ)).stronglyMeasurable).comp_measurable hg.measurable,
      by filter_upwards [hge] with z hz; rw [hz]⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    exact fun j => PiLp.norm_apply_le (p := 2) (X z) j

lemma ae_wtMeasure_of_ae_volume {φ : FormDu d → ℝ} {E : Type*}
    {u v : FormDu d → E} (h : u =ᵐ[(volume : Measure (FormDu d))] v) :
    u =ᵐ[wtMeasure φ] v :=
  (MeasureTheory.withDensity_absolutelyContinuous (μ := (volume : Measure (FormDu d)))
    (f := wtDensity φ)).ae_eq h

lemma ae_volume_of_ae_wtMeasure {φ : FormDu d → ℝ} (hφ : Continuous φ) {E : Type*}
    {u v : FormDu d → E} (h : u =ᵐ[wtMeasure φ] v) :
    u =ᵐ[(volume : Measure (FormDu d))] v :=
  Commons.MeasureTheory.eventuallyEq_volume_of_ae_withDensity_ofReal_pos
    (F := fun z => Real.exp (-(φ z))) (Real.continuous_exp.comp hφ.neg)
    (fun z => Real.exp_pos _) h

lemma convFun_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : FormDu d → ℝ} {V W : FormDu d → E}
    (h : V =ᵐ[(volume : Measure (FormDu d))] W) :
    convFun ρ V = convFun ρ W := by
  funext z
  rw [convFun_apply, convFun_apply]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_sub_left z).quasiMeasurePreserving.ae_eq_comp h]
    with y hy
  simp only [Function.comp_apply] at hy
  rw [hy]

end


section DefectLimit

variable {d : ℕ}
variable {φ : FormDu d → ℝ}

/-- Unfolding of `dbarAdjDefect` into the form in which the fleet's oscillation estimate is
stated. -/
lemma dbarAdjDefect_apply (φ : FormDu d → ℝ) (ρ : FormDu d → ℝ) (X : FormDu d → FormSpace d)
    (u : FormDu d) :
    dbarAdjDefect φ ρ X u
      = ∫ y, ρ y • (∑ j, (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u)
          * toFormFun X (u - y) j) := rfl

/-- **The defect of the `ϑ_φ`-side mollification tends to `0` in the weighted `L²` sense.** -/
theorem tendsto_lintegral_dbarAdjDefect (hφ : ContDiff ℝ ∞ φ)
    {K : ℕ → FormDu d → ℝ} (hKnn : ∀ n y, 0 ≤ K n y)
    (hK1 : ∀ n, ∫ y, K n y = 1)
    (hKi : ∀ n, Integrable (K n) (volume : Measure (FormDu d)))
    {Rk : ℕ → ℝ} (hRnn : ∀ n, 0 ≤ Rk n) (hRt : Tendsto Rk atTop (nhds 0))
    (hRs : ∀ n y, Rk n < ‖y‖ → K n y = 0)
    {X : FormDu d → FormSpace d}
    (hXm : MemLp (toFormFun X) 2 (volume : Measure (FormDu d)))
    (hXc : HasCompactSupport (toFormFun X)) :
    Tendsto (fun n => ∫⁻ u, ENNReal.ofReal
      (‖dbarAdjDefect φ (K n) X u‖ ^ 2 * Real.exp (-(φ u))))
      atTop (nhds 0) := by
  have hg : ∀ j : Fin d, ContDiff ℝ 1 (fun w => partialZ j (toC φ) w) :=
    fun j => (contDiff_partialZ_top (contDiff_toC hφ) j).of_le (WithTop.coe_le_coe.mpr le_top)
  have h := Commons.Analysis.Convolution.tendsto_lintegral_oscillation_defect_sq_vec
    (d := d) (ι := ℕ) (l := atTop)
    (g := fun j w => partialZ j (toC φ) w) hg
    (fun z => Real.exp (-(φ z))) (Real.continuous_exp.comp hφ.continuous.neg)
    (fun z => Real.exp_nonneg _) K hKnn hKi hK1 Rk hRnn hRt hRs
    (toFormFun X) hXm hXc
  refine h.congr fun n => ?_
  refine lintegral_congr fun u => ?_
  rw [dbarAdjDefect_apply]

end DefectLimit

section Approx

variable {d : ℕ}
variable {φ : FormDu d → ℝ}

/-- `MemLp` for `μ_φ` from an `L²`-energy bound against Lebesgue measure. -/
lemma memLp_wtMeasure_of_lintegral_lt_top (hφ : Continuous φ) {E : Type*}
    [NormedAddCommGroup E] {f : FormDu d → E}
    (haesm : AEStronglyMeasurable f (volume : Measure (FormDu d)))
    (h : ∫⁻ u, ENNReal.ofReal (‖f u‖ ^ 2 * Real.exp (-(φ u))) < ⊤) :
    MemLp f 2 (wtMeasure φ) := by
  have haesmμ : AEStronglyMeasurable f (wtMeasure φ) := by
    obtain ⟨g, hg, hge⟩ := haesm
    exact ⟨g, hg, ae_wtMeasure_of_ae_volume hge⟩
  rw [memLp_two_iff_integrable_sq_norm haesmμ]
  refine ⟨haesmμ.norm.pow 2, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun u => sq_nonneg _)]
  rw [lintegral_wtMeasure hφ]
  refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) h
  rw [wtDensity_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  ring

theorem exists_smoothApprox (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {x : H2 φ} (hxS : x ∈ (dbarOp2 φ).domain) (hxA : x ∈ (dbarAdjOp φ).domain)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : SmoothForm φ,
      ‖y.toH2 - x‖ < δ ∧
      ‖y.Sval - (dbarOp2 φ) ⟨x, hxS⟩‖ < δ ∧
      ‖y.Aval - (dbarAdjOp φ) ⟨x, hxA⟩‖ < δ := by
  classical
  have hφc : Continuous φ := hφ.continuous
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hFc : Continuous (fun z : FormDu d => Real.exp (-(φ z))) :=
    Real.continuous_exp.comp hφc.neg
  have hFnn : ∀ z : FormDu d, 0 ≤ Real.exp (-(φ z)) := fun z => Real.exp_nonneg _
  have hFpos : ∀ z : FormDu d, 0 < Real.exp (-(φ z)) := fun z => Real.exp_pos _
  have hδ2 : 0 < δ / 2 := by linarith
  have hδ4 : 0 < δ / 4 := by linarith
  let S0 : H3 φ := (dbarOp2 φ) ⟨x, hxS⟩
  let A0 : H1 φ := (dbarAdjOp φ) ⟨x, hxA⟩
  -- (a) the cut-off radius
  have hlimX : Tendsto (fun R : ℝ => ‖(memLp_cutX (φ := φ) R x).toLp (cutX (φ := φ) R x) - x‖)
      atTop (nhds 0) := by
    have h := tendsto_cutFamily_sub (φ := φ) hd hφc (Lp.memLp x)
    have hfun : (fun R : ℝ => ‖(memLp_cutX (φ := φ) R x).toLp (cutX (φ := φ) R x) - x‖)
        = (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
              (cutFamily_nonneg d R) (cutFamily_le_one d R) (Lp.memLp x)).toLp
                (fun w => toC (cutFamily d R) w • (x : FormDu d → FormSpace d) w)
            - (Lp.memLp x).toLp (x : FormDu d → FormSpace d)‖) := by
      funext R
      have hL : (memLp_cutX (φ := φ) R x).toLp (cutX (φ := φ) R x)
          = (memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
              (cutFamily_le_one d R) (Lp.memLp x)).toLp
                (fun w => toC (cutFamily d R) w • (x : FormDu d → FormSpace d) w) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall fun z => rfl)
      have hR : (Lp.memLp x).toLp (x : FormDu d → FormSpace d) = x :=
        Lp.toLp_coeFn _ _
      rw [hL, hR]
    rw [hfun]
    exact h
  have hlimS : Tendsto (fun R : ℝ => ‖(memLp_cutZeta (φ := φ) R S0).toLp (cutZeta (φ := φ) R S0)
        + (memLp_cutE2 (d := d) hd R x).toLp (liftForm2 (cutE2 (φ := φ) R x)) - S0‖)
      atTop (nhds 0) := by
    have h := tendsto_cutFamily_S (φ := φ) hd hφc (Lp.memLp S0) (Lp.memLp x)
    have hfun : (fun R : ℝ => ‖(memLp_cutZeta (φ := φ) R S0).toLp (cutZeta (φ := φ) R S0)
          + (memLp_cutE2 (d := d) hd R x).toLp (liftForm2 (cutE2 (φ := φ) R x)) - S0‖)
        = (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
              (cutFamily_nonneg d R) (cutFamily_le_one d R) (Lp.memLp S0)).toLp
                (fun w => toC (cutFamily d R) w • (S0 : FormDu d → FormSpace2 d) w)
            + (memLp_liftForm2_cutErr2 (d := d) hd R (Lp.memLp x)).toLp
                (liftForm2 (cutErr2 d (max R 1) (x : FormDu d → FormSpace d)))
            - (Lp.memLp S0).toLp (S0 : FormDu d → FormSpace2 d)‖) := by
      funext R
      have hA : (memLp_cutZeta (φ := φ) R S0).toLp (cutZeta (φ := φ) R S0)
          = (memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
              (cutFamily_le_one d R) (Lp.memLp S0)).toLp
                (fun w => toC (cutFamily d R) w • (S0 : FormDu d → FormSpace2 d) w) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall fun z => rfl)
      have hB : (memLp_cutE2 (d := d) hd R x).toLp (liftForm2 (cutE2 (φ := φ) R x))
          = (memLp_liftForm2_cutErr2 (d := d) hd R (Lp.memLp x)).toLp
              (liftForm2 (cutErr2 d (max R 1) (x : FormDu d → FormSpace d))) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall fun z => rfl)
      have hC : (Lp.memLp S0).toLp (S0 : FormDu d → FormSpace2 d) = S0 :=
        Lp.toLp_coeFn _ _
      rw [hA, hB, hC]
    rw [hfun]
    exact h
  have hlimA : Tendsto (fun R : ℝ => ‖(memLp_cutZc (φ := φ) R A0).toLp (cutZc (φ := φ) R A0)
        - (memLp_cutE1 (d := d) hd R x).toLp (cutE1 (φ := φ) R x) - A0‖)
      atTop (nhds 0) := by
    have h := tendsto_cutFamily_A (φ := φ) hd hφc (Lp.memLp A0) (Lp.memLp x)
    have hfun : (fun R : ℝ => ‖(memLp_cutZc (φ := φ) R A0).toLp (cutZc (φ := φ) R A0)
          - (memLp_cutE1 (d := d) hd R x).toLp (cutE1 (φ := φ) R x) - A0‖)
        = (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
              (cutFamily_nonneg d R) (cutFamily_le_one d R) (Lp.memLp A0)).toLp
                (fun w => toC (cutFamily d R) w • (A0 : FormDu d → ℂ) w)
            - (memLp_cutErr1 (d := d) hd R (Lp.memLp x)).toLp
                (cutErr1 d (max R 1) (x : FormDu d → FormSpace d))
            - (Lp.memLp A0).toLp (A0 : FormDu d → ℂ)‖) := by
      funext R
      have hA : (memLp_cutZc (φ := φ) R A0).toLp (cutZc (φ := φ) R A0)
          = (memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
              (cutFamily_le_one d R) (Lp.memLp A0)).toLp
                (fun w => toC (cutFamily d R) w • (A0 : FormDu d → ℂ) w) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall fun z => rfl)
      have hB : (memLp_cutE1 (d := d) hd R x).toLp (cutE1 (φ := φ) R x)
          = (memLp_cutErr1 (d := d) hd R (Lp.memLp x)).toLp
              (cutErr1 d (max R 1) (x : FormDu d → FormSpace d)) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall fun z => rfl)
      have hC : (Lp.memLp A0).toLp (A0 : FormDu d → ℂ) = A0 := Lp.toLp_coeFn _ _
      rw [hA, hB, hC]
    rw [hfun]
    exact h
  obtain ⟨R, hR1, hR2, hR3⟩ :=
    ((hlimX.eventually_lt_const hδ2).and
      ((hlimS.eventually_lt_const hδ2).and (hlimA.eventually_lt_const hδ2))).exists
  -- (b) the cut-off data
  let Xc : FormDu d → FormSpace d := cutX (φ := φ) R x
  have hXcm : MemLp Xc 2 (wtMeasure φ) := memLp_cutX R x
  let xc : H2 φ := hXcm.toLp Xc
  let ζ : FormDu d → FormSpace2 d :=
    cutZeta (φ := φ) R S0 + liftForm2 (cutE2 (φ := φ) R x)
  have hζm : MemLp ζ 2 (wtMeasure φ) :=
    (memLp_cutZeta (φ := φ) R S0).add (memLp_cutE2 (d := d) hd R x)
  let Dv : H3 φ := hζm.toLp ζ
  let zr : FormDu d → ℂ := cutZc (φ := φ) R A0 - cutE1 (φ := φ) R x
  have hzrm : MemLp zr 2 (wtMeasure φ) :=
    (memLp_cutZc (φ := φ) R A0).sub (memLp_cutE1 (d := d) hd R x)
  let Ev : H1 φ := hzrm.toLp zr
  have hweakS : DbarWeak2 φ xc Dv := dbarWeak2_cutX (φ := φ) hφ hd hxS R
  have hweakA : dbarAdjWeak φ xc Ev := dbarAdjWeak_cutX (φ := φ) hφ hd hxA R
  have hR1' : ‖xc - x‖ < δ / 2 := hR1
  have hR2' : ‖Dv - S0‖ < δ / 2 := hR2
  have hR3' : ‖Ev - A0‖ < δ / 2 := hR3
  -- (c) the mollifier
  obtain ⟨K, hKnn, hK1, hKc, hKcs, hKs⟩ :=
    Commons.MeasureTheory.Integral.exists_approximate_identity_complex d
  have hKi : ∀ n, Integrable (K n) (volume : Measure (FormDu d)) := fun n =>
    (hKc n).continuous.integrable_of_hasCompactSupport (hKcs n)
  have hRnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := fun n => by positivity
  have hRt : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hRs : ∀ (n : ℕ) (y : FormDu d), (1 : ℝ) / ((n : ℝ) + 1) < ‖y‖ → K n y = 0 := by
    intro n y hy
    by_contra hne
    have h2 := hKs n hne
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  have hXcvol : MemLp Xc 2 (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.memLp_volume_of_memLp_withDensity_of_hasCompactSupport
      hFc hFpos hXcm (hasCompactSupport_cutX R x)
  have hdefLim : Tendsto (fun n => ∫⁻ u, ENNReal.ofReal
      (‖dbarAdjDefect φ (K n) Xc u‖ ^ 2 * Real.exp (-(φ u)))) atTop (nhds 0) :=
    tendsto_lintegral_dbarAdjDefect hφ hKnn hK1 hKi hRnn hRt hRs
      (memLp_toFormFun hXcvol) (hasCompactSupport_toFormFun (hasCompactSupport_cutX R x))
  have hdefFin : ∀ᶠ n in atTop, (∫⁻ u, ENNReal.ofReal
      (‖dbarAdjDefect φ (K n) Xc u‖ ^ 2 * Real.exp (-(φ u)))) < 1 :=
    hdefLim.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdefFin
  let K' : ℕ → FormDu d → ℝ := fun n => K (n + N)
  let Rr : ℕ → ℝ := fun n => (1 : ℝ) / (((n + N : ℕ) : ℝ) + 1)
  have hK'nn : ∀ n y, 0 ≤ K' n y := fun n y => hKnn (n + N) y
  have hK'1 : ∀ n, ∫ y, K' n y = 1 := fun n => hK1 (n + N)
  have hK'i : ∀ n, Integrable (K' n) (volume : Measure (FormDu d)) := fun n => hKi (n + N)
  have hK'cs : ∀ n, HasCompactSupport (K' n) := fun n => hKcs (n + N)
  have hK'c : ∀ n, ContDiff ℝ ∞ (K' n) := fun n => hKc (n + N)
  have hR'nn : ∀ n, 0 ≤ Rr n := fun n => by positivity
  have hR't : Tendsto Rr atTop (nhds 0) := hRt.comp (tendsto_add_atTop_nat N)
  have hR's : ∀ (n : ℕ) (y : FormDu d), Rr n < ‖y‖ → K' n y = 0 := fun n y hy => hRs (n + N) y hy
  have hdefLim' : Tendsto (fun n => ∫⁻ u, ENNReal.ofReal
      (‖dbarAdjDefect φ (K' n) Xc u‖ ^ 2 * Real.exp (-(φ u)))) atTop (nhds 0) :=
    hdefLim.comp (tendsto_add_atTop_nat N)
  -- (d) the `H₂`-side
  have hXcloc : LocallyIntegrable Xc (volume : Measure (FormDu d)) := hXcvol.locallyIntegrable (by norm_num)
  have hYsm : ∀ n, ContDiff ℝ ∞ (convFun (K' n) Xc) := fun n =>
    Commons.Analysis.Convolution.contDiff_integral_smul_sub (hK'c n) (hK'cs n) hXcloc
  have hYcs : ∀ n, HasCompactSupport (convFun (K' n) Xc) := fun n =>
    Commons.Analysis.Convolution.hasCompactSupport_integral_smul_sub (hK'cs n)
      (hasCompactSupport_cutX R x)
  have hYmem : ∀ n, MemLp (convFun (K' n) Xc) 2 (wtMeasure φ) := fun n =>
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc (hYsm n) (hYcs n)
  have hlimY : Tendsto (fun n => ‖(hYmem n).toLp (convFun (K' n) Xc) - xc‖) atTop (nhds 0) := by
    refine Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
      hFc hFnn (w := fun n => convFun (K' n) Xc) (u := Xc) hYmem hXcm ?_
    exact Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq_weight_norm_general
      (E := FormSpace d) (fun z => Real.exp (-(φ z))) hFc hFnn K' hK'nn hK'i hK'1 Rr
      hR'nn hR't hR's Xc hXcvol (hasCompactSupport_cutX R x)
  -- (e) the `∂̄₂`-side
  have hζcs : HasCompactSupport ζ :=
    (hasCompactSupport_cutZeta (φ := φ) R S0).add (hasCompactSupport_cutE2 (φ := φ) R x)
  have hζvol : MemLp ζ 2 (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.memLp_volume_of_memLp_withDensity_of_hasCompactSupport hFc hFpos hζm hζcs
  have hζlocRaw : LocallyIntegrable ζ (volume : Measure (FormDu d)) :=
    hζvol.locallyIntegrable (by norm_num)
  have hζρRaw : ∀ n, MemLp (convFun (K' n) ζ) 2 (wtMeasure φ) := fun n =>
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc
      (Commons.Analysis.Convolution.contDiff_integral_smul_sub (hK'c n) (hK'cs n) hζlocRaw)
      (Commons.Analysis.Convolution.hasCompactSupport_integral_smul_sub (hK'cs n) hζcs)
  have hlimZ : Tendsto (fun n => ‖(hζρRaw n).toLp (convFun (K' n) ζ) - Dv‖) atTop (nhds 0) := by
    refine Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
      hFc hFnn (w := fun n => convFun (K' n) ζ) (u := ζ) hζρRaw hζm ?_
    exact Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq_weight_norm_general
      (E := FormSpace2 d) (fun z => Real.exp (-(φ z))) hFc hFnn K' hK'nn hK'i hK'1 Rr
      hR'nn hR't hR's ζ hζvol hζcs
  -- (f) the `ϑ_φ`-side
  have hzrcs : HasCompactSupport zr :=
    (hasCompactSupport_cutZc (φ := φ) R A0).sub (hasCompactSupport_cutE1 (φ := φ) R x)
  have hzrvol : MemLp zr 2 (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.memLp_volume_of_memLp_withDensity_of_hasCompactSupport hFc hFpos hzrm hzrcs
  have hzrlocRaw : LocallyIntegrable zr (volume : Measure (FormDu d)) := hzrvol.locallyIntegrable (by norm_num)
  have hAzRaw : ∀ n, MemLp (convFun (K' n) zr) 2 (wtMeasure φ) := fun n =>
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc
      (Commons.Analysis.Convolution.contDiff_integral_smul_sub (hK'c n) (hK'cs n) hzrlocRaw)
      (Commons.Analysis.Convolution.hasCompactSupport_integral_smul_sub (hK'cs n) hzrcs)
  have hlimAz : Tendsto (fun n => ‖(hAzRaw n).toLp (convFun (K' n) zr) - Ev‖) atTop (nhds 0) := by
    refine Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
      hFc hFnn (w := fun n => convFun (K' n) zr) (u := zr) hAzRaw hzrm ?_
    exact Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq_weight_norm_general
      (E := ℂ) (fun z => Real.exp (-(φ z))) hFc hFnn K' hK'nn hK'i hK'1 Rr
      hR'nn hR't hR's zr hzrvol hzrcs
  -- the defect
  have hAvXc : ∀ n, MemLp (dbarAdjDefect φ (K' n) Xc) 2 (wtMeasure φ) := fun n =>
    memLp_wtMeasure_of_lintegral_lt_top hφc
      (aestronglyMeasurable_dbarAdjDefect hφ1 (hK'c n).continuous hXcvol.aestronglyMeasurable)
      (lt_of_lt_of_le (hN (n + N) (Nat.le_add_left N n)) le_top)
  have hxXcVol : Xc =ᵐ[(volume : Measure (FormDu d))] (xc : FormDu d → FormSpace d) :=
    (ae_volume_of_ae_wtMeasure hφc (MemLp.coeFn_toLp hXcm)).symm
  have hxcrep : ∀ n, MemLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d)) 2 (wtMeasure φ) :=
    fun n => MemLp.ae_eq
      (Eventually.of_forall fun u => congrFun (dbarAdjDefect_congr_ae hxXcVol) u) (hAvXc n)
  have hlimAv : Tendsto (fun n =>
      ‖(hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))‖) atTop (nhds 0) := by
    have hb := Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
      (ι := ℕ) (l := atTop) hFc hFnn
      (w := fun n => dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))
      (u := (0 : FormDu d → ℂ)) hxcrep (MemLp.zero) ?_
    · refine hb.congr fun n => ?_
      rw [MemLp.toLp_zero, sub_zero]
      rfl
    · refine hdefLim'.congr fun n => ?_
      refine lintegral_congr fun u => ?_
      simp only [Pi.zero_apply, sub_zero]
      rw [dbarAdjDefect_congr_ae hxXcVol]
  -- the weak relations for the mollified forms
  have hDvζ : (Dv : FormDu d → FormSpace2 d) =ᵐ[wtMeasure φ] ζ := MemLp.coeFn_toLp hζm
  have hEvzr : (Ev : FormDu d → ℂ) =ᵐ[wtMeasure φ] zr := MemLp.coeFn_toLp hzrm
  have hXρ : ∀ n, MemLp (convFun (K' n) (xc : FormDu d → FormSpace d)) 2 (wtMeasure φ) := fun n =>
    MemLp.ae_eq (Eventually.of_forall fun z =>
      congrFun (convFun_congr_ae (ρ := K' n) hxXcVol) z) (hYmem n)
  have hζρ : ∀ n, MemLp (convFun (K' n) (Dv : FormDu d → FormSpace2 d)) 2 (wtMeasure φ) := fun n =>
    MemLp.ae_eq (Eventually.of_forall fun z =>
      (congrFun (convFun_congr_ae (ρ := K' n)
        (ae_volume_of_ae_wtMeasure hφc hDvζ)) z).symm) (hζρRaw n)
  have hAz : ∀ n, MemLp (convFun (K' n) (Ev : FormDu d → ℂ)) 2 (wtMeasure φ) := fun n =>
    MemLp.ae_eq (Eventually.of_forall fun z =>
      (congrFun (convFun_congr_ae (ρ := K' n)
        (ae_volume_of_ae_wtMeasure hφc hEvzr)) z).symm) (hAzRaw n)
  have hxcloc : LocallyIntegrable (xc : FormDu d → FormSpace d) (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.locallyIntegrable_toLp_of_memLp_withDensity_of_hasCompactSupport
      hFc hFpos hXcm (hasCompactSupport_cutX R x)
  have hDvloc : LocallyIntegrable (Dv : FormDu d → FormSpace2 d) (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.locallyIntegrable_toLp_of_memLp_withDensity_of_hasCompactSupport
      hFc hFpos hζm hζcs
  have hEvloc : LocallyIntegrable (Ev : FormDu d → ℂ) (volume : Measure (FormDu d)) :=
    Commons.MeasureTheory.locallyIntegrable_toLp_of_memLp_withDensity_of_hasCompactSupport
      hFc hFpos hzrm hzrcs
  have hxcz : dbarAdjWeak φ ((Lp.memLp xc).toLp (xc : FormDu d → FormSpace d))
      ((Lp.memLp Ev).toLp (Ev : FormDu d → ℂ)) := by
    simpa only [Lp.toLp_coeFn] using hweakA
  have hSconv : ∀ n, DbarWeak2 φ ((hYmem n).toLp (convFun (K' n) Xc))
      ((hζρRaw n).toLp (convFun (K' n) ζ)) := by
    intro n
    have h := dbarWeak2_conv (φ := φ) hφ hweakS (hK'c n).continuous (hK'cs n)
      hxcloc hDvloc (hXρ n) (hζρ n)
    rw [show (hXρ n).toLp (convFun (K' n) (xc : FormDu d → FormSpace d))
        = (hYmem n).toLp (convFun (K' n) Xc) from
      MemLp.toLp_congr _ _ (Eventually.of_forall fun z =>
        (congrFun (convFun_congr_ae (ρ := K' n) hxXcVol) z).symm),
      show (hζρ n).toLp (convFun (K' n) (Dv : FormDu d → FormSpace2 d))
        = (hζρRaw n).toLp (convFun (K' n) ζ) from
      MemLp.toLp_congr _ _ (Eventually.of_forall fun z =>
        congrFun (convFun_congr_ae (ρ := K' n)
          (ae_volume_of_ae_wtMeasure hφc hDvζ)) z)] at h
    exact h
  have hAconv : ∀ n, dbarAdjWeak φ ((hYmem n).toLp (convFun (K' n) Xc))
      ((hAzRaw n).toLp (convFun (K' n) zr)
        - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))) := by
    intro n
    have h := dbarAdjWeak_conv (φ := φ) hφ hxcloc hEvloc (Lp.memLp xc) (Lp.memLp Ev) hxcz
      (hK'c n).continuous (hK'cs n) (hXρ n) (hAz n) (hxcrep n)
    have h0 : dbarAdjWeak φ ((hXρ n).toLp (convFun (K' n) (xc : FormDu d → FormSpace d)))
        ((hAz n).toLp (convFun (K' n) (Ev : FormDu d → ℂ))
          - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))) := h
    rw [show (hXρ n).toLp (convFun (K' n) (xc : FormDu d → FormSpace d))
        = (hYmem n).toLp (convFun (K' n) Xc) from
      MemLp.toLp_congr _ _ (Eventually.of_forall fun z =>
        (congrFun (convFun_congr_ae (ρ := K' n) hxXcVol) z).symm),
      show (hAz n).toLp (convFun (K' n) (Ev : FormDu d → ℂ))
        = (hAzRaw n).toLp (convFun (K' n) zr) from
      MemLp.toLp_congr _ _ (Eventually.of_forall fun z =>
        congrFun (convFun_congr_ae (ρ := K' n)
          (ae_volume_of_ae_wtMeasure hφc hEvzr)) z)] at h0
    exact h0
  -- (g) choose the mollifier index
  have he1 : ∀ᶠ n in atTop, ‖(hYmem n).toLp (convFun (K' n) Xc) - xc‖ < δ / 2 :=
    hlimY.eventually_lt_const hδ2
  have he2 : ∀ᶠ n in atTop, ‖(hζρRaw n).toLp (convFun (K' n) ζ) - Dv‖ < δ / 2 :=
    hlimZ.eventually_lt_const hδ2
  have he3 : ∀ᶠ n in atTop, ‖(hAzRaw n).toLp (convFun (K' n) zr) - Ev‖ < δ / 4 :=
    hlimAz.eventually_lt_const hδ4
  have he4 : ∀ᶠ n in atTop,
      ‖(hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))‖ < δ / 4 :=
    hlimAv.eventually_lt_const hδ4
  obtain ⟨n, ⟨⟨hn1, hn2⟩, ⟨hn3, hn4⟩⟩⟩ := ((he1.and he2).and (he3.and he4)).exists
  have hYsmN : ∀ j, ContDiff ℝ ∞ (fun z => toFormFun (convFun (K' n) Xc) z j) := fun j =>
    contDiff_toFormFun (hYsm n) j
  have hYcsN : ∀ j, HasCompactSupport (fun z => toFormFun (convFun (K' n) Xc) z j) := fun j =>
    Submission.FUP.hasCompactSupport_comp j (hasCompactSupport_toFormFun (hYcs n))
  have hYmemS : MemLp (liftForm2 (dbarFormFun2 (toFormFun (convFun (K' n) Xc)))) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc
      (contDiff_liftForm2 (contDiff_dbarFormFun2 hYsmN))
      (hasCompactSupport_liftForm2 (hasCompactSupport_dbarFormFun2 hYcsN))
  have hYmemA : MemLp (dbarAdjoint φ (toFormFun (convFun (K' n) Xc))) 2 (wtMeasure φ) :=
    memLp_dbarAdjoint hφ1 (fun j => (hYsmN j).of_le (WithTop.coe_le_coe.mpr le_top))
      (hasCompactSupport_toFormFun (hYcs n))
  let y : SmoothForm φ :=
    { f := convFun (K' n) Xc
      smooth := hYsm n
      csupport := hYcs n
      memLp := hYmem n
      memLpS := hYmemS
      memLpA := hYmemA }
  have hySval : y.Sval = (hζρRaw n).toLp (convFun (K' n) ζ) :=
    dbarWeak2_unique (φ := φ) hφ1 (y.dbarWeak2 hφ1) (hSconv n)
  have hyAval : y.Aval = (hAzRaw n).toLp (convFun (K' n) zr)
      - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d)) :=
    dbarAdjWeak_unique (φ := φ) hφ1 (y.dbarAdjWeak hφ1) (hAconv n)
  refine ⟨y, ?_, ?_, ?_⟩
  · have h1 : y.toH2 = (hYmem n).toLp (convFun (K' n) Xc) := rfl
    rw [h1]
    have heq : (hYmem n).toLp (convFun (K' n) Xc) - x
        = ((hYmem n).toLp (convFun (K' n) Xc) - xc) + (xc - x) := by abel
    rw [heq]
    linarith [norm_add_le ((hYmem n).toLp (convFun (K' n) Xc) - xc) (xc - x), hn1, hR1']
  · rw [hySval]
    have h1 : ‖(hζρRaw n).toLp (convFun (K' n) ζ) - S0‖
        ≤ ‖(hζρRaw n).toLp (convFun (K' n) ζ) - Dv‖ + ‖Dv - S0‖ := by
      have heq : (hζρRaw n).toLp (convFun (K' n) ζ) - S0
          = ((hζρRaw n).toLp (convFun (K' n) ζ) - Dv) + (Dv - S0) := by abel
      rw [heq]; exact norm_add_le _ _
    linarith
  · rw [hyAval]
    have h1 : ‖(hAzRaw n).toLp (convFun (K' n) zr)
          - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d)) - A0‖
        ≤ (‖(hAzRaw n).toLp (convFun (K' n) zr) - Ev‖
            + ‖(hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))‖)
          + ‖Ev - A0‖ := by
      have heq : (hAzRaw n).toLp (convFun (K' n) zr)
            - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d)) - A0
          = ((hAzRaw n).toLp (convFun (K' n) zr) - Ev)
            - (hxcrep n).toLp (dbarAdjDefect φ (K' n) (xc : FormDu d → FormSpace d))
            + (Ev - A0) := by abel
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    linarith

end Approx


section HBound

variable {d : ℕ}
variable {φ : FormDu d → ℝ}

theorem hbound_friedrichs (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {η : FormDu d → (Fin d → ℂ)} {κ : FormDu d → ℝ}
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (hηc : ∀ j, Continuous (fun z => η z j))
    (hηint : ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤)
    (hhess : HessBound φ κ)
    (hηm : MemLp (liftForm η) 2 (wtMeasure φ))
    (x : H2 φ) (hxS : x ∈ (dbarOp2 φ).domain) (hxA : x ∈ (dbarAdjOp φ).domain) :
    ‖inner ℂ x (hηm.toLp (liftForm η))‖ ^ 2
      ≤ etaKapNorm η φ κ * (‖(dbarOp2 φ) ⟨x, hxS⟩‖ ^ 2 + ‖(dbarAdjOp φ) ⟨x, hxA⟩‖ ^ 2) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have htd : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ n : ℕ, ∃ y : SmoothForm φ, ‖y.toH2 - x‖ < (1 : ℝ) / ((n : ℝ) + 1) ∧
      ‖y.Sval - (dbarOp2 φ) ⟨x, hxS⟩‖ < (1 : ℝ) / ((n : ℝ) + 1) ∧
      ‖y.Aval - (dbarAdjOp φ) ⟨x, hxA⟩‖ < (1 : ℝ) / ((n : ℝ) + 1) := fun n =>
    exists_smoothApprox (φ := φ) hφ hd hxS hxA (by positivity)
  choose Y hY using hex
  have hY1 : ∀ n, ‖(Y n).toH2 - x‖ < (1 : ℝ) / ((n : ℝ) + 1) := fun n => (hY n).1
  have hY2 : ∀ n, ‖(Y n).Sval - (dbarOp2 φ) ⟨x, hxS⟩‖ < (1 : ℝ) / ((n : ℝ) + 1) :=
    fun n => (hY n).2.1
  have hY3 : ∀ n, ‖(Y n).Aval - (dbarAdjOp φ) ⟨x, hxA⟩‖ < (1 : ℝ) / ((n : ℝ) + 1) :=
    fun n => (hY n).2.2
  have hlimX : Tendsto (fun n => (Y n).toH2) atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hY1 n)) htd
  have hlimS : Tendsto (fun n => (Y n).Sval) atTop (nhds ((dbarOp2 φ) ⟨x, hxS⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hY2 n)) htd
  have hlimA : Tendsto (fun n => (Y n).Aval) atTop (nhds ((dbarAdjOp φ) ⟨x, hxA⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hY3 n)) htd
  have hKM : ∀ n, ‖inner ℂ ((Y n).toH2) (hηm.toLp (liftForm η))‖ ^ 2
      ≤ etaKapNorm η φ κ * (‖(Y n).Sval‖ ^ 2 + ‖(Y n).Aval‖ ^ 2) := by
    intro n
    have h := norm_inner_liftForm_sq_le' (φ := φ) (κ := κ) (η := η)
      (x := toFormFun (Y n).f) hφ2 hκc hκpos hηc hηint
      (fun j => ((Y n).contDiff_comp j).of_le (WithTop.coe_le_coe.mpr le_top))
      (fun j => (Y n).hasCompactSupport_apply j) hhess (Y n).memLp_lift hηm
      (Y n).memLpS (Y n).memLpA
    rwa [SmoothForm.toLp_lift_eq_toH2 (y := Y n)] at h
  have hl1 : Tendsto (fun n => ‖inner ℂ ((Y n).toH2) (hηm.toLp (liftForm η))‖ ^ 2) atTop
      (nhds (‖inner ℂ x (hηm.toLp (liftForm η))‖ ^ 2)) :=
    ((hlimX.inner tendsto_const_nhds).norm.pow 2)
  have hl2 : Tendsto (fun n => etaKapNorm η φ κ * (‖(Y n).Sval‖ ^ 2 + ‖(Y n).Aval‖ ^ 2))
      atTop (nhds (etaKapNorm η φ κ
        * (‖(dbarOp2 φ) ⟨x, hxS⟩‖ ^ 2 + ‖(dbarAdjOp φ) ⟨x, hxA⟩‖ ^ 2))) :=
    ((hlimS.norm.pow 2).add (hlimA.norm.pow 2)).const_mul (etaKapNorm η φ κ)
  exact le_of_tendsto_of_tendsto' hl1 hl2 hKM

end HBound

end Submission.FUP
