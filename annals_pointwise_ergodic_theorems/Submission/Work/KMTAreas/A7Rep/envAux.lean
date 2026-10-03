/-
# Auxiliary lemmas for the envelope band extension (Area A7Rep)

The analytic inputs of `Work.KMTAreas.A7Rep.envelopeBandExtendProof`: the Fourier coefficients
`cw m j` of an integrable, bounded, compactly supported `m` form a square summable sequence; the
`L²` circle function with these coefficients is the periodisation `periodize m`; the
conjugation-and-shift identity for `ftLp`; the identity computing the Fourier coefficients of
`periodize m · ftLp v` as the convolution of the coefficient sequences; and the two real-line facts
about `envRealize`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Rep.envDefs
import Submission.Work.KMTPlan.A6.SymSeq_TmKernel_cont
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_ftLp
import Submission.Work.KMTAreas.A7Hi.fourierCoeff_eq_zero_ae

namespace Work.KMTAreas.A7Rep

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. The Fourier coefficients of `ftLp` -/

/-- The `j`-th Fourier coefficient of the `L²` circle function with coefficient sequence `h` is
`h j`. -/
theorem fourierCoeff_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) (j : ℤ) :
    fourierCoeff ((Work.BourgainPlan.IonescuWainger.ftLp h hh) : Circ → ℂ) j = h j := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply,
    Work.BourgainPlan.IonescuWainger.ftLp_coeff]

/-! ## 2. The periodisation of a bounded compactly supported function is `L²` -/

/-- The integers contributing to the periodisation of a function supported in `[-R,R]` evaluated
at a point of the fundamental domain `[0,1)`: every contribution lies in the fixed interval
`[-(⌊R⌋+2), ⌊R⌋+1]`. -/
private lemma periodizeTerm_eq_zero {φ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x : ℝ, R < |x| → φ x = 0) (ξ : Circ) {k : ℤ}
    (hk : k ∉ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)) :
    φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)) = 0 := by
  by_contra hne
  have hx := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop
  rw [Set.mem_Ico] at hx
  have hle : |(AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)| ≤ R := by
    by_contra h
    exact hne (hφ0 _ (lt_of_not_ge h))
  rw [abs_le] at hle
  have h1 : k ≤ ⌊R⌋ + 1 := by
    have hkx : (k : ℝ) ≤ R := by linarith [hle.2, hx.1]
    have := Int.le_floor.mpr hkx
    linarith
  have h2 : -(⌊R⌋ + 2) ≤ k := by
    have hk2 : ((-k - 2 : ℤ) : ℝ) ≤ R := by
      push_cast
      linarith [hle.1, hx.2, hR]
    have := Int.le_floor.mpr hk2
    linarith
  exact hk (by rw [Finset.mem_Icc]; exact ⟨h2, h1⟩)

/-- **The periodisation of a bounded function supported in `[-2δ,2δ]` is bounded.** -/
theorem bdd_periodize {m : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hm0 : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0) (hm1 : ∀ θ : ℝ, ‖m θ‖ ≤ 1) :
    ∃ C : ℝ, ∀ ξ : Circ, ‖Work.Analysis.IonescuWainger.periodize m ξ‖ ≤ C := by
  refine ⟨((Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1)).card : ℝ), fun ξ => ?_⟩
  have hkey : Work.Analysis.IonescuWainger.periodize m ξ
      = ∑ k ∈ Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1),
          m ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)) := by
    change (∑' k : ℤ, m ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ))) = _
    exact tsum_eq_sum fun k hk =>
      periodizeTerm_eq_zero (by linarith) hm0 ξ (by simpa using hk)
  rw [hkey]
  calc ‖∑ k ∈ Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1),
          m ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ))‖
      ≤ ∑ k ∈ Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1),
          ‖m ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => hm1 _
    _ = ((Finset.Icc (-(⌊2 * δ⌋ + 2)) (⌊2 * δ⌋ + 1)).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The periodisation of an integrable, bounded, compactly supported `m` is square integrable. -/
theorem memLp_periodize_two {m : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hm0 : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0) (hm1 : ∀ θ : ℝ, ‖m θ‖ ≤ 1) :
    MemLp (Work.Analysis.IonescuWainger.periodize m) 2
      Work.Analysis.IonescuWainger.circleMeasure := by
  obtain ⟨C, hC⟩ := bdd_periodize hδ hm0 hm1
  have hper1 : MemLp (Work.Analysis.IonescuWainger.periodize m) 1
      Work.Analysis.IonescuWainger.circleMeasure :=
    memLp_one_iff_integrable.mpr (Work.KMTPlan.A6.IntegrablePeriodize hm)
  have htop : MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    MemLp.mono' (memLp_top_const C) hper1.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  exact htop.mono_exponent (by norm_num)

/-! ## 3. The coefficient sequence `cw m` is square summable -/

/-- **The sequence of Fourier coefficients `j ↦ cw m j` is square summable.** -/
theorem memlp_cw {m : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hm : MeasureTheory.Integrable m)
    (hm0 : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0) (hm1 : ∀ θ : ℝ, ‖m θ‖ ≤ 1) :
    Memℓp (fun j : ℤ => Work.KMTAreas.A7.cw m j) 2 := by
  have h2 := memLp_periodize_two hδ hm hm0 hm1
  have hsumm : Summable (fun j : ℤ =>
      ‖fourierCoeff ((h2.toLp (Work.Analysis.IonescuWainger.periodize m)) :
        Circ → ℂ) j‖ ^ 2) :=
    (hasSum_sq_fourierCoeff (h2.toLp (Work.Analysis.IonescuWainger.periodize m))).summable
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  refine Summable.congr hsumm (fun j => ?_)
  have hbase : ‖fourierCoeff ((h2.toLp (Work.Analysis.IonescuWainger.periodize m)) :
        Circ → ℂ) j‖ = ‖Work.KMTAreas.A7.cw m j‖ := by
    rw [congrFun (fourierCoeff_congr_ae h2.coeFn_toLp) j,
      Work.KMTPlan.A6.fourierCoeff_periodize_eq_cw hm j]
  rw [hbase]
  norm_num [ENNReal.toReal_ofNat]

/-! ## 4. The `L²` class with coefficients `cw m` is the periodisation -/

private theorem fourierCoeff_sub_apply {f g : Circ → ℂ}
    (hf : MeasureTheory.Integrable f Work.Analysis.IonescuWainger.circleMeasure)
    (hg : MeasureTheory.Integrable g Work.Analysis.IonescuWainger.circleMeasure) (j : ℤ) :
    fourierCoeff (f - g) j = fourierCoeff f j - fourierCoeff g j := by
  have h1 : fourierCoeff (f + -g) j = fourierCoeff f j + fourierCoeff (-g) j :=
    congrFun (fourierCoeff.add hf hg.neg) j
  have h2 : fourierCoeff (-g) j = - fourierCoeff g j := by
    have h3 := fourierCoeff.const_smul g (-1 : ℂ) j
    rw [show ((-1 : ℂ) • g) = -g from by funext ξ; simp, smul_eq_mul] at h3
    simpa using h3
  rw [show (f - g) = f + -g from sub_eq_add_neg f g, h1, h2]
  ring

/-- **The `L²` circle function whose Fourier coefficients are `cw m j` is the periodisation of
`m`.** -/
theorem ftLp_cw_ae_eq_periodize {m : ℝ → ℂ} (hm : MeasureTheory.Integrable m)
    (hh : Memℓp (fun j : ℤ => Work.KMTAreas.A7.cw m j) 2) :
    Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => Work.KMTAreas.A7.cw m j) hh
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure]
      Work.Analysis.IonescuWainger.periodize m := by
  have hperInt : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize m)
      Work.Analysis.IonescuWainger.circleMeasure := Work.KMTPlan.A6.IntegrablePeriodize hm
  have hLpInt : MeasureTheory.Integrable
      ((Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => Work.KMTAreas.A7.cw m j) hh) :
        Circ → ℂ) Work.Analysis.IonescuWainger.circleMeasure :=
    (Lp.memLp (Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => Work.KMTAreas.A7.cw m j)
      hh)).integrable (by norm_num)
  have hz : ((Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => Work.KMTAreas.A7.cw m j) hh) :
        Circ → ℂ) - Work.Analysis.IonescuWainger.periodize m
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] 0 :=
    Work.KMTAreas.A7Hi.fourierCoeff_eq_zero_ae (hLpInt.sub hperInt) (fun n => by
      rw [fourierCoeff_sub_apply hLpInt hperInt n, fourierCoeff_ftLp hh n,
        Work.KMTPlan.A6.fourierCoeff_periodize_eq_cw hm n, sub_self])
  filter_upwards [hz] with ξ hξ
  simpa using sub_eq_zero.mp hξ

/-! ## 5. The conjugation-and-shift identity for `ftLp` -/

/-- The involution `j ↦ x - j` of `ℤ`. -/
private def shiftNegL (x : ℤ) : ℤ ≃ ℤ where
  toFun j := x - j
  invFun j := x - j
  left_inv j := by simp
  right_inv j := by simp

@[simp] private theorem shiftNegL_apply (x j : ℤ) : shiftNegL x j = x - j := rfl

/-- Conjugation and a shift of a square summable sequence stay square summable. -/
theorem memlp_shift_star {F : ℤ → ℂ} (hF : Memℓp F 2) (x : ℤ) :
    Memℓp (fun j : ℤ => star (F (x - j))) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
  have hF2 : Summable fun n : ℤ => ‖F n‖ ^ ((2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hF
  have hsh : Summable fun j : ℤ => ‖F (x - j)‖ ^ ((2 : ℝ≥0∞).toReal) :=
    (Equiv.summable_iff (shiftNegL x)).mpr hF2
  simpa [Function.comp_def, norm_star] using hsh

/-- **Conjugation and shift of a coefficient sequence.**  The `L²` class of the sequence
`j ↦ conj (F (x - j))` is the modulation of `conj (ftLp F)` by the character `fourier x`. -/
theorem ftLp_star_shift_ae {F : ℤ → ℂ} (hF : Memℓp F 2) (x : ℤ)
    (hh : Memℓp (fun j : ℤ => star (F (x - j))) 2) :
    Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => star (F (x - j))) hh
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure]
      fun ξ : Circ =>
        star ((Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ) ξ)
          * fourier (T := 1) x ξ := by
  set H : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ) with hH
  have hHmem : MemLp (Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ) 2
      (AddCircle.haarAddCircle (T := 1)) := Lp.memLp _
  have hHasm : AEStronglyMeasurable H (AddCircle.haarAddCircle (T := 1)) := hHmem.aestronglyMeasurable
  have hasm : AEStronglyMeasurable
      (fun ξ : Circ => star (H ξ) * fourier (T := 1) x ξ)
      (AddCircle.haarAddCircle (T := 1)) :=
    (Continuous.comp_aestronglyMeasurable continuous_star hHasm).mul
      (((fourier (T := 1) x).continuous).aestronglyMeasurable)
  have hGmem : MemLp (fun ξ : Circ => star (H ξ) * fourier (T := 1) x ξ) 2
      (AddCircle.haarAddCircle (T := 1)) :=
    MemLp.mono' hHmem.norm hasm (Filter.Eventually.of_forall fun ξ => by
      have hf1 : ‖(fourier (T := 1) x) ξ‖ = 1 := by
        simp only [fourier_apply, Circle.norm_coe]
      refine le_of_eq ?_
      rw [norm_mul, norm_star, hf1, mul_one, hH])
  have hLp : Work.BourgainPlan.IonescuWainger.ftLp (fun j : ℤ => star (F (x - j))) hh
      = MemLp.toLp (fun ξ : Circ => star (H ξ) * fourier (T := 1) x ξ) hGmem := by
    refine (fourierBasis (T := 1)).repr.injective ?_
    ext n
    rw [HilbertBasis.repr_apply_apply, Work.BourgainPlan.IonescuWainger.ftLp_coeff hh n,
      fourierBasis_repr, fourierCoeff_congr_ae (MemLp.coeFn_toLp hGmem)]
    rw [fourierCoeff, Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral hF (x - n)]
    have hconj : star (∫ ξ : Circ, H ξ * star (fourier (T := 1) (x - n) ξ)
          ∂AddCircle.haarAddCircle (T := 1))
        = ∫ ξ : Circ, starRingEnd ℂ (H ξ * star (fourier (T := 1) (x - n) ξ))
            ∂AddCircle.haarAddCircle (T := 1) := by
      simp only [← starRingEnd_apply, ← integral_conj]
    rw [hconj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul]
    have h1 : fourier (T := 1) (-n) ξ * fourier (T := 1) x ξ = fourier (T := 1) (x - n) ξ := by
      rw [← fourier_add, show -n + x = x - n from by ring]
    rw [starRingEnd_apply, star_mul, star_star, ← h1]
    ring
  rw [hLp]
  exact MemLp.coeFn_toLp hGmem

/-! ## 6. The support of the periodisation of `m` -/

/-- The periodisation of `m` vanishes outside the arc of radius `2δ`. -/
theorem periodize_eq_zero_of_lt_norm {m : ℝ → ℂ} {δ : ℝ}
    (hm0 : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0) {ξ : Circ} (hξ : 2 * δ < ‖ξ‖) :
    Work.Analysis.IonescuWainger.periodize m ξ = 0 := by
  have hcoe : (((AddCircle.equivIco (1 : ℝ) 0 ξ).val : ℝ) : Circ) = ξ :=
    AddCircle.coe_equivIco
  rw [← hcoe, Work.KMTContract.periodizeCoeEqTsum]
  have hz : (fun k : ℤ => m ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ))) =
      fun _ => (0 : ℂ) := by
    funext k
    refine hm0 _ (lt_of_lt_of_le hξ ?_)
    rw [← hcoe]
    simpa using Work.BourgainPlan.IonescuWainger.norm_circle_coe_le_abs
      ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ))
  rw [hz, tsum_zero]

/-! ## 7. The convolution identity for the coefficients of `periodize m · ftLp v` -/

/-- **`∫ periodize m · ftLp v · conj (fourier x) = Σ_j cw m j · v (x - j)`.** -/
theorem circleValue {m : ℝ → ℂ} (hm : MeasureTheory.Integrable m)
    (hcw : Memℓp (fun j : ℤ => Work.KMTAreas.A7.cw m j) 2)
    {v : ℤ → ℂ} (hv : Memℓp v 2) (x : ℤ) :
    (∫ ξ : Circ, (Work.Analysis.IonescuWainger.periodize m) ξ
        * ((Work.BourgainPlan.IonescuWainger.ftLp v hv) : Circ → ℂ) ξ
        * star (fourier (T := 1) x ξ) ∂Work.Analysis.IonescuWainger.circleMeasure)
      = ∑' j : ℤ, Work.KMTAreas.A7.cw m j * v (x - j) := by
  have hk : Memℓp (fun j : ℤ => star (Work.KMTAreas.A7.cw m (x - j))) 2 :=
    memlp_shift_star hcw x
  have hstarshift := ftLp_star_shift_ae hcw x hk
  have hper := ftLp_cw_ae_eq_periodize hm hcw
  have hP := Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_ftLp hv hk
  have hLHS : (∑' j : ℤ, v j * star (star (Work.KMTAreas.A7.cw m (x - j))))
      = ∑' j : ℤ, Work.KMTAreas.A7.cw m j * v (x - j) := by
    rw [show (fun j : ℤ => v j * star (star (Work.KMTAreas.A7.cw m (x - j))))
        = fun j : ℤ => v j * Work.KMTAreas.A7.cw m (x - j) from by
      funext j; rw [star_star]]
    rw [← Equiv.tsum_eq (shiftNegL x) (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))]
    refine tsum_congr (fun j => ?_)
    rw [shiftNegL_apply, show x - (x - j) = j from by ring]
    ring
  have hcongr : (fun ξ : Circ => ((Work.BourgainPlan.IonescuWainger.ftLp v hv) : Circ → ℂ) ξ
        * star (((Work.BourgainPlan.IonescuWainger.ftLp
            (fun j : ℤ => star (Work.KMTAreas.A7.cw m (x - j))) hk) : Circ → ℂ) ξ))
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure]
      fun ξ : Circ => (Work.Analysis.IonescuWainger.periodize m) ξ
        * ((Work.BourgainPlan.IonescuWainger.ftLp v hv) : Circ → ℂ) ξ
        * star (fourier (T := 1) x ξ) := by
    filter_upwards [hstarshift, hper] with ξ h1 h2
    rw [h1, h2, star_mul, star_star]
    ring
  calc (∫ ξ : Circ, (Work.Analysis.IonescuWainger.periodize m) ξ
        * ((Work.BourgainPlan.IonescuWainger.ftLp v hv) : Circ → ℂ) ξ
        * star (fourier (T := 1) x ξ) ∂Work.Analysis.IonescuWainger.circleMeasure)
      = ∫ ξ : Circ, ((Work.BourgainPlan.IonescuWainger.ftLp v hv) : Circ → ℂ) ξ
        * star (((Work.BourgainPlan.IonescuWainger.ftLp
            (fun j : ℤ => star (Work.KMTAreas.A7.cw m (x - j))) hk) : Circ → ℂ) ξ)
        ∂Work.Analysis.IonescuWainger.circleMeasure := (integral_congr_ae hcongr).symm
    _ = ∑' j : ℤ, v j * star (star (Work.KMTAreas.A7.cw m (x - j))) := hP.symm
    _ = ∑' j : ℤ, Work.KMTAreas.A7.cw m j * v (x - j) := hLHS

/-! ## 8. The real-line realization of a circle function -/

private theorem volume_addCircle_one_eq_circleMeasure :
    (volume : Measure Circ) = Work.Analysis.IonescuWainger.circleMeasure := by
  rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul]

/-- **The Lebesgue lower integral is invariant under `x ↦ -x`.** -/
theorem lintegral_neg_eq_self {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume) :
    ∫⁻ x : ℝ, f (-x) = ∫⁻ x : ℝ, f x := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hf' : AEMeasurable f ((volume : Measure ℝ).map (fun x : ℝ => -x)) := by
    rw [hmp.map_eq]; exact hf
  have h1 : ∫⁻ x : ℝ, f (-x)
      = ∫⁻ a : ℝ, f a ∂((volume : Measure ℝ).map (fun x : ℝ => -x)) :=
    lintegral_comp' (μ := (volume : Measure ℝ)) (f := f) (g := fun x : ℝ => -x)
      hf' hmp.measurable.aemeasurable
  rw [h1, hmp.map_eq]

/-- **Integrability of the realization.** -/
theorem integrable_envRealize {δ : ℝ} (hδ : 0 < δ) {F : Circ → ℂ}
    (hF : MeasureTheory.Integrable F Work.Analysis.IonescuWainger.circleMeasure) :
    MeasureTheory.Integrable (envRealize δ F) volume := by
  have hvol : (volume : Measure Circ) = Work.Analysis.IonescuWainger.circleMeasure :=
    volume_addCircle_one_eq_circleMeasure
  have hFv : MeasureTheory.Integrable F (volume : Measure Circ) := by rw [hvol]; exact hF
  have hmp : MeasurePreserving (fun x : ℝ => (x : Circ))
      (volume.restrict (Set.Ioc (-(1 / 2)) (1 / 2))) (volume : Measure Circ) := by
    have h := AddCircle.measurePreserving_mk (T := 1) (-(1 / 2))
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 from by norm_num] at h
    exact h
  have hcomp : AEMeasurable (fun x : ℝ => F ((x : ℝ) : Circ))
      (volume.restrict (Set.Ioc (-(1 / 2)) (1 / 2))) :=
    hFv.aemeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have hfun : envRealize δ F = (envBandSet δ).indicator
      (fun ξ : ℝ => F ((ξ : ℝ) : Circ)) := funext fun ξ => envRealize_apply ξ
  have hasm : AEMeasurable (envRealize δ F) volume := by
    rw [hfun]
    exact (aemeasurable_indicator_iff (envBandSet_measurableSet δ)).mpr
      (hcomp.mono_set (envBandSet_subset_Ioc hδ))
  have hnorm : ∀ ξ : ℝ, ‖envRealize δ F ξ‖ₑ
      = (envBandSet δ).indicator (fun ξ : ℝ => ‖F ((ξ : ℝ) : Circ)‖ₑ) ξ := by
    intro ξ
    rw [envRealize_apply]
    by_cases h : ξ ∈ envBandSet δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
  have hfin : ∫⁻ ξ : ℝ, ‖envRealize δ F ξ‖ₑ ∂volume < ∞ := by
    have h1 : ∫⁻ ξ : ℝ, ‖envRealize δ F ξ‖ₑ ∂volume
        = ∫⁻ ξ in envBandSet δ, ‖F ((ξ : ℝ) : Circ)‖ₑ ∂volume := by
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hnorm),
        lintegral_indicator (envBandSet_measurableSet δ)]
    rw [h1]
    have h2 : ∫⁻ ξ in Set.Ioc (-(1 / 2)) (1 / 2), ‖F ((ξ : ℝ) : Circ)‖ₑ ∂volume
        = ∫⁻ ξ : Circ, ‖F ξ‖ₑ := by
      have hle := AddCircle.lintegral_preimage (T := 1) (-(1 / 2))
        (fun ξ : Circ => ‖F ξ‖ₑ)
      rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 from by norm_num] at hle
      exact hle
    exact lt_of_le_of_lt (lintegral_mono_set (envBandSet_subset_Ioc hδ))
      (by rw [h2]; exact hFv.hasFiniteIntegral)
  exact ⟨hasm.aestronglyMeasurable, hfin⟩

/-- **The inverse Fourier transform of the realization, at integers.** -/
theorem fourierInv_envRealize {δ : ℝ} (hδ : 0 < δ) {F : Circ → ℂ}
    (hF : MeasureTheory.Integrable F Work.Analysis.IonescuWainger.circleMeasure)
    (hsupp : ∀ ξ : Circ, 2 * δ < ‖ξ‖ → F ξ = 0) (x : ℤ) :
    FourierTransformInv.fourierInv (envRealize δ F) (x : ℝ)
      = ∫ ξ : Circ, F ξ * fourier (T := 1) x ξ
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
  have hvol : (volume : Measure Circ) = Work.Analysis.IonescuWainger.circleMeasure :=
    volume_addCircle_one_eq_circleMeasure
  rw [Real.fourierInv_eq]
  have hpt : ∀ v : ℝ, Real.fourierChar (inner ℝ v (x : ℝ)) • envRealize δ F v
      = (envBandSet δ).indicator
          (fun v : ℝ => Real.fourierChar (inner ℝ v (x : ℝ)) • F ((v : ℝ) : Circ)) v := by
    intro v
    rw [envRealize_apply]
    by_cases h : v ∈ envBandSet δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_indicator (envBandSet_measurableSet δ)]
  have hchar : ∀ v : ℝ, (Real.fourierChar (inner ℝ v (x : ℝ)) : ℂ)
      = (fourier (T := 1) x ((v : ℝ) : Circ) : ℂ) := by
    intro v
    rw [Real.fourierChar_apply, fourier_coe_apply, Real.inner_apply]
    norm_num
    congr 1
    push_cast
    ring
  have hsub : envBandSet δ ⊆ Set.Ioc (-(1 / 2)) (1 / 2) := envBandSet_subset_Ioc hδ
  have hvanish : ∀ v ∈ Set.Ioc (-(1 / 2)) (1 / 2), v ∉ envBandSet δ →
      Real.fourierChar (inner ℝ v (x : ℝ)) • F ((v : ℝ) : Circ) = 0 := by
    intro v hv hvI
    by_cases h : 4 * δ < 1
    · rw [envBandSet_of_lt h] at hvI
      rw [Set.mem_Icc, not_and_or] at hvI
      have hnorm : 2 * δ < ‖((v : ℝ) : Circ)‖ := by
        rw [Set.mem_Ioc] at hv
        rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
          (by rw [abs_le, abs_one]; exact ⟨by linarith [hv.1], hv.2⟩)]
        rcases hvI with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hsupp _ hnorm, smul_zero]
    · rw [envBandSet_of_not_lt h] at hvI
      exact absurd hv hvI
  have hind : (envBandSet δ).indicator
        (fun v : ℝ => Real.fourierChar (inner ℝ v (x : ℝ)) • F ((v : ℝ) : Circ))
      = (Set.Ioc (-(1 / 2)) (1 / 2)).indicator
        (fun v : ℝ => Real.fourierChar (inner ℝ v (x : ℝ)) • F ((v : ℝ) : Circ)) := by
    funext v
    by_cases hv : v ∈ envBandSet δ
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hsub hv)]
    · by_cases hv2 : v ∈ Set.Ioc (-(1 / 2)) (1 / 2)
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_mem hv2, hvanish v hv2 hv]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv2]
  rw [← integral_indicator (envBandSet_measurableSet δ), hind,
    integral_indicator measurableSet_Ioc]
  have hpoint : ∫ v in Set.Ioc (-(1 / 2)) (1 / 2),
        (fourier (T := 1) x ((v : ℝ) : Circ) : ℂ) • F ((v : ℝ) : Circ) ∂volume
      = ∫ ξ : Circ, (fourier (T := 1) x ξ : ℂ) • F ξ := by
    have hle := AddCircle.integral_preimage (T := 1) (-(1 / 2))
      (fun ξ : Circ => (fourier (T := 1) x ξ : ℂ) • F ξ)
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 from by norm_num] at hle
    exact hle
  refine Eq.trans (b := ∫ ξ : Circ, (fourier (T := 1) x ξ : ℂ) • F ξ) ?_ ?_
  · rw [show (fun v : ℝ => Real.fourierChar (inner ℝ v (x : ℝ)) • F ((v : ℝ) : Circ))
        = fun v : ℝ => (fourier (T := 1) x ((v : ℝ) : Circ) : ℂ) • F ((v : ℝ) : Circ) from
      funext fun v => by rw [Circle.smul_def, hchar v]]
    exact hpoint
  · rw [← hvol]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring

end

end Work.KMTAreas.A7Rep
