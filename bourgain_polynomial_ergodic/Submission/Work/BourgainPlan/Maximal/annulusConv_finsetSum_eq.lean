import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSum_mikhlin
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSquare_l2
import Submission.Work.BourgainPlan.Maximal.annulusK_memLp
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size

namespace Work.BourgainPlan.Maximal

set_option linter.style.haveILetI false

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

/-! ## Auxiliary facts

`𝓕⁻ (b m)` is continuous (it is the inverse Fourier transform of the integrable function `b m`),
and it decays like `(1 + |z|)^{-2}`, so it lies in `L^r` for every `1 ≤ r`.
-/

private lemma continuous_fourierInv_of_integrable_annulus2 {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (FourierTransformInv.fourierInv f) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf.comp_neg

/-- The annulus kernel is continuous. -/
private lemma continuous_annulusK_annulus2 (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    Continuous (annulusK b m) := by
  have hbint : Integrable (b m) volume := by
    simpa only [iteratedDeriv_zero] using annulusK_integrable b hb hsmooth m 0
  simpa only [annulusK] using continuous_fourierInv_of_integrable_annulus2 hbint

private lemma annulusK_rpow_inv_sq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = x⁻¹ ^ 2 := by
  rw [Real.rpow_neg hx]; norm_num

private lemma annulusK_rpow_compare {a z : ℝ} (ha : 0 < a) :
    (1 + a * |z|) ^ (-(2 : ℝ)) ≤ ((min 1 a)⁻¹ ^ 2) * (1 + |z|) ^ (-(2 : ℝ)) := by
  have hc : 0 < min 1 a := lt_min one_pos ha
  have h1 : min 1 a * (1 + |z|) ≤ 1 + a * |z| := by
    rcases lt_or_ge a 1 with h | h
    · rw [min_eq_right h.le]; nlinarith [abs_nonneg z]
    · rw [min_eq_left h]; nlinarith [abs_nonneg z]
  have hstep : (1 + a * |z|) ^ (-(2 : ℝ)) ≤ (min 1 a * (1 + |z|)) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have hsplit : (min 1 a * (1 + |z|)) ^ (-(2 : ℝ))
      = (min 1 a)⁻¹ ^ 2 * (1 + |z|) ^ (-(2 : ℝ)) := by
    rw [Real.mul_rpow (le_of_lt hc) (by positivity), annulusK_rpow_inv_sq (le_of_lt hc)]
  exact le_trans hstep hsplit.le

/-- **Pointwise decay of the annulus kernel**: `‖K_m z‖ ≤ K (1 + |z|)^{-2}` with a constant `K`
independent of `z` (but depending on `m`). -/
private lemma annulusK_pointwise_bound (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, ‖annulusK b m z‖ ≤ K * (1 + |z|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := annulusKernel_size b hb hsmooth 2
  refine ⟨C * (2 : ℝ) ^ (-m) * ((min 1 ((2 : ℝ) ^ (-m)))⁻¹ ^ 2), ?_, fun z => ?_⟩
  · positivity
  · have ha : 0 < (2 : ℝ) ^ (-m) := by positivity
    have h := hC m z
    have hstep : C * (2 : ℝ) ^ (-m) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(2 : ℝ))
        ≤ C * (2 : ℝ) ^ (-m)
          * (((min 1 ((2 : ℝ) ^ (-m)))⁻¹ ^ 2) * (1 + |z|) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (annulusK_rpow_compare ha) (by positivity)
    calc ‖annulusK b m z‖ = ‖FourierTransform.fourierInv (b m) z‖ := rfl
      _ ≤ C * (2 : ℝ) ^ (-m) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(2 : ℝ)) := h
      _ ≤ C * (2 : ℝ) ^ (-m)
            * (((min 1 ((2 : ℝ) ^ (-m)))⁻¹ ^ 2) * (1 + |z|) ^ (-(2 : ℝ))) := hstep
      _ = C * (2 : ℝ) ^ (-m) * ((min 1 ((2 : ℝ) ^ (-m)))⁻¹ ^ 2)
            * (1 + |z|) ^ (-(2 : ℝ)) := by ring

/-- **The annulus kernel lies in `L^r` for every `1 ≤ r`.** -/
lemma memLp_annulusK_ofReal (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ)
    {r : ℝ} (hr : 1 ≤ r) :
    MemLp (annulusK b m) (ENNReal.ofReal r) volume := by
  obtain ⟨K, hKnn, hbound⟩ := annulusK_pointwise_bound b hb hsmooth m
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hGz : ∀ z : ℝ, 0 ≤ K * (1 + |z|) ^ (-(2 : ℝ)) := fun z =>
    mul_nonneg hKnn (Real.rpow_nonneg (by positivity) _)
  rw [memLp_iff, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hr0) ENNReal.ofReal_ne_top
        (continuous_annulusK_annulus2 b hb hsmooth m).aestronglyMeasurable,
      ENNReal.toReal_ofReal hr0.le]
  refine (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0 : ℝ) < 1 / r)).mpr ?_
  -- the explicit `L^r` majorant
  have hbase : Integrable (fun z : ℝ => K ^ r * (1 + |z|) ^ (-(2 * r))) volume := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ)) (r := 2 * r)
      (by rw [Module.finrank_self]; norm_num; linarith)).const_mul (K ^ r)
    simpa only [Real.norm_eq_abs] using h
  have hInt : Integrable (fun z : ℝ => (K * (1 + |z|) ^ (-(2 : ℝ))) ^ r) volume := by
    refine hbase.congr (Eventually.of_forall fun z => ?_)
    have h1 : (K * (1 + |z|) ^ (-(2 : ℝ))) ^ r
        = K ^ r * ((1 + |z|) ^ (-(2 : ℝ))) ^ r :=
      Real.mul_rpow hKnn (Real.rpow_nonneg (by positivity) _)
    have h2 : ((1 + |z|) ^ (-(2 : ℝ))) ^ r = (1 + |z|) ^ (-(2 : ℝ) * r) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + |z|) (-(2 : ℝ)) r).symm
    change K ^ r * (1 + |z|) ^ (-(2 * r)) = (K * (1 + |z|) ^ (-(2 : ℝ))) ^ r
    rw [h1, h2, show -(2 : ℝ) * r = -(2 * r) by ring]
  have hofreal : ∫⁻ z : ℝ, ENNReal.ofReal ((K * (1 + |z|) ^ (-(2 : ℝ))) ^ r)
      = ENNReal.ofReal (∫ z : ℝ, (K * (1 + |z|) ^ (-(2 : ℝ))) ^ r) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall fun z => Real.rpow_nonneg (hGz z) r)).symm
  calc ∫⁻ z : ℝ, ‖annulusK b m z‖ₑ ^ r
      ≤ ∫⁻ z : ℝ, (ENNReal.ofReal (K * (1 + |z|) ^ (-(2 : ℝ)))) ^ r := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm (annulusK b m z)]
        exact ENNReal.rpow_le_rpow ((ENNReal.ofReal_le_ofReal_iff (hGz z)).mpr (hbound z)) hr0.le
    _ = ∫⁻ z : ℝ, ENNReal.ofReal ((K * (1 + |z|) ^ (-(2 : ℝ))) ^ r) := by
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (hGz z) hr0.le]
    _ = ENNReal.ofReal (∫ z : ℝ, (K * (1 + |z|) ^ (-(2 : ℝ))) ^ r) := hofreal
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- `y ↦ x - y` preserves Lebesgue measure on `ℝ`. -/
lemma measurePreserving_annulusSub (x : ℝ) :
    MeasurePreserving (fun y : ℝ => x - y) volume volume := by
  refine ⟨?_, ?_⟩
  · fun_prop
  · have h1 : (fun y : ℝ => x - y) = (fun z : ℝ => -z) ∘ (fun y : ℝ => y - x) := by
      funext y; simp
    rw [h1, ← Measure.map_map (g := fun z : ℝ => -z) (f := fun y : ℝ => y - x)
        (by fun_prop) (by fun_prop)]
    rw [(measurePreserving_sub_right volume x).map_eq, Measure.map_neg_eq_self volume]

/-- The reflected annulus kernel `y ↦ K_m (x - y)` lies in `L^r` for every `1 ≤ r`. -/
lemma memLp_shifted_annulusK (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (x : ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    MemLp (fun y : ℝ => annulusK b m (x - y)) (ENNReal.ofReal r) volume :=
  (memLp_annulusK_ofReal b hb hsmooth m hr).comp_measurePreserving
    (measurePreserving_annulusSub x)

/-- The inverse Fourier transform of a finite linear combination `∑_{n ∈ F} ε n · b (j+n)` is the
finite linear combination of the inverse transforms, for integrable `b n`.  (This linearity is not
an `instance` for plain function spaces: on non-integrable functions Mathlib's `𝓕⁻` is the junk
value `0`, and additivity genuinely fails there.) -/
lemma fourierInv_annulusSymbolSum_apply (b : ℤ → ℝ → ℂ)
    (hbint : ∀ n : ℤ, Integrable (b n) volume)
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (z : ℝ) :
    FourierTransform.fourierInv (annulusSymbolSum b j F ε) z
      = ∑ n ∈ F, ε n * FourierTransform.fourierInv (b (j + n)) z := by
  rw [fourierInv_eq_polyE_integral]
  have hcongr : (fun β : ℝ => polyE (β * z) * annulusSymbolSum b j F ε β)
      = fun β : ℝ => ∑ n ∈ F, polyE (β * z) * (ε n * b (j + n) β) := by
    funext β
    rw [annulusSymbolSum_apply, Finset.mul_sum]
  rw [hcongr, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (fun β : ℝ => polyE (β * z) * (ε n * b (j + n) β))
          = fun β : ℝ => ε n * (polyE (β * z) * b (j + n) β) by funext β; ring]
    rw [MeasureTheory.integral_const_mul, ← fourierInv_eq_polyE_integral (b (j + n)) z]
  · intro n _
    exact (hbint (j + n)).const_mul (ε n) |>.mul_of_top_right
      (memLp_top_of_bound
        ((continuous_polyE.comp (continuous_id.mul continuous_const)).aestronglyMeasurable) 1
        (Eventually.of_forall fun β => by simp))

/-- **The signed sum of the annulus convolutions is the convolution with the signed sum of the
kernels**, stated with the symbol on the right-hand side.

`annulusConv b m f x = ∫ y, annulusK b m (x - y) * f y` with `annulusK b m = 𝓕⁻ (b m)`, and
`annulusSymbolSum b j F ε = fun ξ => ∑_{n ∈ F} ε n * b (j + n) ξ`.  The claim is the pointwise
identity

  `∑_{n ∈ F} ε n * (K_{j+n} * f)(x) = ∫ y, 𝓕⁻ (∑_{n ∈ F} ε n · b (j+n)) (x - y) · f y`

for every `f ∈ L^p(ℝ)` (`p ≥ 1`), every finite `F`, every coefficient family `ε` and every `x`.

Two ingredients:

(i) `𝓕⁻ (∑_{n ∈ F} ε n · b (j+n)) z = ∑_{n∈F} ε n · K_{j+n} z` for every `z`
(`fourierInv_annulusSymbolSum_apply`; note that this linearity is genuinely only available for
integrable `b n`).

(ii) the swap of the finite sum over `n` with the Bochner integral over `y`, which needs the
per-term integrability of `y ↦ annulusK b (j+n) (x - y) * f y`.  Since `b (j+n)` is smooth with
compact support, `annulusK b (j+n)` is in `L^r` for every `1 ≤ r`
(`memLp_annulusK_ofReal`); Hölder (`MeasureTheory.MemLp.integrable_mul`) against `f ∈ L^p` gives
the integrability, and `MeasureTheory.integral_finsetSum` (plus
`MeasureTheory.integral_const_mul` for the `ε n` factor) gives the identity. -/
theorem annulusConv_finsetSum_eq (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    {p : ℝ} (hp : 1 ≤ p) (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (f : ℝ → ℂ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    (∑ n ∈ F, ε n * Work.BourgainPlan.Maximal.annulusConv b (j + n) f x)
      = ∫ y : ℝ,
          FourierTransformInv.fourierInv (Work.BourgainPlan.Maximal.annulusSymbolSum b j F ε)
            (x - y) * f y := by
  have hbint : ∀ n : ℤ, Integrable (b n) volume := fun n => by
    simpa only [iteratedDeriv_zero] using annulusK_integrable b hb hsmooth n 0
  have hlin : ∀ z : ℝ, FourierTransform.fourierInv (annulusSymbolSum b j F ε) z
      = ∑ n ∈ F, ε n * annulusK b (j + n) z := fun z =>
    fourierInv_annulusSymbolSum_apply b hbint j F ε z
  -- integrability of every summand
  have hInt : ∀ n : ℤ, Integrable (fun y : ℝ => (ε n * annulusK b (j + n) (x - y)) * f y) := by
    intro n
    by_cases hp1 : p = 1
    · have hf1 : MemLp f 1 volume := by
        rw [hp1, ENNReal.ofReal_one] at hf
        exact hf
      obtain ⟨C, hCpos, hC⟩ := annulusKernel_size b hb hsmooth 0
      have hCbnd : ∀ z : ℝ, ‖annulusK b (j + n) z‖ ≤ C * (2 : ℝ) ^ (-(j + n)) := by
        intro z
        have h := hC (j + n) z
        simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, annulusK] using h
      have hφ : MemLp (fun y : ℝ => ε n * annulusK b (j + n) (x - y)) ∞ volume := by
        refine memLp_top_of_bound ?_ (‖ε n‖ * (C * (2 : ℝ) ^ (-(j + n)))) ?_
        · exact (continuous_const.mul
            ((continuous_annulusK_annulus2 b hb hsmooth (j + n)).comp
              (continuous_const.sub continuous_id))).aestronglyMeasurable
        · filter_upwards with y
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hCbnd (x - y)) (norm_nonneg _)
      exact (memLp_one_iff_integrable.mp hf1).mul_of_top_right hφ
    · have hp1' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
      have hppos : 0 < p := lt_trans zero_lt_one hp1'
      have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1'
      have hqpos : 0 < p.conjExponent := by
        rw [Real.conjExponent]; exact div_pos hppos (by linarith)
      have hq1 : 1 ≤ p.conjExponent := by
        rw [Real.conjExponent, le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]; linarith
      have hk : MemLp (fun y : ℝ => annulusK b (j + n) (x - y))
          (ENNReal.ofReal p.conjExponent) volume :=
        memLp_shifted_annulusK b hb hsmooth (j + n) x hq1
      have hεk : MemLp (fun y : ℝ => ε n * annulusK b (j + n) (x - y))
          (ENNReal.ofReal p.conjExponent) volume := hk.const_mul (ε n)
      haveI : (ENNReal.ofReal p.conjExponent).HolderTriple (ENNReal.ofReal p) 1 := by
        refine (ENNReal.holderTriple_iff _ _ 1).mpr ?_
        simp only [inv_one]
        rw [← ENNReal.ofReal_inv_of_pos hqpos, ← ENNReal.ofReal_inv_of_pos hppos,
          ← ENNReal.ofReal_add (inv_nonneg.mpr hqpos.le) (inv_nonneg.mpr hppos.le),
          add_comm p.conjExponent⁻¹ p⁻¹, (Real.holderConjugate_iff.mp hpq).2, ENNReal.ofReal_one]
      exact hεk.integrable_mul hf
  -- the two sides agree
  have hcongr : (fun y : ℝ =>
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
      = fun y : ℝ => ∑ n ∈ F, (ε n * annulusK b (j + n) (x - y)) * f y := by
    funext y
    rw [hlin (x - y), Finset.sum_mul]
  have key : (∫ y : ℝ,
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
      = ∑ n ∈ F, ε n * annulusConv b (j + n) f x := by
    rw [hcongr, MeasureTheory.integral_finsetSum F (fun n _ => hInt n)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (fun y : ℝ => (ε n * annulusK b (j + n) (x - y)) * f y)
          = fun y : ℝ => ε n * (annulusK b (j + n) (x - y) * f y) by funext y; ring]
    rw [MeasureTheory.integral_const_mul]
    rfl
  exact key.symm

end Work.BourgainPlan.Maximal
