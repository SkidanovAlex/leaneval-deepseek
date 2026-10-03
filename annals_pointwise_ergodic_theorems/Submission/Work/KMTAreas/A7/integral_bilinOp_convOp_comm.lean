import Mathlib
import Submission.Work.A7.ModelApproxCore_kernelComp
import Submission.Work.KMTPlan.A6.tsum_norm_kernComp_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

/-- A family of complex functions whose `lintegral` norms have finite total sum has summable
`L¹`-norms.  (Elementary `ENNReal`/`NNReal` bookkeeping.) -/
private lemma summable_integral_norm_of_tsum_lintegral_ne_top {ι : Type*} [Countable ι]
    {μ : Measure ℝ} {φ : ι → ℝ → ℂ}
    (hint : ∀ i, Integrable (fun x : ℝ => ‖φ i x‖) μ)
    (hfin : (∑' i : ι, ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) ≠ ⊤) :
    Summable (fun i : ι => ∫ x : ℝ, ‖φ i x‖ ∂μ) := by
  have hterm : ∀ i : ι, (∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top hfin (ENNReal.le_tsum (f := fun i : ι => ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) i)
  have hnn : ∀ i : ι, 0 ≤ ∫ x : ℝ, ‖φ i x‖ ∂μ :=
    fun i => integral_nonneg fun x => norm_nonneg _
  have hofReal : ∀ i : ι,
      ENNReal.ofReal (∫ x : ℝ, ‖φ i x‖ ∂μ) = ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ := by
    intro i
    simpa only [ofReal_norm] using
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint i)
        (Eventually.of_forall (fun x => norm_nonneg _))
  have hcoe : ∀ i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ := by
    intro i
    rw [Real.toNNReal_of_nonneg (hnn i), ← ENNReal.ofReal_eq_coe_nnreal (hnn i), hofReal i]
  have hsum : (∑' i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
    rw [show (∑' i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞))
        = ∑' i : ι, ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ from tsum_congr hcoe]
    exact hfin
  have h1 : Summable (fun i : ι => (∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hsum
  have h2 : Summable (fun i : ι => (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h1
  exact h2.congr (fun i => Real.coe_toNNReal _ (hnn i))

/-- **Exchange of the interval integral with the two `tsum`s of a composed bilinear convolution.**

`bilinOp K u v x = ∑'_a ∑'_b K a b · u (x-a) · v (x-b)` and
`kernComp K κ κ' a b = ∑'_{a'} ∑'_{b'} K (a-a') (b-b') κ a' κ' b'` are the defining iterated sums of
`Work.KMTAreas.A7`.  If `K ∈ ℓ¹(ℤ²)`, the families `κ t`, `κ' t` are `ℓ¹(ℤ)` for `t ∈ (1/2, 1]`
with `t`-uniform mass bounds `B1`, `B2`, each coefficient is measurable in `t`, and `f`, `g` are
bounded, then

  `∫_{1/2}^{1} bilinOp K (convOp (κ t) f) (convOp (κ' t) g) x dt = bilinOp (∫_{1/2}^{1} kernComp K (κ t) (κ' t) dt) f g x`.

This is the Fubini/Tonelli step of the §6 model-operator analysis: the §7 model operator is the
`t`-integral of the twisted bilinear multiplier whose kernel is the *composed* kernel
`Work.KMTAreas.A7.smallKmod`, and the identity requested by the A7 area is exactly this swap.

Route: write both sides as a *single* sum over `p : ℤ × ℤ` (`Submission.Work.A7.
ModelApproxCore_aux.bilinOp_eq_tsum`), exchange the interval integral with that sum
(`MeasureTheory.integral_tsum` for `μ = volume.restrict (Set.Ioc (1/2) 1)`, with its finiteness
hypothesis supplied by comparing `∑' p, ∫⁻ t, ‖F p t‖ₑ` with the uniform mass bound
`∑' p, ‖kernComp K (κ t) (κ' t) p‖ ≤ BK · B1 · B2` obtained from
`Work.KMTPlan.A6.tsum_norm_kernComp_le`), then pull the constants `f (x - p.1)`, `g (x - p.2)` out
of the integral (`intervalIntegral.integral_mul_const`) and fold the single sum back into the
iterated form (`bilinOp_eq_tsum` again, its summability following from
`‖∫ t, k‖ ≤ ∫⁻ t, ‖k‖ₑ` and the finiteness already proved).  Per `t` the integrand equals
`bilinOp (kernComp K (κ t) (κ' t)) f g x` by `Work.A7.ModelApproxCore_kernelComp`, and
`Work.A7.ModelApproxCore_aux.summable_kernComp` supplies the `ℓ¹(ℤ²)`-ness of the composed kernel.
A near-complete version of this very argument (all ingredients set up, only the final reassembly
left open) is the scratch file `_lmvs2.lean` at the workspace root: it should be read first. -/
theorem integral_bilinOp_convOp_comm (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ) (f g : ℤ → ℂ)
    (BK B1 B2 Cf Cg : ℝ) (x : ℤ)
    (hK : Summable (fun p : ℤ × ℤ => ‖K p.1 p.2‖))
    (hKb : (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) ≤ BK)
    (hκ : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ t j‖))
    (hκ' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ' t j‖))
    (hκb : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ t j‖) ≤ B1)
    (hκb' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ' t j‖) ≤ B2)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hBK : 0 ≤ BK) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hmκ : ∀ j : ℤ, Measurable (fun t : ℝ => κ t j))
    (hmκ' : ∀ j : ℤ, Measurable (fun t : ℝ => κ' t j)) :
    (∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.bilinOp K
        (Work.KMTAreas.A7.convOp (κ t) f) (Work.KMTAreas.A7.convOp (κ' t) g) x)
      = Work.KMTAreas.A7.bilinOp (fun a b : ℤ =>
          ∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b) f g x := by
  classical
  have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have hae_mem : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      t ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun t ht => ht))
  have hsm : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Summable (fun p : ℤ × ℤ => ‖kernComp K (κ t) (κ' t) p.1 p.2‖) :=
    fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hK (hκ t ht) (hκ' t ht)
  have hmass : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      (∑' p : ℤ × ℤ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖) ≤ BK * B1 * B2 := by
    intro t ht
    refine (Work.KMTPlan.A6.tsum_norm_kernComp_le hK (hκ t ht) (hκ' t ht)).trans ?_
    have h1 : (∑' j : ℤ, ‖κ t j‖) ≤ B1 := hκb t ht
    have h2 : (∑' j : ℤ, ‖κ' t j‖) ≤ B2 := hκb' t ht
    have h0 : (0 : ℝ) ≤ ∑' j : ℤ, ‖κ t j‖ := tsum_nonneg (fun _ => norm_nonneg _)
    have h0' : (0 : ℝ) ≤ ∑' j : ℤ, ‖κ' t j‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul (mul_le_mul hKb h1 h0 hBK) h2 h0' (mul_nonneg hBK hB1)
  have hkern_meas : ∀ a b : ℤ, Measurable (fun t : ℝ => kernComp K (κ t) (κ' t) a b) := by
    intro a b
    rw [show (fun t : ℝ => kernComp K (κ t) (κ' t) a b)
        = fun t : ℝ => ∑' a' : ℤ, ∑' b' : ℤ,
            K (a - a') (b - b') * κ t a' * κ' t b' from rfl]
    refine Measurable.tsum (fun a' => ?_)
    refine Measurable.tsum (fun b' => ?_)
    exact (measurable_const.mul (hmκ a')).mul (hmκ' b')
  have hbndG : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      (∑' p : ℤ × ℤ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ)
        ≤ ENNReal.ofReal (BK * B1 * B2) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall ?_)
    intro t ht
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hsm t ht)]
    exact ENNReal.ofReal_le_ofReal (hmass t ht)
  have hGint : ∀ p : ℤ × ℤ,
      Integrable (fun t : ℝ => ‖kernComp K (κ t) (κ' t) p.1 p.2‖)
        (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    refine MeasureTheory.Integrable.of_bound
      (((hkern_meas p.1 p.2).aemeasurable.norm).aestronglyMeasurable.restrict) (BK * B1 * B2) ?_
    filter_upwards [hae_mem] with t ht
    have h := (Summable.le_tsum (hsm t ht) p (fun q _ => norm_nonneg _)).trans (hmass t ht)
    simpa using h
  have hfinG : (∑' p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≠ ⊤ := by
    have hEq : (∑' p : ℤ × ℤ,
        ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        = ⨆ s : Finset (ℤ × ℤ),
            ∑ p ∈ s, ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := ENNReal.tsum_eq_iSup_sum
    have hbdd : ∀ s : Finset (ℤ × ℤ),
        (∑ p ∈ s, ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          ≤ ENNReal.ofReal (BK * B1 * B2) := by
      intro s
      have hsum_eq : (∑ p ∈ s, ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          = ∫⁻ t : ℝ, ∑ p ∈ s, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
        (lintegral_finsetSum s (fun p _ => (hkern_meas p.1 p.2).enorm)).symm
      have hle1 : (∫⁻ t : ℝ, ∑ p ∈ s, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          ≤ ∫⁻ t : ℝ, ∑' p : ℤ × ℤ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
        lintegral_mono (fun t => ENNReal.sum_le_tsum s)
      have hle2 : (∫⁻ t : ℝ, ∑' p : ℤ × ℤ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          ≤ ∫⁻ t : ℝ, ENNReal.ofReal (BK * B1 * B2)
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
        lintegral_mono_ae hbndG
      have hconst : (∫⁻ t : ℝ, ENNReal.ofReal (BK * B1 * B2)
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          ≤ ENNReal.ofReal (BK * B1 * B2) := by
        rw [MeasureTheory.lintegral_const,
          MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
        exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_one.mpr (by norm_num))).trans
          (le_of_eq (mul_one _))
      exact (le_of_eq hsum_eq).trans (hle1.trans (hle2.trans hconst))
    rw [hEq]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hbdd)
  have hsum_normG : Summable (fun p : ℤ × ℤ =>
      ∫ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    summable_integral_norm_of_tsum_lintegral_ne_top hGint hfinG
  have hK' : Summable (fun p : ℤ × ℤ =>
      ‖∫ t in (1 / 2 : ℝ)..1, kernComp K (κ t) (κ' t) p.1 p.2‖) := by
    have h1 : Summable (fun p : ℤ × ℤ =>
        ‖∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _)
        (fun p => MeasureTheory.norm_integral_le_integral_norm
          (fun t : ℝ => kernComp K (κ t) (κ' t) p.1 p.2)) hsum_normG
    exact h1.congr (fun p => by rw [intervalIntegral.integral_of_le h12])
  have hpt_bound : ∀ (p : ℤ × ℤ) (t : ℝ), t ∈ Set.Ioc (1 / 2 : ℝ) 1 →
      ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖
        ≤ (BK * B1 * B2) * (Cf * Cg) := by
    intro p t ht
    have hle : ‖kernComp K (κ t) (κ' t) p.1 p.2‖ ≤ BK * B1 * B2 :=
      (Summable.le_tsum (hsm t ht) p (fun q _ => norm_nonneg _)).trans (hmass t ht)
    simp only [norm_mul]
    refine (mul_le_mul (mul_le_mul hle (hf (x - p.1)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hBK hB1) hB2)) (hg (x - p.2)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg hBK hB1) hB2) hCf)).trans ?_
    exact le_of_eq (by ring)
  have hF_str : ∀ p : ℤ × ℤ, AEStronglyMeasurable
      (fun t : ℝ => kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2))
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    exact ((((hkern_meas p.1 p.2).mul measurable_const).mul measurable_const).aemeasurable.aestronglyMeasurable).restrict
  have hFint : ∀ p : ℤ × ℤ, Integrable (fun t : ℝ =>
      kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2))
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    refine MeasureTheory.Integrable.of_bound (hF_str p) ((BK * B1 * B2) * (Cf * Cg)) ?_
    filter_upwards [hae_mem] with t ht
    simpa using hpt_bound p t ht
  have hFint_norm : ∀ p : ℤ × ℤ, Integrable (fun t : ℝ =>
      ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    refine MeasureTheory.Integrable.of_bound ((hF_str p).norm) ((BK * B1 * B2) * (Cf * Cg)) ?_
    filter_upwards [hae_mem] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpt_bound p t ht
  have hFmass : ∀ p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
        ≤ (∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
          * ENNReal.ofReal (Cf * Cg) := by
    intro p
    have h1 : ‖f (x - p.1)‖ₑ ≤ ENNReal.ofReal Cf := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hf (x - p.1))
    have h2 : ‖g (x - p.2)‖ₑ ≤ ENNReal.ofReal Cg := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hg (x - p.2))
    have hstep : (∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1)
            * g (x - p.2)‖ₑ ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        ≤ ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ * ENNReal.ofReal (Cf * Cg)
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
      refine MeasureTheory.lintegral_mono (fun t => ?_)
      rw [enorm_mul, enorm_mul]
      exact (mul_le_mul' (mul_le_mul' le_rfl h1) h2).trans
        (le_of_eq (by rw [mul_assoc, ← ENNReal.ofReal_mul hCf]))
    exact hstep.trans (le_of_eq (MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_ne_top))
  have hle_F : (∑' p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
      ≤ (∑' p : ℤ × ℤ, ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * ENNReal.ofReal (Cf * Cg) := by
    exact (ENNReal.tsum_le_tsum hFmass).trans (le_of_eq ENNReal.tsum_mul_right)
  have hfinF : (∑' p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hfinG ENNReal.ofReal_ne_top) hle_F
  have hsum_normF : Summable (fun p : ℤ × ℤ =>
      ∫ t : ℝ, ‖kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)‖
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    summable_integral_norm_of_tsum_lintegral_ne_top hFint_norm hfinF
  have hswap : (∫ t : ℝ, ∑' p : ℤ × ℤ,
        kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
      = ∑' p : ℤ × ℤ, ∫ t : ℝ,
          kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsum_normF).symm
  have hpull : ∀ p : ℤ × ℤ,
      (∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        = (∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * f (x - p.1) * g (x - p.2) := by
    intro p
    have hcongr : (fun t : ℝ => kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2))
        = fun t : ℝ => kernComp K (κ t) (κ' t) p.1 p.2 * (f (x - p.1) * g (x - p.2)) := by
      funext t; ring
    rw [hcongr, MeasureTheory.integral_mul_const, mul_assoc]
  have hLHS : (∫ t in (1 / 2 : ℝ)..1, bilinOp K (convOp (κ t) f) (convOp (κ' t) g) x)
      = ∫ t : ℝ, ∑' p : ℤ × ℤ,
          kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le h12]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_mem] with t ht
    rw [← Work.A7.ModelApproxCore_kernelComp (K := K) (κ := κ t) (κ' := κ' t) (u := f) (v := g)
      (Cu := Cf) (Cv := Cg) hK (hκ t ht) (hκ' t ht) hf hg x]
    exact Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := kernComp K (κ t) (κ' t))
      (u := f) (v := g) (Cu := Cf) (Cv := Cg) (hsm t ht) hf hg x
  have hRHS : bilinOp (fun a b : ℤ =>
        ∫ t in (1 / 2 : ℝ)..1, kernComp K (κ t) (κ' t) a b) f g x
      = ∑' p : ℤ × ℤ,
          (∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * f (x - p.1) * g (x - p.2) := by
    rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := fun a b : ℤ =>
          ∫ t in (1 / 2 : ℝ)..1, kernComp K (κ t) (κ' t) a b)
        (u := f) (v := g) (Cu := Cf) (Cv := Cg) hK' hf hg x]
    refine tsum_congr (fun p => ?_)
    show (∫ t in (1 / 2 : ℝ)..1, kernComp K (κ t) (κ' t) p.1 p.2)
          * f (x - p.1) * g (x - p.2)
        = (∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * f (x - p.1) * g (x - p.2)
    rw [intervalIntegral.integral_of_le h12]
  have hsumcongr : (∑' p : ℤ × ℤ, ∫ t : ℝ,
        kernComp K (κ t) (κ' t) p.1 p.2 * f (x - p.1) * g (x - p.2)
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
      = ∑' p : ℤ × ℤ,
          (∫ t : ℝ, kernComp K (κ t) (κ' t) p.1 p.2
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * f (x - p.1) * g (x - p.2) :=
    tsum_congr hpull
  exact hLHS.trans (hswap.trans (hsumcongr.trans hRHS.symm))

end

end Work.KMTAreas.A7
