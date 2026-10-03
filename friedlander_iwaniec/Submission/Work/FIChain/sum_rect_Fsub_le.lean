import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj_le_defs
import Submission.Work.FIChain.inner_Fsub_measurable
import Submission.Work.FIChain.sum_rect_Fsub_pre

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

set_option autoImplicit false
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FIChain.sum_rect_Fsub_le`

The last bookkeeping step of the REM majorant (`s3RemPlus_maj_le`, companion's (8.4)): the
`ℓ`-sum of the per-`ℓ` substituted integrals over the common rectangle is at most the integral of
the `ℓ`-summed integrand `Ksub` over the same rectangle.

The mathematical content is *only* the finite-sum/integral interchange plus the pointwise
comparison: on the `w`-range `[1, x/Cm]` (`x/Cm ≤ x` because `1 ≤ Cm`) the joint integrand `Ksub`
is the full `ℓ`-sum `Σ_{ℓ ≤ x} Fsub` (`Ksub_eq_sum_Fsub_of_le`), so

`Σ_{ℓ ≤ ⌊x/Cm⌋₊} ∫∫ Fsub ℓ/(v w) = ∫∫ (Σ_{ℓ ≤ ⌊x/Cm⌋₊} Fsub ℓ)/(v w)
   ≤ ∫∫ (Σ_{ℓ ≤ x} Fsub ℓ)/(v w) = ∫∫ Ksub/(v w)`,

the interchange being legitimate because all the functions are bounded and measurable on the
finite-measure rectangle.
-/

/-! ## 1. Integrability of one `ℓ`-term (the `w`-integration) -/

/-- The divided `ℓ`-th rectangle integrand is integrable in `w` on `Ioc 1 (x/Cm)` as soon as
`v > 0`: it is measurable (`measurable_Fsub`) and bounded by the constant
`τ(ℓ)²·(x·4·Ã(x))/v` there (`Fsub_div_abs_le`), because `w > 1` and `Cm·w ≤ Cm·(x/Cm) = x`. -/
lemma sum_rect_Fsub_integrable_w (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm)
    (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ)) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun w : ℝ => Fsub x Cm B ℓ v w / (v * w))
      (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ))) volume := by
  have h1 : Measurable (fun w : ℝ => Fsub x Cm B ℓ v w) :=
    (measurable_Fsub x Cm B ℓ).comp (Measurable.prodMk measurable_const measurable_id)
  have hmeas : Measurable (fun w : ℝ => Fsub x Cm B ℓ v w / (v * w)) :=
    h1.div (measurable_const.mul measurable_id)
  refine Measure.integrableOn_of_bounded
    (measure_Ioc_lt_top (a := (1 : ℝ)) (b := (x : ℝ) / (Cm : ℝ))).ne
    hmeas.aestronglyMeasurable
    (M := ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / v) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun w hw => ?_)
  rw [Real.norm_eq_abs]
  exact Fsub_div_abs_le x Cm B ℓ hv (le_of_lt hw.1)
    (Cm_mul_le_of_le_div x Cm hCm1 hw.2)

/-! ## 2. Integrability in `v` of the `w`-inner integral of one `ℓ`-term -/

/-- The `w`-inner integral of the `ℓ`-th rectangle integrand is integrable in `v` over
`Ioc (zc x B) (⌊x/Cm⌋₊·(e·zc x B))`: it is measurable (`inner_Fsub_measurable`) and bounded by
`τ(ℓ)²·(x·4·Ã(x))/zc · (x/Cm − 1)`, since on the `w`-range the integrand is at most
`τ(ℓ)²·(x·4·Ã(x))/v ≤ τ(ℓ)²·(x·4·Ã(x))/zc` in absolute value. -/
lemma sum_rect_Fsub_integrable_inner (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm)
    (hzcp : 0 < zc x B) (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ))
    (hV : zc x B ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)) :
    IntegrableOn (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w))
      (Set.Ioc (zc x B) (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)))
      volume := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hK : 0 ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by positivity
  refine Measure.integrableOn_of_bounded
    (measure_Ioc_lt_top (a := zc x B)
      (b := ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B))).ne
    (inner_Fsub_measurable x Cm B ℓ).aestronglyMeasurable
    (M := ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B
      * ((x : ℝ) / (Cm : ℝ) - 1)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun v hv => ?_)
  have hv0 : 0 < v := lt_trans hzcp hv.1
  have hconv : (∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w))
      = ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w) :=
    (intervalIntegral.integral_of_le hc1).symm
  have hnorm : |∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w)|
      ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B
        * ((x : ℝ) / (Cm : ℝ) - 1) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := (x : ℝ) / (Cm : ℝ))
      (C := ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B)
      (f := fun w : ℝ => Fsub x Cm B ℓ v w / (v * w)) ?_
    · rw [Real.norm_eq_abs] at h1
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ) / (Cm : ℝ) - 1)] at h1
      exact h1
    · intro w hw
      rw [Set.uIoc_of_le hc1] at hw
      have hCw : (Cm : ℝ) * w ≤ (x : ℝ) := Cm_mul_le_of_le_div x Cm hCm1 hw.2
      rw [Real.norm_eq_abs]
      exact le_trans (Fsub_div_abs_le x Cm B ℓ hv0 (le_of_lt hw.1) hCw)
        (div_le_div_of_nonneg_left hK hzcp hv.1.le)
  rw [hconv, Real.norm_eq_abs]
  exact hnorm

/-! ## 3. The abstract finite-sum / iterated-integral interchange -/

/-- **Abstract interchange lemma.** For a finite family `f i` and a function `g` with
`Σ_i f i v w / (v·w) ≤ g v w / (v·w)` on the rectangle, and all the integrability needed to
interchange `Σ` with the two integrals, the sum of the iterated integrals is at most the iterated
integral of `g`. -/
theorem sum_setIntegral_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) {a b c d : ℝ}
    (hf : ∀ i ∈ s, Integrable (fun v : ℝ => ∫ w in Set.Ioc c d, f i v w / (v * w))
      (volume.restrict (Set.Ioc a b)))
    (hwf : ∀ i ∈ s, ∀ v ∈ Set.Ioc a b, Integrable (fun w : ℝ => f i v w / (v * w))
      (volume.restrict (Set.Ioc c d)))
    (hgw : ∀ v ∈ Set.Ioc a b, Integrable (fun w : ℝ => g v w / (v * w))
      (volume.restrict (Set.Ioc c d)))
    (hg : Integrable (fun v : ℝ => ∫ w in Set.Ioc c d, g v w / (v * w))
      (volume.restrict (Set.Ioc a b)))
    (hle : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Ioc c d,
      ∑ i ∈ s, f i v w / (v * w) ≤ g v w / (v * w)) :
    (∑ i ∈ s, ∫ v in Set.Ioc a b, ∫ w in Set.Ioc c d, f i v w / (v * w))
      ≤ ∫ v in Set.Ioc a b, ∫ w in Set.Ioc c d, g v w / (v * w) := by
  have hGl : ∀ v ∈ Set.Ioc a b,
      (∑ i ∈ s, ∫ w in Set.Ioc c d, f i v w / (v * w))
        ≤ ∫ w in Set.Ioc c d, g v w / (v * w) := by
    intro v hv
    rw [← integral_finsetSum s (fun i hi => hwf i hi v hv)]
    exact MeasureTheory.integral_mono_ae
      (integrable_finsetSum s (fun i hi => hwf i hi v hv))
      (hgw v hv)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun w hw => hle v hv w hw))
  have hF : Integrable (fun v : ℝ => ∑ i ∈ s, ∫ w in Set.Ioc c d, f i v w / (v * w))
      (volume.restrict (Set.Ioc a b)) :=
    integrable_finsetSum s (fun i hi => hf i hi)
  calc (∑ i ∈ s, ∫ v in Set.Ioc a b, ∫ w in Set.Ioc c d, f i v w / (v * w))
      = ∫ v in Set.Ioc a b, ∑ i ∈ s, ∫ w in Set.Ioc c d, f i v w / (v * w) :=
        (integral_finsetSum s (fun i hi => hf i hi)).symm
    _ ≤ ∫ v in Set.Ioc a b, ∫ w in Set.Ioc c d, g v w / (v * w) :=
        MeasureTheory.integral_mono_ae hF hg
          (ae_restrict_of_forall_mem measurableSet_Ioc hGl)

/-! ## 4. The target -/

theorem sum_rect_Fsub_le (x Cm : ℕ) (B : ℝ) (hCm1 : 1 ≤ Cm) (hzcp : 0 < zc x B)
    (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ))
    (hV : zc x B ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B))
    (hMx : ⌊(x : ℝ) / (Cm : ℝ)⌋₊ ≤ x) :
    (∑ ℓ ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
        ∫ v in zc x B..(((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w))
      ≤ ∫ v in zc x B..(((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Ksub x Cm B v w / (v * w) := by
  simp only [intervalIntegral.integral_of_le hV, intervalIntegral.integral_of_le hc1]
  -- identification of `Ksub` with the full `ℓ`-sum on the `w`-range
  have hid : ∀ v w : ℝ, w ≤ (x : ℝ) →
      Ksub x Cm B v w = ∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w :=
    fun v w hw => Ksub_eq_sum_Fsub_of_le x Cm B hw
  have hwx : ∀ w ∈ Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)), w ≤ (x : ℝ) :=
    fun w hw => le_trans hw.2 (div_Cm_le_self x Cm hCm1)
  -- (1) integrability in `v` of each single `ℓ`-term
  have hf : ∀ i ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
      Integrable (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B i v w / (v * w))
        (volume.restrict (Set.Ioc (zc x B)
          (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)))) :=
    fun i _ => sum_rect_Fsub_integrable_inner x Cm B i hCm1 hzcp hc1 hV
  -- (2) integrability in `w` of each single `ℓ`-term
  have hwf : ∀ i ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
      ∀ v ∈ Set.Ioc (zc x B) (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
      Integrable (fun w : ℝ => Fsub x Cm B i v w / (v * w))
        (volume.restrict (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)))) :=
    fun i _ v hv => sum_rect_Fsub_integrable_w x Cm B i hCm1 hc1 v (lt_trans hzcp hv.1)
  -- (3) integrability in `w` of `Ksub` (via the identification on the `w`-range)
  have hgw : ∀ v ∈ Set.Ioc (zc x B)
        (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
      Integrable (fun w : ℝ => Ksub x Cm B v w / (v * w))
        (volume.restrict (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)))) := by
    intro v hv
    have hbase : Integrable (fun w : ℝ =>
        ∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w / (v * w))
        (volume.restrict (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)))) :=
      integrable_finsetSum _ (fun ℓ _ =>
        sum_rect_Fsub_integrable_w x Cm B ℓ hCm1 hc1 v (lt_trans hzcp hv.1))
    refine hbase.congr (ae_restrict_of_forall_mem measurableSet_Ioc (fun w hw => ?_))
    change (∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w / (v * w)) = Ksub x Cm B v w / (v * w)
    rw [hid v w (hwx w hw), Finset.sum_div]
  -- (4) integrability in `v` of the `w`-inner integral of `Ksub`
  have hgtot : Integrable (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Ksub x Cm B v w / (v * w))
      (volume.restrict (Set.Ioc (zc x B)
        (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)))) := by
    have hbase : Integrable (fun v : ℝ =>
        ∑ ℓ ∈ Finset.Icc 1 x, ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
          Fsub x Cm B ℓ v w / (v * w))
        (volume.restrict (Set.Ioc (zc x B)
          (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)))) :=
      integrable_finsetSum _ (fun ℓ _ => sum_rect_Fsub_integrable_inner x Cm B ℓ hCm1 hzcp hc1 hV)
    refine hbase.congr (ae_restrict_of_forall_mem measurableSet_Ioc (fun v hv => ?_))
    symm
    change (∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)), Ksub x Cm B v w / (v * w))
      = ∑ ℓ ∈ Finset.Icc 1 x,
          ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w)
    have heq : (fun w : ℝ => Ksub x Cm B v w / (v * w))
        =ᵐ[volume.restrict (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)))]
        (fun w : ℝ => ∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w / (v * w)) :=
      ae_restrict_of_forall_mem measurableSet_Ioc (fun w hw => by
        change Ksub x Cm B v w / (v * w) = ∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w / (v * w)
        rw [hid v w (hwx w hw), Finset.sum_div])
    rw [MeasureTheory.integral_congr_ae heq]
    exact integral_finsetSum _ (fun ℓ _ =>
      sum_rect_Fsub_integrable_w x Cm B ℓ hCm1 hc1 v (lt_trans hzcp hv.1))
  -- (5) the pointwise comparison of the integrands
  have hle : ∀ v ∈ Set.Ioc (zc x B)
        (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
      ∀ w ∈ Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        ∑ i ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊, Fsub x Cm B i v w / (v * w)
          ≤ Ksub x Cm B v w / (v * w) := by
    intro v hv w hw
    have hv0 : 0 < v := lt_trans hzcp hv.1
    have hw0 : 0 < w := lt_trans one_pos hw.1
    have hsub : Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊ ⊆ Finset.Icc 1 x := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ ⊢
      exact ⟨hℓ.1, le_trans hℓ.2 hMx⟩
    rw [← Finset.sum_div, hid v w (hwx w hw)]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ℓ _ _ => Fsub_nonneg x Cm B ℓ v w))
      (mul_pos hv0 hw0).le
  exact sum_setIntegral_le (Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊)
    (fun ℓ v w => Fsub x Cm B ℓ v w) (fun v w => Ksub x Cm B v w) hf hwf hgw hgtot hle

end

end Work.FIChain
