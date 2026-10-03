/-
# The two §6 symbols `symC`, `symM` have `ℓ¹(ℤ²)` kernels

`Work.KMTPlan.A6.symC` and `Work.KMTPlan.A6.symM` (`LowSmallSymDefs`) are the symbols of the two
columns compared in the §6 model approximation of Krause--Mirek--Tao:

* `symC = symSeq (tmKer ρ l₁ φ_N) ⊗ symSeq (tmKer ρ l₂ φ̃_N) · halfSym N P` is the symbol of the
  concrete column (halved average composed with the two exact-height Ionescu--Wainger factors);
* `symM = ∫_{1/2}^{1} symSeq2 (arithKerM …) · symSeq (tmKer ρ l₁ φ_{N,t}) ⊗
  symSeq (tmKer ρ l₂ φ̃_{N,t}) dt` is the symbol of the model column (the twisted bilinear
  multiplier applied to the two modulated exact-height pieces).

This module proves that the coefficient kernels of both symbols are `ℓ¹(ℤ²)`:

  `p ↦ ‖coeff2 (symC …) p.1 p.2‖` and `p ↦ ‖coeff2 (symM …) p.1 p.2‖` are summable.

For `symC` this is the kernel identity `cesb_kernComp_eq_coeff2_symC` combined with the ℓ¹ Young
inequality `Work.A7.ModelApproxCore_aux.summable_kernComp` for the composition of a bilinear
kernel with two linear convolutions, the three factors being `khalf N P` (finitely supported),
`tmKer ρ l₁ (φ_N)` and `tmKer ρ l₂ (φ̃_N)` (both `ℓ¹` by `cesb_summable_tmKer_*`).

For `symM` the coefficient kernel is the `t`-integral of the composed kernels
`kernComp (arithKerM …) (tmKer ρ l₁ φ_{N,t}) (tmKer ρ l₂ φ̃_{N,t})`: the identity
`coeff2 (∫ t, σ t) = ∫ t, coeff2 (σ t)` (Fubini on the compact box `[1/2,1]×[0,1]²`, valid since
the integrand is jointly measurable and bounded) reduces it to
`SymSeq2_kernComp_coeff`, and the `t`-uniform ℓ¹ estimates
(`Work.KMTAreas.A7.uniform_tmKer_varphiNt`, `…_varphitildeNt`, `summable_arithKerM`) together
with Tonelli give the summability of the family of integrals.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.colSmall_eq_bilinOp_symC
import Submission.Work.KMTPlan.A6.lowModel_eq_bilinOp_symM

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

noncomputable section

/-! ## §1.  Elementary facts about the sequence symbols -/

/-- The symbol `symSeq κ` of a summable kernel is bounded by the `ℓ¹` mass of the kernel. -/
private lemma a6_norm_symSeq_le {κ : ℤ → ℂ} (hκ : Summable fun j : ℤ => ‖κ j‖) (x : ℝ) :
    ‖symSeq κ x‖ ≤ ∑' j : ℤ, ‖κ j‖ := by
  have hF : Summable (fun j : ℤ => κ j * eeC ((j : ℝ) * x)) :=
    Summable.of_norm_bounded hκ (fun j => by rw [norm_mul, norm_eeC, mul_one])
  rw [symSeq]
  calc ‖∑' j : ℤ, κ j * eeC ((j : ℝ) * x)‖
      ≤ ∑' j : ℤ, ‖κ j * eeC ((j : ℝ) * x)‖ := norm_tsum_le_tsum_norm hF.norm
    _ = ∑' j : ℤ, ‖κ j‖ := tsum_congr (fun j => by rw [norm_mul, norm_eeC, mul_one])

/-- The symbol `symSeq2 K` of a summable two-dimensional kernel is bounded by the `ℓ¹` mass. -/
private lemma a6_norm_symSeq2_le {K : ℤ → ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (x y : ℝ) :
    ‖symSeq2 K x y‖ ≤ ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ := by
  have hF : Summable (fun p : ℤ × ℤ => K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)) :=
    Summable.of_norm_bounded hK (fun p => by rw [norm_mul, norm_eeC, mul_one])
  have htsum : (∑' p : ℤ × ℤ, K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y))
      = ∑' p : ℤ, ∑' r : ℤ, K p r * eeC ((p : ℝ) * x + (r : ℝ) * y) :=
    Summable.tsum_prod hF
  rw [symSeq2, ← htsum]
  calc ‖∑' p : ℤ × ℤ, K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖
      ≤ ∑' p : ℤ × ℤ, ‖K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖ :=
        norm_tsum_le_tsum_norm hF.norm
    _ = ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ :=
        tsum_congr (fun p => by rw [norm_mul, norm_eeC, mul_one])

/-- The two-dimensional sequence symbol is jointly measurable (no summability needed). -/
private lemma a6_measurable_symSeq2 (K : ℤ → ℤ → ℂ) :
    Measurable (fun q : ℝ × ℝ => symSeq2 K q.1 q.2) := by
  rw [show (fun q : ℝ × ℝ => symSeq2 K q.1 q.2) = fun q : ℝ × ℝ =>
      ∑' p : ℤ, ∑' r : ℤ, K p r * eeC ((p : ℝ) * q.1 + (r : ℝ) * q.2) from by
    funext q; rw [symSeq2]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun p => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun r => ?_)
  have hc : Continuous (fun q : ℝ × ℝ => eeC ((p : ℝ) * q.1 + (r : ℝ) * q.2)) := by
    unfold eeC; fun_prop
  exact hc.measurable.const_mul _

/-- Joint measurability of `(x,t) ↦ symSeq (κ t) x` for a family measurable in `t`. -/
private lemma a6_measurable_symSeq_pair {κ : ℝ → ℤ → ℂ}
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) := by
  rw [show (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) = fun q : ℝ × ℝ =>
      ∑' j : ℤ, κ q.2 j * eeC ((j : ℝ) * q.1) from by funext q; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun q : ℝ × ℝ => κ q.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by
    have hc : Continuous (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by unfold eeC; fun_prop
    exact hc.measurable
  exact h1.mul h2

/-- Joint measurability of the three-factor symbol
`(t,x,y) ↦ symSeq2 Kar x y · symSeq (κ₁ t) x · symSeq (κ₂ t) y`. -/
private lemma a6_measurable_sym_product {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hKar : Measurable (fun q : ℝ × ℝ => symSeq2 Kar q.1 q.2))
    (h₁ : Measurable (fun q : ℝ × ℝ => symSeq (κ₁ q.2) q.1))
    (h₂ : Measurable (fun q : ℝ × ℝ => symSeq (κ₂ q.2) q.1)) :
    Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) := by
  have hA : Measurable (fun q : ℝ × ℝ × ℝ => symSeq2 Kar q.2.1 q.2.2) :=
    hKar.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  have hB : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₁ q.1) q.2.1) :=
    h₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hC : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₂ q.1) q.2.2) :=
    h₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  exact (hA.mul hB).mul hC

/-- The three-factor norm bound. -/
private lemma a6_norm_sym_product_le {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {S B₁ B₂ : ℝ}
    {t x y : ℝ} (hKar : ‖symSeq2 Kar x y‖ ≤ S) (h₁ : ‖symSeq (κ₁ t) x‖ ≤ B₁)
    (h₂ : ‖symSeq (κ₂ t) y‖ ≤ B₂) (hS : 0 ≤ S) (hB₁ : 0 ≤ B₁) :
    ‖symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖ ≤ S * B₁ * B₂ := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hKar h₁ (norm_nonneg _) hS) h₂ (norm_nonneg _)
    (mul_nonneg hS hB₁)

/-! ## §2.  `coeff2` of a `t`-integral is the `t`-integral of `coeff2` -/

/-- **Fubini for `coeff2`**: the `(a,b)`-Fourier coefficient of the `t`-integral of a jointly
measurable bounded family `σ` is the `t`-integral of the coefficients. -/
private lemma a6_coeff2_intervalIntegral_swap (σ : ℝ → ℝ → ℝ → ℂ) (a b : ℤ)
    (hσm : Measurable (fun p : ℝ × ℝ × ℝ => σ p.1 p.2.1 p.2.2))
    {C : ℝ} (hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ, ‖σ t x y‖ ≤ C) :
    coeff2 (fun x y => ∫ t in (1/2 : ℝ)..1, σ t x y) a b
      = ∫ t in (1/2 : ℝ)..1, coeff2 (σ t) a b := by
  have hE : ∀ z : ℝ, ‖eeC z‖ = 1 := fun z => by
    rw [eeC]; simp [Complex.norm_exp]
  unfold coeff2
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
  set mx : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hmx
  set mt : Measure ℝ := volume.restrict (Set.Ioc (1/2:ℝ) 1) with hmt
  have hrealx : mx.real Set.univ = 1 := by
    show (((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)) Set.univ).toReal = 1
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    simp
  have step1 : ∀ x y : ℝ, (∫ t, σ t x y ∂mt) * eeC (-(a : ℝ) * x - (b : ℝ) * y)
      = ∫ t, σ t x y * eeC (-(a : ℝ) * x - (b : ℝ) * y) ∂mt :=
    fun x y => (MeasureTheory.integral_mul_const _ _).symm
  simp_rw [step1]
  have hInt1 : ∀ x : ℝ, Integrable (fun z : ℝ × ℝ =>
      σ z.1 x z.2 * eeC (-(a : ℝ) * x - (b : ℝ) * z.2)) (mt.prod mx) := by
    intro x
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · have h1 : Measurable (fun z : ℝ × ℝ => σ z.1 x z.2) :=
        hσm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have h2 : Measurable (fun z : ℝ × ℝ =>
          eeC (-(a : ℝ) * x - (b : ℝ) * z.2)) := by
        have hc : Continuous (fun z : ℝ × ℝ =>
            eeC (-(a : ℝ) * x - (b : ℝ) * z.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact (h1.mul h2).aestronglyMeasurable
    · have hbox : mt.prod mx = (volume.prod volume).restrict
          (Set.Ioc (1/2 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) := by
        rw [hmt, hmx, Measure.prod_restrict]
      rw [hbox]
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      have ht : z.1 ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt hz.1.1, hz.1.2⟩
      rw [norm_mul, hE]
      simpa using hσb z.1 ht x z.2
  have step2 : ∀ x : ℝ, (∫ y, ∫ t, σ t x y * eeC (-(a : ℝ) * x - (b : ℝ) * y)
        ∂mt ∂mx)
      = ∫ t, ∫ y, σ t x y * eeC (-(a : ℝ) * x - (b : ℝ) * y) ∂mx ∂mt := by
    intro x
    exact (MeasureTheory.integral_integral_swap
      (f := fun t y => σ t x y * eeC (-(a : ℝ) * x - (b : ℝ) * y))
      (hInt1 x)).symm
  simp_rw [step2]
  refine MeasureTheory.integral_integral_swap
    (f := fun x t => ∫ y, σ t x y * eeC (-(a : ℝ) * x - (b : ℝ) * y) ∂mx) ?_
  refine MeasureTheory.Integrable.of_bound ?_ C ?_
  · have hf : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        σ w.1.2 w.1.1 w.2 * eeC (-(a : ℝ) * w.1.1 - (b : ℝ) * w.2)) := by
      have h1 : Measurable (fun w : (ℝ × ℝ) × ℝ => σ w.1.2 w.1.1 w.2) :=
        hσm.comp ((measurable_snd.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      have h2 : Measurable (fun w : (ℝ × ℝ) × ℝ =>
          eeC (-(a : ℝ) * w.1.1 - (b : ℝ) * w.2)) := by
        have hc : Continuous (fun w : (ℝ × ℝ) × ℝ =>
            eeC (-(a : ℝ) * w.1.1 - (b : ℝ) * w.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact h1.mul h2
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' hf.aestronglyMeasurable
  · have hbox : mx.prod mt = (volume.prod volume).restrict
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (1/2 : ℝ) 1) := by
      rw [hmx, hmt, Measure.prod_restrict]
    rw [hbox]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    have ht : z.2 ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt hz.2.1, hz.2.2⟩
    have hbound : ∀ᵐ y ∂mx, ‖σ z.2 z.1 y * eeC (-(a : ℝ) * z.1 - (b : ℝ) * y)‖ ≤ C := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      rw [norm_mul, hE]
      simpa using hσb z.2 ht z.1 y
    calc ‖∫ y, σ z.2 z.1 y * eeC (-(a : ℝ) * z.1 - (b : ℝ) * y) ∂mx‖
        ≤ C * mx.real Set.univ := MeasureTheory.norm_integral_le_of_norm_le_const hbound
      _ = C := by rw [hrealx, mul_one]

/-! ## §3.  The `ℓ¹` summability of the `t`-integral of composed kernels -/

/-- Measurability in `t` of the composed kernel `kernComp Kar (κ₁ t) (κ₂ t)`. -/
private lemma a6_measurable_kernComp_family {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) := by
  intro p
  show Measurable (fun t : ℝ => ∑' a' : ℤ, ∑' b' : ℤ,
    Kar (p.1 - a') (p.2 - b') * κ₁ t a' * κ₂ t b')
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun a' => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun b' => ?_)
  exact (measurable_const.mul (hm₁ a')).mul (hm₂ b')

/-- **The `ℓ¹` summability of the family of `t`-integrals of composed kernels**, from the
`t`-uniform `ℓ¹` bounds of the two linear factors. -/
private lemma a6_summable_intervalIntegral_kernComp {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    {B₁ B₂ : ℝ}
    (hKar : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hb₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₁ t j‖) ≤ B₁)
    (hb₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₂ t j‖) ≤ B₂)
    (hB₁0 : 0 ≤ B₁)
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    Summable (fun p : ℤ × ℤ =>
      ‖∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖) := by
  set mt : Measure ℝ := volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hmt
  have hae : ∀ᵐ t ∂mt, t ∈ Set.Icc (1/2 : ℝ) 1 := by
    rw [hmt]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hunivt : mt Set.univ = ENNReal.ofReal (1/2) := by
    rw [hmt, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    congr 1
    norm_num
  have hKtMeas : ∀ p : ℤ × ℤ,
      Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) :=
    a6_measurable_kernComp_family hm₁ hm₂
  have hKtsum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Summable (fun p : ℤ × ℤ => ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖) :=
    fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hKar (hκ₁ t ht) (hκ₂ t ht)
  have hKtbound : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖)
        ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ := by
    intro t ht
    refine le_trans (tsum_norm_kernComp_le hKar (hκ₁ t ht) (hκ₂ t ht)) ?_
    have h0 : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hb₁ t ht) h0) (hb₂ t ht)
      (tsum_nonneg (fun _ => norm_nonneg _)) (mul_nonneg h0 hB₁0)
  have hpoint : ∀ᵐ t ∂mt, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
      ≤ ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) := by
    filter_upwards [hae] with t ht
    have h1 : (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ :=
      tsum_congr (fun p => by simp [enorm_eq_nnnorm])
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hKtsum t ht)]
    exact ENNReal.ofReal_le_ofReal (hKtbound t ht)
  have hdom : (∑' p : ℤ × ℤ, ∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ ∂mt) ≠ ⊤ := by
    rw [← MeasureTheory.lintegral_tsum (fun p => ((hKtMeas p).enorm).aemeasurable)]
    exact ne_of_lt (by
      calc ∫⁻ t, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ) ∂mt
          ≤ ∫⁻ t, ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) ∂mt :=
            lintegral_mono_ae hpoint
        _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) * mt Set.univ :=
            lintegral_const _
        _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂)
              * ENNReal.ofReal (1/2) := by rw [hunivt]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hcoe : ∀ z : ℂ, (‖z‖ₑ).toReal = ‖z‖ := fun z => by
    rw [show ‖z‖ₑ = ENNReal.ofReal ‖z‖ from by simp [enorm_eq_nnnorm]]; simp
  have hsum_int : Summable (fun p : ℤ × ℤ =>
      ‖∫ t, kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2 ∂mt‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => by
        have h1 : ‖∫ t, kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2 ∂mt‖ₑ
            ≤ ∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ ∂mt :=
          MeasureTheory.enorm_integral_le_lintegral_enorm _
        calc ‖∫ t, kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2 ∂mt‖
            = (‖∫ t, kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2 ∂mt‖ₑ).toReal := (hcoe _).symm
          _ ≤ (∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ ∂mt).toReal :=
              ENNReal.toReal_mono (ne_top_of_le_ne_top hdom (ENNReal.le_tsum
                (f := fun p : ℤ × ℤ => ∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ ∂mt) p)) h1)
      (ENNReal.summable_toReal hdom)
  refine hsum_int.congr (fun p => ?_)
  rw [hmt]
  simp only [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]

/-! ## §4.  The two symbols of §6 -/

theorem symC_symM_summable (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (N l₁ l₂ k₁ k₂ : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖Work.KMTPlan.A6.coeff2
        (Work.KMTPlan.A6.symC ρ P N l₁ l₂ k₁ k₂) p.1 p.2‖) ∧
      Summable (fun p : ℤ × ℤ => ‖Work.KMTPlan.A6.coeff2
        (Work.KMTPlan.A6.symM ρ P N l₁ l₂ k₁ k₂) p.1 p.2‖) := by
  constructor
  · -- the concrete column: the kernel is the composition of `khalf` with the two factors
    have hS : Summable (fun p : ℤ × ℤ => ‖kernComp (khalf N P)
        (tmKer ρ l₁ (varphiN N k₁)) (tmKer ρ l₂ (varphitildeN P.natDegree N k₂)) p.1 p.2‖) :=
      Work.A7.ModelApproxCore_aux.summable_kernComp (cesb_summable_khalf N P)
        (cesb_summable_tmKer_varphiN ρ hρ hρ1 l₁ N k₁)
        (cesb_summable_tmKer_varphitildeN ρ hρ hρ1 l₂ P.natDegree N k₂)
    rwa [cesb_kernComp_eq_coeff2_symC ρ hρ hρ1 P l₁ l₂ k₁ k₂ N] at hS
  · -- the model column
    obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ l₁ N k₁
    obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P l₂ N k₂
    have hKar : Summable (fun p : ℤ × ℤ => ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) :=
      summable_arithKerM ρ P l₁ l₂ k₁ k₂
    have hκ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
        Summable (fun j : ℤ => ‖tmKer ρ l₁ (varphiNt N k₁ t) j‖) :=
      fun t ht => (hB₁ t ht).1
    have hκ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
        Summable (fun j : ℤ => ‖tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j‖) :=
      fun t ht => (hB₂ t ht).1
    have hb₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
        (∑' j : ℤ, ‖tmKer ρ l₁ (varphiNt N k₁ t) j‖) ≤ B₁ := fun t ht => (hB₁ t ht).2
    have hb₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
        (∑' j : ℤ, ‖tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j‖) ≤ B₂ :=
      fun t ht => (hB₂ t ht).2
    have hm₁ : ∀ j : ℤ, Measurable (fun t : ℝ => tmKer ρ l₁ (varphiNt N k₁ t) j) :=
      measurable_tmKer_varphiNt ρ l₁ N k₁
    have hm₂ : ∀ j : ℤ, Measurable (fun t : ℝ =>
        tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j) :=
      measurable_tmKer_varphitildeNt ρ P l₂ N k₂
    -- The `ℓ¹` summability of the family of `t`-integrals of the composed kernels.
    have hsumK : Summable (fun p : ℤ × ℤ => ‖∫ t in (1/2 : ℝ)..1,
        kernComp (arithKerM ρ P l₁ l₂ k₁ k₂)
          (tmKer ρ l₁ (varphiNt N k₁ t))
          (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖) :=
      a6_summable_intervalIntegral_kernComp
        (Kar := arithKerM ρ P l₁ l₂ k₁ k₂)
        (κ₁ := fun t => tmKer ρ l₁ (varphiNt N k₁ t))
        (κ₂ := fun t => tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        (B₁ := B₁) (B₂ := B₂) hKar hκ₁ hκ₂ hb₁ hb₂ hB₁0 hm₁ hm₂
    -- The uniform bound on the integrand of `symM`.
    have hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
        ‖symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
          * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
          * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y‖
          ≤ (∑' p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂ := by
      intro t ht x y
      have h1 : ‖symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y‖
          ≤ ∑' p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ :=
        a6_norm_symSeq2_le hKar x y
      have h2 : ‖symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x‖ ≤ B₁ :=
        le_trans (a6_norm_symSeq_le (hκ₁ t ht) x) (hb₁ t ht)
      have h3 : ‖symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y‖ ≤ B₂ :=
        le_trans (a6_norm_symSeq_le (hκ₂ t ht) y) (hb₂ t ht)
      have h4 : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ :=
        tsum_nonneg (fun _ => norm_nonneg _)
      exact a6_norm_sym_product_le
        (Kar := arithKerM ρ P l₁ l₂ k₁ k₂)
        (κ₁ := fun t => tmKer ρ l₁ (varphiNt N k₁ t))
        (κ₂ := fun t => tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        (S := ∑' p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖)
        (B₁ := B₁) (B₂ := B₂) h1 h2 h3 h4 hB₁0
    have hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
        symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) q.2.1 q.2.2
          * symSeq (tmKer ρ l₁ (varphiNt N k₁ q.1)) q.2.1
          * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ q.1)) q.2.2) :=
      a6_measurable_sym_product
        (Kar := arithKerM ρ P l₁ l₂ k₁ k₂)
        (κ₁ := fun t => tmKer ρ l₁ (varphiNt N k₁ t))
        (κ₂ := fun t => tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        (a6_measurable_symSeq2 _)
        (a6_measurable_symSeq_pair hm₁) (a6_measurable_symSeq_pair hm₂)
    have hsM : symM ρ P N l₁ l₂ k₁ k₂ = fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
        symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
          * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
          * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y := rfl
    -- The Fubini step: the coefficient of the `t`-integral is the `t`-integral of coefficients.
    have hstep1 : ∀ a b : ℤ, coeff2 (fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
          symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
            * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
            * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y) a b
        = ∫ t in (1/2 : ℝ)..1, coeff2 (fun x y : ℝ =>
            symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
              * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
              * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y) a b := by
      intro a b
      exact a6_coeff2_intervalIntegral_swap (σ := fun t x y =>
        symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
          * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
          * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y) a b hσm hσb
    -- The identity `coeff2 (symSeq2 K · symSeq κ · symSeq κ') = kernComp K κ κ'`.
    have hstep2 : ∀ a b : ℤ, (∫ t in (1/2 : ℝ)..1, coeff2 (fun x y : ℝ =>
            symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
              * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
              * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y) a b)
        = ∫ t in (1/2 : ℝ)..1, kernComp (arithKerM ρ P l₁ l₂ k₁ k₂)
            (tmKer ρ l₁ (varphiNt N k₁ t))
            (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b := by
      intro a b
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
      exact SymSeq2_kernComp_coeff (arithKerM ρ P l₁ l₂ k₁ k₂)
        (tmKer ρ l₁ (varphiNt N k₁ t))
        (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        hKar (hκ₁ t ht).of_norm (hκ₂ t ht).of_norm a b
    have hcoeff : coeff2 (symM ρ P N l₁ l₂ k₁ k₂) = fun a b : ℤ =>
        ∫ t in (1/2 : ℝ)..1, kernComp (arithKerM ρ P l₁ l₂ k₁ k₂)
          (tmKer ρ l₁ (varphiNt N k₁ t))
          (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b := by
      funext a b
      rw [hsM]
      exact (hstep1 a b).trans (hstep2 a b)
    rw [hcoeff]
    exact hsumK
    -- (the `hB₂0` estimate is not needed; `hb₂` already gives `0 ≤ B₂`)

end

end Work.KMTPlan.A6
