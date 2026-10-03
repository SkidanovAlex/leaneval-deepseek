
import Mathlib
import Submission.Work.Analysis.Interpolation.BilinearThreeLines
import Submission.Work.Analysis.Interpolation.bddAbove_bilinear_family
import Submission.Work.Analysis.Interpolation.analyticFamily_eq_sum
import Submission.Port.Aesm

/-!
# Riesz--Thorin interpolation for a linear operator

This module proves `Work.Analysis.Interpolation.riesz_thorin_linear`: the Riesz--Thorin
interpolation theorem for a `C`-linear operator `T` bounded from `L^{p0}` to `L^{q0}` with
constant `M0` and from `L^{p1}` to `L^{q1}` with constant `M1`; then `T` maps `L^p` to `L^q` with
constant `M0^{1-theta} M1^theta`.

The proof is the classical one: Hadamard's three-lines theorem
(`Complex.HadamardThreeLines`, through the wrapper `norm_le_interp_of_strip_edges`) applied to
the analytic family `z |-> ∫ y, (T (f_z)) y * (g_z) y ∂ν`, where `f_z` and `g_z` are the
level-set analytic families of `Submission.Work.Analysis.Interpolation.Basic` attached to simple
functions `f` and `g` (with exponents `p/pᵢ` for `f` and the conjugate exponents `q'/qᵢ'` for a
test function `g`, where `q' = q/(q-1)` and `qᵢ' = qᵢ/(qᵢ-1)`), followed by duality for
`eLpNorm`.

The two analytic inputs of the three-lines theorem (entireness and boundedness on the strip) come
from the level-set decomposition of the pairing integral
(`integral_pairing_analyticFamily_eq_sum`), which reduces the family to a finite sum of
exponentials of affine functions of `z`; this is the analogue, for a *linear* operator, of
`stein_bilinear_of_decomposition`.  The endpoint estimates of that decomposition come from
Hölder's inequality (`enorm_integral_mul_le`) together with the two hypotheses `h₀`, `h₁`; the
identities `eLpNorm_analyticFamily_re_zero`/`_re_one` evaluate the two families on the boundary
lines.  The final duality step is `eLpNorm_le_of_forall_simpleFunc_integral_le`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Work.Analysis.Interpolation

/-! ## Hölder's inequality for the pairing `∫ a y * b y ∂ν` -/

/-- **Hölder's inequality** for the pointwise product of two a.e.-measurable complex functions,
at the exponent `1`, in the `eLpNorm` formulation. -/
lemma eLpNorm_mul_le {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ} (hq : 1 < q)
    {a b : β → ℂ} (ha : AEMeasurable a ν) (hb : AEMeasurable b ν) :
    eLpNorm (fun y => a y * b y) 1 ν ≤
      eLpNorm a (ENNReal.ofReal q) ν * eLpNorm b (ENNReal.ofReal (q / (q - 1))) ν := by
  have hInst : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal (q / (q - 1))) 1 :=
    Real.HolderConjugate.ennrealOfReal ((Real.holderConjugate_iff_eq_conjExponent hq).mpr rfl)
  simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := ENNReal.ofReal q)
    (q := ENNReal.ofReal (q / (q - 1))) (r := 1) (fun x y => x * y) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) ha.aestronglyMeasurable hb.aestronglyMeasurable (by filter_upwards with y; simp)
    (hpqr := hInst)

/-- **Hölder's inequality** for the pairing integral. -/
lemma enorm_integral_mul_le {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ} (hq : 1 < q)
    {a b : β → ℂ} (ha : AEMeasurable a ν) (hb : AEMeasurable b ν) :
    ‖∫ y, a y * b y ∂ν‖ₑ ≤
      eLpNorm a (ENNReal.ofReal q) ν * eLpNorm b (ENNReal.ofReal (q / (q - 1))) ν := by
  calc ‖∫ y, a y * b y ∂ν‖ₑ ≤ ∫⁻ y, ‖a y * b y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y => a y * b y) 1 ν := (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm
    _ ≤ eLpNorm a (ENNReal.ofReal q) ν * eLpNorm b (ENNReal.ofReal (q / (q - 1))) ν :=
        eLpNorm_mul_le hq ha hb

/-- Integrability of a pointwise product of two functions in `L^q`, `L^{q'}` with conjugate
exponents. -/
lemma integrable_mul_of_eLpNorm_lt_top {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ}
    (hq : 1 < q) {a b : β → ℂ} (ha : AEMeasurable a ν) (hb : AEMeasurable b ν)
    (ha' : eLpNorm a (ENNReal.ofReal q) ν < ⊤)
    (hb' : eLpNorm b (ENNReal.ofReal (q / (q - 1))) ν < ⊤) :
    Integrable (fun y => a y * b y) ν := by
  rw [← memLp_one_iff_integrable]
  refine (MeasureTheory.memLp_iff.mpr (?_))
  rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top ha' hb')
  rw [← eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  exact eLpNorm_mul_le hq ha hb

/-- The `L^r` seminorm of the indicator function of a set: `‖1_S‖_r = (ν S)^{1/r}`. -/
lemma eLpNorm_indicator_one {β : Type*} [MeasurableSpace β] {ν : Measure β} {S : Set β}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r) :
    eLpNorm (Set.indicator S (fun _ => (1 : ℂ))) (ENNReal.ofReal r) ν = (ν S) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hr)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le]
  have hpt : ∀ y : β, ‖Set.indicator S (fun _ => (1 : ℂ)) y‖ₑ ^ r
      = S.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp [ENNReal.zero_rpow_of_pos hr]
  rw [lintegral_congr hpt]
  congr 1
  rw [lintegral_indicator hS, setLIntegral_const, one_mul]

/-- The indicator function of a set of finite measure is in `L^r` for every `r > 0`. -/
lemma memLp_indicator_one {β : Type*} [MeasurableSpace β] {ν : Measure β} {S : Set β}
    (hS : MeasurableSet S) (hSfin : ν S < ⊤) {r : ℝ} (hr : 0 < r) :
    MemLp (Set.indicator S (fun _ => (1 : ℂ))) (ENNReal.ofReal r) ν := by
  rw [MeasureTheory.memLp_iff, eLpNorm_indicator_one hS hr]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt hSfin)

/-- Nonzero level sets of a simple function, tested against its range, are of finite measure. -/
lemma simpleFunc_fiber_lt_top_of_range {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : SimpleFunc α ℂ) (hf : ∀ c ∈ f.range, c ≠ 0 → μ (f ⁻¹' {c}) < ⊤) :
    ∀ c : ℂ, c ≠ 0 → μ (f ⁻¹' {c}) < ⊤ := by
  intro c hc
  by_cases h : c ∈ f.range
  · exact hf c h hc
  · have hempty : f ⁻¹' {c} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxc : (f : α → ℂ) x = c := by simpa using hx
      exact h (hxc ▸ SimpleFunc.mem_range_self f x)
    rw [hempty]
    simp

/-! ## The level-set decomposition of the pairing integral -/

/-- **Level-set decomposition of the pairing integral.**  For a `C`-linear `T` and simple
functions `f`, `g`, the integral of `T (f_z)` against `g_z` expands as the finite double sum over
the level sets of `f` and `g`, with `z`-dependent coefficients in front of the `z`-independent
"matrix coefficients" `∫ y, T 1_{f⁻¹{c}} y * 1_{g⁻¹{d}} y ∂ν`. -/
lemma integral_pairing_analyticFamily_eq_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β}
    (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) {q₀ : ℝ} (hq₀ : 1 < q₀)
    (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (a₀ a₁ b₀ b₁ : ℝ)
    (hg : ∀ d ∈ g.range, d ≠ 0 → ν (g ⁻¹' {d}) < ⊤)
    (hT : ∀ c ∈ f.range, c ≠ 0 →
      MemLp (T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) (ENNReal.ofReal q₀) ν)
    (z : ℂ) :
    (∫ y, (T (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)) y *
        (analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z) y ∂ν)
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
            (∫ y, (T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) y *
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) y ∂ν) := by
  classical
  have hTf : T (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)
      = ∑ c ∈ f.range, phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) •
          T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) := by
    rw [analyticFamily_eq_sum]
    simp only [map_sum, map_smul]
  have hpoint : ∀ y, (T (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)) y *
        (analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z) y
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
            ((T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) y *
              (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) y) := by
    intro y
    rw [hTf, analyticFamily_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    ring
  have hint : ∀ c ∈ f.range, ∀ d ∈ g.range,
      Integrable (fun y =>
        (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
          ((T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) y *
            (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) y)) ν := by
    intro c hc d hd
    by_cases hc0 : c = 0
    · rw [hc0]
      have hz : (fun y => (phasePow 0 (expFamily (a₀ : ℂ) (a₁ : ℂ) z) *
            phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
          ((T (Set.indicator (f ⁻¹' {0}) (fun _ => (1 : ℂ)))) y *
            (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) y)) = fun _ : β => 0 := by
        funext y
        simp [phasePow_zero_left]
      rw [hz]
      exact integrable_zero β ℂ ν
    by_cases hd0 : d = 0
    · rw [hd0]
      have hz : (fun y => (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) *
            phasePow 0 (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
          ((T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) y *
            (Set.indicator (g ⁻¹' {0}) (fun _ => (1 : ℂ))) y)) = fun _ : β => 0 := by
        funext y
        simp [phasePow_zero_left]
      rw [hz]
      exact integrable_zero β ℂ ν
    have hdlev : MeasurableSet (g ⁻¹' {d}) :=
      measurableSet_preimage (SimpleFunc.measurable g) (measurableSet_singleton d)
    have h1 : MemLp (T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) (ENNReal.ofReal q₀) ν :=
      hT c hc hc0
    have h2 : MemLp (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
        (ENNReal.ofReal (q₀ / (q₀ - 1))) ν :=
      memLp_indicator_one hdlev (hg d hd hd0) (div_pos (by linarith) (by linarith))
    haveI : ENNReal.HolderTriple (ENNReal.ofReal q₀) (ENNReal.ofReal (q₀ / (q₀ - 1))) 1 :=
      Real.HolderConjugate.ennrealOfReal ((Real.holderConjugate_iff_eq_conjExponent hq₀).mpr rfl)
    exact (h1.integrable_mul h2).const_mul _
  rw [show (∫ y, (T (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)) y *
        (analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z) y ∂ν)
      = ∫ y, (∑ c ∈ f.range, ∑ d ∈ g.range,
          (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
            ((T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) y *
              (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) y)) ∂ν from
    integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (fun d hd => hint c hc d hd))]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [integral_finsetSum _ (fun d hd => hint c hc d hd)]
  exact Finset.sum_congr rfl fun d hd => integral_const_mul _ _

/-! ## The extremal dual of a simple function and duality for `eLpNorm` -/

/-- The extremal dual of a simple function `s` for the exponent `q`: its value at `c` is
`conj c * ‖c‖ ^ (q - 2)`, so that `s * dual s = ‖s‖ ^ q` pointwise and
`‖dual s‖_{q'} = ‖s‖_q^{q-1}` for the conjugate exponent `q' = q/(q-1)`. -/
noncomputable def simpleFuncDual {β : Type*} [MeasurableSpace β] (q : ℝ) (s : SimpleFunc β ℂ) :
    SimpleFunc β ℂ :=
  s.map (fun c : ℂ => starRingEnd ℂ c * (((‖c‖ : ℝ) ^ (q - 2) : ℝ) : ℂ))

@[simp] lemma simpleFuncDual_apply {β : Type*} [MeasurableSpace β] (q : ℝ) (s : SimpleFunc β ℂ)
    (y : β) :
    simpleFuncDual q s y = starRingEnd ℂ (s y) * (((‖s y‖ : ℝ) ^ (q - 2) : ℝ) : ℂ) :=
  SimpleFunc.map_apply _ _ _

/-- The modulus of the extremal dual: `‖dual s‖ = ‖s‖ ^ (q-1)` pointwise. -/
lemma norm_simpleFuncDual {β : Type*} [MeasurableSpace β] {q : ℝ} (hq : 1 < q)
    (s : SimpleFunc β ℂ) (y : β) :
    ‖simpleFuncDual q s y‖ = ‖s y‖ ^ (q - 1) := by
  rw [simpleFuncDual_apply, norm_mul]
  have hstar : ‖starRingEnd ℂ (s y)‖ = ‖s y‖ := by
    rw [starRingEnd_apply, norm_star]
  have h2 : ‖((((‖s y‖ : ℝ) ^ (q - 2) : ℝ)) : ℂ)‖ = ‖s y‖ ^ (q - 2) := by
    have h := RCLike.norm_ofReal (K := ℂ) ((‖s y‖ : ℝ) ^ (q - 2))
    simpa [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) (q - 2))] using h
  rw [hstar, h2]
  rcases eq_or_lt_of_le (norm_nonneg (s y)) with h0 | hpos
  · have hz : ‖s y‖ = 0 := h0.symm
    rw [hz, zero_mul, Real.zero_rpow (ne_of_gt (sub_pos.mpr hq))]
  · have h := (Real.rpow_add hpos 1 (q - 2)).symm
    rw [Real.rpow_one] at h
    rw [show (1:ℝ) + (q - 2) = q - 1 by ring] at h
    exact h

/-- The pointwise product of a simple function and its extremal dual is `‖s‖ ^ q`. -/
lemma simpleFunc_mul_dual {β : Type*} [MeasurableSpace β] {q : ℝ} (hq : 1 < q)
    (s : SimpleFunc β ℂ) (y : β) :
    s y * simpleFuncDual q s y = ((‖s y‖ ^ q : ℝ) : ℂ) := by
  rw [simpleFuncDual_apply, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_mul]
  congr 1
  rcases eq_or_lt_of_le (norm_nonneg (s y)) with h0 | hpos
  · have hz : ‖s y‖ = 0 := h0.symm
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hq))]
  · rw [← Real.rpow_natCast (‖s y‖) 2]
    have h := (Real.rpow_add hpos 2 (q - 2)).symm
    rw [show (2:ℝ) + (q - 2) = q by ring] at h
    exact h

/-- The `L^{q'}` seminorm of the extremal dual is `‖s‖_q ^ (q-1)`. -/
lemma eLpNorm_simpleFuncDual {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ}
    (hq : 1 < q) (s : SimpleFunc β ℂ) :
    eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν =
      eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ (q - 1) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq'0 : 0 < q / (q - 1) := div_pos hq0 (by linarith)
  have hpt : ∀ y, ‖(simpleFuncDual q s : β → ℂ) y‖ₑ ^ (q / (q - 1)) = ‖(s : β → ℂ) y‖ₑ ^ q := by
    intro y
    have h1 : ‖(simpleFuncDual q s : β → ℂ) y‖ₑ = ‖(s : β → ℂ) y‖ₑ ^ (q - 1) := by
      rw [← ofReal_norm, norm_simpleFuncDual hq s y,
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ q - 1), ← ofReal_norm]
    rw [h1, ← ENNReal.rpow_mul]
    congr 1
    rw [mul_comm]
    exact div_mul_cancel₀ q (by linarith : q - 1 ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hq'0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq'0.le,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
  rw [lintegral_congr hpt]
  rw [show ((∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν) ^ (1 / q)) ^ (q - 1)
      = (∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν) ^ ((1 / q) * (q - 1)) from
        (ENNReal.rpow_mul _ _ _).symm]
  congr 1
  field_simp

/-- The pairing of a simple function with its extremal dual is `‖s‖_q ^ q`. -/
lemma enorm_integral_simpleFuncDual {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ}
    (hq : 1 < q) (s : SimpleFunc β ℂ) (hs : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν < ⊤) :
    ‖∫ y, s y * simpleFuncDual q s y ∂ν‖ₑ =
      eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hI : ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν
      = eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le, one_div,
      ENNReal.rpow_inv_rpow hq0.ne']
  have hItop : ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν < ⊤ := by
    rw [hI]; exact ENNReal.rpow_lt_top_of_nonneg hq0.le (ne_of_lt hs)
  have hEq : ∫⁻ y, ENNReal.ofReal ((‖(s : β → ℂ) y‖ : ℝ) ^ q) ∂ν
      = ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ← ofReal_norm]
  have hmeas : Measurable fun y : β => (‖(s : β → ℂ) y‖ : ℝ) ^ q := by measurability
  have hnonneg : 0 ≤ᵐ[ν] (fun y : β => (‖(s : β → ℂ) y‖ : ℝ) ^ q) :=
    Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg ((s : β → ℂ) y)) q
  have hnorm' : ‖(((∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν) : ℝ) : ℂ)‖
      = ∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν :=
    (RCLike.norm_ofReal (K := ℂ) (∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν)).trans
      (abs_of_nonneg (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg ((s : β → ℂ) y)) q))
  have hnorm : ‖(((∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν) : ℝ) : ℂ)‖ₑ
      = ENNReal.ofReal (∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν) := by
    rw [← ofReal_norm, hnorm']
  have hint : ∫ y, s y * simpleFuncDual q s y ∂ν
      = (((∫ y, (‖(s : β → ℂ) y‖ : ℝ) ^ q ∂ν) : ℝ) : ℂ) := by
    simp only [simpleFunc_mul_dual hq s]
    exact integral_ofReal
  rw [hint, hnorm, integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable,
    hEq, ENNReal.ofReal_toReal (ne_of_lt hItop), hI]

/-- Exponent arithmetic for a finite extended nonnegative real: `x ^ q = x ^ (q - 1) * x`
for `q > 1`. -/
lemma rpow_eq_rpow_sub_mul {x : ℝ≥0∞} (hx : x ≠ ⊤) {q : ℝ} (hq : 1 < q) :
    x ^ q = x ^ (q - 1) * x := by
  conv_lhs => rw [show q = (q - 1) + 1 by ring]
  rw [ENNReal.rpow_add_of_add_pos hx (q - 1) 1 (by linarith), ENNReal.rpow_one]

/-- **Duality for `eLpNorm`.**  If the pairings of an a.e.-measurable function `h` with finite
`L^q` seminorm against every simple function `g` of finite `L^{q'}` seminorm are bounded by
`C * ‖g‖_{q'}`, then `‖h‖_q ≤ C`. -/
theorem eLpNorm_le_of_forall_simpleFunc_integral_le {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {q : ℝ} (hq : 1 < q) {h : β → ℂ} (hh : AEMeasurable h ν)
    (hfin : eLpNorm h (ENNReal.ofReal q) ν < ⊤) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc β ℂ, eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν < ⊤ →
      ‖∫ y, h y * (g : β → ℂ) y ∂ν‖ₑ ≤
        C * eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν) :
    eLpNorm h (ENNReal.ofReal q) ν ≤ C := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  have hmem : MemLp h (ENNReal.ofReal q) ν := (MeasureTheory.memLp_iff.mpr (hfin))
  obtain ⟨s, hs, hsmem⟩ := hmem.exists_simpleFunc_eLpNorm_sub_lt ENNReal.ofReal_ne_top
    (ε := ((ε / 2 : ℝ≥0) : ℝ≥0∞)) (by
      simp only [ne_eq, ENNReal.coe_eq_zero]
      exact ne_of_gt (half_pos hε))
  have hs_top : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν < ⊤ := hsmem.eLpNorm_lt_top
  have hsub : eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν < ⊤ :=
    hs.trans ENNReal.coe_lt_top
  have hsaem : AEMeasurable (s : β → ℂ) ν := SimpleFunc.aemeasurable s
  have hhsub : AEMeasurable (h - (s : β → ℂ)) ν := hh.sub hsaem
  have hS : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ≤ C + ↑(ε / 2) := by
    by_cases hS0 : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν = 0
    · rw [hS0]; exact zero_le
    · have hSpos : 0 < eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν := pos_iff_ne_zero.mpr hS0
      have hdual_norm : eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν
          = eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ (q - 1) := eLpNorm_simpleFuncDual hq s
      have hdual_fin : eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν < ⊤ := by
        rw [hdual_norm]
        exact ENNReal.rpow_lt_top_of_nonneg (by linarith) (ne_of_lt hs_top)
      have hdaem : AEMeasurable (simpleFuncDual q s : β → ℂ) ν := SimpleFunc.aemeasurable _
      have hmain := hC (simpleFuncDual q s) hdual_fin
      have hint1 : Integrable (fun y => h y * (simpleFuncDual q s : β → ℂ) y) ν :=
        integrable_mul_of_eLpNorm_lt_top hq hh hdaem hfin hdual_fin
      have hint2 : Integrable (fun y => (h y - (s : β → ℂ) y) * (simpleFuncDual q s : β → ℂ) y) ν :=
        integrable_mul_of_eLpNorm_lt_top hq hhsub hdaem hsub hdual_fin
      have hsub_int : ∫ y, (s : β → ℂ) y * (simpleFuncDual q s : β → ℂ) y ∂ν
          = ∫ y, h y * (simpleFuncDual q s : β → ℂ) y ∂ν
            - ∫ y, (h y - (s : β → ℂ) y) * (simpleFuncDual q s : β → ℂ) y ∂ν := by
        rw [← integral_sub hint1 hint2]
        congr 1
        ext y
        ring
      have hholder : ‖∫ y, (h y - (s : β → ℂ) y) * (simpleFuncDual q s : β → ℂ) y ∂ν‖ₑ
          ≤ eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν
            * eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν :=
        enorm_integral_mul_le hq hhsub hdaem
      have hchain : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ q
          ≤ (C + eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν)
            * eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ (q - 1) := by
        calc eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ q
            = ‖∫ y, (s : β → ℂ) y * (simpleFuncDual q s : β → ℂ) y ∂ν‖ₑ :=
              (enorm_integral_simpleFuncDual hq s hs_top).symm
          _ = ‖∫ y, h y * (simpleFuncDual q s : β → ℂ) y ∂ν
                - ∫ y, (h y - (s : β → ℂ) y) * (simpleFuncDual q s : β → ℂ) y ∂ν‖ₑ := by
              rw [hsub_int]
          _ ≤ ‖∫ y, h y * (simpleFuncDual q s : β → ℂ) y ∂ν‖ₑ
                + ‖∫ y, (h y - (s : β → ℂ) y) * (simpleFuncDual q s : β → ℂ) y ∂ν‖ₑ :=
              enorm_sub_le
          _ ≤ C * eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν
                + eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν
                  * eLpNorm (simpleFuncDual q s : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν :=
              add_le_add hmain hholder
          _ = (C + eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν)
                * eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ (q - 1) := by
              rw [hdual_norm, add_mul]
      rw [rpow_eq_rpow_sub_mul (ne_of_lt hs_top) hq] at hchain
      rw [mul_comm (C + eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν)
        (eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν ^ (q - 1))] at hchain
      rw [ENNReal.mul_le_mul_iff_right
        (ne_of_gt (ENNReal.rpow_pos hSpos (ne_of_lt hs_top)))
        (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith) (ne_of_lt hs_top)))] at hchain
      exact hchain.trans (add_le_add le_rfl (le_of_lt hs))
  have hU : eLpNorm h (ENNReal.ofReal q) ν
      ≤ eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν
        + eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν := by
    have h := eLpNorm_add_le (μ := ν) (f := h - (s : β → ℂ)) (g := (s : β → ℂ)) hq1
    rwa [sub_add_cancel] at h
  calc eLpNorm h (ENNReal.ofReal q) ν
      ≤ eLpNorm (h - (s : β → ℂ)) (ENNReal.ofReal q) ν + eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν := hU
    _ ≤ ↑(ε / 2) + (C + ↑(ε / 2)) := add_le_add (le_of_lt hs) hS
    _ = C + ↑ε := by
        have h2 : (↑(ε / 2 : ℝ≥0) : ℝ≥0∞) + ↑(ε / 2) = ↑ε := by
          rw [← ENNReal.coe_add, add_halves]
        calc (↑(ε / 2 : ℝ≥0) : ℝ≥0∞) + (C + ↑(ε / 2))
            = ((↑(ε / 2 : ℝ≥0) : ℝ≥0∞) + ↑(ε / 2)) + C := by ring
          _ = ↑ε + C := by rw [h2]
          _ = C + ↑ε := by rw [add_comm]

/-! ## The three-lines core -/

/-- Arithmetic of conjugate exponents: the complement relation is preserved. -/
lemma one_div_conjExponent_interp {q₀ q₁ q θ : ℝ} (hq₀ : 1 < q₀) (hq₁ : 1 < q₁) (hq : 1 < q)
    (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁) :
    1 / (q / (q - 1)) = (1 - θ) / (q₀ / (q₀ - 1)) + θ / (q₁ / (q₁ - 1)) := by
  have key : ∀ c a : ℝ, a ≠ 0 → a - 1 ≠ 0 → c / (a / (a - 1)) = c * (1 - 1 / a) := by
    intro c a ha ha1
    field_simp
  rw [key 1 q (ne_of_gt (lt_trans zero_lt_one hq)) (by linarith),
    key (1 - θ) q₀ (ne_of_gt (lt_trans zero_lt_one hq₀)) (by linarith),
    key θ q₁ (ne_of_gt (lt_trans zero_lt_one hq₁)) (by linarith), one_mul]
  have hexp : (1 - θ) * (1 - 1 / q₀) + θ * (1 - 1 / q₁)
      = ((1 - θ) + θ) - ((1 - θ) / q₀ + θ / q₁) := by ring
  rw [hexp, show (1 - θ) + θ = 1 by ring, ← hqθ]

/-- **The three-lines bound for the pairing of `T f` against a simple `g`.** -/
theorem integral_pairing_le_interp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (hT : ∀ u, AEMeasurable (T u) ν)
    {p₀ p₁ q₀ q₁ p q θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 1 < q₀) (hq₁ : 1 < q₁)
    (hp : 0 < p) (hq : 1 < q) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ u, eLpNorm (T u) (ENNReal.ofReal q₀) ν ≤
      (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) μ)
    (h₁ : ∀ u, eLpNorm (T u) (ENNReal.ofReal q₁) ν ≤
      (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) μ)
    (f : SimpleFunc α ℂ) (hf : ∀ c ∈ f.range, c ≠ 0 → μ (f ⁻¹' {c}) < ⊤)
    (g : SimpleFunc β ℂ) (hg : ∀ d ∈ g.range, d ≠ 0 → ν (g ⁻¹' {d}) < ⊤) :
    ‖∫ y, (T (f : α → ℂ)) y * (g : β → ℂ) y ∂ν‖ₑ
      ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
        * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ
        * eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν := by
  classical
  set q' : ℝ := q / (q - 1) with hq'def
  set q₀' : ℝ := q₀ / (q₀ - 1) with hq₀'def
  set q₁' : ℝ := q₁ / (q₁ - 1) with hq₁'def
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq'0 : 0 < q' := by rw [hq'def]; exact div_pos hq0 (by linarith)
  have hq₀'0 : 0 < q₀' := by rw [hq₀'def]; exact div_pos (by linarith) (by linarith)
  have hq₁'0 : 0 < q₁' := by rw [hq₁'def]; exact div_pos (by linarith) (by linarith)
  have hcomp : 1 / q' = (1 - θ) / q₀' + θ / q₁' := by
    rw [hq'def, hq₀'def, hq₁'def]
    exact one_div_conjExponent_interp hq₀ hq₁ hq hqθ
  set U : ℝ≥0∞ := eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ with hUdef
  set V : ℝ≥0∞ := eLpNorm (g : β → ℂ) (ENNReal.ofReal q') ν with hVdef
  have hUfin : U < ⊤ := by
    rw [hUdef]
    exact (SimpleFunc.memLp_of_finite_measure_preimage _
      (simpleFunc_fiber_lt_top_of_range f hf)).eLpNorm_lt_top
  have hVfin : V < ⊤ := by
    rw [hVdef]
    exact (SimpleFunc.memLp_of_finite_measure_preimage _
      (simpleFunc_fiber_lt_top_of_range g hg)).eLpNorm_lt_top
  have hTmem : ∀ c ∈ f.range, c ≠ 0 →
      MemLp (T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))) (ENNReal.ofReal q₀) ν := by
    intro c hc hc0
    refine (MeasureTheory.memLp_iff.mpr (?_))
    have h1 : eLpNorm (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (ENNReal.ofReal p₀) μ < ⊤ := by
      rw [eLpNorm_indicator_one (measurableSet_preimage (SimpleFunc.measurable f)
        (measurableSet_singleton c)) hp₀]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt (hf c hc hc0))
    exact lt_of_le_of_lt (h₀ _) (ENNReal.mul_lt_top ENNReal.coe_lt_top h1)
  set F : ℂ → ℂ := fun z => (fun u v => ∫ y, (T u) y * v y ∂ν)
      (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily (g : β → ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) z) with hFdef
  have hΛ : ∀ z : ℂ, (fun u v => ∫ y, (T u) y * v y ∂ν)
      (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily (g : β → ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) z)
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (phasePow c (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            * phasePow d (expFamily ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) z))
            * ((fun u v => ∫ y, (T u) y * v y ∂ν) (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))) := by
    intro z
    exact integral_pairing_analyticFamily_eq_sum T hq₀ f g (p / p₀) (p / p₁) (q' / q₀') (q' / q₁')
      hg hTmem z
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]
    exact differentiable_of_decomposition (fun u v => ∫ y, (T u) y * v y ∂ν) f g
      ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) hΛ
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    rw [hFdef]
    exact bddAbove_bilinear_family (fun u v => ∫ y, (T u) y * v y ∂ν) f g
      (p / p₀) (p / p₁) (q' / q₀') (q' / q₁') hΛ
  have hedge0 : ∀ z ∈ Complex.re ⁻¹' {0},
      ‖F z‖ ≤ (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀') := by
    intro z hz
    have hz' : z.re = 0 := hz
    have h1 : ‖F z‖ₑ ≤ (M₀ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₀) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) z)
            (ENNReal.ofReal q₀') ν := by
      rw [hFdef]
      exact (enorm_integral_mul_le hq₀ (hT _)
        (aemeasurable_analyticFamily g _ _ z)).trans
        (mul_le_mul_of_nonneg_right (h₀ _) zero_le)
    rw [eLpNorm_analyticFamily_re_zero (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f _ _ z).aestronglyMeasurable f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_zero (μ := ν) hq₀'0 hq₁'0 hq'0 hz'
        (aemeasurable_analyticFamily g _ _ z).aestronglyMeasurable g.aestronglyMeasurable,
      ← hUdef, ← hVdef] at h1
    have h2 : (M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q' / q₀')
        = ENNReal.ofReal ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀')) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₀),
        ← ofReal_toReal_const_eq (M₀ : ℝ) (by positivity) U V (p / p₀) (q' / q₀')
          (by positivity) (by positivity) (Or.inl hUfin) (Or.inl hVfin)]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hedge1 : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖F z‖ ≤ (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁') := by
    intro z hz
    have hz' : z.re = 1 := hz
    have h1 : ‖F z‖ₑ ≤ (M₁ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₁) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) z)
            (ENNReal.ofReal q₁') ν := by
      rw [hFdef]
      exact (enorm_integral_mul_le hq₁ (hT _)
        (aemeasurable_analyticFamily g _ _ z)).trans
        (mul_le_mul_of_nonneg_right (h₁ _) zero_le)
    rw [eLpNorm_analyticFamily_re_one (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f _ _ z).aestronglyMeasurable f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_one (μ := ν) hq₀'0 hq₁'0 hq'0 hz'
        (aemeasurable_analyticFamily g _ _ z).aestronglyMeasurable g.aestronglyMeasurable,
      ← hUdef, ← hVdef] at h1
    have h2 : (M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q' / q₁')
        = ENNReal.ofReal ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁')) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₁),
        ← ofReal_toReal_const_eq (M₁ : ℝ) (by positivity) U V (p / p₁) (q' / q₁')
          (by positivity) (by positivity) (Or.inl hUfin) (Or.inl hVfin)]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hhad := norm_le_interp_of_strip_edges hθ₀.le hθ₁.le hFdiff hB hedge0 hedge1
  have hselfp : (1 - (θ : ℂ)) * ((p / p₀ : ℝ) : ℂ) + (θ : ℂ) * ((p / p₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hp) hpθ
  have hselfq : (1 - (θ : ℂ)) * ((q' / q₀' : ℝ) : ℂ) + (θ : ℂ) * ((q' / q₁' : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hq'0) hcomp
  have hFθ : F (θ : ℂ) = (fun u v => ∫ y, (T u) y * v y ∂ν) (f : α → ℂ) (g : β → ℂ) := by
    show (fun u v => ∫ y, (T u) y * v y ∂ν)
      (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) (θ : ℂ))
      (analyticFamily (g : β → ℂ) ((q' / q₀' : ℝ) : ℂ) ((q' / q₁' : ℝ) : ℂ) (θ : ℂ))
      = (fun u v => ∫ y, (T u) y * v y ∂ν) (f : α → ℂ) (g : β → ℂ)
    rw [analyticFamily_self hselfp, analyticFamily_self hselfq]
  have hgoal : ‖(fun u v => ∫ y, (T u) y * v y ∂ν) (f : α → ℂ) (g : β → ℂ)‖ₑ
      ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V := by
    rcases eq_or_ne U 0 with hU0 | hU0
    · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀') = 0 := by
        rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₀)), mul_zero,
          zero_mul]
      have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁') = 0 := by
        rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₁)), mul_zero,
          zero_mul]
      have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
        have h := hhad
        rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
          Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
        exact h
      have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V = 0 := by
        rw [hU0, mul_zero, zero_mul]
      rw [hRHS, ← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rcases eq_or_ne V 0 with hV0 | hV0
    · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀') = 0 := by
        rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq'0 hq₀'0)), mul_zero]
      have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁') = 0 := by
        rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq'0 hq₁'0)), mul_zero]
      have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
        have h := hhad
        rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
          Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
        exact h
      have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V = 0 := by
        rw [hV0, mul_zero]
      rw [hRHS, ← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    have hUpos : 0 < U := pos_iff_ne_zero.mpr hU0
    have hVpos : 0 < V := pos_iff_ne_zero.mpr hV0
    have hα : (1 - θ) * (p / p₀) + θ * (p / p₁) = 1 := interp_self (ne_of_gt hp) hpθ
    have hβ : (1 - θ) * (q' / q₀') + θ * (q' / q₁') = 1 := interp_self (ne_of_gt hq'0) hcomp
    have harith : (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀')) ^ (1 - θ)
        * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁')) ^ θ)
        = (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * U.toReal * V.toReal :=
      rpow_interp_arith (by positivity) (by positivity)
        (ENNReal.toReal_pos hU0 (ne_of_lt hUfin)) (ENNReal.toReal_pos hV0 (ne_of_lt hVfin))
        hα hβ
    have hconv : ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀')) ^ (1 - θ)
        * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁')) ^ θ)
        = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V := by
      rw [harith, ofReal_arith_convert (by positivity) (by positivity) hUfin hVfin hθ₀.le hθ₁.le,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    calc ‖(fun u v => ∫ y, (T u) y * v y ∂ν) (f : α → ℂ) (g : β → ℂ)‖ₑ
        = ENNReal.ofReal ‖F (θ : ℂ)‖ := by rw [hFθ, ofReal_norm]
      _ ≤ ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q' / q₀')) ^ (1 - θ)
            * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q' / q₁')) ^ θ) :=
          ENNReal.ofReal_le_ofReal hhad
      _ = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V := hconv
  exact hgoal

/-! ## Riesz--Thorin interpolation for a linear operator -/

theorem riesz_thorin_linear {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SigmaFinite ν] (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (hT : ∀ u, AEMeasurable (T u) ν) {p₀ p₁ q₀ q₁ p q θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 1 < q₀) (hq₁ : 1 < q₁) (hp : 0 < p) (hq : 1 < q) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁) {M₀ M₁ : ℝ≥0} (h₀ : ∀ u, eLpNorm (T u) (ENNReal.ofReal q₀) ν ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) μ) (h₁ : ∀ u, eLpNorm (T u) (ENNReal.ofReal q₁) ν ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) μ) (f : SimpleFunc α ℂ) (hf : ∀ c ∈ f.range, c ≠ 0 → μ (f ⁻¹' {c}) < ⊤) : eLpNorm (T (f : α → ℂ)) (ENNReal.ofReal q) ν ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hf' : ∀ c : ℂ, c ≠ 0 → μ (f ⁻¹' {c}) < ⊤ := simpleFunc_fiber_lt_top_of_range f hf
  have hfA : MemLp (f : α → ℂ) (ENNReal.ofReal p₀) μ :=
    SimpleFunc.memLp_of_finite_measure_preimage _ hf'
  have hfB : MemLp (f : α → ℂ) (ENNReal.ofReal p₁) μ :=
    SimpleFunc.memLp_of_finite_measure_preimage _ hf'
  have hA : eLpNorm (T (f : α → ℂ)) (ENNReal.ofReal q₀) ν < ⊤ :=
    lt_of_le_of_lt (h₀ (f : α → ℂ)) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfA.eLpNorm_lt_top)
  have hB : eLpNorm (T (f : α → ℂ)) (ENNReal.ofReal q₁) ν < ⊤ :=
    lt_of_le_of_lt (h₁ (f : α → ℂ)) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfB.eLpNorm_lt_top)
  have hq₀0 : (0 : ℝ) < q₀ := lt_trans zero_lt_one hq₀
  have hq₁0 : (0 : ℝ) < q₁ := lt_trans zero_lt_one hq₁
  have hfin : eLpNorm (T (f : α → ℂ)) (ENNReal.ofReal q) ν < ⊤ :=
    (Interp.eLpNorm_interp (μ := ν) (f := T (f : α → ℂ)) hq₀0 hq₁0 hq0 hθ₀ hθ₁ hqθ (hT _)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) (ne_of_lt hA))
        (ENNReal.rpow_lt_top_of_nonneg hθ₀.le (ne_of_lt hB)))
  refine eLpNorm_le_of_forall_simpleFunc_integral_le
    (C := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ)
    hq (hT _) hfin ?_
  intro g hgV
  have hglevel : ∀ d ∈ g.range, d ≠ 0 → ν (g ⁻¹' {d}) < ⊤ := fun d hd hd0 =>
    SimpleFunc.measure_preimage_lt_top_of_memLp
      (ENNReal.ofReal_ne_zero_iff.mpr (div_pos hq0 (by linarith))) ENNReal.ofReal_ne_top g
      (MeasureTheory.memLp_iff.mpr (hgV)) d hd0
  exact integral_pairing_le_interp T hT hp₀ hp₁ hq₀ hq₁ hp hq hθ₀ hθ₁ hpθ hqθ h₀ h₁ f hf g hglevel

end Work.Analysis.Interpolation
