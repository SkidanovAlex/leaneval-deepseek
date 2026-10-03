/-
# The general support region `A ≤ g(t₁,t₂) ≤ B` for the §7 Fourier integral

`Work.FIArea2.lemma_7_1` proves Lemma 7.1 of Friedlander–Iwaniec for a majorant `f` supported in
`[M/4, 4M]`.  Round 6 needs the same estimate for the *general* majorant of `IsMajorant6`
(a `C⁴` function supported in `[A,B]` with `M/64 ≤ A`, `B ≤ 64 M`, `|f^{(j)}| ≤ Cder·M^{-j}`), whose
support is allowed to spread over `[M/64, 64 M]` — three more dyadic scales on each side.

This module collects the geometric facts about the general region
`regG A B γ = {p | A ≤ g γ p.1 p.2 ∧ g γ p.1 p.2 ≤ B}`, `g γ t₁ t₂ = t₁⁴ − 2γt₁²t₂² + t₂⁴`,
that replace `Work.FIArea2.reg`/`region_bounds` in the proof of Lemma 7.1:

* `quarter_sq_le_gq`: `g ≥ (1−γ²)/4·(t₁²+t₂²)²` (the inequality behind `t₁⁴+t₂² ≲ √M/δ`);
* `regG_slice_subset`: for `0 ≤ B`, the `t₁`-slice of the region lies in `|t₁| ≤ sliceR B γ`,
  `sliceR B γ = √(2√B/√(1−γ²))`, so slices have finite length;
* the slice/integrand integrability lemmas, `norm_FintInt_le_indicator_gen` and
  `integrable_FintInt_gen`, with the bound `|f| ≤ Cder` in place of `|f| ≤ 1`.
-/
import Mathlib
import Submission.Work.FIArea2.lemma_7_1_aux
import Submission.Work.FIArea2.lemma_7_1

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory
open scoped BigOperators
open scoped Topology

noncomputable section

/-- The general support region `A ≤ g(t₁,t₂) ≤ B` of the biquadratic form (7.1). -/
def regG (A B γ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | A ≤ Work.FIArea2.gq γ p.1 p.2 ∧ Work.FIArea2.gq γ p.1 p.2 ≤ B}

lemma isClosed_regG (A B γ : ℝ) : IsClosed (regG A B γ) := by
  have hcont : Continuous (fun p : ℝ × ℝ => Work.FIArea2.gq γ p.1 p.2) := by
    simp only [Work.FIArea2.gq]; fun_prop
  exact IsClosed.inter (isClosed_le continuous_const hcont) (isClosed_le hcont continuous_const)

lemma measurableSet_regG (A B γ : ℝ) : MeasurableSet (regG A B γ) :=
  (isClosed_regG A B γ).measurableSet

lemma mem_regG_iff (A B γ : ℝ) (t₁ t₂ : ℝ) :
    (t₁, t₂) ∈ regG A B γ ↔ A ≤ Work.FIArea2.gq γ t₁ t₂ ∧ Work.FIArea2.gq γ t₁ t₂ ≤ B := Iff.rfl

/-- `g ≥ 0` for `0 ≤ γ ≤ 1`, from `g = (t₁²−t₂²)² + 2(1−γ)t₁²t₂²`. -/
lemma gq_nonneg (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (t₁ t₂ : ℝ) :
    0 ≤ Work.FIArea2.gq γ t₁ t₂ := by
  have h1 : Work.FIArea2.gq γ t₁ t₂ = (t₁ ^ 2 - t₂ ^ 2) ^ 2 + 2 * (1 - γ) * t₁ ^ 2 * t₂ ^ 2 := by
    simp only [Work.FIArea2.gq]; ring
  rw [h1]
  have h2 : 0 ≤ 2 * (1 - γ) * t₁ ^ 2 * t₂ ^ 2 := by
    have : (0 : ℝ) ≤ 2 * (1 - γ) := by linarith
    positivity
  have h3 : 0 ≤ (t₁ ^ 2 - t₂ ^ 2) ^ 2 := sq_nonneg _
  linarith

/-- **The basic lower bound for the general region**: for `0 ≤ γ ≤ 1`,
`g(t₁,t₂) ≥ (1−γ²)/4·(t₁²+t₂²)²`.  The proof is the identity
`g − (1−γ²)/4·(t₁²+t₂²)² = ((3+γ²)/4)(t₁²−t₂²)² + (1−γ)²t₁²t₂²`. -/
lemma quarter_sq_le_gq (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (t₁ t₂ : ℝ) :
    (1 - γ ^ 2) / 4 * (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ Work.FIArea2.gq γ t₁ t₂ := by
  have hkey : Work.FIArea2.gq γ t₁ t₂ - (1 - γ ^ 2) / 4 * (t₁ ^ 2 + t₂ ^ 2) ^ 2
      = ((3 + γ ^ 2) / 4) * (t₁ ^ 2 - t₂ ^ 2) ^ 2 + (1 - γ) ^ 2 * (t₁ ^ 2 * t₂ ^ 2) := by
    simp only [Work.FIArea2.gq]; ring
  have h1 : 0 ≤ ((3 + γ ^ 2) / 4) * (t₁ ^ 2 - t₂ ^ 2) ^ 2 := by
    have : (0 : ℝ) ≤ (3 + γ ^ 2) / 4 := by nlinarith [sq_nonneg γ]
    positivity
  have h2 : 0 ≤ (1 - γ) ^ 2 * (t₁ ^ 2 * t₂ ^ 2) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith [hkey, h1, h2]

/-- Outside the region (above `B`), `f ∘ g` vanishes when `f` is supported in `[A,B]`. -/
lemma f_gq_eq_zero_gen (A B γ : ℝ) (f : ℝ → ℝ)
    (hfsupp : ∀ u, f u ≠ 0 → A ≤ u ∧ u ≤ B) {t₁ t₂ : ℝ}
    (h : ¬ (A ≤ Work.FIArea2.gq γ t₁ t₂ ∧ Work.FIArea2.gq γ t₁ t₂ ≤ B)) :
    f (Work.FIArea2.gq γ t₁ t₂) = 0 := by
  by_contra hf
  exact h (hfsupp _ hf)

/-! ## The `t₁`-slices of the general region -/

/-- The threshold beyond which the `t₁`-slice of `regG A B γ` is empty:
`sliceR B γ² = 2√B/√(1−γ²)`. -/
def sliceR (B γ : ℝ) : ℝ := Real.sqrt (2 * Real.sqrt B / Real.sqrt (1 - γ ^ 2))

lemma sliceR_nonneg (B γ : ℝ) : 0 ≤ sliceR B γ := Real.sqrt_nonneg _

lemma sliceR_sq (B γ : ℝ) (hB : 0 ≤ B) (h1γ : 0 < 1 - γ ^ 2) :
    sliceR B γ ^ 2 = 2 * Real.sqrt B / Real.sqrt (1 - γ ^ 2) := by
  rw [sliceR, Real.sq_sqrt]
  have h1 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr h1γ
  positivity

lemma sliceR_pow_four (B γ : ℝ) (hB : 0 ≤ B) (h1γ : 0 < 1 - γ ^ 2) :
    sliceR B γ ^ 4 = 4 * B / (1 - γ ^ 2) := by
  have h : sliceR B γ ^ 4 = (sliceR B γ ^ 2) ^ 2 := by ring
  rw [h, sliceR_sq B γ hB h1γ]
  have hB' : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have h1γ' : Real.sqrt (1 - γ ^ 2) ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt h1γ.le
  rw [div_pow, mul_pow, hB', h1γ']
  norm_num

/-- **The slice bound**: for `0 ≤ B`, the `t₁`-section of `regG A B γ` at height `t₂` lies in
`|t₁| ≤ sliceR B γ`. -/
lemma regG_slice_subset (A B γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : 0 ≤ B) (t₂ : ℝ) :
    {t₁ : ℝ | (t₁, t₂) ∈ regG A B γ} ⊆ Set.Icc (-(sliceR B γ)) (sliceR B γ) := by
  have h1γ : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have hγ1' : γ ≤ 1 := le_of_lt hγ1
  intro t₁ ht
  have hgq : Work.FIArea2.gq γ t₁ t₂ ≤ B := ht.2
  have hq := quarter_sq_le_gq γ hγ0 hγ1' t₁ t₂
  have hpos4 : (0 : ℝ) < (1 - γ ^ 2) / 4 := by positivity
  have hle1 : (t₁ ^ 2 + t₂ ^ 2) ^ 2 * ((1 - γ ^ 2) / 4) ≤ B := by
    have h := le_trans hq hgq
    linarith [show (1 - γ ^ 2) / 4 * (t₁ ^ 2 + t₂ ^ 2) ^ 2
      = (t₁ ^ 2 + t₂ ^ 2) ^ 2 * ((1 - γ ^ 2) / 4) by ring]
  have hle : (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ 4 * B / (1 - γ ^ 2) := by
    have h2 : (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ B / ((1 - γ ^ 2) / 4) := (le_div_iff₀ hpos4).mpr hle1
    have h3 : B / ((1 - γ ^ 2) / 4) = 4 * B / (1 - γ ^ 2) := by
      rw [div_div_eq_mul_div]; ring
    rwa [h3] at h2
  have ht1 : t₁ ^ 4 ≤ sliceR B γ ^ 4 := by
    have h2 : (t₁ ^ 2) ^ 2 ≤ (t₁ ^ 2 + t₂ ^ 2) ^ 2 := by nlinarith [sq_nonneg t₂]
    calc t₁ ^ 4 = (t₁ ^ 2) ^ 2 := by ring
      _ ≤ (t₁ ^ 2 + t₂ ^ 2) ^ 2 := h2
      _ ≤ 4 * B / (1 - γ ^ 2) := hle
      _ = sliceR B γ ^ 4 := (sliceR_pow_four B γ hB h1γ).symm
  have habs : |t₁| ≤ sliceR B γ := by
    have hR : (0 : ℝ) ≤ sliceR B γ := sliceR_nonneg B γ
    have h2 : (t₁ ^ 2) ≤ sliceR B γ ^ 2 := by
      have hpow : (t₁ ^ 2) ^ 2 ≤ (sliceR B γ ^ 2) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        exact ht1
      nlinarith [hpow, sq_nonneg t₁, hR]
    calc |t₁| = Real.sqrt (t₁ ^ 2) := (Real.sqrt_sq_eq_abs t₁).symm
      _ ≤ Real.sqrt (sliceR B γ ^ 2) := Real.sqrt_le_sqrt h2
      _ = sliceR B γ := Real.sqrt_sq hR
  simp only [Set.mem_Icc]
  exact ⟨by linarith [neg_abs_le t₁], by linarith [le_abs_self t₁]⟩

/-- The `t₁`-slice of a general region has finite measure, hence its indicator is integrable. -/
lemma integrable_indicator_regG_slice (A B γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : 0 ≤ B)
    (t₂ : ℝ) :
    Integrable (fun t₁ : ℝ => Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
  have hmeas : MeasurableSet {t₁ : ℝ | (t₁, t₂) ∈ regG A B γ} :=
    (isClosed_regG A B γ).measurableSet.preimage (by fun_prop)
  have hfin : volume {t₁ : ℝ | (t₁, t₂) ∈ regG A B γ} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (regG_slice_subset A B γ hγ0 hγ1 hB t₂)) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  exact (integrable_indicator_iff hmeas).mpr (integrableOn_const (ne_of_lt hfin))

/-- Finiteness of the general region gives integrability of its indicator. -/
lemma integrable_indicator_regG (A B γ : ℝ) (hvol : volume (regG A B γ) < ⊤) :
    Integrable (Set.indicator (regG A B γ) (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff (isClosed_regG A B γ).measurableSet]
  exact integrableOn_const (ne_of_lt hvol)

/-! ## The integrand of (7.1) for the general region -/

/-- The integrand of (7.1) is bounded by `Cder` times the indicator of the general region. -/
lemma norm_FintInt_le_indicator_gen (γ A B Cder : ℝ) (f : ℝ → ℝ) (hC0 : 0 ≤ Cder)
    (hb : ∀ u : ℝ, |f u| ≤ Cder) (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B)
    (u₁ u₂ : ℝ) (p : ℝ × ℝ) :
    ‖Work.FIArea2.FintInt f γ u₁ u₂ p‖
      ≤ Cder * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) p := by
  rw [Work.FIArea2.FintInt, norm_mul]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2) : ℂ)
        = ((2 * Real.pi * (u₁ * p.1 + u₂ * p.2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  by_cases hp : p ∈ regG A B γ
  · rw [Set.indicator_of_mem hp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hb _
  · rw [Set.indicator_of_notMem hp, mul_zero]
    have hzero : f (Work.FIArea2.gq γ p.1 p.2) = 0 :=
      f_gq_eq_zero_gen A B γ f hfsupp (fun h => hp ⟨h.1, h.2⟩)
    rw [hzero, Complex.ofReal_zero, norm_zero]

/-- The integrand of (7.1) is integrable for a general `C⁴`, compactly supported majorant of
strength `Cder`, once the general region has finite measure. -/
lemma integrable_FintInt_gen (γ A B Cder : ℝ) (f : ℝ → ℝ) (hvol : volume (regG A B γ) < ⊤)
    (hf : Continuous f) (hC0 : 0 ≤ Cder) (hb : ∀ u : ℝ, |f u| ≤ Cder)
    (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B) (u₁ u₂ : ℝ) :
    Integrable (Work.FIArea2.FintInt f γ u₁ u₂) := by
  have hcont : Continuous (fun p : ℝ × ℝ => ((f (Work.FIArea2.gq γ p.1 p.2) : ℝ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (hf.comp (by simp only [Work.FIArea2.gq]; fun_prop))
    · fun_prop
  have hcont' : Continuous (Work.FIArea2.FintInt f γ u₁ u₂) := hcont
  refine Integrable.mono' ((integrable_indicator_regG A B γ hvol).const_mul Cder)
    hcont'.aestronglyMeasurable ?_
  filter_upwards with p
  exact norm_FintInt_le_indicator_gen γ A B Cder f hC0 hb hfsupp u₁ u₂ p

/-! ## Vanishing of the slice functions outside a compact set -/

/-- For a general majorant supported in `[A,B]` (`0 ≤ B`), the slice functions
`s ↦ f(g(γ,s,t₂))` vanish beyond `|s| = sliceR B γ`. -/
lemma hfun_eq_zero_outside_gen (A B γ : ℝ) (f : ℝ → ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hB : 0 ≤ B) (hfsupp : ∀ u, f u ≠ 0 → A ≤ u ∧ u ≤ B) (t₂ : ℝ) :
    (∀ x : ℝ, x < -(sliceR B γ) → (f (Work.FIArea2.gq γ x t₂) : ℂ) = 0) ∧
    (∀ x : ℝ, sliceR B γ < x → (f (Work.FIArea2.gq γ x t₂) : ℂ) = 0) := by
  have h1γ : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have hγ1' : γ ≤ 1 := le_of_lt hγ1
  have hRp4 : sliceR B γ ^ 4 = 4 * B / (1 - γ ^ 2) := sliceR_pow_four B γ hB h1γ
  have key : ∀ x : ℝ, sliceR B γ < |x| →
      f (Work.FIArea2.gq γ x t₂) = 0 := by
    intro x hx
    have hx2 : sliceR B γ ^ 2 < x ^ 2 := by
      have h1 : sliceR B γ ^ 2 < |x| ^ 2 := by
        nlinarith [sliceR_nonneg B γ, abs_nonneg x]
      rwa [sq_abs] at h1
    have h4 : sliceR B γ ^ 4 < (x ^ 2) ^ 2 := by
      have h1 : sliceR B γ ^ 4 = (sliceR B γ ^ 2) ^ 2 := by ring
      rw [h1]
      exact pow_lt_pow_left₀ hx2 (pow_nonneg (sliceR_nonneg B γ) 2) (by norm_num)
    have hbig : 4 * B / (1 - γ ^ 2) < (x ^ 2 + t₂ ^ 2) ^ 2 := by
      have h2 : (x ^ 2) ^ 2 ≤ (x ^ 2 + t₂ ^ 2) ^ 2 := by nlinarith [sq_nonneg t₂]
      rw [← hRp4]
      linarith
    have hq := quarter_sq_le_gq γ hγ0 hγ1' x t₂
    have hqgt : B < Work.FIArea2.gq γ x t₂ := by
      have hpos : (0 : ℝ) < 1 - γ ^ 2 := h1γ
      have hcalc : (1 - γ ^ 2) / 4 * (4 * B / (1 - γ ^ 2)) = B := by field_simp
      have h3 : (1 - γ ^ 2) / 4 * (4 * B / (1 - γ ^ 2))
          < (1 - γ ^ 2) / 4 * (x ^ 2 + t₂ ^ 2) ^ 2 := by
        apply mul_lt_mul_of_pos_left hbig; positivity
      rw [hcalc] at h3
      linarith
    exact f_gq_eq_zero_gen A B γ f hfsupp (fun h => absurd h.2 (not_le.mpr hqgt))
  constructor
  · intro x hx
    rw [Complex.ofReal_eq_zero]
    have hx0 : x < 0 := by have := sliceR_nonneg B γ; linarith
    exact key x (by rw [abs_of_neg hx0]; linarith [sliceR_nonneg B γ, hx])
  · intro x hx
    rw [Complex.ofReal_eq_zero]
    have hx0 : 0 < x := by have := sliceR_nonneg B γ; linarith
    exact key x (by rw [abs_of_pos hx0]; linarith [sliceR_nonneg B γ, hx])

/-- The slice functions are `C⁴` with integrable derivatives. -/
lemma contDiff_integrable_hfun_gen (A B γ : ℝ) (f : ℝ → ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hB : 0 ≤ B) (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → A ≤ u ∧ u ≤ B) (t₂ : ℝ) :
    ContDiff ℝ 4 (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)) ∧
    (∀ n : ℕ, n ≤ 4 → Integrable (iteratedDeriv n (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)))) := by
  have h1 : ContDiff ℝ 4 (fun s : ℝ => Work.FIArea2.gq γ s t₂) := by
    simp only [Work.FIArea2.gq]; fun_prop
  have hcd : ContDiff ℝ 4 (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp h1)
  obtain ⟨hleft, hright⟩ := hfun_eq_zero_outside_gen A B γ f hγ0 hγ1 hB hfsupp t₂
  exact ⟨hcd, fun n hn =>
    Work.FIArea2.integrable_iteratedDeriv_of_eq_zero_outside _ _ _ hcd hleft hright hn⟩

end

end Work.FIArea2.R6
