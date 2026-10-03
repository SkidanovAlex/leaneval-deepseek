/-
# The per-scale-pair Khintchine step of the bilinear Rademacher--Menshov corollary

This module proves the `L^q` bound for a *fixed* pair of block families: given families
`v : ℕ → V`, `w : ℕ → W` with a.e.-measurable pairwise `B`-values, a Khintchine constant `c` for the
two-step Rademacher average (`Work.Analysis.Variation.double_khintchine`), and the bound `T` on the
individual Rademacher terms (which the caller obtains from the tiling identity
`Work.Analysis.Variation.bilinear_tiling_sum` and the supremum in the statement of `rm-bil`), the
`L^q` norm of the `ℓ²`-norm of the family `(B (v i) (w j) ·)_{i < n₁, j < n₂}` is at most `c⁻¹ T`.
-/
import Mathlib
import Submission.Work.Analysis.Variation.bilinear_basic
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace Work.Analysis.Variation

section Averages

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The sum of a constant over all sign vectors `Fin n → Bool`, in `ℝ≥0∞`. -/
lemma sum_const_bool_fun (n : ℕ) (a : ℝ≥0∞) :
    (∑ _ : Fin n → Bool, a) = (2 : ℝ≥0∞) ^ n * a := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul, Fintype.card_bool,
    Fintype.card_fin]
  norm_num

/-- For an `ℝ≥0∞`-valued function, `eLpNorm` against `ofReal q` is the `q`-th root of the
`q`-th `lintegral`. -/
lemma eLpNorm_ennreal_eq {q : ℝ} (hq : 0 < q) (G : X → ℝ≥0∞)
    (hG : AEStronglyMeasurable G μ := by pw_aesm) :
    eLpNorm G (ENNReal.ofReal q) μ = (∫⁻ x, G x ^ q ∂μ) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hG) (ENNReal.ofReal_pos.mpr hq).ne'
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  simp only [enorm_eq_self]

/-- The `q`-th power of the `L^q` seminorm of a complex-valued function is the `q`-th `lintegral`
of its `ℝ≥0∞`-norm. -/
lemma lintegral_enorm_rpow_eq_eLpNorm_pow {q : ℝ} (hq : 0 < q) (F : X → ℂ)
    (hF : AEStronglyMeasurable F μ := by pw_aesm) :
    ∫⁻ x, ‖F x‖ₑ ^ q ∂μ = (eLpNorm F (ENNReal.ofReal q) μ) ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hF) (ENNReal.ofReal_pos.mpr hq).ne'
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul]
  rw [show (1 / q) * q = 1 by field_simp, ENNReal.rpow_one]

/-- `ofReal` of a finite sum of `q`-th powers of complex norms is the corresponding sum of `q`-th
powers of the `ℝ≥0∞`-norms. -/
lemma ofReal_sum_enorm_rpow {ι : Type*} {q : ℝ} (hq : 0 ≤ q) (s : Finset ι) (F : ι → ℂ) :
    ENNReal.ofReal (∑ i ∈ s, ‖F i‖ ^ q) = ∑ i ∈ s, ‖F i‖ₑ ^ q := by
  rw [ENNReal.ofReal_sum_of_nonneg (s := s) (f := fun i => ‖F i‖ ^ q)
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  exact Finset.sum_congr rfl fun i _ => (enorm_complex_rpow_eq_ofReal (F i) hq).symm

/-- The `q = 2` case of `ofReal_sum_enorm_rpow`, in the shape needed for the `ℓ²` norm. -/
lemma ofReal_sum_enorm_sq {ι : Type*} (s : Finset ι) (F : ι → ℂ) :
    ENNReal.ofReal (∑ i ∈ s, ‖F i‖ ^ 2) = ∑ i ∈ s, ‖F i‖ₑ ^ (2 : ℝ) := by
  rw [show (∑ i ∈ s, ‖F i‖ ^ 2) = ∑ i ∈ s, ‖F i‖ ^ (2 : ℝ) from
    Finset.sum_congr rfl fun i _ => (Real.rpow_two (‖F i‖)).symm,
    ofReal_sum_enorm_rpow (by norm_num : (0 : ℝ) ≤ 2) s F]

end Averages

section Main

variable {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [MeasurableSpace X] {μ : Measure X}

/-- `ofReal` of the real Rademacher average of `‖B (∑ sgn • v) (∑ sgn • w)‖^q` is the `ℝ≥0∞`
Rademacher average of `‖B (∑ sgn • v) (∑ sgn • w)‖ₑ^q`. -/
lemma ofReal_ave_eq {q : ℝ} (hq : 0 ≤ q) (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (n₁ n₂ : ℕ) (v : ℕ → V) (w : ℕ → W) (x : X) :
    ENNReal.ofReal ((∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
      / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂))
      = (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
          ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q)
        / ((2 : ℝ≥0∞) ^ n₁ * (2 : ℝ≥0∞) ^ n₂) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun d₁ : Fin n₁ → Bool => ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
      (fun d₁ _ => Finset.sum_nonneg fun d₂ _ => Real.rpow_nonneg (norm_nonneg _) _)]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun d₂ : Fin n₂ → Bool =>
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
      (fun d₂ _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact Finset.sum_congr rfl fun d₂ _ => (enorm_complex_rpow_eq_ofReal _ hq).symm
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_pow (by norm_num)]
    norm_num

/-- **Pointwise Khintchine step.**  For fixed `x`, the `ℓ²`-norm of the family
`(B (v i) (w j) x)_{i,j}` is bounded by the two-dimensional Rademacher average of the bilinear
values on the signed sums. -/
lemma blockFamily_pointwise {q : ℝ} (hq : 0 < q) (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {c : ℝ} (hc : 0 < c)
    (hkh : ∀ (n₁ n₂ : ℕ) (y : Fin n₁ → Fin n₂ → ℂ),
      c * (∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((∑ e₁ : Fin n₁ → Bool, ∑ e₂ : Fin n₂ → Bool,
              ‖∑ i : Fin n₁, ∑ j : Fin n₂, (sgn (e₁ i) * sgn (e₂ j)) * y i j‖ ^ q)
            / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) ^ ((1 : ℝ) / q))
    {n₁ n₂ : ℕ} (v : ℕ → V) (w : ℕ → W) (x : X) :
    (∑ p ∈ (Finset.range n₁).product (Finset.range n₂), ‖B (v p.1) (w p.2) x‖ ^ 2) ^ (q / 2)
      ≤ c ^ (-q) * ((∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
          ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
        / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) := by
  have h := hkh n₁ n₂ (fun i j => B (v (i : ℕ)) (w (j : ℕ)) x)
  have hinner : ∀ (e₁ : Fin n₁ → Bool) (e₂ : Fin n₂ → Bool),
      ‖∑ i : Fin n₁, ∑ j : Fin n₂,
          (sgn (e₁ i) * sgn (e₂ j)) * B (v (i : ℕ)) (w (j : ℕ)) x‖
        = ‖B (∑ i : Fin n₁, sgn (e₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (e₂ j) • w (j : ℕ)) x‖ := by
    intro e₁ e₂
    rw [(bil_sum_sum_fin_apply B hadd₁ hsmul₁ hadd₂ hsmul₂ e₁ e₂ v w x).symm]
  have h1 : c * (∑ i : Fin n₁, ∑ j : Fin n₂, ‖B (v (i : ℕ)) (w (j : ℕ)) x‖ ^ 2)
        ^ ((1 : ℝ) / 2)
      ≤ ((∑ e₁ : Fin n₁ → Bool, ∑ e₂ : Fin n₂ → Bool,
            ‖B (∑ i : Fin n₁, sgn (e₁ i) • v (i : ℕ))
                (∑ j : Fin n₂, sgn (e₂ j) • w (j : ℕ)) x‖ ^ q)
          / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) ^ ((1 : ℝ) / q) := by
    simpa only [hinner] using h
  rw [← sum_product_range_eq_sum_fin n₁ n₂ (fun i j => ‖B (v i) (w j) x‖ ^ 2)] at h1
  set S : ℝ := ∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
    ‖B (v p.1) (w p.2) x‖ ^ 2 with hS
  set A : ℝ := (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
      ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
          (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
      / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂) with hA
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (Finset.sum_nonneg fun d₁ _ => Finset.sum_nonneg fun d₂ _ =>
      Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hcq : 0 < c ^ q := Real.rpow_pos_of_pos hc q
  have hAq : (A ^ (1 / q)) ^ q = A := by
    rw [← Real.rpow_mul hAnn, show (1 / q) * q = 1 by field_simp, Real.rpow_one]
  have hmain : c ^ q * S ^ (q / 2) ≤ A := by
    calc c ^ q * S ^ (q / 2) = c ^ q * S ^ ((1 : ℝ) / 2 * q) := by
          congr 1; ring
      _ = c ^ q * (S ^ ((1 : ℝ) / 2)) ^ q := by rw [Real.rpow_mul hSnn]
      _ = (c * S ^ ((1 : ℝ) / 2)) ^ q := by
          rw [Real.mul_rpow hc.le (Real.rpow_nonneg hSnn _)]
      _ ≤ A := by rw [← hAq]; exact Real.rpow_le_rpow (by positivity) h1 hq.le
  rw [Real.rpow_neg hc.le, ← div_eq_inv_mul]
  exact (le_div_iff₀ hcq).mpr (by rw [mul_comm]; exact hmain)

/-- **The per-scale-pair Khintchine bound.** -/
theorem eLpNorm_blockFamily_le {q : ℝ} (hq : 0 < q) (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {c : ℝ} (hc : 0 < c)
    (hkh : ∀ (n₁ n₂ : ℕ) (y : Fin n₁ → Fin n₂ → ℂ),
      c * (∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((∑ e₁ : Fin n₁ → Bool, ∑ e₂ : Fin n₂ → Bool,
              ‖∑ i : Fin n₁, ∑ j : Fin n₂, (sgn (e₁ i) * sgn (e₂ j)) * y i j‖ ^ q)
            / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) ^ ((1 : ℝ) / q))
    {n₁ n₂ : ℕ} (v : ℕ → V) (w : ℕ → W)
    (hmeas : ∀ (i j : ℕ), _root_.AEMeasurable (fun x => B (v i) (w j) x) μ)
    (T : ℝ≥0∞)
    (hT : ∀ (d₁ : Fin n₁ → Bool) (d₂ : Fin n₂ → Bool),
      eLpNorm (fun x => B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
          (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x) (ENNReal.ofReal q) μ ≤ T) :
    eLpNorm (fun x => (∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
        ‖B (v p.1) (w p.2) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal (c⁻¹) * T := by
  classical
  set D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ n₁ * (2 : ℝ≥0∞) ^ n₂ with hD
  set Ave : X → ℝ≥0∞ := fun x => (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
      ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
          (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) / D with hAve
  have hD0 : D ≠ 0 := by
    rw [hD]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  have hDT : D ≠ ⊤ := by
    rw [hD]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.pow_ne_top (by norm_num))
  -- a.e.-measurability
  have hmeasbil : ∀ (d₁ : Fin n₁ → Bool) (d₂ : Fin n₂ → Bool),
      _root_.AEMeasurable (fun x => B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
          (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x) μ :=
    fun d₁ d₂ => aemeasurable_bilinear_fin B hadd₁ hsmul₁ hadd₂ hsmul₂ v w d₁ d₂ hmeas
  have hmeasq : ∀ (d₁ : Fin n₁ → Bool) (d₂ : Fin n₂ → Bool),
      _root_.AEMeasurable (fun x => ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
          (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) μ :=
    fun d₁ d₂ => ((hmeasbil d₁ d₂).enorm).pow_const q
  have hAve_meas : _root_.AEMeasurable Ave μ := by
    show _root_.AEMeasurable (fun x => (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) / D) μ
    rw [show (fun x => (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
          ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) / D)
        = fun x => D⁻¹ * (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
              ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                  (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) from by
      funext x; rw [div_eq_mul_inv, mul_comm]]
    exact (Finset.aemeasurable_fun_sum Finset.univ fun d₁ _ =>
      Finset.aemeasurable_fun_sum Finset.univ fun d₂ _ => hmeasq d₁ d₂).const_mul D⁻¹
  -- the pointwise bound
  set G : X → ℝ≥0∞ := fun x => (∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
      ‖B (v p.1) (w p.2) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) with hG
  have hGq : ∀ x, G x ^ q ≤ (ENNReal.ofReal c⁻¹) ^ q * Ave x := by
    intro x
    have hpt := blockFamily_pointwise (n₁ := n₁) (n₂ := n₂) hq B hadd₁ hsmul₁ hadd₂ hsmul₂
      hc hkh v w x
    have hSnn : 0 ≤ ∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
        ‖B (v p.1) (w p.2) x‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
    have hGx : G x = ENNReal.ofReal
        ((∑ p ∈ (Finset.range n₁).product (Finset.range n₂), ‖B (v p.1) (w p.2) x‖ ^ 2)
          ^ ((1 : ℝ) / 2)) := by
      show (∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
          ‖B (v p.1) (w p.2) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = _
      rw [← ofReal_sum_enorm_sq ((Finset.range n₁).product (Finset.range n₂))
        (fun p => B (v p.1) (w p.2) x)]
      exact ENNReal.ofReal_rpow_of_nonneg hSnn (by norm_num)
    have hAveR : ENNReal.ofReal ((∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
        / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) = Ave x := by
      rw [hAve, hD]
      exact ofReal_ave_eq hq.le B hadd₁ hsmul₁ hadd₂ hsmul₂ n₁ n₂ v w x
    have hcinv : c ^ (-q) = (c⁻¹) ^ q := by
      rw [Real.rpow_neg hc.le, ← Real.inv_rpow hc.le]
    calc G x ^ q
        = ENNReal.ofReal (((∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
              ‖B (v p.1) (w p.2) x‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ q) := by
          rw [hGx, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hSnn _) hq.le]
      _ = ENNReal.ofReal ((∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
              ‖B (v p.1) (w p.2) x‖ ^ 2) ^ (q / 2)) := by
          congr 1
          rw [← Real.rpow_mul hSnn]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (c ^ (-q) * ((∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
              ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                  (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ ^ q)
            / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂))) :=
          ENNReal.ofReal_le_ofReal hpt
      _ = ENNReal.ofReal (c ^ (-q)) * Ave x := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), hAveR]
      _ = (ENNReal.ofReal c⁻¹) ^ q * Ave x := by
          rw [hcinv, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hc.le) hq.le]
  -- integration
  have hInt : ∫⁻ x, G x ^ q ∂μ ≤ (ENNReal.ofReal c⁻¹) ^ q * ∫⁻ x, Ave x ∂μ := by
    calc ∫⁻ x, G x ^ q ∂μ ≤ ∫⁻ x, (ENNReal.ofReal c⁻¹) ^ q * Ave x ∂μ :=
          lintegral_mono hGq
      _ = (ENNReal.ofReal c⁻¹) ^ q * ∫⁻ x, Ave x ∂μ := lintegral_const_mul'' _ hAve_meas
  -- the average is at most `T ^ q`
  have hAve_le : ∫⁻ x, Ave x ∂μ ≤ T ^ q := by
    have h1 : ∫⁻ x, Ave x ∂μ = D⁻¹ * ∫⁻ x, (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) ∂μ := by
      show ∫⁻ x, (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
          ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) / D ∂μ = _
      rw [show (fun x => (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
            ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) / D)
          = fun x => D⁻¹ * (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
                ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                    (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) from by
        funext x; rw [div_eq_mul_inv, mul_comm]]
      rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum Finset.univ fun d₁ _ =>
        Finset.aemeasurable_fun_sum Finset.univ fun d₂ _ => hmeasq d₁ d₂)]
    have h2 : ∫⁻ x, (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
        ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
            (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) ∂μ ≤ D * T ^ q := by
      rw [lintegral_finsetSum' Finset.univ (fun d₁ _ =>
        Finset.aemeasurable_fun_sum Finset.univ fun d₂ _ => hmeasq d₁ d₂)]
      have hstep : ∀ d₁ : Fin n₁ → Bool,
          ∫⁻ x, (∑ d₂ : Fin n₂ → Bool, ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) ∂μ
            ≤ (2 : ℝ≥0∞) ^ n₂ * T ^ q := by
        intro d₁
        rw [lintegral_finsetSum' Finset.univ (fun d₂ _ => hmeasq d₁ d₂)]
        calc ∑ d₂ : Fin n₂ → Bool, ∫⁻ x, ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q ∂μ
            = ∑ d₂ : Fin n₂ → Bool,
                (eLpNorm (fun x => B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                  (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x) (ENNReal.ofReal q) μ) ^ q :=
              Finset.sum_congr rfl fun d₂ _ => lintegral_enorm_rpow_eq_eLpNorm_pow hq _
          _ ≤ ∑ _d₂ : Fin n₂ → Bool, T ^ q :=
              Finset.sum_le_sum fun d₂ _ => ENNReal.rpow_le_rpow (hT d₁ d₂) hq.le
          _ = (2 : ℝ≥0∞) ^ n₂ * T ^ q := sum_const_bool_fun n₂ _
      calc ∑ d₁ : Fin n₁ → Bool, ∫⁻ x, (∑ d₂ : Fin n₂ → Bool,
            ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
                (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) ∂μ
          ≤ ∑ _d₁ : Fin n₁ → Bool, (2 : ℝ≥0∞) ^ n₂ * T ^ q :=
            Finset.sum_le_sum fun d₁ _ => hstep d₁
        _ = (2 : ℝ≥0∞) ^ n₁ * ((2 : ℝ≥0∞) ^ n₂ * T ^ q) := sum_const_bool_fun n₁ _
        _ = D * T ^ q := by rw [hD]; ring
    calc ∫⁻ x, Ave x ∂μ = D⁻¹ * ∫⁻ x, (∑ d₁ : Fin n₁ → Bool, ∑ d₂ : Fin n₂ → Bool,
          ‖B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
              (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x‖ₑ ^ q) ∂μ := h1
      _ ≤ D⁻¹ * (D * T ^ q) := mul_le_mul' le_rfl h2
      _ = T ^ q := by rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDT, one_mul]
  -- conclusion
  have hfin : eLpNorm G (ENNReal.ofReal q) μ ≤ ENNReal.ofReal c⁻¹ * T := by
    rw [eLpNorm_ennreal_eq hq G]
    calc (∫⁻ x, G x ^ q ∂μ) ^ (1 / q)
        ≤ ((ENNReal.ofReal c⁻¹) ^ q * ∫⁻ x, Ave x ∂μ) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hInt (by positivity)
      _ ≤ ((ENNReal.ofReal c⁻¹) ^ q * T ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hAve_le) (by positivity)
      _ = ((ENNReal.ofReal c⁻¹) ^ q) ^ (1 / q) * (T ^ q) ^ (1 / q) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal c⁻¹ * T := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one, ENNReal.rpow_one]
  show eLpNorm (fun x => (∑ p ∈ (Finset.range n₁).product (Finset.range n₂),
      ‖B (v p.1) (w p.2) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal c⁻¹ * T
  exact hfin

end Main

end Work.Analysis.Variation
