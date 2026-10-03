/-
# The deviation kernel of the lacunary bump-dilation family: elementary bounds

Elementary estimates on the deviation kernel

  `devKern K σ n j = (1/σ_n) K (j/σ_n) − (∫K) · triKernel (lacLev σ n) j`

used by the square-function bound `Work.KMTAreas.A7.lacDilDevSqSum`: the Schwartz decay
(`devKern_norm_le`), summability, the kernel-convolution representations of `devOp` and of the
linearized operators (`devOp_eq_tsum`, `lacDevLin_conv`), and the uniform pointwise bound
(`lacDevLin_norm_le`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform

noncomputable section

/-! ## The mean of the kernel is the Fourier transform at `0` -/

theorem lacConst_eq_fourier_zero (K : SchwartzMap ℝ ℂ) :
    lacConst K = (𝓕 (K : ℝ → ℂ)) 0 := by
  rw [Real.fourier_real_eq]
  simp [lacConst]

/-- `1 ≤ σ n` gives a positive real scale. -/
lemma scale_pos {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) :
    (0 : ℝ) < ((σ n : ℕ) : ℝ) := by
  have h : (1 : ℝ) ≤ ((σ n : ℕ) : ℝ) := by exact_mod_cast hσ1 n
  linarith

/-! ## The triangular kernel vanishes off its support -/

/-- The triangular kernel vanishes where `|j| > 2^L`. -/
lemma triKernel_eq_zero_of_abs (L : ℕ) {j : ℤ} (h : (((2 : ℤ) ^ L : ℤ) : ℝ) < |(j : ℝ)|) :
    Work.Analysis.Hilbert.triKernel L j = 0 := by
  have hcast : (2 : ℝ) ^ L = (((2 : ℤ) ^ L : ℤ) : ℝ) := by push_cast; ring
  have h2L : (0 : ℝ) ≤ (((2 : ℤ) ^ L : ℤ) : ℝ) := by positivity
  rw [Work.Analysis.Hilbert.triKernel, hcast]
  refine max_eq_left ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  rcases le_total (0 : ℤ) j with hj | hj
  · have hj' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [abs_of_nonneg hj'] at h ⊢
    linarith
  · have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    rw [abs_of_nonpos hj'] at h ⊢
    linarith

/-- The triangular kernel vanishes off `[-2^L, 2^L]`. -/
lemma triKernel_eq_zero_of_notMem (L : ℕ) {j : ℤ}
    (hj : j ∉ Finset.Icc (-((2 : ℤ) ^ L)) ((2 : ℤ) ^ L)) :
    Work.Analysis.Hilbert.triKernel L j = 0 := by
  refine triKernel_eq_zero_of_abs L ?_
  have h2L : (0 : ℝ) ≤ (((2 : ℤ) ^ L : ℤ) : ℝ) := by positivity
  have hcases : j < -((2 : ℤ) ^ L) ∨ ((2 : ℤ) ^ L) < j := by
    by_contra hc
    push_neg at hc
    exact hj (Finset.mem_Icc.mpr ⟨hc.1, hc.2⟩)
  rcases hcases with h | h
  · have h' : (j : ℝ) < -(((2 : ℤ) ^ L : ℤ) : ℝ) := by exact_mod_cast h
    have hj' : (j : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hj']
    linarith
  · have h' : (((2 : ℤ) ^ L : ℤ) : ℝ) < (j : ℝ) := by exact_mod_cast h
    have hj' : (0 : ℝ) ≤ (j : ℝ) := by linarith
    rw [abs_of_nonneg hj']
    linarith

/-! ## Elementary `ℤ`-summability and lacunary arithmetic -/

/-- `j ↦ (1 + |j|)^{-2}` is summable on `ℤ`. -/
theorem summable_int_one_add_abs_neg_two :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ (-2 : ℝ)) := by
  have hsum : Summable (fun j : ℤ => (1 : ℝ) / |(j : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr (by norm_num)
  refine Summable.of_nonneg_of_le (f := fun j : ℤ => (1 : ℝ) / |(j : ℝ) + 1 / 2| ^ (2 : ℝ))
    (g := fun j : ℤ => (1 + |(j : ℝ)|) ^ (-2 : ℝ))
    (fun j => Real.rpow_nonneg (by positivity) _) (fun j => ?_) hsum
  have hsq : |(j : ℝ) + 1 / 2| ≤ 1 + |(j : ℝ)| := by
    calc |(j : ℝ) + 1 / 2| ≤ |(j : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ = |(j : ℝ)| + 1 / 2 := by norm_num
      _ ≤ 1 + |(j : ℝ)| := by linarith
  have e1 : (1 + |(j : ℝ)|) ^ (-2 : ℝ) = ((1 + |(j : ℝ)|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |(j : ℝ)|), Real.rpow_two]
  have e2 : (1 : ℝ) / |(j : ℝ) + 1 / 2| ^ (2 : ℝ) = (|(j : ℝ) + 1 / 2| ^ 2)⁻¹ := by
    rw [one_div, Real.rpow_two]
  rw [e1, e2]
  have hpos : (0 : ℝ) < |(j : ℝ) + 1 / 2| := by
    rcases (by omega : j ≤ -1 ∨ 0 ≤ j) with hj | hj
    · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast hj
      have hneg : (j : ℝ) + 1 / 2 ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
    · have hj' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hnn : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 := by linarith
      rw [abs_of_nonneg hnn]
      linarith
  refine (inv_le_inv₀ (by positivity : (0 : ℝ) < (1 + |(j : ℝ)|) ^ 2)
    (pow_pos hpos 2)).mpr ?_
  nlinarith [abs_nonneg ((j : ℝ) + 1 / 2), hsq]

/-- For `σ ≥ 1` and real `t`: `(1 + |t|/σ)^{-2} ≤ σ² (1 + |t|)^{-2}`. -/
theorem one_add_div_rpow_neg_two_le (σ : ℝ) (hσ : 1 ≤ σ) (t : ℝ) :
    (1 + |t| / σ) ^ (-2 : ℝ) ≤ σ ^ 2 * (1 + |t|) ^ (-2 : ℝ) := by
  have hσpos : 0 < σ := by linarith
  have h1 : (1 + |t|) / σ ≤ 1 + |t| / σ := by
    rw [div_le_iff₀ hσpos, mul_comm (1 + |t| / σ) σ, mul_add, mul_one]
    have h3 : σ * (|t| / σ) = |t| := by field_simp
    rw [h3]
    nlinarith [abs_nonneg t]
  have hA : (0 : ℝ) < 1 + |t| := by linarith [abs_nonneg t]
  have h2 : (0 : ℝ) < (1 + |t|) / σ := div_pos hA hσpos
  have e1 : ((1 + |t|) / σ) ^ (-2 : ℝ) = (((1 + |t|) / σ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_two]
  have e2 : (1 + |t|) ^ (-2 : ℝ) = ((1 + |t|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hA), Real.rpow_two]
  calc (1 + |t| / σ) ^ (-2 : ℝ) ≤ ((1 + |t|) / σ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos h2 h1 (by norm_num)
    _ = σ ^ 2 * (1 + |t|) ^ (-2 : ℝ) := by
        rw [e1, e2]
        field_simp

/-- For a `2`-lacunary scale sequence with `1 ≤ σ n`, the sum of the reciprocal scales over any
finite index set is at most `2`. -/
theorem sum_inv_scale_le_two (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ) :
    ∑ n ∈ U, ((σ n : ℝ))⁻¹ ≤ 2 := by
  have hpow : ∀ n : ℕ, 2 ^ n ≤ σ n := by
    intro n
    induction n with
    | zero => simpa using hσ1 0
    | succ k ih =>
        have h2 : 2 * 2 ^ k ≤ σ (k + 1) := le_trans (Nat.mul_le_mul_left 2 ih) (hσ2 k)
        calc 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
          _ ≤ σ (k + 1) := h2
  have hgeom : ∑ n ∈ U, ((2 : ℝ) ^ n)⁻¹ ≤ 2 := by
    have hsum : Summable (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) := by
      simpa only [one_div, inv_pow] using
        summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hle := hsum.sum_le_tsum U (fun n _ => inv_nonneg.mpr (pow_nonneg (by norm_num) n))
    have hval : (∑' n : ℕ, ((2 : ℝ) ^ n)⁻¹) = 2 := by
      rw [show (∑' n : ℕ, ((2 : ℝ) ^ n)⁻¹) = ∑' n : ℕ, (1 / 2 : ℝ) ^ n from
        tsum_congr fun n => by rw [one_div, inv_pow]]
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [hval] at hle
    exact hle
  refine (Finset.sum_le_sum fun n _ => ?_).trans hgeom
  have h1 : (2 : ℝ) ^ n ≤ ((σ n : ℕ) : ℝ) := by exact_mod_cast hpow n
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [inv_le_inv₀ (scale_pos hσ1 n) h2]
  exact h1

/-- The triangular (Fejér) kernel at the dyadic level `lacLev σ n` is at most `2/σ n`. -/
theorem triKernel_lacLev_le (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) (j : ℤ) :
    Work.Analysis.Hilbert.triKernel (lacLev σ n) j ≤ 2 * ((σ n : ℝ))⁻¹ := by
  have hLpos : (0 : ℝ) < (2 : ℝ) ^ (lacLev σ n) := by positivity
  have h1 : Work.Analysis.Hilbert.triKernel (lacLev σ n) j ≤ ((2 : ℝ) ^ (lacLev σ n))⁻¹ := by
    rw [Work.Analysis.Hilbert.triKernel]
    refine max_le ?_ ?_
    · positivity
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * lacLev σ n))]
      have hpow : (2 : ℝ) ^ (2 * lacLev σ n)
          = (2 : ℝ) ^ (lacLev σ n) * (2 : ℝ) ^ (lacLev σ n) := by
        rw [← pow_add]
        ring_nf
      rw [hpow, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hLpos), one_mul]
      linarith [abs_nonneg (j : ℝ)]
  refine h1.trans ?_
  have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := scale_pos hσ1 n
  have hle : ((σ n : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (lacLev σ n) := by
    have h3 : σ n ≤ 2 ^ (lacLev σ n + 1) := le_two_pow_lacLev (σ := σ) n
    have h2 : (σ n : ℝ) ≤ (2 : ℝ) ^ (lacLev σ n + 1) := by
      calc (σ n : ℝ) = ((σ n : ℕ) : ℝ) := rfl
        _ ≤ (((2 : ℕ) ^ (lacLev σ n + 1) : ℕ) : ℝ) := by exact_mod_cast h3
        _ = (2 : ℝ) ^ (lacLev σ n + 1) := by push_cast; ring
    rw [pow_succ] at h2
    linarith
  calc ((2 : ℝ) ^ (lacLev σ n))⁻¹ ≤ (2 / ((σ n : ℕ) : ℝ)) := by
        rw [inv_le_comm₀ hLpos (div_pos two_pos hσpos)]
        rw [inv_div]
        linarith
    _ = 2 * (((σ n : ℕ) : ℝ))⁻¹ := by rw [div_eq_mul_inv]

/-! ## The pointwise decay of the deviation kernel -/

/-- The bump part of the deviation kernel: `‖(1/σ) K (j/σ)‖ ≤ B σ⁻¹ W` with
`W = (1 + |j|/σ)^{-2}`. -/
lemma bumpKern_norm_le (K : SchwartzMap ℝ ℂ) {B : ℝ}
    (hB : ∀ x : ℝ, ‖K x‖ ≤ B * (1 + |x|) ^ (-2 : ℝ))
    (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) (j : ℤ) :
    ‖bumpKern K σ n j‖
      ≤ B * ((σ n : ℝ))⁻¹ * (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) := by
  have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := scale_pos hσ1 n
  have h := hB ((j : ℝ) / ((σ n : ℕ) : ℝ))
  have hfeq : (1 + |(j : ℝ) / ((σ n : ℕ) : ℝ)|) = (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hσpos]
  rw [hfeq] at h
  rw [bumpKern, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hσpos.le, one_div]
  calc (((σ n : ℕ) : ℝ))⁻¹ * ‖K ((j : ℝ) / ((σ n : ℕ) : ℝ))‖
      ≤ (((σ n : ℕ) : ℝ))⁻¹ * (B * (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hσpos.le)
    _ = B * (((σ n : ℕ) : ℝ))⁻¹ * (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) ^ (-2 : ℝ) := by ring

/-- **Schwartz decay of the deviation kernel**: at scale `σ n` the kernel `devKern` is bounded by
a constant times `(1/σ n) (1 + |j|/σ n)^{-2}`. -/
theorem devKern_norm_le (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → ∀ n (j : ℤ),
      ‖devKern K σ n j‖ ≤ A * ((σ n : ℝ))⁻¹ * (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real K 2
  refine ⟨B + 18 * ‖lacConst K‖ + 1, by positivity, ?_⟩
  intro σ hσ1 n j
  have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := scale_pos hσ1 n
  have hinv : (0 : ℝ) ≤ (((σ n : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr hσpos.le
  set W : ℝ := (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) ^ (-2 : ℝ) with hW
  have hWnn : (0 : ℝ) ≤ W := by rw [hW]; positivity
  have hWpos : (0 : ℝ) < W := by rw [hW]; positivity
  have hbump := bumpKern_norm_le K hB σ hσ1 n j
  have htri : ‖(((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)‖
      ≤ 2 * (((σ n : ℕ) : ℝ))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤
      Work.Analysis.Hilbert.triKernel (lacLev σ n) j from le_max_left _ _)]
    exact triKernel_lacLev_le σ hσ1 n j
  by_cases hcase : |(j : ℝ)| ≤ (2 : ℝ) ^ (lacLev σ n)
  · have hW9 : (1 / 9 : ℝ) ≤ W := by
      rw [hW]
      have h2 : (2 : ℝ) ^ (lacLev σ n) ≤ 2 * ((σ n : ℕ) : ℝ) := by
        exact_mod_cast pow_lacLev_le hσ1 n
      have h3 : (1 : ℝ) + |(j : ℝ)| / ((σ n : ℕ) : ℝ) ≤ 3 := by
        have h4 : |(j : ℝ)| / ((σ n : ℕ) : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hσpos]
          linarith [hcase, h2]
        linarith
      have h5 : (0 : ℝ) < 1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ) := by
        have := div_nonneg (abs_nonneg (j : ℝ)) hσpos.le
        linarith
      calc (1 / 9 : ℝ) = (3 : ℝ) ^ (-2 : ℝ) := by norm_num
        _ ≤ (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos h5 h3 (by norm_num)
    have hstep : ‖lacConst K
        * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)‖
        ≤ 18 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ))⁻¹ * W := by
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left htri (norm_nonneg _)).trans ?_
      have h2 : (2 : ℝ) * (((σ n : ℕ) : ℝ))⁻¹
          ≤ (18 * (((σ n : ℕ) : ℝ))⁻¹) * W := by
        have h6 : (2 : ℝ) * (((σ n : ℕ) : ℝ))⁻¹ = 18 * (((σ n : ℕ) : ℝ))⁻¹ * (1 / 9) := by ring
        rw [h6]
        exact mul_le_mul_of_nonneg_left hW9 (by positivity)
      calc ‖lacConst K‖ * (2 * (((σ n : ℕ) : ℝ))⁻¹)
          ≤ ‖lacConst K‖ * ((18 * (((σ n : ℕ) : ℝ))⁻¹) * W) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = 18 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ))⁻¹ * W := by ring
    have hdec : ‖devKern K σ n j‖ ≤ ‖bumpKern K σ n j‖
        + ‖lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)‖ := by
      rw [devKern]
      exact norm_sub_le _ _
    calc ‖devKern K σ n j‖
        ≤ B * (((σ n : ℕ) : ℝ))⁻¹ * W
          + 18 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ))⁻¹ * W :=
          hdec.trans (add_le_add hbump hstep)
      _ = (B + 18 * ‖lacConst K‖) * (((σ n : ℕ) : ℝ))⁻¹ * W := by ring
      _ ≤ (B + 18 * ‖lacConst K‖ + 1) * (((σ n : ℕ) : ℝ))⁻¹ * W := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hinv) hWnn
          linarith [norm_nonneg (lacConst K)]
      _ = (B + 18 * ‖lacConst K‖ + 1) * ((σ n : ℝ))⁻¹
            * (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) := by rw [hW]
  · have htri0 : Work.Analysis.Hilbert.triKernel (lacLev σ n) j = 0 := by
      refine triKernel_eq_zero_of_abs (lacLev σ n) ?_
      have h' : (((2 : ℤ) ^ (lacLev σ n) : ℤ) : ℝ) = (2 : ℝ) ^ (lacLev σ n) := by
        push_cast
        ring
      rw [h']
      exact not_le.mp hcase
    have hdev : devKern K σ n j = bumpKern K σ n j := by
      rw [devKern, htri0]
      simp
    rw [hdev]
    refine hbump.trans ?_
    have h7 : B ≤ B + 18 * ‖lacConst K‖ + 1 := by linarith [norm_nonneg (lacConst K)]
    calc B * (((σ n : ℕ) : ℝ))⁻¹ * W
        ≤ (B + 18 * ‖lacConst K‖ + 1) * (((σ n : ℕ) : ℝ))⁻¹ * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h7 hinv) hWnn
      _ = (B + 18 * ‖lacConst K‖ + 1) * ((σ n : ℝ))⁻¹
            * (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) := by rw [hW]

/-! ## Summability of the sampled bump kernel and of the deviation kernel -/

/-- The sampled bump kernel at scale `σ n ≥ 1` is summable. -/
theorem bumpKern_summable (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) :
    Summable (bumpKern K σ n) := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real K 2
  have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := scale_pos hσ1 n
  have hσne : ((σ n : ℕ) : ℝ) ≠ 0 := ne_of_gt hσpos
  refine Summable.of_norm_bounded (f := bumpKern K σ n)
    (g := fun j : ℤ => B * ((σ n : ℕ) : ℝ) * (1 + |(j : ℝ)|) ^ (-2 : ℝ)) ?_ ?_
  · exact summable_int_one_add_abs_neg_two.mul_left _
  · intro j
    have h := hB ((j : ℝ) / ((σ n : ℕ) : ℝ))
    have hfeq : (1 + |(j : ℝ) / ((σ n : ℕ) : ℝ)|) = (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) := by
      rw [abs_div, abs_of_pos hσpos]
    rw [hfeq] at h
    rw [bumpKern, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hσpos.le, one_div]
    have hnn : (0 : ℝ) ≤ (((σ n : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr hσpos.le
    calc (((σ n : ℕ) : ℝ))⁻¹ * ‖K ((j : ℝ) / ((σ n : ℕ) : ℝ))‖
        ≤ (((σ n : ℕ) : ℝ))⁻¹
            * (B * (1 + |(j : ℝ)| / ((σ n : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h hnn
      _ ≤ (((σ n : ℕ) : ℝ))⁻¹
            * (B * (((σ n : ℕ) : ℝ) ^ 2 * (1 + |(j : ℝ)|) ^ (-2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hBpos.le) hnn
          exact one_add_div_rpow_neg_two_le _ (by exact_mod_cast hσ1 n) _
      _ = B * ((σ n : ℕ) : ℝ) * (1 + |(j : ℝ)|) ^ (-2 : ℝ) := by
          field_simp

/-- The deviation kernel at scale `σ n ≥ 1` is summable. -/
theorem devKern_summable (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) :
    Summable (devKern K σ n) := by
  have hb := bumpKern_summable K σ hσ1 n
  have ht : Summable (fun j : ℤ => lacConst K
      * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) := by
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-((2 : ℤ) ^ (lacLev σ n))) ((2 : ℤ) ^ (lacLev σ n))) ?_
    intro j hj
    rw [triKernel_eq_zero_of_notMem (lacLev σ n) hj]
    simp
  have hsub : Summable (fun j : ℤ => bumpKern K σ n j
      - lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) := hb.sub ht
  exact hsub


/-- A summable sequence multiplied pointwise by a bounded sequence shifted by `x` is summable. -/
lemma summable_mul_bounded (g : ℤ → ℂ) (hg : Summable g) (f : ℤ → ℂ) (M : ℝ)
    (hM : ∀ x : ℤ, ‖f x‖ ≤ M) (x : ℤ) : Summable (fun j : ℤ => g j * f (x - j)) := by
  have hnorm : Summable (fun j : ℤ => ‖g j‖ * M) := hg.norm.mul_right M
  have hle : ∀ j : ℤ, ‖g j * f (x - j)‖ ≤ ‖g j‖ * M := by
    intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM (x - j)) (norm_nonneg _)
  have hsum2 : Summable (fun j : ℤ => ‖g j * f (x - j)‖) :=
    Summable.of_nonneg_of_le (f := fun j : ℤ => ‖g j‖ * M)
      (g := fun j : ℤ => ‖g j * f (x - j)‖) (fun j => norm_nonneg _) hle hnorm
  exact hsum2.of_norm

/-! ## The deviation operator as a kernel convolution -/

/-- The `n`-th deviation operator is the convolution with the deviation kernel (for bounded `f`,
the case in which the `tsum` converges absolutely). -/
theorem devOp_eq_tsum (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ)
    (f : ℤ → ℂ) (hf : ∃ M : ℝ, ∀ x : ℤ, ‖f x‖ ≤ M) (x : ℤ) :
    devOp K σ n f x = ∑' j : ℤ, devKern K σ n j * f (x - j) := by
  obtain ⟨M, hM⟩ := hf
  have hb : Summable (fun j : ℤ => bumpKern K σ n j * f (x - j)) :=
    summable_mul_bounded (bumpKern K σ n) (bumpKern_summable K σ hσ1 n) f M hM x
  have ht : Summable (fun j : ℤ =>
      (lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) * f (x - j)) := by
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-((2 : ℤ) ^ (lacLev σ n))) ((2 : ℤ) ^ (lacLev σ n))) ?_
    intro j hj
    rw [triKernel_eq_zero_of_notMem (lacLev σ n) hj]
    simp
  have hbump : bumpOp K σ n f x = ∑' j : ℤ, bumpKern K σ n j * f (x - j) := by
    rw [bumpOp]
    exact tsum_congr fun j => by rw [bumpKern]
  have htri : triSmooth σ n f x =
      ∑' j : ℤ, (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ) * f (x - j) := by
    rw [triSmooth, Work.Analysis.Hilbert.triConv]
    exact (tsum_eq_sum (s := Finset.Icc (-((2 : ℤ) ^ (lacLev σ n))) ((2 : ℤ) ^ (lacLev σ n)))
      (fun j hj => by rw [triKernel_eq_zero_of_notMem (lacLev σ n) hj]; simp)).symm
  have hscale : lacConst K
        * (∑' j : ℤ, (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ) * f (x - j))
      = ∑' j : ℤ, (lacConst K
          * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) * f (x - j) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [devOp, hbump, htri, hscale]
  calc (∑' j : ℤ, bumpKern K σ n j * f (x - j))
        - (∑' j : ℤ, (lacConst K
            * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) * f (x - j))
      = ∑' j : ℤ, (bumpKern K σ n j * f (x - j)
          - (lacConst K
            * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℝ)) : ℂ)) * f (x - j)) :=
        (Summable.tsum_sub hb ht).symm
    _ = ∑' j : ℤ, devKern K σ n j * f (x - j) := by
        refine tsum_congr fun j => ?_
        rw [devKern]
        ring

/-! ## Uniform bounds and the convolution identity for the signed sums -/

/-- The signed-sum kernel is uniformly bounded. -/
theorem lacDevLin_norm_le (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (j : ℤ), ‖lacDevLin K σ U ω j‖ ≤ B := by
  obtain ⟨A, hApos, hA⟩ := devKern_norm_le K
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2 U ω j
  have hW1 : ∀ n : ℕ, (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) ≤ 1 := by
    intro n
    have h1 : (1 : ℝ) ≤ 1 + |(j : ℝ)| / (σ n : ℝ) := by
      have := div_nonneg (abs_nonneg (j : ℝ)) (scale_pos hσ1 n).le
      linarith
    calc (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ) ≤ (1 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by norm_num)
      _ = 1 := by norm_num
  have hstep : ∑ n ∈ U, ‖devKern K σ n j‖ ≤ ∑ n ∈ U, A * ((σ n : ℝ))⁻¹ := by
    refine Finset.sum_le_sum fun n _ => ?_
    refine (hA σ hσ1 n j).trans ?_
    calc A * ((σ n : ℝ))⁻¹ * (1 + |(j : ℝ)| / (σ n : ℝ)) ^ (-2 : ℝ)
        ≤ A * ((σ n : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hW1 n)
            (mul_nonneg hApos.le (inv_nonneg.mpr (scale_pos hσ1 n).le))
      _ = A * ((σ n : ℝ))⁻¹ := by ring
  calc ‖lacDevLin K σ U ω j‖
      = ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devKern K σ n j‖ := rfl
    _ ≤ ∑ n ∈ U, ‖devKern K σ n j‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun n _ => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
    _ ≤ ∑ n ∈ U, A * ((σ n : ℝ))⁻¹ := hstep
    _ = A * ∑ n ∈ U, ((σ n : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ A * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_scale_le_two σ hσ1 hσ2 U) hApos.le
    _ ≤ 2 * A + 1 := by linarith

/-- The signed sum of the deviation operators is the convolution with the signed-sum kernel. -/
theorem lacDevLin_conv (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ) (hf : ∃ M : ℝ, ∀ x : ℤ, ‖f x‖ ≤ M) (x : ℤ) :
    (∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devOp K σ n f x)
      = ∑' j : ℤ, lacDevLin K σ U ω j * f (x - j) := by
  obtain ⟨M, hM⟩ := hf
  have hsum : ∀ n ∈ U, Summable (fun j : ℤ =>
      Work.KMTAreas.ADev.bSign ω n * (devKern K σ n j * f (x - j))) := by
    intro n _
    exact (summable_mul_bounded (devKern K σ n) (devKern_summable K σ hσ1 n) f M hM x).mul_left _
  calc (∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devOp K σ n f x)
      = ∑ n ∈ U, ∑' j : ℤ, Work.KMTAreas.ADev.bSign ω n
          * (devKern K σ n j * f (x - j)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [devOp_eq_tsum K σ hσ1 n f ⟨M, hM⟩ x, ← tsum_mul_left]
        try exact tsum_congr fun j => by ring
    _ = ∑' j : ℤ, ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (devKern K σ n j * f (x - j)) :=
        (Summable.tsum_finsetSum (fun n hn => hsum n hn)).symm
    _ = ∑' j : ℤ, (∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devKern K σ n j) * f (x - j) := by
        refine tsum_congr fun j => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = ∑' j : ℤ, lacDevLin K σ U ω j * f (x - j) := rfl

end

end Work.KMTAreas.A7
