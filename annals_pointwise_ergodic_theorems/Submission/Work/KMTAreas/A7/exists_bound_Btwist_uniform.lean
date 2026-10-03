/-
# A uniform-in-`t` bound for the twisted bilinear multiplier `Btwist`

This module proves `Work.KMTAreas.A7.exists_bound_Btwist_uniform`: if the Fourier coefficients
`cw m₁`, `cw m₂` of the two one-variable symbols decay at least quadratically, and the two `t`-dependent
inputs `h t`, `k t` are uniformly bounded on `t ∈ [1/2,1]`, then the twisted bilinear multiplier

  `Btwist ρ P l₁ l₂ m₁ m₂ (h t) (k t) x = ∑' j₁, ∑' j₂, K(j₁,j₂) · h t (x-j₁) · k t (x-j₂)`

is bounded uniformly in `t`.

The proof is the elementary double-series estimate.  The arithmetic kernel
`K(j₁,j₂) = arithKernel ρ P Q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂` is bounded by the constant
`#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}` (`arithKernel` is a *finite* double sum of terms of modulus at most
one), and the two remaining factors are controlled by the decay hypothesis and the uniform
`ℓ^∞`-bounds.  The double series is then dominated by

  `#A₁ · #A₂ · Cd₁ · Cd₂ · Ch · Ck · (∑_j 1/(1+j²))²`,

which is finite by `Work.KMTAreas.tsum_inv_sq_shift_le`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## The arithmetic symbol and kernel are uniformly bounded -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one, hence has
modulus at most one. -/
private lemma kmtMz_norm_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- The uniform bound on the arithmetic kernel: the cardinality of the arithmetic frequency sets
`(ℚ/ℤ)_{≤l₁}`, `(ℚ/ℤ)_{≤l₂}`. -/
private def kmtKernB (ρ : ℝ) (l₁ l₂ : ℕ) : ℝ :=
  ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)

private lemma kmtKernB_nonneg (ρ : ℝ) (l₁ l₂ : ℕ) : 0 ≤ kmtKernB ρ l₁ l₂ :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma kmtArithKernel_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ ≤ kmtKernB ρ l₁ l₂ := by
  unfold arithKernel kmtKernB
  calc ‖∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
          * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ‖∑ α₂ ∈ iwArithFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ iwArithFreqs ρ l₁, ∑ _α₂ ∈ iwArithFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact kmtMz_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The kernel of `Btwist` and its summability -/

/-- The kernel of the twisted bilinear multiplier, as a function of the two summation variables. -/
private def kmtBtwK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

private theorem kmtBtwist_eq (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (a b : ℤ → ℂ) (x : ℤ) :
    Btwist ρ P l₁ l₂ m₁ m₂ a b x
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂) := rfl

private lemma kmtBtwK_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (j₁ j₂ : ℤ) :
    ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂‖ ≤ kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖ := by
  have hk := kmtArithKernel_norm_le ρ P l₁ l₂ j₁ j₂
  have hKB := kmtKernB_nonneg ρ l₁ l₂
  unfold kmtBtwK
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hk le_rfl (norm_nonneg _) hKB) le_rfl (norm_nonneg _)
    (mul_nonneg hKB (norm_nonneg _))

/-- `‖z₁ z₂ z₃‖ ≤ Z₁ Z₂ Z₃` for `‖zᵢ‖ ≤ Zᵢ`. -/
private lemma kmtNorm_mul_mul_le {z₁ z₂ z₃ : ℂ} {Z₁ Z₂ Z₃ : ℝ} (h₁ : ‖z₁‖ ≤ Z₁)
    (h₂ : ‖z₂‖ ≤ Z₂) (h₃ : ‖z₃‖ ≤ Z₃) : ‖z₁ * z₂ * z₃‖ ≤ Z₁ * Z₂ * Z₃ := by
  have h₁' : 0 ≤ Z₁ := le_trans (norm_nonneg z₁) h₁
  have h₂' : 0 ≤ Z₂ := le_trans (norm_nonneg z₂) h₂
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) h₁') h₃ (norm_nonneg _)
    (mul_nonneg h₁' h₂')

/-- **Absolute summability of an iterated series.**  If `‖F j₁ j₂‖ ≤ G j₁ · H j₂` with `G`, `H`
summable, then `j₁ ↦ ∑' j₂, F j₁ j₂` is summable. -/
private lemma kmtSummable_tsum_of_bound {F : ℤ → ℤ → ℂ} {G H : ℤ → ℝ}
    (hG : Summable G) (hH : Summable H) (hF : ∀ j₁ j₂, ‖F j₁ j₂‖ ≤ G j₁ * H j₂) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ, F j₁ j₂) := by
  have hnorm : ∀ j₁ : ℤ, Summable (fun j₂ : ℤ => ‖F j₁ j₂‖) := fun j₁ =>
    Summable.of_nonneg_of_le (fun j₂ => norm_nonneg _) (fun j₂ => hF j₁ j₂)
      (hH.mul_left (G j₁))
  refine Summable.of_norm_bounded (g := fun j₁ : ℤ => G j₁ * (∑' j₂ : ℤ, H j₂))
    (hG.mul_right _) (fun j₁ => ?_)
  calc ‖∑' j₂ : ℤ, F j₁ j₂‖ ≤ ∑' j₂ : ℤ, ‖F j₁ j₂‖ := norm_tsum_le_tsum_norm (hnorm j₁)
    _ ≤ ∑' j₂ : ℤ, G j₁ * H j₂ :=
        Summable.tsum_le_tsum (fun j₂ => hF j₁ j₂) (hnorm j₁) (hH.mul_left (G j₁))
    _ = G j₁ * ∑' j₂ : ℤ, H j₂ := tsum_mul_left

/-- Summability of the inner series of `Btwist` in the second summation variable. -/
private lemma kmtBtwist_inner_summable (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x j₁ : ℤ) :
    Summable (fun j₂ : ℤ => kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine Summable.of_norm_bounded
    (g := fun j₂ : ℤ => (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖)
    (hm₂.mul_left _) (fun j₂ => ?_)
  calc ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
      ≤ (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
        kmtNorm_mul_mul_le (kmtBtwK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂) (ha _) (hb _)
    _ = (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-- **Absolute summability of the iterated series defining `Btwist`.** -/
private lemma kmtBtwist_summable_of_bounded (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x : ℤ) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁)
      * b (x - j₂)) := by
  refine kmtSummable_tsum_of_bound (G := fun j₁ : ℤ => kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb)
    (H := fun j₂ : ℤ => ‖cw m₂ j₂‖) ?_ hm₂ ?_
  · exact ((hm₁.mul_left (kmtKernB ρ l₁ l₂)).mul_right Ca).mul_right Cb
  · intro j₁ j₂
    calc ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
        ≤ (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
          kmtNorm_mul_mul_le (kmtBtwK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂) (ha _) (hb _)
      _ = (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-! ## The uniform bound -/

theorem exists_bound_Btwist_uniform (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℝ → ℤ → ℂ) (x : ℤ)
    (hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hb₁ : ∃ Ch : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ, ‖h t y‖ ≤ Ch)
    (hb₂ : ∃ Ck : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ, ‖k t y‖ ≤ Ck) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (h t) (k t) x‖ ≤ C := by
  classical
  obtain ⟨Cd₁, hd₁⟩ := hdec₁
  obtain ⟨Cd₂, hd₂⟩ := hdec₂
  obtain ⟨Ch, hh⟩ := hb₁
  obtain ⟨Ck, hk⟩ := hb₂
  -- the constants are non-negative (evaluate the bounds at `j = 0`, resp. `t = 1/2`, `y = 0`)
  have hCd₁ : 0 ≤ Cd₁ := by
    have h0 : ‖cw m₁ 0‖ ≤ Cd₁ := by simpa using hd₁ 0
    exact le_trans (norm_nonneg _) h0
  have hCd₂ : 0 ≤ Cd₂ := by
    have h0 : ‖cw m₂ 0‖ ≤ Cd₂ := by simpa using hd₂ 0
    exact le_trans (norm_nonneg _) h0
  have hCh : 0 ≤ Ch :=
    le_trans (norm_nonneg _) (hh (1/2) (by constructor <;> norm_num) 0)
  have hCk : 0 ≤ Ck :=
    le_trans (norm_nonneg _) (hk (1/2) (by constructor <;> norm_num) 0)
  -- the summability weight `g j = 1/(1+j²)` and its total mass `SG`
  set g : ℤ → ℝ := fun j => 1 / (1 + (j : ℝ) ^ 2) with hg
  obtain ⟨B, hB0, hBfun⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  have hg_sum : Summable g := by
    rw [hg]; simpa using (hBfun 0).1
  set SG : ℝ := ∑' j : ℤ, g j with hSG
  have hSG_nonneg : 0 ≤ SG := by
    rw [hSG]
    refine tsum_nonneg (fun j => ?_)
    rw [hg]
    positivity
  have hSM₂_le : (∑' j : ℤ, ‖cw m₂ j‖) ≤ Cd₂ * SG := by
    have hle : ∀ j : ℤ, ‖cw m₂ j‖ ≤ Cd₂ * g j := by
      intro j
      have hstep : (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 ≤ g j := by
        rw [hg]
        apply one_div_le_one_div_of_le (a := 1 + (j : ℝ) ^ 2) (b := (1 + |(j : ℝ)|) ^ 2)
        · nlinarith [sq_nonneg (j : ℝ)]
        · nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
      calc ‖cw m₂ j‖ ≤ Cd₂ / (1 + |(j : ℝ)|) ^ 2 := hd₂ j
        _ = Cd₂ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
        _ ≤ Cd₂ * g j := mul_le_mul_of_nonneg_left hstep hCd₂
    calc ∑' j : ℤ, ‖cw m₂ j‖ ≤ ∑' j : ℤ, Cd₂ * g j :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle
            (hg_sum.mul_left Cd₂)) (hg_sum.mul_left Cd₂)
      _ = Cd₂ * SG := by rw [hSG]; exact tsum_mul_left
  have hSM₂_nonneg : 0 ≤ ∑' j : ℤ, ‖cw m₂ j‖ :=
    tsum_nonneg (fun j => norm_nonneg _)
  have hSM₁_le : (∑' j : ℤ, ‖cw m₁ j‖) ≤ Cd₁ * SG := by
    have hle : ∀ j : ℤ, ‖cw m₁ j‖ ≤ Cd₁ * g j := by
      intro j
      have hstep : (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 ≤ g j := by
        rw [hg]
        apply one_div_le_one_div_of_le (a := 1 + (j : ℝ) ^ 2) (b := (1 + |(j : ℝ)|) ^ 2)
        · nlinarith [sq_nonneg (j : ℝ)]
        · nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
      calc ‖cw m₁ j‖ ≤ Cd₁ / (1 + |(j : ℝ)|) ^ 2 := hd₁ j
        _ = Cd₁ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
        _ ≤ Cd₁ * g j := mul_le_mul_of_nonneg_left hstep hCd₁
    calc ∑' j : ℤ, ‖cw m₁ j‖ ≤ ∑' j : ℤ, Cd₁ * g j :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle
            (hg_sum.mul_left Cd₁)) (hg_sum.mul_left Cd₁)
      _ = Cd₁ * SG := by rw [hSG]; exact tsum_mul_left
  have hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => by
        have hstep : (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 ≤ g j := by
          rw [hg]
          apply one_div_le_one_div_of_le (a := 1 + (j : ℝ) ^ 2) (b := (1 + |(j : ℝ)|) ^ 2)
          · nlinarith [sq_nonneg (j : ℝ)]
          · nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
        calc ‖cw m₁ j‖ ≤ Cd₁ / (1 + |(j : ℝ)|) ^ 2 := hd₁ j
          _ = Cd₁ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
          _ ≤ Cd₁ * g j := mul_le_mul_of_nonneg_left hstep hCd₁)
      (hg_sum.mul_left Cd₁)
  have hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => by
        have hstep : (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 ≤ g j := by
          rw [hg]
          apply one_div_le_one_div_of_le (a := 1 + (j : ℝ) ^ 2) (b := (1 + |(j : ℝ)|) ^ 2)
          · nlinarith [sq_nonneg (j : ℝ)]
          · nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
        calc ‖cw m₂ j‖ ≤ Cd₂ / (1 + |(j : ℝ)|) ^ 2 := hd₂ j
          _ = Cd₂ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
          _ ≤ Cd₂ * g j := mul_le_mul_of_nonneg_left hstep hCd₂)
      (hg_sum.mul_left Cd₂)
  set SM₂ : ℝ := ∑' j : ℤ, ‖cw m₂ j‖ with hSM₂
  have hSM₂_le' : SM₂ ≤ Cd₂ * SG := by rw [hSM₂]; exact hSM₂_le
  have hSM₂_nonneg' : 0 ≤ SM₂ := by rw [hSM₂]; exact hSM₂_nonneg
  set Pc : ℝ := kmtKernB ρ l₁ l₂ * Ch * Ck * SM₂ with hPc
  have hPc_nonneg : 0 ≤ Pc := by
    rw [hPc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (kmtKernB_nonneg ρ l₁ l₂) hCh) hCk) hSM₂_nonneg'
  refine ⟨kmtKernB ρ l₁ l₂ * Ch * Ck * Cd₂ * Cd₁ * SG * SG, fun t ht => ?_⟩
  have ha : ∀ y : ℤ, ‖h t y‖ ≤ Ch := fun y => hh t ht y
  have hb : ∀ y : ℤ, ‖k t y‖ ≤ Ck := fun y => hk t ht y
  have hsumOuter : Summable (fun j₁ : ℤ =>
      ∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)) :=
    kmtBtwist_summable_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂ (h t) (k t) ha hb x
  have hinner : ∀ j₁ : ℤ,
      ‖∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖
        ≤ Pc * ‖cw m₁ j₁‖ := by
    intro j₁
    have hinnerSum : Summable (fun j₂ : ℤ =>
        kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)) :=
      kmtBtwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ (h t) (k t) ha hb x j₁
    have hinnerNorm : Summable (fun j₂ : ℤ =>
        ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖) := hinnerSum.norm
    have hpt : ∀ j₂ : ℤ,
        ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖
          ≤ (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ := by
      intro j₂
      calc ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖
          ≤ (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ch * Ck :=
            kmtNorm_mul_mul_le (kmtBtwK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂) (ha _) (hb _)
        _ = (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ := by ring
    calc ‖∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖
        ≤ ∑' j₂ : ℤ, ‖kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖ :=
          norm_tsum_le_tsum_norm hinnerNorm
      _ ≤ ∑' j₂ : ℤ, (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ :=
          Summable.tsum_le_tsum hpt hinnerNorm (hm₂.mul_left _)
      _ = (kmtKernB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ch * Ck) * SM₂ := by
          rw [hSM₂]; exact tsum_mul_left
      _ = Pc * ‖cw m₁ j₁‖ := by rw [hPc]; ring
  calc ‖Btwist ρ P l₁ l₂ m₁ m₂ (h t) (k t) x‖
      = ‖∑' j₁ : ℤ, ∑' j₂ : ℤ,
          kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖ := by
        rw [kmtBtwist_eq]
    _ ≤ ∑' j₁ : ℤ,
          ‖∑' j₂ : ℤ, kmtBtwK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖ :=
        norm_tsum_le_tsum_norm hsumOuter.norm
    _ ≤ ∑' j₁ : ℤ, Pc * ‖cw m₁ j₁‖ :=
        Summable.tsum_le_tsum hinner hsumOuter.norm (hm₁.mul_left Pc)
    _ = Pc * (∑' j₁ : ℤ, ‖cw m₁ j₁‖) := tsum_mul_left
    _ ≤ Pc * (Cd₁ * SG) := mul_le_mul_of_nonneg_left hSM₁_le hPc_nonneg
    _ ≤ kmtKernB ρ l₁ l₂ * Ch * Ck * Cd₂ * Cd₁ * SG * SG := by
        rw [hPc]
        have h1 : kmtKernB ρ l₁ l₂ * Ch * Ck * SM₂ ≤ kmtKernB ρ l₁ l₂ * Ch * Ck * (Cd₂ * SG) :=
          mul_le_mul_of_nonneg_left hSM₂_le'
            (mul_nonneg (mul_nonneg (kmtKernB_nonneg ρ l₁ l₂) hCh) hCk)
        have h2 : (kmtKernB ρ l₁ l₂ * Ch * Ck * SM₂) * (Cd₁ * SG)
            ≤ (kmtKernB ρ l₁ l₂ * Ch * Ck * (Cd₂ * SG)) * (Cd₁ * SG) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hCd₁ hSG_nonneg)
        calc (kmtKernB ρ l₁ l₂ * Ch * Ck * SM₂) * (Cd₁ * SG)
            ≤ (kmtKernB ρ l₁ l₂ * Ch * Ck * (Cd₂ * SG)) * (Cd₁ * SG) := h2
          _ = kmtKernB ρ l₁ l₂ * Ch * Ck * Cd₂ * Cd₁ * SG * SG := by ring

end

end Work.KMTAreas.A7
