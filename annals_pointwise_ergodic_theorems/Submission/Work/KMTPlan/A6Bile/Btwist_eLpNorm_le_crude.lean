/-
# The crude `ℓ¹ → ℓ² × ℓ²` bound for the twisted bilinear multiplier `Btwist`

`Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k` is the bilinear convolution of `h` and `k` with the
kernel

  `K(j₁,j₂) = arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`,

where `arithKernel` is the *finite* double sum, over the arithmetic frequencies
`α₁ ∈ (ℚ/ℤ)_{≤l₁}`, `α₂ ∈ (ℚ/ℤ)_{≤l₂}`, of `m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)`.  Every summand has
modulus at most one (`‖m_Ẑ‖ ≤ 1` and the characters have modulus one), so

  `‖arithKernel …‖ ≤ #(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}`

uniformly in `j₁, j₂`.  Hence the kernel is dominated by
`#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂} · ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖`, whose `ℓ¹(ℤ²)` mass is
`#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂} · (∑'_j ‖cw m₁ j‖) · (∑'_j ‖cw m₂ j‖)`.

Young's inequality for the bilinear convolution (`Work.KMTAreas.A7.BilinOpLp` at
`(p,p₁,p₂) = (1,2,2)`) therefore gives

  `‖Btwist … h k‖_{ℓ¹} ≤ C ‖h‖_{ℓ²} ‖k‖_{ℓ²}`,

with `C` exactly the constant of the statement.  Finally, on `ℤ` with counting measure one has
`‖·‖_{ℓ^r} ≤ ‖·‖_{ℓ¹}` for every `r ≥ 1` (the terms of the `ℓ¹`-sum dominate the terms of the
`ℓ^r`-sum, since `a^r ≤ (∑ a)^r` for `a ≥ 0`), which upgrades the `ℓ¹` bound to the `ℓ^r` bound.

This is the *crude* (no gain) estimate for `Btwist` that the §8 model analysis uses for the
small scales; it is the `≤`-frequency counterpart of
`Work.KMTPlan.A6.exists_bound_BtwistEx_crude`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Bile

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

/-! ## The characters of the circle, and the arithmetic symbol -/

/-- The characters `x ↦ e(n x)` of the circle have modulus one. -/
private lemma norm_fourier_eq_one (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- The arithmetic symbol `m_Ẑ` is the average over `ℤ/qℤ` of a product of two characters, hence
has modulus at most one. -/
private lemma norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ]
  by_cases hq : q = 0
  · subst hq; simp
  · have hqr : (0 : ℝ) < q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
      exact_mod_cast h1
    have hsum : ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
        * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
      calc ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
          ≤ ∑ n ∈ Finset.range q, ‖fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [norm_mul, norm_fourier_eq_one, norm_fourier_eq_one, mul_one]
        _ = (q : ℝ) := by simp
    calc ‖(q : ℂ)⁻¹ * ∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        = ‖(q : ℂ)⁻¹‖ * ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := norm_mul _ _
      _ ≤ (q : ℝ)⁻¹ * (q : ℝ) := by
          rw [norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqr.le)
      _ = 1 := by field_simp

/-- **The arithmetic kernel of `Btwist` is bounded by the product of the two cardinalities** of
the arithmetic frequency sets: it is a double sum of `#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}` terms
`m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)` of modulus at most one. -/
private lemma norm_arithKernel_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
      ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)) := by
  rw [arithKernel]
  calc ‖∑ α₁ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        ∑ α₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          ‖∑ α₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
              * fourier (T := 1) (-j₂) α₂‖ := norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          ∑ α₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
              * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          ∑ _α₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        rw [norm_mul, norm_mul, norm_fourier_eq_one, norm_fourier_eq_one, mul_one, mul_one]
        exact norm_mZ_le_one P (arithQ ρ (max l₁ l₂)) a b
    _ = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The kernel of `Btwist` and Young's inequality -/

/-- The kernel of the twisted bilinear multiplier, as a function of the two summation
variables. -/
private def btwK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- `Btwist` is the bilinear convolution operator with kernel `btwK` (definitional). -/
private lemma btwist_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h k = bilinOp (btwK ρ P l₁ l₂ m₁ m₂) h k := rfl

/-- **The crude `ℓ¹` bound for `Btwist`**, with the exact constant of the target statement. -/
private theorem eLpNorm_btwist_one_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (h₁ : Summable (fun j : ℤ => ‖cw m₁ j‖))
    (h₂ : Summable (fun j : ℤ => ‖cw m₂ j‖)) (h k : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => Btwist ρ P l₁ l₂ m₁ m₂ h k x) 1
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)
            * (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
                * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)))
          * MeasureTheory.eLpNorm h 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          * MeasureTheory.eLpNorm k 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hprod : Summable fun q : ℤ × ℤ => ‖cw m₁ q.1‖ * ‖cw m₂ q.2‖ :=
    h₁.mul_of_nonneg h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hc0 : 0 ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
      * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by positivity
  have hpt : ∀ j₁ j₂ : ℤ, ‖btwK ρ P l₁ l₂ m₁ m₂ j₁ j₂‖
      ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
        * (‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) := by
    intro j₁ j₂
    have hK := norm_arithKernel_le ρ P l₁ l₂ j₁ j₂
    rw [btwK, norm_mul, norm_mul]
    calc ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ * ‖cw m₁ j₁‖
          * ‖cw m₂ j₂‖
        = ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
          * (‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) := by ring
      _ ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
          * (‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) :=
          mul_le_mul hK le_rfl (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc0
  have hmaj : Summable fun q : ℤ × ℤ =>
      (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
        * (‖cw m₁ q.1‖ * ‖cw m₂ q.2‖) := hprod.mul_left _
  have hKsum : Summable fun q : ℤ × ℤ => ‖btwK ρ P l₁ l₂ m₁ m₂ q.1 q.2‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hpt q.1 q.2) hmaj
  have hmass : ∑' q : ℤ × ℤ, ‖btwK ρ P l₁ l₂ m₁ m₂ q.1 q.2‖
      ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
        * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
    calc ∑' q : ℤ × ℤ, ‖btwK ρ P l₁ l₂ m₁ m₂ q.1 q.2‖
        ≤ ∑' q : ℤ × ℤ,
            (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
              * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
              * (‖cw m₁ q.1‖ * ‖cw m₂ q.2‖) :=
          Summable.tsum_le_tsum (fun q => hpt q.1 q.2) hKsum hmaj
      _ = (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
              * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
            * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
          rw [tsum_mul_left, h₁.tsum_mul_tsum h₂ hprod]
  rw [btwist_eq_bilinOp]
  refine (BilinOpLp (K := btwK ρ P l₁ l₂ m₁ m₂) (u := h) (v := k)
    (p := 1) (p₁ := 2) (p₂ := 2) ?_ le_rfl hKsum).trans ?_
  · rw [ENNReal.inv_two_add_inv_two, inv_one]
  · refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
    calc ∑' q : ℤ × ℤ, ‖btwK ρ P l₁ l₂ m₁ m₂ q.1 q.2‖
        ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
          * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := hmass
      _ = (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)
            * (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
                * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)) := by ring

/-! ## `ℓ^r ≤ ℓ¹` on `ℤ` with counting measure -/

/-- In `ℝ≥0∞`, the `q`-th power of the sum dominates the sum of the `q`-th powers, for `q ≥ 1`
(the discrete `ℓ^1 ⊆ ℓ^q` inclusion). -/
private lemma tsum_rpow_le_rpow_tsum {g : ℤ → ℝ≥0∞} {q : ℝ} (hq : 1 ≤ q) :
    (∑' n : ℤ, g n ^ q) ≤ (∑' n : ℤ, g n) ^ q := by
  have hq1 : 0 ≤ q - 1 := by linarith
  by_cases hS : (∑' n : ℤ, g n) = 0
  · have hzero : ∀ n, g n = 0 := fun n => le_antisymm (hS ▸ ENNReal.le_tsum n) (by simp)
    have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have h1 : (∑' n : ℤ, g n ^ q) = 0 := by
      have : ∀ n : ℤ, g n ^ q = (0 : ℝ≥0∞) := by
        intro n; rw [hzero n, ENNReal.zero_rpow_of_pos hq0]
      rw [tsum_congr this]; simp
    rw [h1, hS, ENNReal.zero_rpow_of_pos hq0]
  · have hterm : ∀ n : ℤ, g n ^ q ≤ g n * (∑' m : ℤ, g m) ^ (q - 1) := by
      intro n
      have hle : g n ≤ ∑' m : ℤ, g m := ENNReal.le_tsum n
      calc g n ^ q = g n ^ (1 + (q - 1)) := by congr 1; ring
        _ = g n ^ (1 : ℝ) * g n ^ (q - 1) :=
              ENNReal.rpow_add_of_nonneg 1 (q - 1) zero_le_one hq1
        _ = g n * g n ^ (q - 1) := by rw [ENNReal.rpow_one]
        _ ≤ g n * (∑' m : ℤ, g m) ^ (q - 1) :=
            mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hle hq1)
    calc (∑' n : ℤ, g n ^ q) ≤ ∑' n : ℤ, g n * (∑' m : ℤ, g m) ^ (q - 1) :=
          ENNReal.tsum_le_tsum hterm
      _ = (∑' n : ℤ, g n) * (∑' m : ℤ, g m) ^ (q - 1) := ENNReal.tsum_mul_right
      _ = (∑' n : ℤ, g n) ^ (1 : ℝ) * (∑' n : ℤ, g n) ^ (q - 1) := by rw [ENNReal.rpow_one]
      _ = (∑' n : ℤ, g n) ^ (1 + (q - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (q - 1) zero_le_one hq1).symm
      _ = (∑' n : ℤ, g n) ^ q := by congr 1; ring

/-- On `ℤ` with counting measure the `ℒ^p` seminorm is decreasing in `p`: for `1 ≤ p`,
`‖f‖_{ℓ^p} ≤ ‖f‖_{ℓ¹}`. -/
private lemma eLpNorm_count_le_eLpNorm_one {f : ℤ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ MeasureTheory.eLpNorm f 1 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by simp)
  have hq : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp
  have hqpos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hq
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
    MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count,
    MeasureTheory.lintegral_count]
  calc (∑' x : ℤ, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ ((∑' x : ℤ, ‖f x‖ₑ) ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow (tsum_rpow_le_rpow_tsum hq) (by positivity)
    _ = ∑' x : ℤ, ‖f x‖ₑ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hqpos), ENNReal.rpow_one]

/-! ## The crude bound -/

theorem Btwist_eLpNorm_le_crude (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (r : NNReal) (hr : 1 ≤ r)
    (h₁ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖))
    (h₂ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)) :
    ∀ (h k : ℤ → ℂ), MeasureTheory.MemLp h 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp k 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k x)
          (r : ENNReal) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖)
              * (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
                  * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)))
            * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm k 2 MeasureTheory.Measure.count := by
  intro h k _hh _hk
  refine (eLpNorm_count_le_eLpNorm_one (f := fun x : ℤ =>
      Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k x) ?_ ?_).trans
    (eLpNorm_btwist_one_le ρ P l₁ l₂ m₁ m₂ h₁ h₂ h k)
  · rw [← ENNReal.coe_one]; exact ENNReal.coe_le_coe.mpr hr
  · exact ENNReal.coe_ne_top

end

end Work.KMTPlan.A6Bile
