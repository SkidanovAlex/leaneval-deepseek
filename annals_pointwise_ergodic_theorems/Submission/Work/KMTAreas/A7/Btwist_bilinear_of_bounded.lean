/-
# Bilinearity of the twisted bilinear multiplier `Btwist` on bounded sequences

`Work.KMTAreas.A7.Btwist` is defined as the absolutely convergent double series

  `Btwist ρ P l₁ l₂ m₁ m₂ h k x = ∑' j₁, ∑' j₂, K(j₁,j₂) · h(x-j₁) · k(x-j₂)`,

with kernel `K(j₁,j₂) = arithKernel ρ P Q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`.  The summability of the
double family is exactly what the hypotheses `Summable (fun j => ‖cw mᵢ j‖)` together with the
uniform boundedness of the two arguments `h`, `k` provide: the arithmetic kernel is a *finite*
double sum over the arithmetic frequency sets, hence bounded by
`arithKB ρ l₁ l₂ = #(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}`.

This file proves that bound (`arithKernel_norm_le`), the resulting absolute summability of the
iterated series (`btwist_summable_of_bounded`), and derives the bilinearity of `Btwist` in both
variables (additivity and homogeneity) together with its vanishing on `0`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## The arithmetic symbol is bounded by one -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one, hence has
modulus at most one. -/
private lemma mZ_norm_le_one (P : ℤ[X]) (q : ℕ) (hq : 0 < q)
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

/-! ## The arithmetic kernel is a bounded kernel -/

/-- The uniform bound on the arithmetic kernel: the cardinality of the arithmetic frequency sets
`(ℚ/ℤ)_{≤l₁}`, `(ℚ/ℤ)_{≤l₂}`. -/
private def arithKB (ρ : ℝ) (l₁ l₂ : ℕ) : ℝ :=
  ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)

private lemma arithKB_nonneg (ρ : ℝ) (l₁ l₂ : ℕ) : 0 ≤ arithKB ρ l₁ l₂ :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma arithKernel_norm_le (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ ≤ arithKB ρ l₁ l₂ := by
  unfold arithKernel arithKB
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
        exact mZ_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The kernel of `Btwist` and its summability -/

/-- The kernel of the twisted bilinear multiplier, as a function of the two summation variables. -/
private def btwistK (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

private theorem Btwist_eq (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ)
    (x : ℤ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h k x
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * h (x - j₁) * k (x - j₂) := rfl

private lemma btwistK_norm_le (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (j₁ j₂ : ℤ) :
    ‖btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂‖ ≤ arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖ := by
  have hk := arithKernel_norm_le ρ P l₁ l₂ j₁ j₂
  have hKB := arithKB_nonneg ρ l₁ l₂
  unfold btwistK
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hk le_rfl (norm_nonneg _) hKB) le_rfl (norm_nonneg _)
    (mul_nonneg hKB (norm_nonneg _))

/-- `‖z₁ z₂ z₃‖ ≤ Z₁ Z₂ Z₃` for `‖zᵢ‖ ≤ Zᵢ`. -/
private lemma norm_mul_mul_le {z₁ z₂ z₃ : ℂ} {Z₁ Z₂ Z₃ : ℝ} (h₁ : ‖z₁‖ ≤ Z₁)
    (h₂ : ‖z₂‖ ≤ Z₂) (h₃ : ‖z₃‖ ≤ Z₃) : ‖z₁ * z₂ * z₃‖ ≤ Z₁ * Z₂ * Z₃ := by
  have h₁' : 0 ≤ Z₁ := le_trans (norm_nonneg z₁) h₁
  have h₂' : 0 ≤ Z₂ := le_trans (norm_nonneg z₂) h₂
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) h₁') h₃ (norm_nonneg _)
    (mul_nonneg h₁' h₂')

/-- **Absolute summability of an iterated series.**  If `‖F j₁ j₂‖ ≤ G j₁ · H j₂` with `G`, `H`
summable, then `j₁ ↦ ∑' j₂, F j₁ j₂` is summable.  (Only `ℤ`-indexed sums are used, so no Fubini
input on the product type is required.) -/
private lemma summable_tsum_of_bound {F : ℤ → ℤ → ℂ} {G H : ℤ → ℝ}
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
private lemma btwist_inner_summable (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x j₁ : ℤ) :
    Summable (fun j₂ : ℤ => btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine Summable.of_norm_bounded
    (g := fun j₂ : ℤ => (arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖)
    (hm₂.mul_left _) (fun j₂ => ?_)
  calc ‖btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
      ≤ (arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
        norm_mul_mul_le (btwistK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂) (ha _) (hb _)
    _ = (arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-- **Absolute summability of the iterated series defining `Btwist`.** -/
private lemma btwist_summable_of_bounded (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x : ℤ) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine summable_tsum_of_bound (G := fun j₁ : ℤ => arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb)
    (H := fun j₂ : ℤ => ‖cw m₂ j₂‖) ?_ hm₂ ?_
  · exact ((hm₁.mul_left (arithKB ρ l₁ l₂)).mul_right Ca).mul_right Cb
  · intro j₁ j₂
    calc ‖btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
        ≤ (arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
          norm_mul_mul_le (btwistK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂) (ha _) (hb _)
      _ = (arithKB ρ l₁ l₂ * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-! ## Bilinearity of `Btwist` -/

theorem Btwist_bilinear_of_bounded (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖))
    (hm₂ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖))
    (u u' v v' : ℤ → ℂ) (Cu Cu' Cv Cv' : ℝ)
    (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) (hu' : ∀ y : ℤ, ‖u' y‖ ≤ Cu')
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (hv' : ∀ y : ℤ, ‖v' y‖ ≤ Cv') :
    (Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (u + u') v
        = Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u v
          + Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u' v) ∧
    (Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u (v + v')
        = Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u v
          + Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u v') ∧
    (∀ c : ℂ, Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (c • u) v
        = c • Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u v) ∧
    (∀ c : ℂ, Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u (c • v)
        = c • Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u v) ∧
    (Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (0 : ℤ → ℂ) v = 0) ∧
    (Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ u (0 : ℤ → ℂ) = 0) := by
  classical
  have hsum_uv : ∀ x : ℤ, Summable (fun j₁ : ℤ => ∑' j₂ : ℤ,
      btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂)) :=
    fun x => btwist_summable_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂ u v hu hv x
  have hsum_uv' : ∀ x : ℤ, Summable (fun j₁ : ℤ => ∑' j₂ : ℤ,
      btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v' (x - j₂)) :=
    fun x => btwist_summable_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂ u v' hu hv' x
  have hsum_u'v : ∀ x : ℤ, Summable (fun j₁ : ℤ => ∑' j₂ : ℤ,
      btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u' (x - j₁) * v (x - j₂)) :=
    fun x => btwist_summable_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂ u' v hu' hv x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * (u + u') (x - j₁) * v (x - j₂))
        = (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
          + (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u' (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_add
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u v hu hv x j₁)
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u' v hu' hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.add_apply]
      ring
    calc Btwist ρ P l₁ l₂ m₁ m₂ (u + u') v x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * (u + u') (x - j₁) * v (x - j₂) :=
          Btwist_eq ρ P l₁ l₂ m₁ m₂ (u + u') v x
      _ = ∑' j₁ : ℤ, ((∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u' (x - j₁) * v (x - j₂))) :=
          tsum_congr hinner
      _ = (∑' j₁ : ℤ, ∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₁ : ℤ, ∑' j₂ : ℤ,
                btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u' (x - j₁) * v (x - j₂)) :=
          Summable.tsum_add (hsum_uv x) (hsum_u'v x)
      _ = Btwist ρ P l₁ l₂ m₁ m₂ u v x + Btwist ρ P l₁ l₂ m₁ m₂ u' v x := by
          rw [← Btwist_eq ρ P l₁ l₂ m₁ m₂ u v x, ← Btwist_eq ρ P l₁ l₂ m₁ m₂ u' v x]
  · funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * (v + v') (x - j₂))
        = (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
          + (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v' (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_add
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u v hu hv x j₁)
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u v' hu hv' x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.add_apply]
      ring
    calc Btwist ρ P l₁ l₂ m₁ m₂ u (v + v') x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * (v + v') (x - j₂) :=
          Btwist_eq ρ P l₁ l₂ m₁ m₂ u (v + v') x
      _ = ∑' j₁ : ℤ, ((∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v' (x - j₂))) :=
          tsum_congr hinner
      _ = (∑' j₁ : ℤ, ∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₁ : ℤ, ∑' j₂ : ℤ,
                btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v' (x - j₂)) :=
          Summable.tsum_add (hsum_uv x) (hsum_uv' x)
      _ = Btwist ρ P l₁ l₂ m₁ m₂ u v x + Btwist ρ P l₁ l₂ m₁ m₂ u v' x := by
          rw [← Btwist_eq ρ P l₁ l₂ m₁ m₂ u v x, ← Btwist_eq ρ P l₁ l₂ m₁ m₂ u v' x]
  · intro c
    funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * (c • u) (x - j₁) * v (x - j₂))
        = c * (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_mul_left c
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u v hu hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc Btwist ρ P l₁ l₂ m₁ m₂ (c • u) v x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * (c • u) (x - j₁) * v (x - j₂) :=
          Btwist_eq ρ P l₁ l₂ m₁ m₂ (c • u) v x
      _ = ∑' j₁ : ℤ, c * (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁)
            * v (x - j₂)) := tsum_congr hinner
      _ = c * ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂) :=
          Summable.tsum_mul_left c (hsum_uv x)
      _ = c • Btwist ρ P l₁ l₂ m₁ m₂ u v x := by
          rw [← Btwist_eq ρ P l₁ l₂ m₁ m₂ u v x, smul_eq_mul]
  · intro c
    funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * (c • v) (x - j₂))
        = c * (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_mul_left c
        (btwist_inner_summable ρ P l₁ l₂ m₁ m₂ hm₂ u v hu hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc Btwist ρ P l₁ l₂ m₁ m₂ u (c • v) x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * (c • v) (x - j₂) :=
          Btwist_eq ρ P l₁ l₂ m₁ m₂ u (c • v) x
      _ = ∑' j₁ : ℤ, c * (∑' j₂ : ℤ, btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁)
            * v (x - j₂)) := tsum_congr hinner
      _ = c * ∑' j₁ : ℤ, ∑' j₂ : ℤ,
            btwistK ρ P l₁ l₂ m₁ m₂ j₁ j₂ * u (x - j₁) * v (x - j₂) :=
          Summable.tsum_mul_left c (hsum_uv x)
      _ = c • Btwist ρ P l₁ l₂ m₁ m₂ u v x := by
          rw [← Btwist_eq ρ P l₁ l₂ m₁ m₂ u v x, smul_eq_mul]
  · funext x
    simp only [Btwist]
    simp
  · funext x
    simp only [Btwist]
    simp

end

end Work.KMTAreas.A7
