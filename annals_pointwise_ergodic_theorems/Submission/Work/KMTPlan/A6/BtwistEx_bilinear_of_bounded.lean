/-
# Bilinearity of the exact-height twisted bilinear multiplier `BtwistEx`

`Work.KMTPlan.A6.BtwistEx` (the §6 model operator at *exact* arithmetic heights,
`Submission/Work/KMTPlan/A6/LowSmallDefs.lean`) is the absolutely convergent double series

  `BtwistEx ρ P l₁ l₂ m₁ m₂ h k x = ∑' j₁, ∑' j₂, K(j₁,j₂) · h(x-j₁) · k(x-j₂)`,
  `K(j₁,j₂) = arithKernelEx ρ P Q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`.

This is the exact-height analogue of `Work.KMTAreas.A7.Btwist`, whose bilinearity was proved in
`Submission/Work/KMTAreas/A7/Btwist_bilinear_of_bounded.lean`.  The only difference is that the
arithmetic kernel sums over the *exact-height* frequency sets `(ℚ/ℤ)_l = diffFreqs ρ l` instead of
the height-`≤ l` sets; the kernel is still a *finite* double sum, bounded in modulus by
`arithKBE ρ l₁ l₂ = #(ℚ/ℤ)_{l₁} · #(ℚ/ℤ)_{l₂}`.  That bound, together with the summability of
`‖cw mᵢ‖` and the uniform boundedness of the two arguments, makes the defining series absolutely
summable, which is all that bilinearity needs.

The statement is proved in the abstract form `bilinOp_bilinear_of_bound`: for an arbitrary kernel
`K` with `‖K j₁ j₂‖ ≤ B · ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` the bilinear convolution operator `bilinOp K`
is additive and homogeneous in each variable and vanishes on `0`.  The target theorem is the
specialisation `K = btwistExK ρ P l₁ l₂ m₁ m₂`, which is `BtwistEx` up to definitional unfolding.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTAreas.A7.Btwist_bilinear_of_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The arithmetic kernel at exact heights is a bounded kernel -/

/-- The uniform bound on the exact-height arithmetic kernel: the cardinality of the exact-height
frequency sets `(ℚ/ℤ)_{l₁}`, `(ℚ/ℤ)_{l₂}`. -/
private def arithKBE (ρ : ℝ) (l₁ l₂ : ℕ) : ℝ :=
  ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)

private lemma arithKBE_nonneg (ρ : ℝ) (l₁ l₂ : ℕ) : 0 ≤ arithKBE ρ l₁ l₂ :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one, hence has
modulus at most one. -/
private lemma mZ_norm_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
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

private lemma arithKernelEx_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ ≤ arithKBE ρ l₁ l₂ := by
  unfold arithKernelEx arithKBE
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
          * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mZ_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The kernel of `BtwistEx` -/

/-- The kernel of the exact-height twisted bilinear multiplier `BtwistEx`, as a function of the two
summation variables. -/
private def btwistExK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- `BtwistEx` is the bilinear convolution operator with kernel `btwistExK` (definitional). -/
private lemma BtwistEx_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ = bilinOp (btwistExK ρ P l₁ l₂ m₁ m₂) := rfl

private lemma btwistExK_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (j₁ j₂ : ℤ) :
    ‖btwistExK ρ P l₁ l₂ m₁ m₂ j₁ j₂‖
      ≤ arithKBE ρ l₁ l₂ * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖ := by
  have hk := arithKernelEx_norm_le ρ P l₁ l₂ j₁ j₂
  have hKB := arithKBE_nonneg ρ l₁ l₂
  unfold btwistExK
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hk le_rfl (norm_nonneg _) hKB) le_rfl (norm_nonneg _)
    (mul_nonneg hKB (norm_nonneg _))

/-! ## Abstract bilinearity of a bounded bilinear convolution operator -/

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

/-- Summability of the inner series of `bilinOp K` in the second summation variable. -/
private lemma bilinOp_inner_summable {K : ℤ → ℤ → ℂ} {m₁ m₂ : ℝ → ℂ} {B : ℝ}
    (hK : ∀ j₁ j₂, ‖K j₁ j₂‖ ≤ B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖)
    (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x j₁ : ℤ) :
    Summable (fun j₂ : ℤ => K j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine Summable.of_norm_bounded
    (g := fun j₂ : ℤ => (B * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖)
    (hm₂.mul_left _) (fun j₂ => ?_)
  calc ‖K j₁ j₂ * a (x - j₁) * b (x - j₂)‖
      ≤ (B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
        norm_mul_mul_le (hK j₁ j₂) (ha _) (hb _)
    _ = (B * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-- **Absolute summability of the iterated series defining `bilinOp K`.** -/
private lemma bilinOp_summable_of_bound {K : ℤ → ℤ → ℂ} {m₁ m₂ : ℝ → ℂ} {B : ℝ}
    (hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (hK : ∀ j₁ j₂, ‖K j₁ j₂‖ ≤ B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖)
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x : ℤ) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ, K j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine summable_tsum_of_bound (G := fun j₁ : ℤ => B * ‖cw m₁ j₁‖ * Ca * Cb)
    (H := fun j₂ : ℤ => ‖cw m₂ j₂‖) ?_ hm₂ ?_
  · exact ((hm₁.mul_left B).mul_right Ca).mul_right Cb
  · intro j₁ j₂
    calc ‖K j₁ j₂ * a (x - j₁) * b (x - j₂)‖
        ≤ (B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
          norm_mul_mul_le (hK j₁ j₂) (ha _) (hb _)
      _ = (B * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-- **Bilinearity of a bilinear convolution operator with a `cw`-dominated kernel.**  If
`‖K j₁ j₂‖ ≤ B · ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` and the `cw mᵢ` are absolutely summable, then
`bilinOp K` is additive in each variable and homogeneous in each variable, and vanishes when one
argument is `0`. -/
theorem bilinOp_bilinear_of_bound {K : ℤ → ℤ → ℂ} {m₁ m₂ : ℝ → ℂ} {B : ℝ}
    (hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (hK : ∀ j₁ j₂, ‖K j₁ j₂‖ ≤ B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖)
    (u u' v v' : ℤ → ℂ) (Cu Cu' Cv Cv' : ℝ)
    (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) (hu' : ∀ y : ℤ, ‖u' y‖ ≤ Cu')
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (hv' : ∀ y : ℤ, ‖v' y‖ ≤ Cv') :
    (bilinOp K (u + u') v = bilinOp K u v + bilinOp K u' v) ∧
    (bilinOp K u (v + v') = bilinOp K u v + bilinOp K u v') ∧
    (∀ c : ℂ, bilinOp K (c • u) v = c • bilinOp K u v) ∧
    (∀ c : ℂ, bilinOp K u (c • v) = c • bilinOp K u v) ∧
    (bilinOp K (0 : ℤ → ℂ) v = 0) ∧
    (bilinOp K u (0 : ℤ → ℂ) = 0) := by
  classical
  have hsum_uv : ∀ x : ℤ, Summable (fun j₁ : ℤ =>
      ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂)) :=
    fun x => bilinOp_summable_of_bound hm₁ hm₂ hK u v hu hv x
  have hsum_uv' : ∀ x : ℤ, Summable (fun j₁ : ℤ =>
      ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v' (x - j₂)) :=
    fun x => bilinOp_summable_of_bound hm₁ hm₂ hK u v' hu hv' x
  have hsum_u'v : ∀ x : ℤ, Summable (fun j₁ : ℤ =>
      ∑' j₂ : ℤ, K j₁ j₂ * u' (x - j₁) * v (x - j₂)) :=
    fun x => bilinOp_summable_of_bound hm₁ hm₂ hK u' v hu' hv x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, K j₁ j₂ * (u + u') (x - j₁) * v (x - j₂))
        = (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
          + (∑' j₂ : ℤ, K j₁ j₂ * u' (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_add
        (bilinOp_inner_summable hK hm₂ u v hu hv x j₁)
        (bilinOp_inner_summable hK hm₂ u' v hu' hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.add_apply]
      ring
    calc bilinOp K (u + u') v x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * (u + u') (x - j₁) * v (x - j₂) := by
          rw [bilinOp]
      _ = ∑' j₁ : ℤ, ((∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₂ : ℤ, K j₁ j₂ * u' (x - j₁) * v (x - j₂))) := tsum_congr hinner
      _ = (∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u' (x - j₁) * v (x - j₂)) :=
          Summable.tsum_add (hsum_uv x) (hsum_u'v x)
      _ = bilinOp K u v x + bilinOp K u' v x := by
          simp only [bilinOp]
  · funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * (v + v') (x - j₂))
        = (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
          + (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v' (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_add
        (bilinOp_inner_summable hK hm₂ u v hu hv x j₁)
        (bilinOp_inner_summable hK hm₂ u v' hu hv' x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.add_apply]
      ring
    calc bilinOp K u (v + v') x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * (v + v') (x - j₂) := by
          rw [bilinOp]
      _ = ∑' j₁ : ℤ, ((∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v' (x - j₂))) := tsum_congr hinner
      _ = (∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂))
            + (∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v' (x - j₂)) :=
          Summable.tsum_add (hsum_uv x) (hsum_uv' x)
      _ = bilinOp K u v x + bilinOp K u v' x := by
          simp only [bilinOp]
  · intro c
    funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, K j₁ j₂ * (c • u) (x - j₁) * v (x - j₂))
        = c * (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_mul_left c
        (bilinOp_inner_summable hK hm₂ u v hu hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc bilinOp K (c • u) v x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * (c • u) (x - j₁) * v (x - j₂) := by
          rw [bilinOp]
      _ = ∑' j₁ : ℤ, c * (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂)) :=
          tsum_congr hinner
      _ = c * ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂) :=
          Summable.tsum_mul_left c (hsum_uv x)
      _ = c • bilinOp K u v x := by
          simp only [bilinOp, smul_eq_mul]
  · intro c
    funext x
    have hinner : ∀ j₁ : ℤ,
        (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * (c • v) (x - j₂))
        = c * (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂)) := by
      intro j₁
      rw [← Summable.tsum_mul_left c
        (bilinOp_inner_summable hK hm₂ u v hu hv x j₁)]
      refine tsum_congr (fun j₂ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc bilinOp K u (c • v) x
        = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * (c • v) (x - j₂) := by
          rw [bilinOp]
      _ = ∑' j₁ : ℤ, c * (∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂)) :=
          tsum_congr hinner
      _ = c * ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * u (x - j₁) * v (x - j₂) :=
          Summable.tsum_mul_left c (hsum_uv x)
      _ = c • bilinOp K u v x := by
          simp only [bilinOp, smul_eq_mul]
  · funext x
    simp only [bilinOp]
    simp
  · funext x
    simp only [bilinOp]
    simp

/-! ## The target theorem -/

theorem BtwistEx_bilinear_of_bounded (ρ : Real) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : Real → Complex)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (u u' v v' : ℤ → Complex) (Cu Cu' Cv Cv' : Real)
    (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) (hu' : ∀ y : ℤ, ‖u' y‖ ≤ Cu')
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (hv' : ∀ y : ℤ, ‖v' y‖ ≤ Cv') :
    (Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ (u + u') v
          = Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u v
            + Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u' v) ∧
    (Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u (v + v')
          = Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u v
            + Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u v') ∧
    (∀ c : Complex, Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ (c • u) v
          = c • Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u v) ∧
    (∀ c : Complex, Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u (c • v)
          = c • Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u v) ∧
    (Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ (0 : ℤ → Complex) v = 0) ∧
    (Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂ u (0 : ℤ → Complex) = 0) := by
  rw [BtwistEx_eq_bilinOp]
  exact bilinOp_bilinear_of_bound hm₁ hm₂
    (fun j₁ j₂ => btwistExK_norm_le ρ P l₁ l₂ m₁ m₂ j₁ j₂)
    u u' v v' Cu Cu' Cv Cv' hu hu' hv hv'

end

end Work.KMTPlan.A6
