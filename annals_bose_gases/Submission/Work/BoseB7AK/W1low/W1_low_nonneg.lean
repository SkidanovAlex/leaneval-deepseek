import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB7AK.W1low.W1fun_moment_integrable
import Submission.Work.BoseB7AK.W1low.chat_sub_le_abs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.W1low.W1_low_nonneg` — low-momentum positivity of `Ŵ₁`

FS's proof of `thm:BogHamDiag` (`final_v2.tex`, lines 2390–2406) uses the
elementary quadratic estimate

  `|Ŵ₁(k) − Ŵ₁(0)| ≤ ½‖k‖² ∫ ‖y‖²|W₁(y)| dy`,

so that, since `Ŵ₁(0) = ∫W₁ ≥ 0` and `W₁` is supported in `ball 0 R`,

  `Ŵ₁(k) ≥ (1 − ½(‖k‖R)²) ∫W₁ ≥ 0`   whenever `‖k‖R ≤ 1/2`.

This module assembles that chain at the corpus's own kernel
`W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g0 v h)` and proves

  `0 ≤ Work.BoseFixR.chat (W₁) k`   for `‖k‖ R ≤ 1/2`.

## Ingredients (all already in the corpus, or in the two siblings below)

* `Submission.Work.BoseB7AK.W1low.chat_sub_le_abs` — the quadratic Fourier
  estimate in absolute-value form (no sign/evenness of `W`);
* `Submission.Work.BoseB7AK.W1low.W1fun_moment_integrable` — finiteness of the
  second absolute moment of `W₁`, `∫‖y‖²|W₁(y)|dy < ∞`;
* `Submission.BoseGases.wScaled_g0_nonneg_ae` — `0 ≤ W₁` a.e.
  (`W₁ = g₀/(χ⋆χ)_ℓ` with `g₀ ≥ 0` a.e. and `(χ⋆χ)_ℓ ≥ 0` pointwise);
* support: `g₀` (hence `W₁`) vanishes for `‖y‖ ≥ R`
  (`Submission.BoseGases.g0_zero_of_norm_ge`).

Note: the pointwise form `0 ≤ g₀` (hence `0 ≤ W₁`) is *not* available — the
corpus only knows `g₀ ≥ 0` a.e. (`g0_nonneg_ae`); correspondingly the Fourier
estimate is used in the absolute-value form, which behaves correctly on the
exceptional null set.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB7AK.W1low

/-- `Ŵ(0)` is the total mass: the `p`-convention Fourier transform at `k = 0`
is `∫ y, W y`. -/
theorem chat_zero (W : ℝ³ → ℝ) : Work.BoseFixR.chat W 0 = ∫ x, W x := by
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  have h : (∫ y : ℝ³, ((W y : ℝ) : ℂ)) = (((∫ y : ℝ³, W y) : ℝ) : ℂ) := integral_ofReal
  rw [h]
  exact Complex.ofReal_re _

/-- `W₁ = wScaled ℓ (g₀) = g₀/(χ⋆χ)_ℓ` vanishes where `g₀` does, in particular
outside `ball 0 R`. -/
theorem W1fun_eq_zero_of_R_le_norm {v : ℝ³ → ℝ} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    {x : ℝ³} (hx : R ≤ ‖x‖) : Work.BoseFixR.W1fun v h ℓ x = 0 := by
  have hz : Submission.BoseGases.g0 v h x = 0 :=
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]

/-- **Low-momentum positivity of `Ŵ₁`**: `Ŵ₁(k) ≥ 0` for `‖k‖ R ≤ 1/2`.

With `A := ∫W₁ ≥ 0`, `I := ∫‖y‖²|W₁(y)|dy ≤ R²A`, and the quadratic Fourier
estimate `|Ŵ₁(k) − A| ≤ ½‖k‖² I`:

`Ŵ₁(k) ≥ A − ½‖k‖² I ≥ A − ½(‖k‖R)² A ≥ (1 − 1/8) A ≥ 0`. -/
theorem W1_low_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {k : EuclideanSpace ℝ (Fin 3)} (hk : ‖k‖ * R ≤ 1 / 2) :
    0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k := by
  set A : ℝ := ∫ x : ℝ³, Work.BoseFixR.W1fun v h ℓ x with hA
  set c : ℝ := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k with hc
  -- `0 ≤ W₁` a.e.
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hA_nn : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.integral_nonneg_of_ae hWnn
  -- integrability of `W₁` and of its second absolute moment
  have hint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hint2 : MeasureTheory.Integrable
      (fun x : ℝ³ => ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|) :=
    W1fun_moment_integrable hR hℓ hv_supp h hRℓ
  have hchat0 : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 = A := by
    rw [hA]
    exact chat_zero _
  have hintR : MeasureTheory.Integrable
      (fun x : ℝ³ => R ^ 2 * Work.BoseFixR.W1fun v h ℓ x) := hint.const_mul (R ^ 2)
  -- the second absolute moment is bounded by `R² ∫W₁`, using `W₁ ≥ 0` a.e. and
  -- the support of `W₁` in `ball 0 R`
  have hdom : ∀ᵐ x : ℝ³,
      ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x| ≤ R ^ 2 * Work.BoseFixR.W1fun v h ℓ x := by
    filter_upwards [hWnn] with x hxnn
    by_cases hx : ‖x‖ ≤ R
    · have h2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
      rw [abs_of_nonneg hxnn]
      exact mul_le_mul_of_nonneg_right h2 hxnn
    · have hxR : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      have hz : Work.BoseFixR.W1fun v h ℓ x = 0 :=
        W1fun_eq_zero_of_R_le_norm (ℓ := ℓ) hv_supp h hxR
      simp [hz]
  have hIle : (∫ x : ℝ³, ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|) ≤ R ^ 2 * A := by
    have hmono := MeasureTheory.integral_mono_ae hint2 hintR hdom
    rw [MeasureTheory.integral_const_mul, ← hA] at hmono
    exact hmono
  -- the quadratic Fourier estimate at `W₁`
  have hfourier : |c - A| ≤ (1 / 2) * ‖k‖ ^ 2
      * ∫ x : ℝ³, ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x| := by
    have hmain := chat_sub_le_abs hint hint2 k
    rw [hchat0, ← hc] at hmain
    exact hmain
  have hkey : -(1 / 2 * ‖k‖ ^ 2
      * ∫ x : ℝ³, ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|) ≤ c - A :=
    (abs_le.mp hfourier).1
  -- `(1/2)‖k‖²R² ≤ 1/8` by `‖k‖R ≤ 1/2`
  have hk2 : (‖k‖ * R) ^ 2 ≤ (1 / 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (norm_nonneg k) hR.le) hk 2
  have hcoef : (1 / 2) * ‖k‖ ^ 2 * R ^ 2 ≤ 1 / 8 := by
    nlinarith only [hk2]
  have hB : (1 / 2) * ‖k‖ ^ 2
      * ∫ x : ℝ³, ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x| ≤ (1 / 8) * A := by
    have hB1 : (1 / 2) * ‖k‖ ^ 2
        * ∫ x : ℝ³, ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|
          ≤ (1 / 2) * ‖k‖ ^ 2 * (R ^ 2 * A) :=
      mul_le_mul_of_nonneg_left hIle (by positivity)
    have hB2 : (1 / 2) * ‖k‖ ^ 2 * (R ^ 2 * A) ≤ (1 / 8) * A := by
      have h := mul_le_mul_of_nonneg_right hcoef hA_nn
      linarith only [h]
    linarith only [hB1, hB2]
  linarith only [hkey, hB, hA_nn]

end Work.BoseB7AK.W1low
