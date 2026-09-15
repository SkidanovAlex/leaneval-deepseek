import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Commons.Analysis.Convolution.integrable_aniso_tent_scaled
import Submission.Commons.Analysis.Convolution.integral_aniso_tent_scaling
import Submission.Commons.Analysis.Convolution.aniso_tent_decay_two_scale

/-!
# The scaled two-tent convolution estimate

This file proves `aniso_tent_conv_le_scaled`: for `0 < δ₂ ≤ δ₁ ≤ 1`, `A > k` and
`A ≥ k(k+1)/2`, the convolution of the `L¹`-normalised anisotropic tents
`φ̃_{δ₁} * φ̃_{δ₂}` is dominated by a constant times `φ̃_{δ₂}`.  This is the general
(`δ₂ ≤ δ₁`) form of the `δ₁ = 1` estimate `aniso_tent_conv_le` (Guo–Li–Yung–Zorin-Kranich,
Appendix Lemma A.1 / GLYZK Lemma 4.1 `φ_I * φ_J ≲ φ_J` for `J ⊆ I`).

The proof is the standard two-case argument: either the fine tent at `y` is directly
dominated by the fine tent at `x` (pointwise bound), or the fine tent at `y` dominates
`2^A` times the fine tent at `x`, in which case the **two-scale decay lemma**
`aniso_tent_decay_two_scale` says that `x` and `y` are separated in a coordinate weighted
by `δ₂`, which forces the *coarse* (`δ₁`) tent at `x - y` to be small.  Both cases are then
integrated, using `∫ φ̃_δ = ∫ φ̃₁` (`integral_aniso_tent_scaling`).
-/

namespace Commons.Analysis.Convolution

open scoped BigOperators
open MeasureTheory

/-- The isotropic tent `(max 1 (max_i |x i|))^{-A}`. -/
private noncomputable def tent (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (x : Fin k → ℝ) : ℝ :=
  (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    fun i => |x i|)) ^ (-A)

/-- The `L¹`-normalised anisotropic tent `φ̃_δ`, written exactly as in the target
statement (with the factor `δ ^ (k (k+1)/2)` and the weighted sup inside the `max`). -/
private noncomputable def itent (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (x : Fin k → ℝ) : ℝ :=
  δ ^ (k * (k + 1) / 2) *
    (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      fun i => δ ^ (i.val + 1) * |x i|)) ^ (-A)

private lemma itent_nonneg (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (hδ : 0 < δ) (x : Fin k → ℝ) :
    0 ≤ itent k hk A δ x := by
  rw [itent]
  refine mul_nonneg (pow_nonneg (le_of_lt hδ) _) ?_
  exact Real.rpow_nonneg
    (le_trans zero_le_one (le_max_left (1 : ℝ) ((Finset.univ : Finset (Fin k)).sup'
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => δ ^ (i.val + 1) * |x i|))) _

/-- The two ways of writing the anisotropic weight agree: `δ ^ (i+1) * |x i| = |δ ^ (i+1) * x i|`. -/
private lemma sup_abs_form (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 ≤ δ) (x : Fin k → ℝ) :
    ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => δ ^ (i.val + 1) * |x i|)
      = ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |δ ^ (i.val + 1) * x i|) :=
  Finset.sup'_congr _ rfl fun i _ => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ _)]

/-- The anisotropic tent written with the absolute value inside the sup. -/
private lemma itent_abs_form (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (hδ : 0 ≤ δ) (x : Fin k → ℝ) :
    itent k hk A δ x = δ ^ (k * (k + 1) / 2) *
      (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |δ ^ (i.val + 1) * x i|)) ^ (-A) := by
  rw [itent, sup_abs_form k hk hδ x]

private lemma itent_integrable {k : ℕ} (hk : 1 ≤ k) {A δ : ℝ} (hA : (k : ℝ) < A)
    (hδ : 0 < δ) :
    Integrable (fun y : Fin k → ℝ => itent k hk A δ y) := by
  have h := (integrable_aniso_tent_scaled k hk hA hδ).const_mul (δ ^ (k * (k + 1) / 2))
  simpa only [← itent_abs_form k hk A δ (le_of_lt hδ)] using h

private lemma itent_integrable_sub {k : ℕ} (hk : 1 ≤ k) {A δ : ℝ} (hA : (k : ℝ) < A)
    (hδ : 0 < δ) (x : Fin k → ℝ) :
    Integrable (fun y : Fin k → ℝ => itent k hk A δ (x - y)) :=
  (itent_integrable hk hA hδ).comp_sub_left x

private lemma integral_itent_sub {k : ℕ} (hk : 1 ≤ k) (A δ : ℝ) (_hδ : 0 < δ)
    (x : Fin k → ℝ) :
    ∫ y : Fin k → ℝ, itent k hk A δ (x - y) = ∫ y : Fin k → ℝ, itent k hk A δ y :=
  integral_sub_left_eq_self (fun y : Fin k → ℝ => itent k hk A δ y) volume x

private lemma integral_itent {k : ℕ} (hk : 1 ≤ k) {A δ : ℝ} (hA : (k : ℝ) < A)
    (hδ : 0 < δ) :
    ∫ y : Fin k → ℝ, itent k hk A δ y = ∫ y : Fin k → ℝ, tent k hk A y := by
  have h1 : (fun y : Fin k → ℝ => itent k hk A δ y)
      = fun y : Fin k → ℝ => δ ^ (k * (k + 1) / 2) *
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => |δ ^ (i.val + 1) * y i|)) ^ (-A) := by
    funext y
    exact itent_abs_form k hk A δ (le_of_lt hδ) y
  have h2 : (fun y : Fin k → ℝ => tent k hk A y)
      = fun y : Fin k → ℝ =>
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => |y i|)) ^ (-A) := rfl
  rw [h1, h2, integral_const_mul]
  exact integral_aniso_tent_scaling k hk hA hδ

/-- **Two-scale pointwise decay.**  If the `δ₂`-tent at `y` dominates `2^A` times the
`δ₂`-tent at `x`, then `x` and `y` are separated in a coordinate weighted by `δ₂`, and
consequently the *coarse* (`δ₁`) tent at `x - y` is at most `2^A` times the `δ₂`-tent at `x`.
Requires `δ₂ ≤ δ₁ ≤ 1` and `A ≥ k(k+1)/2`. -/
private lemma itent_decay_two_scale (k : ℕ) (hk : 1 ≤ k) {A δ₁ δ₂ : ℝ}
    (hA : (k : ℝ) * (k + 1) / 2 ≤ A) (hδ20 : 0 < δ₂) (hδ21 : δ₂ ≤ 1)
    (hδ12 : δ₂ ≤ δ₁) (hδ11 : δ₁ ≤ 1) (x y : Fin k → ℝ)
    (h : 2 ^ A * itent k hk A δ₂ x < itent k hk A δ₂ y) :
    itent k hk A δ₁ (x - y) ≤ 2 ^ A * itent k hk A δ₂ x := by
  simpa only [itent] using
    aniso_tent_decay_two_scale k hk hA hδ20 hδ21 hδ12 hδ11 x y h

/-- The two-case pointwise domination underlying the convolution estimate. -/
private lemma itent_conv_pointwise (k : ℕ) (hk : 1 ≤ k) {A δ₁ δ₂ : ℝ}
    (hA : (k : ℝ) * (k + 1) / 2 ≤ A) (hδ20 : 0 < δ₂) (hδ21 : δ₂ ≤ 1)
    (hδ12 : δ₂ ≤ δ₁) (hδ11 : δ₁ ≤ 1) (x y : Fin k → ℝ) :
    itent k hk A δ₁ (x - y) * itent k hk A δ₂ y
      ≤ 2 ^ A * itent k hk A δ₂ x * itent k hk A δ₁ (x - y)
        + 2 ^ A * itent k hk A δ₂ x * itent k hk A δ₂ y := by
  have hδ1pos : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  have hTnn : 0 ≤ itent k hk A δ₁ (x - y) := itent_nonneg k hk A δ₁ hδ1pos _
  have hQnn : 0 ≤ itent k hk A δ₂ x := itent_nonneg k hk A δ₂ hδ20 x
  have hPnn : 0 ≤ itent k hk A δ₂ y := itent_nonneg k hk A δ₂ hδ20 y
  have htwoA : (0 : ℝ) ≤ 2 ^ A := le_of_lt (Real.rpow_pos_of_pos (by norm_num) A)
  rcases le_or_gt (itent k hk A δ₂ y) (2 ^ A * itent k hk A δ₂ x) with hle | hlt
  · refine le_trans (mul_le_mul_of_nonneg_left hle hTnn) ?_
    rw [mul_comm (itent k hk A δ₁ (x - y)) (2 ^ A * itent k hk A δ₂ x)]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg htwoA hQnn) hPnn)
  · have hdec : itent k hk A δ₁ (x - y) ≤ 2 ^ A * itent k hk A δ₂ x :=
      itent_decay_two_scale k hk hA hδ20 hδ21 hδ12 hδ11 x y hlt
    refine le_trans (mul_le_mul_of_nonneg_right hdec hPnn) ?_
    exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg htwoA hQnn) hTnn)

/-- The scaled convolution estimate, stated with the anisotropic tent `itent`. -/
private lemma aniso_tent_conv_le_scaled_itent (k : ℕ) (hk : 1 ≤ k) (A : ℝ)
    (hA1 : (k : ℝ) < A) (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₂ → δ₂ ≤ δ₁ → δ₁ ≤ 1 → ∀ x : Fin k → ℝ,
      (∫ y : Fin k → ℝ, itent k hk A δ₁ (x - y) * itent k hk A δ₂ y)
        ≤ C * itent k hk A δ₂ x := by
  set C1 : ℝ := ∫ y : Fin k → ℝ, tent k hk A y with hC1
  have htwoA : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) A
  refine ⟨2 ^ A * (2 * |C1|) + 1, by positivity, ?_⟩
  intro δ₁ δ₂ hδ20 hδ12 hδ11 x
  have hδ1pos : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  have hδ21 : δ₂ ≤ 1 := le_trans hδ12 hδ11
  have hQnn : 0 ≤ itent k hk A δ₂ x := itent_nonneg k hk A δ₂ hδ20 x
  have hIntT : Integrable (fun y : Fin k → ℝ => itent k hk A δ₁ (x - y)) :=
    itent_integrable_sub hk hA1 hδ1pos x
  have hIntP : Integrable (fun y : Fin k → ℝ => itent k hk A δ₂ y) :=
    itent_integrable hk hA1 hδ20
  have hIntG : Integrable (fun y : Fin k → ℝ =>
      2 ^ A * itent k hk A δ₂ x * itent k hk A δ₁ (x - y)
        + 2 ^ A * itent k hk A δ₂ x * itent k hk A δ₂ y) :=
    (hIntT.const_mul (2 ^ A * itent k hk A δ₂ x)).add
      (hIntP.const_mul (2 ^ A * itent k hk A δ₂ x))
  have hIntF : Integrable (fun y : Fin k → ℝ =>
      itent k hk A δ₁ (x - y) * itent k hk A δ₂ y) :=
    Integrable.mono' hIntG (hIntT.aestronglyMeasurable.mul hIntP.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (itent_nonneg k hk A δ₁ hδ1pos _)
            (itent_nonneg k hk A δ₂ hδ20 y))]
        exact itent_conv_pointwise k hk hA2 hδ20 hδ21 hδ12 hδ11 x y)
  have hIT : ∫ y : Fin k → ℝ, itent k hk A δ₁ (x - y) = C1 := by
    rw [hC1, integral_itent_sub (k := k) hk A δ₁ hδ1pos x, integral_itent (k := k) hk hA1 hδ1pos]
  have hIP : ∫ y : Fin k → ℝ, itent k hk A δ₂ y = C1 := by
    rw [hC1]; exact integral_itent (k := k) hk hA1 hδ20
  calc ∫ y : Fin k → ℝ, itent k hk A δ₁ (x - y) * itent k hk A δ₂ y
      ≤ ∫ y : Fin k → ℝ, (2 ^ A * itent k hk A δ₂ x * itent k hk A δ₁ (x - y)
          + 2 ^ A * itent k hk A δ₂ x * itent k hk A δ₂ y) :=
        integral_mono hIntF hIntG
          (fun y => itent_conv_pointwise k hk hA2 hδ20 hδ21 hδ12 hδ11 x y)
    _ = 2 ^ A * itent k hk A δ₂ x * C1 + 2 ^ A * itent k hk A δ₂ x * C1 := by
        rw [integral_add (hIntT.const_mul _) (hIntP.const_mul _),
          integral_const_mul, hIT, integral_const_mul, hIP]
    _ = 2 ^ A * itent k hk A δ₂ x * (2 * C1) := by ring
    _ ≤ (2 ^ A * (2 * |C1|) + 1) * itent k hk A δ₂ x := by
        have h1 : 2 ^ A * itent k hk A δ₂ x * (2 * C1)
            = (2 ^ A * (2 * C1)) * itent k hk A δ₂ x := by ring
        rw [h1]
        have h2 : 2 ^ A * (2 * C1) ≤ 2 ^ A * (2 * |C1|) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self C1]) (le_of_lt htwoA)
        exact le_trans (mul_le_mul_of_nonneg_right h2 hQnn)
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hQnn)

/-- **Scaled two-tent convolution estimate.**  For `0 < δ₂ ≤ δ₁ ≤ 1`, `A > k` and
`A ≥ k(k+1)/2`, there is a constant `C = C(k,A)` with
`∫ φ̃_{δ₁}(x - y) φ̃_{δ₂}(y) dy ≤ C φ̃_{δ₂}(x)` for every `x`, where `φ̃_δ` is the
`L¹`-normalised anisotropic tent `δ^{k(k+1)/2} (max 1 (max_i δ^{i+1}|z_i|))^{-A}`. -/
theorem aniso_tent_conv_le_scaled (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A) (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) : ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₂ → δ₂ ≤ δ₁ → δ₁ ≤ 1 → ∀ x : Fin k → ℝ, (∫ y : Fin k → ℝ, (δ₁ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => δ₁ ^ (i.val + 1) * |(x - y) i|)) ^ (-A)) * (δ₂ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => δ₂ ^ (i.val + 1) * |y i|)) ^ (-A))) ≤ C * (δ₂ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => δ₂ ^ (i.val + 1) * |x i|)) ^ (-A)) := by
  obtain ⟨C, hCpos, hC⟩ := aniso_tent_conv_le_scaled_itent k hk A hA1 hA2
  refine ⟨C, hCpos, fun δ₁ δ₂ hδ20 hδ12 hδ11 x => ?_⟩
  simpa only [itent] using hC δ₁ δ₂ hδ20 hδ12 hδ11 x

end Commons.Analysis.Convolution
