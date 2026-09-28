import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon

/-!
# Assembly of node N08 (`Work.HP.moment_D`)

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 2023,
Lemma D and Lemma D44.  `moment_D` is the estimate

`|Dglob − mainTerm| ≤ K · mainTerm / (log A)^{1/2}`

for `B ≥ B₀`, `B/log B ≤ A ≤ B²`.

This file contains the *analytic tail* of the argument: given the `μ`-split
`Dglob = Σ^{(1)} + Σ^{(2)}` and the two estimates

* `|Σ^{(1)} − mainTerm| ≤ K mainTerm / A^{s₁}`,
* `Σ^{(2)} ≤ K mainTerm / A^{s₂}`      (`s₁, s₂ > 0`)

it produces the required bound, using that `B/log B → ∞` and `(log A)^{1/2} ≤ A^{s}/2`
eventually.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators

namespace Work.HP

/-- `(log A)^{1/2} ≤ A^s / c` for all large `A`, when `s, c > 0`. -/
lemma eventually_log_sqrt_le_rpow_div (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ A in atTop, Real.log A ^ ((1 : ℝ) / 2) ≤ A ^ s / c := by
  have h := (isLittleO_log_rpow_rpow_atTop (1 / 2) hs).bound
    (show (0 : ℝ) < 1 / c by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with A hA hA1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hA1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ A) s)] at hA
  simpa [div_eq_mul_inv, mul_comm] using hA

/-- `B / log B → ∞`. -/
lemma tendsto_div_log_atTop : Tendsto (fun B : ℝ => B / Real.log B) atTop atTop := by
  rw [tendsto_atTop]
  intro c
  by_cases hc : c ≤ 0
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB1
    have h1 : 0 < Real.log B := Real.log_pos hB1
    have : 0 ≤ B / Real.log B := div_nonneg (by linarith) h1.le
    linarith
  · push Not at hc
    have h := (Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / c by positivity))
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with B hB hB1
    have hlog : 0 < Real.log B := Real.log_pos hB1
    have hB' : Real.log B ≤ 1 / c * B := by
      have h2 := hB
      simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (Real.log_nonneg hB1.le),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ B)] at h2
      exact h2
    rw [le_div_iff₀ hlog]
    calc c * Real.log B ≤ c * (1 / c * B) := mul_le_mul_of_nonneg_left hB' hc.le
      _ = B := by field_simp

/-- **N08, main assembly.**  The `μ`-split `Dglob = Σ^{(1)} + Σ^{(2)}` together with the two
estimates `|Σ^{(1)} − mainTerm| ≤ K mainTerm / A^{s₁}` and
`Σ^{(2)} ≤ K mainTerm / A^{s₂}` (`s₁, s₂ > 0`) gives `moment_D`. -/
theorem moment_D_of_two_exponents (d n : ℕ) (s₁ s₂ : ℝ) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hsplit : ∀ A B : ℝ, Dglob d n A B = Sigma1 d n A B + Sigma2 d n A B)
    (hnn : ∀ A B : ℝ, 0 ≤ A → 0 ≤ mainTerm d n A B)
    (hs2 : ∀ A B : ℝ, 0 ≤ A → 0 ≤ Sigma2 d n A B)
    (h1 : ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
        |Sigma1 d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / A ^ s₁)
    (h2 : ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
        Sigma2 d n A B ≤ K * mainTerm d n A B / A ^ s₂) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Dglob d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
  obtain ⟨K₁, B₁, h1⟩ := h1
  obtain ⟨K₂, B₂, h2⟩ := h2
  -- eventual facts in `A`
  have hlogA : ∀ᶠ A in atTop, 2 ≤ A ∧
      Real.log A ^ ((1 : ℝ) / 2) ≤ A ^ s₁ / 2 ∧
      Real.log A ^ ((1 : ℝ) / 2) ≤ A ^ s₂ / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      eventually_log_sqrt_le_rpow_div s₁ 2 hs₁ (by norm_num),
      eventually_log_sqrt_le_rpow_div s₂ 2 hs₂ (by norm_num)]
      with A hA2 hE1 hE2
    exact ⟨hA2, hE1, hE2⟩
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hlogA
  have key : ∀ᶠ B in atTop, ∀ A : ℝ, B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Dglob d n A B - mainTerm d n A B| ≤
        (|K₁| + |K₂|) * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
    filter_upwards [eventually_ge_atTop B₁, eventually_ge_atTop B₂,
      tendsto_div_log_atTop.eventually (eventually_ge_atTop A₀)]
      with B hB1 hB2 hA0
    intro A hA1 hA2
    obtain ⟨hA2', hE1, hE2⟩ := hA₀ A (le_trans hA0 hA1)
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hA2'
    have hu : 0 < Real.log A ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    have hMT : 0 ≤ mainTerm d n A B := hnn A B hApos.le
    have hS2 : 0 ≤ Sigma2 d n A B := hs2 A B hApos.le
    have hX : 0 ≤ mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := div_nonneg hMT hu.le
    -- reciprocal bound
    have hrec : ∀ s : ℝ, Real.log A ^ ((1 : ℝ) / 2) ≤ A ^ s / 2 →
        1 / A ^ s ≤ 1 / (2 * Real.log A ^ ((1 : ℝ) / 2)) := by
      intro s hs
      exact one_div_le_one_div_of_le (by have := hu; positivity) (by linarith)
    -- generic term bound
    have term : ∀ (s kk : ℝ), 0 ≤ kk → 1 / A ^ s ≤ 1 / (2 * Real.log A ^ ((1 : ℝ) / 2)) →
        kk * mainTerm d n A B / A ^ s ≤
          (kk / 2) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) := by
      intro s kk hk hrc
      have hL : kk * mainTerm d n A B / A ^ s = (kk * mainTerm d n A B) * (1 / A ^ s) := by
        rw [div_eq_mul_one_div]
      have hR : (kk / 2) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) =
          (kk * mainTerm d n A B) * (1 / (2 * Real.log A ^ ((1 : ℝ) / 2))) := by
        field_simp
      rw [hL, hR]
      exact mul_le_mul_of_nonneg_left hrc (mul_nonneg hk hMT)
    have b1 : |Sigma1 d n A B - mainTerm d n A B| ≤ |K₁| * mainTerm d n A B / A ^ s₁ :=
      le_trans (h1 A B hB1 hA1 hA2)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K₁) hMT)
          (Real.rpow_nonneg hApos.le _))
    have b2 : Sigma2 d n A B ≤ |K₂| * mainTerm d n A B / A ^ s₂ :=
      le_trans (h2 A B hB2 hA1 hA2)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K₂) hMT)
          (Real.rpow_nonneg hApos.le _))
    have t1 := term s₁ |K₁| (abs_nonneg _) (hrec s₁ hE1)
    have t2 := term s₂ |K₂| (abs_nonneg _) (hrec s₂ hE2)
    calc |Dglob d n A B - mainTerm d n A B|
        = |(Sigma1 d n A B - mainTerm d n A B) + Sigma2 d n A B| := by
          rw [hsplit A B]; ring_nf
      _ ≤ |Sigma1 d n A B - mainTerm d n A B| + |Sigma2 d n A B| := abs_add_le _ _
      _ = |Sigma1 d n A B - mainTerm d n A B| + Sigma2 d n A B := by rw [abs_of_nonneg hS2]
      _ ≤ |K₁| * mainTerm d n A B / A ^ s₁ + |K₂| * mainTerm d n A B / A ^ s₂ := add_le_add b1 b2
      _ ≤ (|K₁| / 2) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) +
          (|K₂| / 2) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) := add_le_add t1 t2
      _ = ((|K₁| / 2) + (|K₂| / 2)) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ (|K₁| + |K₂|) * (mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg K₁, abs_nonneg K₂]) hX
      _ = (|K₁| + |K₂|) * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by ring
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp key
  exact ⟨|K₁| + |K₂|, B₀, fun A B hB hA1 hA2 => hB₀ B hB A hA1 hA2⟩

end Work.HP
