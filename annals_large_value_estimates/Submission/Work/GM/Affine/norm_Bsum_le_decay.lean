import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic

/-!
# `Work.GM.Affine.norm_Bsum_le_decay`

Pointwise decay bound for the `m₂`-sum `Bsum f M₂ x = Σ_{m₂ ∈ R2 M₂} m₂ · f̂(m₂ x)`.

If `‖f̂(ξ)‖ ≤ c j ε · T^ε · (T/|ξ|)^j · Λ` for all `ξ ≠ 0`, then for `x ≠ 0`
`‖Bsum f M₂ x‖ ≤ 4 M₂² · (c j ε · T^ε · Λ) · (T/(M₂|x|))^j`.

The proof is the trivial triangle inequality: `R2 M₂ ⊆ (M₂, 2M₂]` has at most `2M₂` elements,
each term has size at most `2M₂` times the value of the decay bound at `ξ = m₂ x ≥ M₂|x|`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The range `R2 M₂` contains at most `2 * M₂` integers (it is contained in
`[1, ⌊2 M₂⌋]`). -/
private lemma nbld_card_R2_le {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := by
  have hfloor : (0:ℤ) ≤ ⌊2 * M₂⌋ := Int.floor_nonneg.mpr (by linarith)
  have hnat : (R2 M₂).card ≤ (⌊2 * M₂⌋).toNat := by
    calc (R2 M₂).card
        ≤ (Finset.Icc (1:ℤ) ⌊2 * M₂⌋).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = (⌊2 * M₂⌋).toNat := by rw [Int.card_Icc]; congr 1; ring
  have hreal : ((⌊2 * M₂⌋).toNat : ℝ) ≤ 2 * M₂ := by
    have hcast : ((⌊2 * M₂⌋).toNat : ℝ) = (⌊2 * M₂⌋ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hfloor]
    rw [hcast]
    exact Int.floor_le (2 * M₂)
  exact le_trans (by exact_mod_cast hnat) hreal

theorem norm_Bsum_le_decay {f : ℝ → ℝ} {c : ℕ → ℝ → ℝ} {T Λ M₂ : ℝ} {j : ℕ} {ε : ℝ}
    (hT : 0 < T) (hΛ : 0 ≤ Λ) (hcj : 0 ≤ c j ε) (hM₂ : 1 ≤ M₂)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    {x : ℝ} (hx : x ≠ 0) :
    ‖Bsum f M₂ x‖ ≤ 4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ) * (T / (M₂ * |x|)) ^ j := by
  have hM2pos : 0 < M₂ := by linarith
  have hM2nn : 0 ≤ M₂ := hM2pos.le
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hTnn : 0 ≤ T := hT.le
  have hTε : 0 < T ^ ε := Real.rpow_pos_of_pos hT ε
  have hA0 : 0 ≤ c j ε * T ^ ε * Λ :=
    mul_nonneg (mul_nonneg hcj hTε.le) hΛ
  have hDpos : 0 < M₂ * |x| := mul_pos hM2pos hxpos
  have hDnn : 0 ≤ M₂ * |x| := hDpos.le
  have hPnn : 0 ≤ T / (M₂ * |x|) := div_nonneg hTnn hDnn
  set C : ℝ := 2 * M₂ * (c j ε * T ^ ε * Λ) * (T / (M₂ * |x|)) ^ j with hC
  have hCnn : 0 ≤ C := by
    rw [hC]; exact mul_nonneg (mul_nonneg (by linarith) hA0) (pow_nonneg hPnn j)
  have hterm : ∀ m₂ ∈ R2 M₂,
      ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖ ≤ C := by
    intro m₂ hm₂
    have hmpos : 0 < (m₂ : ℝ) := R2_pos' hm₂
    have hmle : (m₂ : ℝ) ≤ 2 * M₂ := R2_le' hm₂
    have hmgt : M₂ < (m₂ : ℝ) := (Finset.mem_filter.mp hm₂).2
    have hξne : (m₂ : ℝ) * x ≠ 0 := mul_ne_zero (ne_of_gt hmpos) hx
    have hdec' := hdec ((m₂ : ℝ) * x) hξne
    have hargle : M₂ * |x| ≤ |(m₂ : ℝ) * x| := by
      rw [abs_mul, abs_of_pos hmpos]
      exact mul_le_mul_of_nonneg_right hmgt.le (abs_nonneg x)
    have hdivle : T / |(m₂ : ℝ) * x| ≤ T / (M₂ * |x|) :=
      div_le_div_of_nonneg_left hTnn hDpos hargle
    have hpowle : (T / |(m₂ : ℝ) * x|) ^ j ≤ (T / (M₂ * |x|)) ^ j :=
      pow_le_pow_left₀ (div_nonneg hTnn (abs_nonneg _)) hdivle j
    have hstep : (m₂ : ℝ) * (T / |(m₂ : ℝ) * x|) ^ j ≤ (2 * M₂) * (T / (M₂ * |x|)) ^ j :=
      mul_le_mul hmle hpowle (pow_nonneg (div_nonneg hTnn (abs_nonneg _)) j) (by linarith)
    have hnorm : ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖
        = (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * x)‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hmpos]
    rw [hC, hnorm]
    calc (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * x)‖
        ≤ (m₂ : ℝ) * (c j ε * T ^ ε * (T / |(m₂ : ℝ) * x|) ^ j * Λ) :=
          mul_le_mul_of_nonneg_left hdec' hmpos.le
      _ = (c j ε * T ^ ε * Λ) * ((m₂ : ℝ) * (T / |(m₂ : ℝ) * x|) ^ j) := by ring
      _ ≤ (c j ε * T ^ ε * Λ) * ((2 * M₂) * (T / (M₂ * |x|)) ^ j) :=
          mul_le_mul_of_nonneg_left hstep hA0
      _ = 2 * M₂ * (c j ε * T ^ ε * Λ) * (T / (M₂ * |x|)) ^ j := by ring
  calc ‖Bsum f M₂ x‖
      ≤ ∑ m₂ ∈ R2 M₂, ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖ := by
        rw [Bsum]; exact norm_sum_le _ _
    _ ≤ ∑ _m₂ ∈ R2 M₂, C := Finset.sum_le_sum hterm
    _ = ((R2 M₂).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * M₂) * C := mul_le_mul_of_nonneg_right (nbld_card_R2_le hM2nn) hCnn
    _ = 4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ) * (T / (M₂ * |x|)) ^ j := by rw [hC]; ring

end

end Work.GM.Affine
