import Mathlib
import Submission.Work.GM.Affine.region_II_resonant_high_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.tsum_resonance_eq_finsum
import Submission.Work.GM.Affine.supf_le_of_decay

namespace Work.GM.Affine

/-!
# GM §9, region II high part: the pointwise Cauchy–Schwarz step

This file proves the pointwise input of the high part of region II of GM Lemma 9.2:
on the region `4 M₁/M₃ < |ξ| ≤ T⁶`, the resonant part `ghatRes` of the Poisson expansion
of `ĝ` satisfies

`‖ghatRes K M₁ M₂ M₃ f ξ‖² ≤ Cc · V² · M₃² · resMajorant M₁ M₂ M₃ T f ξ`,

where `Cc` is the number of resonant pairs `(m₁, ℓ) ∈ R1 M₁ × [-⌈T⁶⌉-2, ⌈T⁶⌉+2]` with
`|ℓ - ξ/m₁| ≤ 2/M₃` and `V` bounds `‖ψ̂₁ K‖`.

The proof is Cauchy–Schwarz over the resonant pairs: `ghatRes` is the `M₃`-multiple of the sum
over *all* pairs in `resPairs M₁ T` of `(1/|m₁|) Bsum(ξ/m₁) · [|ℓ - ξ/m₁| ≤ 2/M₃] ψ̂₁(...)`,
the sum of the squares of whose terms is dominated by `V² · resMajorant`, and only the resonant
pairs contribute, of which there are at most `Cc`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-- The pointwise Cauchy–Schwarz bound for the high part of region II. -/
theorem resHigh_ghatRes_sq_le {K M₁ M₂ M₃ T V Cc : ℝ} (hM₁ : 0 < M₁) (hM₃ : 1 ≤ M₃)
    (hT : 1 ≤ T) (hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V) (hVnn : 0 ≤ V) (hCcnn : 0 ≤ Cc)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) {ξ : ℝ} (hξ : |ξ| ≤ T ^ 6)
    (hcard : (((resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)).card : ℝ) ≤ Cc) :
    ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ Cc * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := by
  -- the summand attached to a pair `(m₁, ℓ)`
  set A : ℤ × ℤ → ℂ := fun p =>
      ((|(p.1 : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (p.1 : ℝ)) *
        (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
          psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))) else 0) with hA
  -- (1) `ghatRes` is `M₃` times the sum over all candidate pairs
  have hghat : ghatRes K M₁ M₂ M₃ f ξ = (M₃ : ℂ) * ∑ p ∈ resPairs M₁ T, A p := by
    simp only [hA]
    -- the resonance sum for `x = ξ/m₁` is supported on `[-⌈T⁶⌉-2, ⌈T⁶⌉+2]`
    have hL : ∀ m₁ ∈ R1 M₁,
        (∑' ℓ : ℤ, if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
            psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0)
        = ∑ ℓ ∈ Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2),
            (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
              psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0) := by
      intro m₁ hm₁
      have hm₁ne : (m₁ : ℝ) ≠ 0 := by
        have hgt : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
        intro h; rw [h, abs_zero] at hgt; linarith
      have hge1 : (1 : ℝ) ≤ |(m₁ : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |m₁| := Int.one_le_abs (by simpa using hm₁ne)
        rw [← Int.cast_abs]; exact_mod_cast h1
      have hx : |ξ / (m₁ : ℝ)| ≤ (((⌈T ^ 6⌉ + 2 : ℤ)) : ℝ) - 2 := by
        have h1 : |ξ / (m₁ : ℝ)| ≤ T ^ 6 := by
          rw [abs_div]
          exact (div_le_self (abs_nonneg _) hge1).trans hξ
        have h2 : T ^ 6 ≤ ((⌈T ^ 6⌉ : ℤ) : ℝ) := Int.le_ceil _
        push_cast
        linarith
      exact tsum_resonance_eq_finsum hM₃ hx
    calc ghatRes K M₁ M₂ M₃ f ξ
        = ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            ((M₃ : ℂ) * ∑' ℓ : ℤ, (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
              psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0)) := rfl
      _ = ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            ((M₃ : ℂ) * ∑ ℓ ∈ Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2),
              (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
                psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0)) :=
          Finset.sum_congr rfl (fun m₁ hm₁ => by rw [hL m₁ hm₁])
      _ = (M₃ : ℂ) * ∑ p ∈ resPairs M₁ T,
          ((|(p.1 : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (p.1 : ℝ)) *
            (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
              psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))) else 0) := by
        rw [show resPairs M₁ T = (R1 M₁) ×ˢ (Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2))
          from rfl]
        rw [Finset.mul_sum]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro m₁ hm₁
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        ring
  -- (2) pointwise bound of the square of the summand by `V² · (weight)`
  have hpt : ∀ p ∈ resPairs M₁ T, |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ →
      ‖A p‖ ^ 2 ≤ V ^ 2 * ((1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2) := by
    intro p hp hc
    have hAval : ‖A p‖ = (1 / |(p.1 : ℝ)|) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ *
        ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖ := by
      simp only [hA, if_pos hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_abs, one_div]
    rw [hAval, mul_pow, mul_pow]
    have hpsi2 : ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖ ^ 2 ≤ V ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hV _) 2
    have hinv : (1 / |(p.1 : ℝ)|) ^ 2 = 1 / (p.1 : ℝ) ^ 2 := by
      rw [one_div, one_div, inv_pow, sq_abs]
    rw [hinv]
    have hnn : (0 : ℝ) ≤ (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 := by positivity
    calc (1 / (p.1 : ℝ) ^ 2 * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2) *
          ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖ ^ 2
        ≤ (1 / (p.1 : ℝ) ^ 2 * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2) * V ^ 2 :=
          mul_le_mul_of_nonneg_left hpsi2 hnn
      _ = V ^ 2 * ((1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2) := by ring
  -- (3) Cauchy–Schwarz over the resonant pairs
  have hCS : ‖∑ p ∈ resPairs M₁ T, A p‖ ^ 2 ≤
      (((resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)).card : ℝ) *
        ∑ p ∈ (resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃), ‖A p‖ ^ 2 := by
    have hle : ‖∑ p ∈ resPairs M₁ T, A p‖ ≤ ∑ p ∈ resPairs M₁ T, ‖A p‖ := norm_sum_le _ _
    have hvan : ∀ p ∈ resPairs M₁ T,
        p ∉ (resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃) → ‖A p‖ = 0 := by
      intro p hp hpt'
      have hnc : ¬ (|(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃) := by
        intro hc; exact hpt' (Finset.mem_filter.mpr ⟨hp, hc⟩)
      simp only [hA, if_neg hnc, mul_zero, norm_zero]
    have hsum_eq : (∑ p ∈ (resPairs M₁ T).filter
          (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃), ‖A p‖)
        = ∑ p ∈ resPairs M₁ T, ‖A p‖ :=
      Finset.sum_subset (Finset.filter_subset _ _) hvan
    calc ‖∑ p ∈ resPairs M₁ T, A p‖ ^ 2
        ≤ (∑ p ∈ resPairs M₁ T, ‖A p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = (∑ p ∈ (resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃),
            ‖A p‖) ^ 2 := by rw [hsum_eq]
      _ ≤ (((resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)).card : ℝ) *
            ∑ p ∈ (resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃),
              ‖A p‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
  -- (4) the sum of the squares is dominated by `V² · resMajorant`
  have hsum_bound : ∑ p ∈ (resPairs M₁ T).filter
        (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃), ‖A p‖ ^ 2
      ≤ V ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := by
    rw [Finset.sum_filter]
    have hstep : ∑ p ∈ resPairs M₁ T, (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then ‖A p‖ ^ 2 else 0)
        ≤ ∑ p ∈ resPairs M₁ T, V ^ 2 * (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
            (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hc : |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃
      · rw [if_pos hc, if_pos hc]; exact hpt p hp hc
      · rw [if_neg hc, if_neg hc, mul_zero]
    refine hstep.trans (le_of_eq ?_)
    rw [resMajorant_eq, ← Finset.mul_sum]
  -- (5) assemble
  have hnormM₃ : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hM₃)]
  calc ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
      = M₃ ^ 2 * ‖∑ p ∈ resPairs M₁ T, A p‖ ^ 2 := by rw [hghat, norm_mul, hnormM₃, mul_pow]
    _ ≤ M₃ ^ 2 * (Cc * (V ^ 2 * resMajorant M₁ M₂ M₃ T f ξ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg M₃)
        calc ‖∑ p ∈ resPairs M₁ T, A p‖ ^ 2
            ≤ (((resPairs M₁ T).filter (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃)).card : ℝ) *
                ∑ p ∈ (resPairs M₁ T).filter
                  (fun p => |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃), ‖A p‖ ^ 2 := hCS
          _ ≤ Cc * (V ^ 2 * resMajorant M₁ M₂ M₃ T f ξ) :=
              mul_le_mul hcard hsum_bound (by positivity) hCcnn
    _ = Cc * V ^ 2 * M₃ ^ 2 * resMajorant M₁ M₂ M₃ T f ξ := by ring

end

end Work.GM.Affine
