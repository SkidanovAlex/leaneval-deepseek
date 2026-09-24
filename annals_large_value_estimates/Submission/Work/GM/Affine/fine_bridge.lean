import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.supf_le_of_decay_three
import Submission.Work.GM.Affine.gSum_fourier
import Submission.Work.GM.Affine.affineSum_sq_le_gSum_sq

/-!
# GM §9: the fine case from the `gSum` bound (Route A bridge)

The affine sum is dominated pointwise by GM's majorant `gSum` (`affineSum_sq_le_gSum_sq`), so the
fine case of Proposition 9.1 follows from the corresponding bound for `∫ (gSum)²` — this is the
statement `hG` below, in the `Λ`-form with `Λ := supf f` (the `supf`-form of the decay hypothesis,
via `supf_le_of_decay_three`).  The file is a clean copy of the bridge, with no dependency on the
cancelled Route B (`lemma_9_2_fine`).

Note the contract's shape: `C' T^δ (Mbig^6 (∫f)^2 + Mbig^4 ∫f^2)` — in particular the second
term is `Mbig^4 ∫f²`, NOT `Mbig^2 √(∫f²) · √(…)`; the bridge from a `√`-shaped bound is done
separately by AM–GM.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- **Route A bridge**: the fine case of GM Proposition 9.1 follows from the `gSum` bound
`hG` of the contract's shape, in the `Λ`-form. -/
theorem fine_bridge
    (hG : ∀ (C₀ K T₀ : ℝ), 1 ≤ C₀ → 0 < K → 1 ≤ T₀ →
      ∀ (c : ℕ → ℝ → ℝ) (δ : ℝ), 0 < δ →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          ∀ Λ : ℝ, 0 < Λ →
          (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
            ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
          Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
          ∀ Mbig M₁ M₂ M₃ : ℝ,
          0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig → Mbig ≤ T ^ 4 →
          ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤
            C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2))
    {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        DecayHyp c T f → ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig → Mbig ≤ T ^ 4 →
        ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 ≤
          C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  obtain ⟨C', hC'pos, hGb⟩ := hG C₀ K T₀ hC₀ hK hT₀ c δ hδ
  refine ⟨C', hC'pos, ?_⟩
  intro T hT f hf hnn hsupp hdec Mbig M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMbT
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  have hV : (0 : ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hRHSnn : (0 : ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2 :=
    add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hV)
  by_cases hsup0 : supf f = 0
  · have hfz : ∀ u, f u = 0 := eq_zero_of_supf_eq_zero hf hcs hnn hsup0
    have hJ0 : ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 = 0 := by
      have hpt : ∀ u : ℝ, Submission.GM.affineSum K M₁ M₂ M₃ f u = 0 := by
        intro u
        simp [Submission.GM.affineSum, hfz]
      have hfun : (fun u => (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext u; rw [hpt u]; norm_num
      rw [hfun]; simp
    rw [hJ0]
    exact mul_nonneg (mul_nonneg hC'pos.le (Real.rpow_nonneg (by linarith) _)) hRHSnn
  · have hpos : 0 < supf f :=
      lt_of_le_of_ne (supf_nonneg hf hcs hnn) (Ne.symm hsup0)
    have hcompat : supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u :=
      supf_le_of_decay_three hT1 hf hcs hnn hdec hpos
    have hgb := hGb T hT f hf hnn hsupp (supf f) hpos hdec hcompat Mbig M₁ M₂ M₃
      hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMbT
    calc ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2
        ≤ ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 :=
          affineSum_sq_le_gSum_sq hK hM₁ hM₂ hM₃ hf hcs hnn
      _ ≤ C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := hgb

end

end Work.GM.Affine
