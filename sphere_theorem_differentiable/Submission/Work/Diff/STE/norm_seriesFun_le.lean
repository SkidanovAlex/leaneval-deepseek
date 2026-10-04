import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sup-norm bound for a Fourier series in terms of its weighted `ℓ²` norm

For a coefficient family `c : (ι → ℤ) → ℂ` whose weighted `ℓ²`-norm
`CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²` is finite, and `card ι < 2 s` (Sobolev exponent above
the critical one `d/2`), the Fourier series `seriesFun c x = Σ_k c k · exp (2πi k·x)`
is bounded uniformly in `x`:

  `‖seriesFun c x‖ ≤ C · √(CSq s c)`,

with `C = √(Σ_k ⟨k⟩^{-2s})` depending only on `ι` and `s`.

The proof is the elementary Sobolev embedding step: the unit-modulus characters give
`‖seriesFun c x‖ ≤ Σ_k ‖c k‖`, and the weighted `ℓ²`-norm controls `Σ_k ‖c k‖`
(Cauchy–Schwarz against the dual weight `⟨k⟩^{-2s}`, which is summable precisely for
`card ι < 2 s` — this is `Work.Diff.STE.l1_le_sqrt_CSq`).  To obtain summability of the
series itself we use the arithmetic–geometric mean inequality
`‖c k‖ = √(⟨k⟩^{2s}‖c k‖²) · √(⟨k⟩^{-2s}) ≤ (⟨k⟩^{2s}‖c k‖² + ⟨k⟩^{-2s})/2`.
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted `ℓ¹`-norm `Σ_k ‖c k‖` is finite as soon as the weighted `ℓ²`-norm
`CSq s c = Σ_k ⟨k⟩^{2s}‖c k‖²` is finite and `card ι < 2 s`. -/
private lemma summable_norm_of_CSq (s : ℕ) (hs : Fintype.card ι < 2 * s)
    (c : (ι → ℤ) → ℂ)
    (h : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖c k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => ‖c k‖) := by
  -- The dual weight `⟨k⟩^{-2s}` is summable because `card ι < 2 s`.
  have hB : Summable (fun k : ι → ℤ => ((wt k) ^ s)⁻¹) := by
    refine (summable_wt_zpow (ι := ι) s hs).congr fun k => ?_
    rw [zpow_neg, zpow_natCast]
  -- Arithmetic–geometric mean: `‖c k‖ ≤ (⟨k⟩^{2s}‖c k‖² + ⟨k⟩^{-2s})/2`.
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((h.add hB).div_const 2)
  have hA : 0 ≤ (wt k) ^ s * ‖c k‖ ^ 2 :=
    mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _)
  have hBk : 0 ≤ ((wt k) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (wt_pos k).le s)
  have hw : ((wt k) ^ s) ≠ 0 := pow_ne_zero s (wt_pos k).ne'
  have hsq : (wt k) ^ s * ‖c k‖ ^ 2 * ((wt k) ^ s)⁻¹ = ‖c k‖ ^ 2 :=
    calc (wt k) ^ s * ‖c k‖ ^ 2 * ((wt k) ^ s)⁻¹
        = ‖c k‖ ^ 2 * ((wt k) ^ s * ((wt k) ^ s)⁻¹) := by ring
      _ = ‖c k‖ ^ 2 := by rw [mul_inv_cancel₀ hw, mul_one]
  have hsqrt : Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2 * ((wt k) ^ s)⁻¹) = ‖c k‖ := by
    rw [hsq, Real.sqrt_sq (norm_nonneg _)]
  have hamgm : Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹)
      ≤ ((wt k) ^ s * ‖c k‖ ^ 2 + ((wt k) ^ s)⁻¹) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) - Real.sqrt (((wt k) ^ s)⁻¹)),
      Real.sq_sqrt hA, Real.sq_sqrt hBk]
  have hstep : Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) = ‖c k‖ := by
    rw [← Real.sqrt_mul hA, hsqrt]
  calc ‖c k‖ = Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) := hstep.symm
    _ ≤ ((wt k) ^ s * ‖c k‖ ^ 2 + ((wt k) ^ s)⁻¹) / 2 := hamgm

theorem norm_seriesFun_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hs : Fintype.card ι < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      ∀ x : ι → ℝ, ‖Work.Diff.STE.seriesFun c x‖ ≤ C * Real.sqrt (Work.Diff.STE.CSq s c) := by
  obtain ⟨C, hC, hbound⟩ := l1_le_sqrt_CSq (ι := ι) s hs
  refine ⟨C, hC, fun c h x => ?_⟩
  -- Summability of the series, from the weighted `ℓ²` bound.
  have hnorm : Summable (fun k : ι → ℤ => ‖c k‖) := summable_norm_of_CSq s hs c h
  have hser : Summable (fun k : ι → ℤ => ‖c k * fourierExp k x‖) :=
    hnorm.congr fun k => by rw [norm_mul, norm_fourierExp, mul_one]
  calc ‖seriesFun c x‖ = ‖∑' k : ι → ℤ, c k * fourierExp k x‖ := rfl
    _ ≤ ∑' k : ι → ℤ, ‖c k * fourierExp k x‖ := norm_tsum_le_tsum_norm hser
    _ = ∑' k : ι → ℤ, ‖c k‖ := tsum_congr fun k => by rw [norm_mul, norm_fourierExp, mul_one]
    _ ≤ C * Real.sqrt (CSq s c) := hbound c h

end Work.Diff.STE
