import Mathlib
import Submission.Work.Pert.PinAux.log_div_le
import Submission.Work.Pert.PinAux.log_max_div_le
import Submission.Work.Pert.PinAux.log_max_div_le_v2

/-!
# `Work.Pert.PinAux.collar_arith_fixed`

## Why this file exists

The statement requested as `Work.Pert.PinAux.collar_arith` (in `collar_arith.lean`) is **false**,
and so is its sibling `Work.Pert.PinAux.collar_arith2` (in `collar_arith2.lean`): in both, `M` is
only bounded **above**,

`M ≤ |z.im| + (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2`,

while the conclusion contains `A * Real.log (M / mz)`.  In this Mathlib `Real.log` is an even
function (`Real.log_neg_eq_log : Real.log (-x) = Real.log x`, i.e. `Real.log x = Real.log |x|`), so
`Real.log (M / mz) = Real.log (|M| / mz)` is *unbounded above* as `M → -∞`, while the right-hand
side does not depend on `M` at all.  Concretely, with `A = 1`, `K = 0`, `c = 0`, `R₁ = 1`, `Ξ = 1`,
`α = 1`, `z = 0`, `mz = 1`, `lo = hi = 0` and `M = -exp (Λ * (1 + log 2) + 2)` (all hypotheses are
satisfied, since `M` is negative) the claimed inequality reduces to `2 ≤ 0`.  This refutation is
machine-checked in `NOTES_collar_arith.md`; see also the `declare_false` report.

The missing hypothesis is `0 < M`.  It holds at every intended call site: in the assembly of
`collar_to_medial` one takes `M = minmarg Ξ α (med Ξ α z.im)`, a gate margin, which is positive.

## What is proved here

* `collar_arith_aux` / `collar_arith_aux_v2`: the abstract arithmetic, with the two bounds on `M`
  and on `max |lo| |hi|` kept as separate parameters `B`, `C`.
* `collar_arith_fixed`: the requested statement with `0 < M` added (original hypothesis on
  `max |lo| |hi|`).
* `collar_arith2_fixed`: `collar_arith2` with `0 < M` added; this is the shape whose `max |lo| |hi|`
  hypothesis is the one actually discharged at the call site of `collar_to_medial` (there,
  `max |lo| |hi| ≤ 2 * ‖z‖ + (|(1 / α).re| + |(1 / α).im|) + Ξ`).
-/

namespace Work.Pert.PinAux

/-- Abstract collar arithmetic, with the hypothesis on `max |lo| |hi|` in the form
`|z.im| + B`.  The constant produced is `A * ((1+B)/R₁ + 1) + 8K * ((1+B)*(2/Ξ) + 1) + 1`. -/
lemma collar_arith_aux (A K c R₁ Ξ B : ℝ) (z : ℂ) (M mz lo hi : ℝ)
    (hΞ : 0 < Ξ) (hΞB : Ξ ≤ B) (hB : 0 ≤ B) (hR₁ : 0 < R₁) (hA : 0 < A) (hK : 0 ≤ K)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256)
    (hmz : R₁ ≤ mz) (hMpos : 0 < M) (hM : M ≤ |z.im| + B)
    (hmax : max |lo| |hi| ≤ |z.im| + B) :
    A * Real.log (M / mz) + (c / (1 - c)) * (hi - lo)
        + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ (A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1)
          * (1 + Real.log (2 + ‖z‖)) + (c / (1 - c)) * ((hi - lo) + 1) := by
  have hA0 : 0 ≤ A := le_of_lt hA
  have hC1nn : 0 ≤ (1 + B) / R₁ := div_nonneg (by linarith) (le_of_lt hR₁)
  have hC2nn : 0 ≤ (1 + B) * (2 / Ξ) := mul_nonneg (by linarith) (by positivity)
  have hθnn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by have h := norm_nonneg z; linarith)
  have hcc : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
  have hM1 := log_div_le z M mz B R₁ hB hR₁ hmz hMpos hM
  have hX1 := log_max_div_le z lo hi B Ξ hB hΞB hΞ hmax
  have h1 : A * Real.log (M / mz) ≤ A * ((1 + B) / R₁ + Real.log (2 + ‖z‖)) :=
    mul_le_mul_of_nonneg_left hM1 hA0
  have h2 : 2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2))
      ≤ 2 + 2 * ((1 + B) * (2 / Ξ) + Real.log (2 + ‖z‖)) := by linarith
  have h3 : 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ 4 * K * (2 + 2 * ((1 + B) * (2 / Ξ) + Real.log (2 + ‖z‖))) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hΛc : A * ((1 + B) / R₁) + 8 * K + 8 * K * ((1 + B) * (2 / Ξ))
      ≤ A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1 := by
    nlinarith [hA0]
  have hΛl : A + 8 * K ≤ A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1 := by
    have hA1 : 0 ≤ A * ((1 + B) / R₁) := mul_nonneg hA0 hC1nn
    have hK1 : 0 ≤ 8 * K * ((1 + B) * (2 / Ξ)) := by
      have := mul_nonneg hK hC2nn
      linarith
    linarith
  have hsplit : (c / (1 - c)) * ((hi - lo) + 1)
      = (c / (1 - c)) * (hi - lo) + c / (1 - c) := by ring
  have hmain : A * Real.log (M / mz)
        + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ (A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1)
          * (1 + Real.log (2 + ‖z‖)) + c / (1 - c) := by
    nlinarith [h1, h3, hΛc, hΛl, hθnn, hcc, mul_le_mul_of_nonneg_right hΛl hθnn]
  rw [hsplit]
  linarith [hmain]

/-- Abstract collar arithmetic, with the hypothesis on `max |lo| |hi|` in the form `2 * ‖z‖ + C`
(the shape produced by the call site).  The constant produced is
`A * ((1+B)/R₁ + 1) + 8K * ((2*(2/Ξ) + (2/Ξ)*C + 1) + 1) + 1`. -/
lemma collar_arith_aux_v2 (A K c R₁ Ξ B C : ℝ) (z : ℂ) (M mz lo hi : ℝ)
    (hΞ : 0 < Ξ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR₁ : 0 < R₁) (hA : 0 < A) (hK : 0 ≤ K)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256)
    (hmz : R₁ ≤ mz) (hMpos : 0 < M) (hM : M ≤ |z.im| + B)
    (hmax : max |lo| |hi| ≤ 2 * ‖z‖ + C) :
    A * Real.log (M / mz) + (c / (1 - c)) * (hi - lo)
        + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ (A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1)
          * (1 + Real.log (2 + ‖z‖)) + (c / (1 - c)) * ((hi - lo) + 1) := by
  have hA0 : 0 ≤ A := le_of_lt hA
  have hC1nn : 0 ≤ (1 + B) / R₁ := div_nonneg (by linarith) (le_of_lt hR₁)
  have h2Ξ : 0 < 2 / Ξ := by positivity
  have hDnn : 0 ≤ 2 * (2 / Ξ) + (2 / Ξ) * C + 1 := by
    have := mul_nonneg (le_of_lt h2Ξ) hC
    linarith
  have hθnn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by have h := norm_nonneg z; linarith)
  have hcc : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
  have hM1 := log_div_le z M mz B R₁ hB hR₁ hmz hMpos hM
  have hX1 := log_max_div_le_v2 z lo hi Ξ C hΞ hC hmax
  have h1 : A * Real.log (M / mz) ≤ A * ((1 + B) / R₁ + Real.log (2 + ‖z‖)) :=
    mul_le_mul_of_nonneg_left hM1 hA0
  have h2 : 2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2))
      ≤ 2 + 2 * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + Real.log (2 + ‖z‖)) := by linarith
  have h3 : 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ 4 * K * (2 + 2 * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + Real.log (2 + ‖z‖))) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hΛc : A * ((1 + B) / R₁) + 8 * K + 8 * K * (2 * (2 / Ξ) + (2 / Ξ) * C + 1)
      ≤ A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1 := by
    nlinarith [hA0]
  have hΛl : A + 8 * K
      ≤ A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1 := by
    have hA1 : 0 ≤ A * ((1 + B) / R₁) := mul_nonneg hA0 hC1nn
    have hK1 : 0 ≤ 8 * K * (2 * (2 / Ξ) + (2 / Ξ) * C + 1) :=
      mul_nonneg (by linarith) hDnn
    linarith
  have hsplit : (c / (1 - c)) * ((hi - lo) + 1)
      = (c / (1 - c)) * (hi - lo) + c / (1 - c) := by ring
  have hmain : A * Real.log (M / mz)
        + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
      ≤ (A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1)
          * (1 + Real.log (2 + ‖z‖)) + c / (1 - c) := by
    nlinarith [h1, h3, hΛc, hΛl, hθnn, hcc, mul_le_mul_of_nonneg_right hΛl hθnn]
  rw [hsplit]
  linarith [hmain]

/-- The statement requested as `collar_arith`, with the missing hypothesis `0 < M` added.
Without it the statement is false (see the module docstring). -/
theorem collar_arith_fixed (A K c R₁ Ξ : ℝ) (α : ℂ) (hΞ : 0 < Ξ) (hR₁ : 0 < R₁) (hA : 0 < A)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (z : ℂ) (M mz lo hi : ℝ),
      R₁ ≤ mz → 0 < mz → 0 < M →
      M ≤ |z.im| + (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 →
      max |lo| |hi| ≤ |z.im| + (|(1 / α).re| + |(1 / α).im|) / 2 + Ξ →
      0 ≤ hi - lo →
      A * Real.log (M / mz) + (c / (1 - c)) * (hi - lo)
          + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
        ≤ Λ * (1 + Real.log (2 + ‖z‖)) + (c / (1 - c)) * ((hi - lo) + 1) := by
  set B : ℝ := (|(1 / α).re| + |(1 / α).im|) / 2 + Ξ with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hΞB : Ξ ≤ B := by
    rw [hBdef]
    have h1 := abs_nonneg (1 / α).re
    have h2 := abs_nonneg (1 / α).im
    linarith
  have hΛpos : 0 < A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1 := by
    have h1 : 0 < (1 + B) / R₁ := div_pos (by linarith) hR₁
    have h3 : 0 < A * ((1 + B) / R₁ + 1) := mul_pos hA (by linarith)
    have h4 : 0 ≤ 8 * K * ((1 + B) * (2 / Ξ) + 1) := by
      refine mul_nonneg (by linarith) ?_
      have : 0 < (1 + B) * (2 / Ξ) := mul_pos (by linarith) (by positivity)
      linarith
    linarith
  refine ⟨A * ((1 + B) / R₁ + 1) + 8 * K * ((1 + B) * (2 / Ξ) + 1) + 1, hΛpos, ?_⟩
  intro z M mz lo hi hmz _h0mz hMpos hM hmax hhi
  have hMB : (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 = B := by rw [hBdef]; ring
  have hMx : M ≤ |z.im| + B := by linarith [hM, hMB]
  have hmaxB : |z.im| + (|(1 / α).re| + |(1 / α).im|) / 2 + Ξ = |z.im| + B := by
    rw [hBdef]; ring
  have hmaxx : max |lo| |hi| ≤ |z.im| + B := by linarith [hmax, hmaxB]
  exact collar_arith_aux A K c R₁ Ξ B z M mz lo hi hΞ hΞB hBnn hR₁ hA hK hc0 hc hmz hMpos hMx hmaxx

/-- `collar_arith2` (the shape actually discharged at the call site of `collar_to_medial`), with
the missing hypothesis `0 < M` added.  Without it the statement is false. -/
theorem collar_arith2_fixed (A K c R₁ Ξ : ℝ) (α : ℂ) (hΞ : 0 < Ξ) (hR₁ : 0 < R₁) (hA : 0 < A)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (z : ℂ) (M mz lo hi : ℝ),
      R₁ ≤ mz → 0 < mz → 0 < M →
      M ≤ |z.im| + (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 →
      max |lo| |hi| ≤ 2 * ‖z‖ + (|(1 / α).re| + |(1 / α).im|) + Ξ →
      0 ≤ hi - lo →
      A * Real.log (M / mz) + (c / (1 - c)) * (hi - lo)
          + 4 * K * (2 + 2 * Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)))
        ≤ Λ * (1 + Real.log (2 + ‖z‖)) + (c / (1 - c)) * ((hi - lo) + 1) := by
  set B : ℝ := (|(1 / α).re| + |(1 / α).im|) / 2 + Ξ with hBdef
  set C : ℝ := (|(1 / α).re| + |(1 / α).im|) + Ξ with hCdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hΛpos : 0 < A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1 := by
    have h1 : 0 < (1 + B) / R₁ := div_pos (by linarith) hR₁
    have h3 : 0 < A * ((1 + B) / R₁ + 1) := mul_pos hA (by linarith)
    have h4 : 0 ≤ 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) := by
      refine mul_nonneg (by linarith) ?_
      have h2Ξ : 0 < 2 / Ξ := by positivity
      have := mul_nonneg (le_of_lt h2Ξ) hCnn
      linarith
    linarith
  refine ⟨A * ((1 + B) / R₁ + 1) + 8 * K * ((2 * (2 / Ξ) + (2 / Ξ) * C + 1) + 1) + 1, hΛpos, ?_⟩
  intro z M mz lo hi hmz _h0mz hMpos hM hmax hhi
  have hMB : (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 = B := by rw [hBdef]; ring
  have hMx : M ≤ |z.im| + B := by linarith [hM, hMB]
  have hCB : 2 * ‖z‖ + (|(1 / α).re| + |(1 / α).im|) + Ξ = 2 * ‖z‖ + C := by rw [hCdef]; ring
  have hmaxx : max |lo| |hi| ≤ 2 * ‖z‖ + C := by linarith [hmax, hCB]
  exact collar_arith_aux_v2 A K c R₁ Ξ B C z M mz lo hi hΞ hBnn hCnn hR₁ hA hK hc0 hc hmz hMpos
    hMx hmaxx

end Work.Pert.PinAux
