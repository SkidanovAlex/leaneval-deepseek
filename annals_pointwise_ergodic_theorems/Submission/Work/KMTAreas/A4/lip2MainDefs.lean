/-
# Definitions for the assembly of Proposition `lip-2` (`Work.KMTAreas.A4.lip2`)

This module fixes the vocabulary shared by the main-case assembly of `Work.KMTAreas.A4.lip2`
(Krause--Mirek--Tao, §5.2, proof of Proposition `lip-2`) and the delegated lemmas about it.

## The objects

* `lip2Avg N P M γ g s y` — the *windowed polynomial average of `g`* at the shift `s`:
  `(1/N) ∑_{N/2 < n ≤ N} win M γ (n - s) · g (y + P(n))`.  This is `1/N` times the
  interval-restricted exponential sum window applied to `g`; its `y`-Plancherel identity is
  `Work.KMTAreas.A4.lip2PlancherelIcc`, and its inverse-Weyl inversion is
  `Work.KMTAreas.A4.lip2WeylIcc` (applied to the multiplier `winSumIcc`).

  The main-case expansion of `lip2` reads
  `⟨Ã*_N(h,g), F⟩ = ∑_s ∑_y h y · F (y + s) · lip2Avg N P M γ g s y`
  when `𝓕_ℤ F` is supported in the arc of radius `1/(2M)` around `γ` (see
  `Work.KMTAreas.A4.lip2WindowExpansion`), and its truncation to `|s| ≤ S` costs a term
  bounded in `Work.KMTAreas.A4.lip2WindowTail`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The windowed polynomial average of `g` at the shift `s`:
`lip2Avg N P M γ g s y = (1/N) ∑_{N/2 < n ≤ N} win M γ (n - s) · g (y + P(n))`. -/
noncomputable def lip2Avg (N : ℕ) (P : Polynomial ℤ) (M : ℝ)
    (γ : Work.Analysis.InverseTheory.FreqCircle) (g : ℤ → ℂ) (s y : ℤ) : ℂ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
    win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))

end Work.KMTAreas.A4
