/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.iwSymbolSet_mul
import Submission.Work.Analysis.IonescuWainger.Height

/-!
# Major arcs, good major arcs and the Ionescu–Wainger projections

This file collects the definitional interface used in §5 of Krause–Mirek–Tao together with the
symbol-level manipulations of the IW projections:

* `iwArithFreqsNew ρ l` — the "new" arithmetic frequencies `(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`;
* `iwSymbol_eq_sdiff` — the decomposition `T^{≤l}_Φ = T^{≤l-1}_Φ + T^l_Φ` (`iw-prop`, first part);
* `etaCut` and `iwProj` — the Littlewood–Paley cutoffs `η_{≤k}` and the paper's projections
  `Π_{≤l,≤k} = T^{≤l}_{η_{≤k}}`;
* `iwOpSet_comp` — the functional calculus `T^{≤l}_{Φ₁Φ₂} = T^{≤l}_{Φ₁} ∘ T^{≤l}_{Φ₂}`
  (`iw-prop`, functional calculus) at the level of operators, under non-aliasing;
* `exists_goodMajorArcs_nonAliasing` — good major arcs imply non-aliasing (Theorem `thm:iw`,
  first assertion).

## Main definitions

* `Work.Analysis.IonescuWainger.iwArithFreqsNew`
* `Work.Analysis.IonescuWainger.etaCut`
* `Work.Analysis.IonescuWainger.iwProj`
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- The "new" arithmetic frequencies of height exactly `2^l`:
`(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`, with `(ℚ/ℤ)_{≤-1} = ∅`. -/
noncomputable def iwArithFreqsNew (ρ : ℝ) (l : ℕ) : Finset Circle :=
  iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1)

/-- The Littlewood–Paley cutoff `η_{≤k}(θ) = η(θ / 2^k)` of the paper's Section
"Averages, indicators, and cutoffs". -/
noncomputable def etaCut (η : ℝ → ℂ) (k : ℤ) : ℝ → ℂ :=
  fun θ => η (θ / (2 : ℝ) ^ k)

/-- The Ionescu–Wainger Fourier projection `Π_{≤l,≤k} = T^{≤l}_{η_{≤k}}` of the paper's §5. -/
noncomputable def iwProj (η : ℝ → ℂ) (ρ : ℝ) (l : ℕ) (k : ℤ)
    (h : MemLp (iwSymbol ρ l (periodize (etaCut η k))) ⊤ circleMeasure) : L2Z →L[ℂ] L2Z :=
  iwOp ρ l (periodize (etaCut η k)) h

/-- **Decomposition of the IW projections** (`iw-prop`, `T^{≤l}_Φ = T^{≤l-1}_Φ + T^{l}_Φ`): the
symbol of height `≤ l` splits into the symbols of height `≤ l - 1` and of height exactly `l`. -/
theorem iwSymbol_eq_sdiff {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (Φ : Circle → ℂ) :
    iwSymbol ρ l Φ = iwSymbol ρ (l - 1) Φ + iwSymbolSet (iwArithFreqsNew ρ l) Φ := by
  simp only [iwSymbol, iwArithFreqsNew]
  exact iwSymbolSet_sdiff (iwArithFreqs ρ l) (iwArithFreqs ρ (l - 1))
    (iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)) Φ

end Work.Analysis.IonescuWainger
