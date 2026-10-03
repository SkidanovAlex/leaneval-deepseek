/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.Defs

/-!
# The non-aliasing half of Theorem `thm:iw`

The first assertion of the vector-valued Ionescu–Wainger multiplier theorem (Theorem `thm:iw` of
Krause–Mirek–Tao), namely that *good major arcs do not alias the Ionescu–Wainger arithmetic
frequencies*, is already available in the Ionescu–Wainger API as
`Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing` (proved there from the separation
of `(ℚ/ℤ)_{≤l}`).  Here we record it in the vocabulary of Theorem `thm:iw`, i.e. as the statement
`Work.Analysis.IWMultiplier.IWNonAliasingStatement`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- **The non-aliasing half of Theorem `thm:iw`**, in the vocabulary of this area. -/
theorem iwNonAliasingStatement : IWNonAliasingStatement := by
  intro ρ hρ _
  obtain ⟨Cρ, hCρ, h⟩ := exists_goodMajorArcs_nonAliasing hρ
  exact ⟨Cρ, hCρ, fun l k hk => h l k hk⟩

/-- The non-aliasing half of Theorem `thm:iw` holds: instance form, giving the non-aliasing
hypothesis required by the multiplier theorem for a given good-major-arcs constant. -/
theorem iwNonAliasing_of_goodMajorArcsConstant {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l) := by
  obtain ⟨Cρ, hCρ, h⟩ := exists_goodMajorArcs_nonAliasing hρ
  exact ⟨Cρ, hCρ, h⟩

end Work.Analysis.IWMultiplier
