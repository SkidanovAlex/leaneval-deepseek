/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.Assembly

/-!
# The "display" of `small_shift` / `U2_to_progression` at an arbitrary scale

The conclusion of `Work.Peluse.PeluseULowering` (and of the chapters `Ulower/gap_regime`,
`Ulower/U2_to_progression`, `Ulower/small_shift`) is a three-part display in the two parameters
`q, N'`:

* a bound on `q`,
* a bound `N' ≥ …`,
* a bound `progAvgSum N' q f₁ ≥ …`,

whose two bases are `D / M` and `M / D`, where `M` is the **scale** at which the dual function
`F₂ = dualFn N P f₀ f₁` is analysed.  For `PeluseULowering` one has `M = N ^ P.natDegree` (the
theorem `Work.Peluse.Ulower.Display`); the balanced chapters are stated with `M = Ns` (the declared
support range, `Scaled Ns N d`).  `Work.Peluse.Ulower.DisplayAt` is the common generalisation.

The lemma `small_shift` reduces to `Display` by analysing the dual function at the balanced scale
`Ns := max N₀ (N ^ P.natDegree)`, which is legitimate exactly because the hypothesis of `small_shift`
is `D ≤ N ^ P.natDegree / 2`, so that `D ≤ Ns` — and the two scales are comparable,
`N ^ d / 2 ≤ Ns ≤ 2 * N ^ d`.

* `DisplayAt` — the display at scale `M`;
* `display_iff_displayAt` — `Display` is the case `M = N ^ P.natDegree`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The three-part display of `PeluseULowering` at an arbitrary scale `M`: there are `q, N'` with
`1 ≤ q ≤ C A'^K (M/D)^K δ^{-K}`, `1 ≤ N' ≤ N`, and

`δ^K (D/M)^K N ≤ C A'^K (M/D)^K δ^{-K} N'`,
`δ^K (D/M)^K N₀ ≤ C A'^K (M/D)^K δ^{-K} progAvgSum N' q f₁`. -/
def DisplayAt (P : Polynomial ℤ) (C K : ℕ) (A' : ℝ) (M N N₀ D : ℕ) (f₁ : ℤ → ℂ) (δ : ℝ) : Prop :=
  ∃ q N' : ℕ, 1 ≤ q ∧
    (q : ℝ) ≤ (C : ℝ) * A' ^ K * ((M : ℝ) / (D : ℝ)) ^ K * (δ⁻¹) ^ K ∧
    1 ≤ N' ∧ N' ≤ N ∧
    δ ^ K * ((D : ℝ) / (M : ℝ)) ^ K * (N : ℝ) ≤
      (C : ℝ) * A' ^ K * ((M : ℝ) / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ) ∧
    δ ^ K * ((D : ℝ) / (M : ℝ)) ^ K * (N₀ : ℝ) ≤
      (C : ℝ) * A' ^ K * ((M : ℝ) / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
        Work.Peluse.progAvgSum N' (q : ℤ) f₁

/-- `Display` (the display of `PeluseULowering`, used by `Ulower/gap_regime`) is the case
`M = N ^ P.natDegree` of `DisplayAt`. -/
lemma display_iff_displayAt {P : Polynomial ℤ} {C K : ℕ} {A' : ℝ} {N N₀ D : ℕ}
    {f₁ : ℤ → ℂ} {δ : ℝ} :
    Display P C K A' N N₀ D f₁ δ ↔
      DisplayAt P C K A' (N ^ P.natDegree) N N₀ D f₁ δ := by
  unfold Display DisplayAt
  rw [Nat.cast_pow]

end

end Work.Peluse.Ulower
