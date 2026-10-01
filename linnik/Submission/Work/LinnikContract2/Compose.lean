/-
# LinnikContract2 — Compose.lean  (ROUND 2)

`linnik_of_areas`: the areas of the round-2 contract imply the challenge statement.  This file
is fully proved (no `sorry`, no axioms): all the analysis lives in the areas.

Imports: `Areas` (the contract), `Submission.Commons.NumberTheory.PrimesInAP.leastPrimeBound_of_large`
(the elementary small-modulus lifting) and `Submission.Linnik.Basic` (the elementary theory of
`p a d`).  The composition takes the seven paper areas and nothing else: it carries no numbering
input (`Area0` is a theorem of this development) and no setting clause (the window `¬ IsZ χ₁ ρ₁`
is closed inside `Area7` by `A7/WindowAssembly.lean`).
-/
import Submission.Work.LinnikContract2.Areas
import Submission.Commons.NumberTheory.PrimesInAP.leastPrimeBound_of_large
import Submission.Linnik.Basic

set_option linter.style.haveILetI false

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

open LeanEval.NumberTheory.Linnik

/-- **Composition (round 2).**  The areas of the round-2 contract give Linnik's theorem with
the explicit exponent `11/2 = 5.5`.

`Area 7` is instantiated at the `lamS` supplied by `Area 6` (which chooses the Siegel
threshold) and at the three certificates `h3 h1`, `h4 h1`, `h5 h1`; the §6 numbered zero is
supplied *inside* `Area 7` by the proved `Area0`.  `Area 2` is instantiated
at the resulting `η` (which chooses the box radius `R = R(η)`); the threshold `q₀` of the final
statement is `max (max q₂ q₆) (max q₇ 2)`; small moduli are handled by
`leastPrimeBound_of_large`. -/
theorem linnik_of_areas (h1 : Area1) (h2 : Area2) (h3 : Area3)
    (h4 : Area4) (h5 : Area5) (h6 : Area6) (h7 : Area7) :
    ∃ c : ℝ, ∀ ⦃a d : ℕ⦄, 0 < a → a < d → a.Coprime d → p a d ≤ c * d ^ (5.5 : ℝ) := by
  -- Area 6: the Siegel-zero threshold `lamS` and its threshold `q₆`.
  obtain ⟨lamS, hS0, q₆, hS⟩ := h6
  -- Area 7 at `lamS`: the gap `η` and, for every radius `R`, the threshold `q₇`.
  obtain ⟨η, hη, hZ⟩ := h7 (h3 h1) (h4 h1) (h5 h1) lamS hS0
  -- Area 2 at `η`: the box radius `R` and the threshold `q₂`.
  obtain ⟨R, hR, q₂, hRed⟩ := h2 η hη
  obtain ⟨q₇, hq₇⟩ := hZ R hR
  -- the large-modulus threshold
  set Q0 : ℕ := max (max q₂ q₆) (max q₇ 2) with hQ0
  -- for `d ≥ Q0`: a prime of the progression, of size `≤ d^(11/2)`
  have hH : ∀ ⦃a d : ℕ⦄, Q0 ≤ d → 0 < a → a < d → a.Coprime d →
      ∃ r : ℕ, r.Prime ∧ r ≡ a [MOD d] ∧ (r : ℝ) ≤ (d : ℝ) ^ (5.5 : ℝ) := by
    intro a d hdQ ha hd hcop
    haveI : NeZero d := ⟨by omega⟩
    have hd2 : q₂ ≤ d := by omega
    have hd6 : q₆ ≤ d := by omega
    have hd7 : q₇ ≤ d := by omega
    have hexp : (d : ℝ) ^ (11 / 2 : ℝ) = (d : ℝ) ^ (5.5 : ℝ) := by norm_num
    by_cases hSz : SiegelZero d lamS
    · -- Siegel case: Area 6 supplies the prime, `(r : ℝ) ≤ d^(11/2)`
      obtain ⟨r, hpr, hmr, hbr⟩ := hS d hd6 hSz a hcop
      rw [hexp] at hbr
      exact ⟨r, hpr, hmr, hbr⟩
    · -- otherwise the box sum is bounded away from `K²`, and Area 2 supplies the prime
      obtain ⟨r, hpr, hmr, hbr⟩ := hRed d hd2 a hcop (hq₇ d hd7 hSz a hcop)
      rw [hexp] at hbr
      exact ⟨r, hpr, hmr, hbr⟩
  -- lift from large moduli to all moduli
  obtain ⟨c, hc0, hc⟩ :=
    Commons.NumberTheory.PrimesInAP.leastPrimeBound_of_large (q₀ := Q0) (cH := 1) (by
      intro a d hdQ ha hd hcop
      obtain ⟨r, hpr, hmr, hbr⟩ := hH hdQ ha hd hcop
      exact ⟨r, hpr, hmr, by simpa using hbr⟩)
  refine ⟨c, ?_⟩
  intro a d ha hd hcop
  -- `c > 0`, so `0 < c * d^5.5`; a prime `r ≡ a` below that bound bounds the least prime
  obtain ⟨r, har, hbr, hpr, hmr⟩ := hc ha hd hcop
  have hle : p a d ≤ r := Submission.Linnik.p_le_of_prime_modEq hpr har hmr
  have hle' : ((p a d : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
  exact le_trans hle' hbr

end Work.LinnikContract2
