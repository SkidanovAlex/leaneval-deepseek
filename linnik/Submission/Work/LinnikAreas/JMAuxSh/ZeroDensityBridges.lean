
import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.ZeroDensity.Defs

/-!
# Bridges from the shared zero-density chapter (`Work.ZeroDensity`) to the Area 2 inputs

The subproject `Submission/Work/ZeroDensity` states the family zero-density theorems in its own
vocabulary (`famCount`, `FamDensityEpsRange`, `MontgomerySharp`).  The two theorems below
transliterate them into the two inputs of `Work.LinnikAreas.area2`, so that as soon as the
chapter's targets are proved the deliverable can be closed by importing them.
-/

namespace Work.LinnikAreas.JMAuxSh

open DirichletCharacter
open scoped Classical BigOperators

/-- Jutila's log-free family zero-density estimate, in the chapter's `ε`-in-the-base form on
`σ ≥ 4/5`, is the Area 2 input `FamilyZeroDensityJutila`. -/
theorem familyZeroDensityJutila_of_famDensityEpsRange
    (h : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2) :
    Work.LinnikAreas.FamilyZeroDensityJutila := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  exact hh q hq σ T hσ hσ1 hT

/-- Montgomery's sharp density theorem, in the chapter's `MontgomerySharp` form for every
logarithmic power `B`, is the sharp input of Area 2. -/
theorem familyZeroDensityMontgomerySharp_of_montgomerySharp
    (h : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikAreas.FamilyZeroDensityMontgomerySharp := by
  intro ε hε B hB
  obtain ⟨C, hC, hh⟩ := h B hB ε hε
  exact ⟨C, hC, fun q hq _inst σ T hσ hσ1 hT => hh q hq σ T hσ hσ1 hT⟩

/-- **A single non-principal character's near-line zero count at height `1`, from the
*non-principal* form of Jutila's bound.**

This is the non-principal analogue of `Work.LinnikAreas.nearLineCount_of_familyDensityJutila`
(the same conclusion, `zeroCountIn χ σ 1 ≤ C·q^{c(1-σ)}` for `χ ≠ 1` and `σ ≥ 1 - 1/c`), but it
consumes the *weaker* hypothesis `FamilyZeroDensityJutilaNP`: the single character `χ ≠ 1` is
dominated by the sum over `Finset.univ.erase 1` (`Finset.single_le_sum`, available exactly because
`χ ≠ 1`), and the all-character statement is never used.  Consumers that only ever need a single
non-principal character should use this version, since `FamilyZeroDensityJutilaNP` — and not its
all-character strengthening — is Jutila's theorem. -/
theorem nearLineCount_of_jutilaNP (h : FamilyZeroDensityJutilaNP) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
        1 - 1 / c ≤ σ → σ ≤ 1 →
        zeroCountIn χ σ 1 ≤ C * (q : ℝ) ^ (c * (1 - σ)) := by
  obtain ⟨C, hCpos, hC⟩ := h 1 (by norm_num)
  refine ⟨C, hCpos, 5, by norm_num, 2, ?_⟩
  intro q hq _inst χ hχ σ hσc hσ1
  have hq2 : 2 ≤ q := hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hσ45 : (4 : ℝ) / 5 ≤ σ := by linarith
  have hfam : (∑ χ' ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ' σ 1)
      ≤ C * (q : ℝ) ^ (3 * (1 - σ)) := by
    have h := hC q hq2 σ 1 hσ45 hσ1 le_rfl
    have hexp : ((q : ℝ) * 1) ^ ((2 + 1 : ℝ) * (1 - σ)) = (q : ℝ) ^ (3 * (1 - σ)) := by
      rw [mul_one, show (2 + 1 : ℝ) = 3 by norm_num]
    rwa [hexp] at h
  have hsingle : zeroCountIn χ σ 1
      ≤ ∑ χ' ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ' σ 1 :=
    Finset.single_le_sum (f := fun χ' => zeroCountIn χ' σ 1)
      (fun i _ => zeroCountIn_nonneg i σ 1) (Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ _⟩)
  refine le_trans (le_trans hsingle hfam) (mul_le_mul_of_nonneg_left ?_ hCpos.le)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [hσ1])

end Work.LinnikAreas.JMAuxSh
