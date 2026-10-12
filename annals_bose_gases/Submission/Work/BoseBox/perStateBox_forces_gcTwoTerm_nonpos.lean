import ChallengeDeps
import Submission.Work.BoseBox.Word
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.perStateBox_forces_gcTwoTerm_nonpos`

The per-state box bound `Work.BoseBox.PerStateBox` (every admissible state of
every large box has canonical energy shifted by `8π(a v)ρN` at least
`L³·gcTwoTerm (a v) C (1/2+η₀) ρ`) **forces** the two-term value to be
nonpositive at small diluteness.

The mechanism is the empty box `N = 0` (the same sector that pins `R' = 0` in
`Work.UBBInputs.dlSlide_forces_Rprime_nonpos`): a `0`-particle state of the box
`(0, L)` is admissible (`0 ≤ 2ρL³`) for every `ρ > 0` and `L > 0`, its
Rayleigh quotient vanishes (`𝓗 0 v Ψ = 0`, both sums of the Hamiltonian being
empty), and no chemical-potential shift is applied (`8π(a v)ρ·0 = 0`).  So the
per-state bound reads `L³·gcTwoTerm (a v) C (1/2+η₀) ρ ≤ 0`, and dividing by
`L³ > 0` gives the claim.

This is exactly the statement that the value FS subtracts at the chemical
potential `8π(a v)ρ` dominates the LHY two-term value — the consistency
condition of the `G`-chain (compare `Work.BoseBox.Lambda_nonpos_of_small`,
which proves the same inequality for `Λ` from `A ≥ 0`, `C ≥ 0`).
-/

noncomputable section

open MeasureTheory
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

namespace Work.BoseBox


set_option autoImplicit false

/-- `𝓗 0 v Ψ = 0`: both sums defining the Hamiltonian are empty in the
`0`-particle sector. -/
lemma hamiltonian_zero (v : ℝ³ → ℝ) (Ψ : X 0 → ℝ) (x : X 0) :
    _root_.BoseGases.𝓗 0 v Ψ x = 0 := by
  simp [_root_.BoseGases.𝓗]

/-- The canonical Rayleigh quotient of a `0`-particle box state vanishes. -/
lemma rayl_zero_of_empty {v : ℝ³ → ℝ} (L : ℝ) (Ψ : CInfty0Box 0 L) :
    Rayl 0 L v Ψ = 0 := by
  have hnum : (∫ x in box 0 L, (Ψ : X 0 → ℝ) x * _root_.BoseGases.𝓗 0 v (Ψ : X 0 → ℝ) x) = 0 := by
    simp [hamiltonian_zero]
  simp [Rayl, hnum]

theorem perStateBox_forces_gcTwoTerm_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {η₀ C : ℝ} (hps : Work.BoseBox.PerStateBox v η₀ C) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ → Submission.BoseGases.gcTwoTerm (_root_.BoseGases.a v) C (1 / 2 + η₀) ρ ≤ 0 := by
  rcases hps with ⟨ε₀, hε₀, hps⟩
  refine ⟨ε₀, hε₀, fun ρ hρ hρsmall => ?_⟩
  rcases hps ρ hρ hρsmall with ⟨L₀, hL₀, hL⟩
  -- the empty box of side `L := max L₀ 1 ≥ L₀` is admissible
  set L : ℝ := max L₀ 1 with hLdef
  have hLL₀ : L₀ ≤ L := le_max_left _ _
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  obtain ⟨Ψ⟩ := nonempty_CInfty0Box 0 hLpos
  have hadm : ((0 : ℕ) : ℝ) ≤ 2 * ρ * L ^ 3 := by
    have h2 : (0 : ℝ) ≤ 2 * ρ := by linarith
    have h3 : (0 : ℝ) ≤ L ^ 3 := pow_nonneg hLpos.le 3
    have : (0 : ℝ) ≤ 2 * ρ * L ^ 3 := mul_nonneg h2 h3
    simpa using this
  have hb := hL L hLL₀ 0 hadm Ψ
  simp [rayl_zero_of_empty L Ψ] at hb
  by_contra hcon
  have hcon' : 0 < Submission.BoseGases.gcTwoTerm (_root_.BoseGases.a v) C (1 / 2 + η₀) ρ :=
    not_le.mp hcon
  have hpos : 0 < L ^ 3 * Submission.BoseGases.gcTwoTerm (_root_.BoseGases.a v) C (1 / 2 + η₀) ρ :=
    mul_pos (pow_pos hLpos 3) hcon'
  linarith

end Work.BoseBox
