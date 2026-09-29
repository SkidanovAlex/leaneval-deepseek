import Mathlib
import Submission.Work.TMComp.C7Aux.Fresh.RTLv3

/-!
# S1 of the lead's C7 design — as a corollary of the proved `RTLv3`

The finite avalanche tower at a rational frequency is **already proved** in
`Submission/Work/TMComp/C7Aux/Fresh/RTLv3.lean` as
`Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3` (axiom-clean), with a statement that is
verbatim this one.  Per the lead's instruction (`C7_INPUTS_LEAD.md` follow-up) we therefore do
*not* re-prove it here: this file is a one-line derivation, so that callers of
`Work.TMC7Core.Scale.rat_tower_lower` (in particular `Scale/p_bj_of_dichotomy.lean`) get the
proved tower and no `sorry` stays on the critical path.
-/

namespace Work.TMC7Core.Scale

open Work.TMC7Core

/-- **S1** of the lead's C7 design (see `Scale/S1_GUIDE.md`): the finite rational tower,
derived from the proved `Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3`. -/
theorem rat_tower_lower (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ) (hLDT : HasLDTOn lam K c C)
    (hLEB : HasLEBound lam K C₀) (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 200)
    (b : ℝ) (hb : 0 < b) :
    ∃ B T : ℝ, 0 < B ∧ ∀ (k : ℕ) (P : ℕ → ℤ) (Q : ℕ → ℕ),
      (∀ i ≤ k, 1 ≤ Q i) → (∀ i < k, Q i < Q (i + 1)) →
      (∀ i ≤ k, Nat.Coprime (Int.natAbs (P i)) (Q i)) →
      (∀ i < k, |(P k : ℝ) / (Q k) - (P i : ℝ) / (Q i)| < 1 / ((Q i : ℝ) ^ 2)) →
      (∀ i < k, (Q (i + 1) : ℝ) ≤ Real.exp (b * (Q i : ℝ))) →
      T ≤ (Q 0 : ℝ) →
      ∀ E ∈ K, ∀ N₀ : ℕ, C * (κ ^ 2)⁻¹ * (Q 0 : ℝ) ≤ (N₀ : ℝ) →
      200 * κ < lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀ →
      (9 / 10) * lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
          < lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀) →
      2 * lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀)
          - lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
        ≤ lyap ((P k : ℝ) / (Q k)) lam (E : ℂ)
          + B * Real.exp (-(c * κ * (Q 0 : ℝ) / 8)) :=
  Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3 lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1 b hb

end Work.TMC7Core.Scale
