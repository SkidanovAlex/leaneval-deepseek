import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs

/-!
# The round of the §5 chain, with a bound on the level **and window bounds**

`Work.Peluse.Prop36SW.RoundStmtT` (`roundStmtT.lean`, proved as `Work.Prop36SW.roundPeelAuxT`)
concludes with a family of multiplicities and windows

    `∃ (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ), (∀ s, t s ≤ T) ∧ 1 ≤ card (Σ s, Fin (t s)) ∧
       (∀ s, M₂ ≤ Lw s) ∧ N ≤ N' ∧ C γ^E ≤ (the family bound)`.

The §5 chain of `Work.Peluse.prop36SW_of_ladderA` also needs **quantitative information on the
windows `Lw s`**, because the chain's *state window* `M₁'` of the next state is obtained from the
round's windows by shrinking them all (to a common value `Lw₀ = peelL M₁ M₂ γw`), and (a) the chain's
window must grow by a factor `≈ M₂` per round (the paper's `δ'M^j → δ'M^{j+1}`), and (b) the state's
side conditions `M₁' M₂ ≤ N`, `|p| M₁' M₂ ≤ N` need an *upper* bound for `M₁'`.

Neither bound is derivable from `RoundStmtT`'s conclusion, but both hold for the witnesses produced
by its proof, where

* the peeled slot's window is `⌊γ' M₁ M₂⌋` with `γ' = γ^K/C₀` (`γ ≤ 1`, `C₀ > 0` the ladder's
  constant), hence `Lw s ≤ M₁M₂/C₀` and `Lw s ≥ γ^KM₁M₂/(2C₀)` (the second because the round's proof
  proves `M₂ ≤ Lw s ≥ 2`, so `γ'M₁M₂ ≥ 2` and `⌊x⌋ ≥ x/2`);
* the remaining windows are the sub-round's windows, for which the same bounds hold by induction.

`RoundStmtW m` is `RoundStmtT m` with the existential bundle extended by three further
data-independent constants `c₀ > 0`, `E₀ : ℕ`, `C₁ ≥ 1` and the two window bounds

    `∀ s, c₀ · γ^{E₀} · M₁ · M₂ ≤ Lw s`  and  `∀ s, (Lw s : ℝ) ≤ C₁ · M₁ · M₂`.

The constants are again quantified *before* the instance data `(M₁, M₂, N, A, g, γ)`, i.e. they
depend only on the round's datum `(ι, kω, p, Dc)`.

## How to prove `roundPeelAuxW`

Copy the proof of the proved `Work.Prop36SW.roundPeelAuxT`
(`Submission/Work/Prop36SW/roundPeelAuxT.lean`, whose helpers `roundPeelStepT` and
`Work.Prop36SW.roundInfeasibleStepT` live in the same file resp.
`Submission/Work/Prop36SW/roundInfeasibleStep.lean`), adding the three constants and the two window
conjuncts to the existential bundle and to the conclusion.  Nothing else changes.

* In the infeasible branch (`roundInfeasibleStepT`) the witness is `Lw := fun _ => L'` with
  `L' := (⌊γ' * M₁ * M₂⌋).toNat`, `γ' := γ ^ K / C₀`, and the existing proof already has
  `hLw : ∀ s, M₂ ≤ Lw s` (via `roundWindowGe`).  Take `c₀ := 1 / (2 * C₀)`, `E₀ := K`,
  `C₁ := max 1 (1 / C₀)`.  Upper: `L' ≤ γ' M₁ M₂ = γ^K M₁M₂/C₀ ≤ M₁M₂/C₀` using `γ ≤ 1`.
  Lower: `M₂ ≤ L'` and `M₂ ≥ 1` give `γ' M₁ M₂ ≥ L' ≥ 2`, hence `⌊x⌋ ≥ x - 1 ≥ x/2` for
  `x = γ' M₁ M₂`, i.e. `L' ≥ γ^K M₁M₂ / (2 C₀)`.
* In the peel branch (`roundPeelStepT`) the new slot `s₀` gets `Lw s₀ = L'` (same bounds as above)
  and every other slot inherits the sub-round's window `Lrest s`, for which the induction
  hypothesis (the W-statement at the peeled slot type) gives
  `c₀' γ₁^{E₀'} M₁ M₂ ≤ Lrest s ≤ C₁' M₁ M₂`; combine with the existing
  `hγ₁ge : cc₂ * γ ^ Ae ≤ γ₁` and `γ₁ ≤ 1` to get
  `c₀' cc₂^{E₀'} γ^{Ae·E₀'} M₁M₂ ≤ Lrest s`.  Take
  `c₀ := min (1/(2C₀)) (c₀' * cc₂^{E₀'})`, `E₀ := max K (Ae * E₀')`, `C₁ := max 1 (max (1/C₀) C₁')`,
  and use `γ ≤ 1` (`γ^a ≥ γ^{a+b}`) to merge the two exponents.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- **The round of the §5 chain with a level bound and window bounds.** -/
def RoundStmtW (m : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = m →
  ∀ (n : ℕ) (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (Dc : ℕ),
    ∃ (C : ℝ) (E : ℕ) (Cn : ℝ) (Mn : ℕ) (T : ℕ) (c₀ : ℝ) (E₀ : ℕ) (C₁ : ℝ),
      0 < C ∧ 0 < Cn ∧ 1 ≤ Mn ∧ 1 ≤ T ∧ 0 < c₀ ∧ 1 ≤ C₁ ∧
      ∀ (M₁ M₂ N : ℕ) (A : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℤ → ℂ) (γ : ℝ),
        LStateAbs kω p M₁ M₂ N Dc A g γ →
        Cn * γ ^ (-(Mn : ℤ)) ≤ (M₂ : ℝ) →
        ∃ (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ),
          (∀ s : ι, t s ≤ T) ∧
          1 ≤ Fintype.card (Σ s : ι, Fin (t s)) ∧ (∀ s : ι, M₂ ≤ Lw s) ∧ N ≤ N' ∧
          (∀ s : ι, c₀ * γ ^ E₀ * (M₁ : ℝ) * (M₂ : ℝ) ≤ (Lw s : ℝ)) ∧
          (∀ s : ι, (Lw s : ℝ) ≤ C₁ * (M₁ : ℝ) * (M₂ : ℝ)) ∧
          C * γ ^ E ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
              (fun i => Work.Peluse.arithIcc
                (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
                (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
              (Work.Peluse.symIcc N') (g a)

end

end Work.Peluse.Prop36SW
