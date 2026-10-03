import Mathlib
import Submission.Work.Prop36SW.roundToNextDefs

/-!
# The interfaces of the §5 chain's rounds

The §5 chain of `Work.Peluse.prop36SW_of_ladderA` runs the round
(`Submission/Work/Prop36SW/roundToNextState.lean`, with a partial proof in
`Submission/Work/Prop36SW/roundToNext.lean`) `d - 2` times, and then one *final* round at slot
level `0` (`Work.Prop36SW.LastStep`, the endgame) which produces a uniformity-norm power directly.

**The constants must be data-independent.**  The chain's constants feed the node's
`∃ s, ∃ A, ∃ K` in `Work.Peluse.C46.Prop36SW`, which are quantified *before* the instance data
`(N, M, f, η, δ')`; in particular they may not depend on the data window `H = ⌊δ'M⌋`.  Hence the
existential bundles below are quantified **before** `H`, `M₁`, `M₂`, `N`, `f`, `γ`.

The state invariants maintained by the chain are, at slot level `m` with box window `M₂ = H+1`:

* the window bounds `c_m · γ^{e_m} · M₂^{d-1-m} ≤ M₁ ≤ M₂^{d-1-m}`: the window grows by a factor
  `≈ M₂` per round (the paper's `δ'M^j → δ'M^{j+1}`), and its *lower* bound is what makes the final
  window dominate the target's `⌊η^K δ'^d M^d / A⌋`;
* the ambient bound `ambK D d c · M₂^d ≤ N`;
* the strength bound `γ ≥ c · η^e` with data-independent `c > 0`, `e ≥ 1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- **The round, as a state-to-state step** (slot level `m+1 → m`), with the existential bundle
quantified before the data (see the module docstring). -/
def RoundStep (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) (Λ : ℕ)
    (kω : SlotSet (D.S (m + 2)) (fun _ => 1) → ℕ) : Prop :=
  ∃ (C : ℝ) (E : ℕ) (Cn : ℝ) (Mn : ℕ) (T' : ℕ) (c₁ : ℝ) (e₁ : ℕ),
    0 < C ∧ 0 < Cn ∧ 1 ≤ Mn ∧ 1 ≤ T' ∧ 0 < c₁ ∧ 1 ≤ e₁ ∧
    ∀ (H : ℕ) (hH : 1 ≤ H) (M₁ N : ℕ) (f : ℤ → ℂ) (γ : ℝ),
      LStateBox kω (pFlat D d c (m + 1) Λ) M₁ (H + 1) N 1 (Abox D (m + 2) H) (fun _ => f) γ →
      (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) →
      ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N : ℝ) →
      4 * (((Abox D (m + 2) H).filter
            (fun a => ∃ i, pFlat D d c (m + 1) Λ i a = 0)).card : ℝ)
        ≤ γ * ((Abox D (m + 2) H).card : ℝ) →
      Cn * (3 * γ / 4) ^ (-(Mn : ℤ)) ≤ ((H : ℝ) + 1) →
      ∃ (M₁' N' : ℕ) (γ' : ℝ),
        0 < γ' ∧ γ' ≤ 1 ∧ (M₁' : ℝ) ≤ (M₁ : ℝ) * ((H : ℝ) + 1) ∧
        c₁ * γ ^ e₁ * (M₁ : ℝ) * ((H : ℝ) + 1) ≤ (M₁' : ℝ) ∧ 2 ≤ M₁' ∧ N ≤ N' ∧
        C * γ ^ E ≤ γ' ∧
        LStateBox (regroupKω D (m + 1) (fun _ => T'))
          (pFlat D d c m (Λ * (d - (m + 1))))
          M₁' (H + 1) N' 1 (Abox D (m + 1) H) (fun _ => f) γ'

/-- The round at every level of the chain, with the datum's side conditions. -/
def RoundAll (D : IdxDatum) (d : ℕ) (c : ℤ) : Prop :=
  ∀ (m : ℕ) (Λ : ℕ) (kω : SlotSet (D.S (m + 2)) (fun _ => 1) → ℕ),
    1 ≤ Fintype.card (D.S (m + 2)) → m + 2 ≤ d → Λ ≤ Nat.factorial (d - 1) →
    RoundStep D d c m Λ kω

/-- **The endgame**: the round at slot level `0`, which turns the state's box-norm family into a
uniformity-norm power at the constant coefficient `Λ·d·c`.  The output window satisfies the lower
bound `c₀ γ^{e₀} (H+1)^d`, which is what dominates the target's window. -/
def LastStep (D : IdxDatum) (d : ℕ) (c : ℤ) (Λ : ℕ)
    (kω : SlotSet (D.S 1) (fun _ => 1) → ℕ) : Prop :=
  ∃ (C : ℝ) (E : ℕ) (S : ℕ) (Cn : ℝ) (Mn : ℕ),
    0 < C ∧ 2 ≤ S ∧ 0 < Cn ∧ 1 ≤ Mn ∧
    ∀ (c_h : ℝ) (e_h : ℕ), 0 < c_h → 1 ≤ e_h →
      ∃ (c₀ : ℝ) (e₀ : ℕ), 0 < c₀ ∧ 1 ≤ e₀ ∧
      ∀ (H : ℕ) (hH : 1 ≤ H) (M₁ N : ℕ) (f : ℤ → ℂ) (γ : ℝ),
        LStateBox kω (pFlat D d c 0 Λ) M₁ (H + 1) N 1 (Abox D 1 H) (fun _ => f) γ →
        (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1) →
        c_h * γ ^ e_h * ((H : ℝ) + 1) ^ (d - 1) ≤ (M₁ : ℝ) →
        ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N : ℝ) →
        4 * (((Abox D 1 H).filter
              (fun a => ∃ i, pFlat D d c 0 Λ i a = 0)).card : ℝ)
          ≤ γ * ((Abox D 1 H).card : ℝ) →
        Cn * (3 * γ / 4) ^ (-(Mn : ℤ)) ≤ ((H : ℝ) + 1) →
        ∃ (Lw₀ N' : ℕ),
          N ≤ N' ∧ c₀ * γ ^ e₀ * ((H : ℝ) + 1) ^ d ≤ (Lw₀ : ℝ) ∧
          C * γ ^ E ≤ uNormPow S (arithIcc (Λ * d * c) Lw₀) (symIcc N') f

end

end Work.Prop36SW
