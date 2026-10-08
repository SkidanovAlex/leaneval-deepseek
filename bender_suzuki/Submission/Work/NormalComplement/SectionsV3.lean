/-
# Area `NormalComplement`: `Section2Prop` without the `KInvariantUnderD` input

The lead's ruling of 2026-10-05 (`NOTES_LEAD_bs_appxgap.md`) on the `AppXGap` gap: the
hypothesis `KInvariantUnderD H t` of `Section2Prop` is **not needed**.  Peterfalvi's proof of
Ch. III §2 Prop. 1 is correct if the case split of the proof is made *after* conjugating the
`p`-subgroup `U ≤ E` into `V = C_D(t)` (Ch. II §4 Prop. 2(b), `prop2b_conj_into_centD`): then in
case 2 the argument `U₁` can be taken *inside* `U^d ≤ V`, so Ch. II §4 Prop. 3(b) applies directly
with `X = U^d` and `Y = U₁`, and no `D`-conjugation of `K` is needed; in case 3, `U^d ≤ V` makes
`U^d` cyclic by App. I (5)(c) (`cyclic_of_fpf_on_centD`).  The normalizer conditions of the
`p`-control criterion are invariant under `d ∈ D` (`normalizerCond_conj`), which transports the
result back to `U`.

This module defines the resulting `Prop`, `Section2Prop'` (= `Section2Prop` with the
`KInvariantUnderD H t →` hypothesis deleted), and records that the old `Section2Prop` follows from
it (so that the older files that still take `hKinv` as a parameter keep compiling).
-/
import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.NormalComplement.Sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §2 Proposition 1** (p.175), *without* the `KInvariantUnderD H t`
hypothesis: with `H` strongly embedded, `t ∉ H` an involution, `D = H ∩ H^t`, `W ⊴ H` with
`H = W·D`, `E = W ∩ D`, and `p | |E|`: either `E` is `p`-control in `W`, or `E` has a `p`-Sylow
subgroup `P ⊆ V = C_D(t)` which acts fixed-point-freely on `K = J(D,t)` and is cyclic. -/
def Section2Prop' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, W ≤ H →
      H ≤ Subgroup.normalizer (W : Set G) → W ⊔ twoPoint H t = H →
        ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(W ⊓ twoPoint H t) →
          IsPControl p (W ⊓ twoPoint H t) W ∨
            ∃ P : Subgroup G, IsSylowIn p P (W ⊓ twoPoint H t) ∧ P ≤ centD H t ∧
              (∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) ∧
              IsCyclic P

/-- The old `Section2Prop` (with the redundant `KInvariantUnderD` hypothesis) follows from
`Section2Prop'`. -/
theorem Section2Prop_of_Section2Prop' (h : Section2Prop') : Section2Prop := by
  intro G _ _ hSit H hH t ht htH W hW hHn hsup _hKinv p hp hpE
  exact h G hSit H hH t ht htH W hW hHn hsup p hp hpE

end Work.NormalComplement
