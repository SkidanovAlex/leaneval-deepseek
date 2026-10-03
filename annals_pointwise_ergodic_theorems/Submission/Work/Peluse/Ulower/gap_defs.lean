/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.Peel.boxSumPow_peel

/-!
# The gap regime: the iterated difference produced by the peel

This module fixes the object produced by the *peel* of the `s`-fold box sum of the dual function
(Peluse's `boxSumPow_split`, applied `s - 2` times): the iterated difference

`iterDelta (s-2) sh F = Δ'_{(sh 0).1,(sh 0).2} (Δ'_{(sh 1).1,(sh 1).2} (⋯ (Δ'_{sh (s-3)} F)))`,

whose shift pairs are drawn from the shift set `arithIcc c D` of the box norm.  The peel
(`Work.Peluse.Ulower.boxSumPow_split`) is an *identity*, so for `1`-bounded `F` the average of the
level-two box norms of these iterated differences dominates the level-`s` box norm; this is the
input of the "many shift-tuples" interface `Work.Peluse.Ulower.gap_peel_many`.

## Main definition

* `Work.Peluse.Ulower.iterDelta`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- One step of `Δ'`: `Δ'_{a,b} F = fun x => F (x + a) * conj (F (x + b))` (this is
`Work.Peluse.DeltaP` with the two factors in the opposite order). -/
def iterDeltaStep (s : ℤ × ℤ) (F : ℤ → ℂ) : ℤ → ℂ :=
  fun x => F (x + s.1) * star (F (x + s.2))

/-- The iterated difference `Δ'_{(sh 0)}(Δ'_{(sh 1)}(⋯ Δ'_{sh (k-1)} F))`: the object produced by
applying Peluse's peel `boxSumPow_split` `k` times.  The `0`-th shift pair is applied *outermost*,
exactly as in the peel identity
`boxSumPow (t+1) Q S F = ((Q 0).card ^ 2)⁻¹ * ∑ a b, boxSumPow t (Q ∘ succ) S (Δ'_{a,b} F)`. -/
def iterDelta : (k : ℕ) → (Fin k → ℤ × ℤ) → (ℤ → ℂ) → (ℤ → ℂ) :=
  Nat.rec (motive := fun k => (Fin k → ℤ × ℤ) → (ℤ → ℂ) → (ℤ → ℂ))
    (fun _ F => F)
    (fun k ih sh F => iterDeltaStep (sh 0) (ih (fun i => sh i.succ) F))

lemma iterDelta_zero (sh : Fin 0 → ℤ × ℤ) (F : ℤ → ℂ) : iterDelta 0 sh F = F := rfl

lemma iterDelta_succ (k : ℕ) (sh : Fin (k+1) → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDelta (k+1) sh F
      = fun x => iterDelta k (fun i => sh i.succ) F (x + (sh 0).1) *
          star (iterDelta k (fun i => sh i.succ) F (x + (sh 0).2)) := rfl

/-- `iterDelta 1 sh F = Δ'_{(sh 0).1, (sh 0).2} F`, the first step of the peel. -/
lemma iterDelta_one (sh : Fin 1 → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDelta 1 sh F
      = fun x => F (x + (sh 0).1) * star (F (x + (sh 0).2)) := by
  rw [iterDelta_succ, iterDelta_zero]

/-- Boundedness is inherited by the iterated difference. -/
lemma norm_iterDelta_le_one : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    (∀ x : ℤ, ‖F x‖ ≤ 1) → ∀ x : ℤ, ‖iterDelta k sh F x‖ ≤ 1 := by
  intro k
  induction k with
  | zero =>
      intro sh F hF x
      rw [iterDelta_zero]
      exact hF x
  | succ k ih =>
      intro sh F hF x
      rw [iterDelta_succ, norm_mul, norm_star]
      exact mul_le_one₀ (ih (fun i => sh i.succ) F hF (x + (sh 0).1))
        (norm_nonneg _) (ih (fun i => sh i.succ) F hF (x + (sh 0).2))

/-- **The "many shift-tuples" hypothesis.**  There is a positive constant `c` and a set `H` of
shift tuples (each entry in the shift set `arithIcc P.leadingCoeff D`) occupying a `c`-fraction of
all shift tuples, such that for every `sh ∈ H` the *level-two* box norm of the iterated difference
`iterDelta (s-2) sh (dualFn N P f₀ f₁)` is at least `c`.

This is the conclusion of the peel `Work.Peluse.Ulower.gap_peel_many`, obtained from the hypothesis
`δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P N₀ N)) (dualFn N P f₀ f₁)` of the gap
regime; it is the input of `Work.Peluse.Ulower.gap_local_control`. -/
def ManyShiftsHyp (P : Polynomial ℤ) (s N₀ N D : ℕ) (f₀ f₁ : ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ H : Finset (Fin (s - 2) → ℤ × ℤ),
    (∀ sh ∈ H, ∀ i, (sh i).1 ∈ Work.Peluse.arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ Work.Peluse.arithIcc P.leadingCoeff D) ∧
    c * (((Work.Peluse.arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2)) ≤ (H.card : ℝ) ∧
    (∀ sh ∈ H, c ≤ Work.Peluse.boxNormPow 2
      (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
      (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))
      (iterDelta (s - 2) sh (Work.Peluse.dualFn N P f₀ f₁)))

/-- **The "many shift-tuples" hypothesis, with the level tied to `δ`.**

There is a set `H` of shift tuples (each entry in the shift set `arithIcc P.leadingCoeff D`) whose
cardinality is at least a `δ`-fraction of all shift tuples, such that for every `sh ∈ H` the
*level-two* box norm of the iterated difference `iterDelta (s-2) sh (dualFn N P f₀ f₁)` is at least
`δ/4`.  This is *exactly* the conclusion of the peel `Work.Peluse.Ulower.gap_peel_many`.

**Warning (do not weaken).**  The level `δ/4` must stay tied to `δ`: the "variant" in which the
level is merely *some* `c > 0` is **false** — see
`Submission/Work/Peluse/Ulower/gap_local_control_counterexample.lean` — because `dualFn` is linear in
`f₁` and `boxNormPow 2` is of degree `2^s` in the iterated difference, so rescaling
`f₁ ↦ ε • f₁` rescales the box-norm level by `ε^{2^s}` while `progAvgSum` only scales by `ε`.
(This is also why the target's own hypothesis `δ ≤ uNormPow s …` must be used at its *level* `δ`.) -/
def ManyShiftsHypδ (P : Polynomial ℤ) (s N₀ N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ) : Prop :=
  ∃ H : Finset (Fin (s - 2) → ℤ × ℤ),
    (∀ sh ∈ H, ∀ i, (sh i).1 ∈ Work.Peluse.arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ Work.Peluse.arithIcc P.leadingCoeff D) ∧
    (δ / 4 / (1 + (s : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|)) *
        (((Work.Peluse.arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2)) ≤ (H.card : ℝ) ∧
    (∀ sh ∈ H, δ / 4 ≤ Work.Peluse.boxNormPow 2
      (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
      (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))
      (iterDelta (s - 2) sh (Work.Peluse.dualFn N P f₀ f₁)))

end

end Work.Peluse.Ulower
