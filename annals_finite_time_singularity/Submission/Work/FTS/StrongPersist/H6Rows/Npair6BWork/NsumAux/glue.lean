/-
Copyright: work module for the Elgindi finite-time singularity project.

# `NsumAux/glue` — the assembly glue for `Npair6BWork.nsumBounds`

The per-slot bound for the whole level-six `N`-row sum (`Npair6BWork.nsumBounds`) is assembled
from the twenty per-piece bounds (`NsumG.nsumG1`, `nsumG2`, `nsumG3`, `nsumGK`, `nsumG5`) by

1. splitting the pairing of the sum into the sum of the pairings
   (`slotPairing_sum_range_succ`, by induction on `Finset.range` with `SlotPairingSplit6`),
2. applying the triangle inequality (`Finset.abs_sum_le_sum_abs`) and the per-piece bounds
   (`Finset.sum_le_card_nsmul`),
3. absorbing the twenty constants and the slack in the powers of `α`, `(1+|Ce|+|Cs|)`, `(1+M)`.

This module contains step 1 (the only part with mathematical content: it needs the `C⁶`/`ℋ⁶`
regularity of the pieces, which the caller reads off `H6Row6.NS6.pieces`) together with a
general statement of the assembly, so that the target file only has to instantiate the twenty
piece bounds.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotPairingSplit6
import Submission.Work.FTS.StrongPersist.H6Row6.NS6.Pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `C⁶`-regularity on the open quadrant, the finite smoothness used by the pairing split. -/
abbrev Smooth6 (u : Fn) : Prop :=
  ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0

/-- **The pairing of a finite sum splits into the sum of the pairings** (for `N + 1` summands,
so that the base case is the single summand `u 0`).

By induction on `N`: the sum over `range (n+2)` is the sum over `range (n+1)` plus `u (n+1)`
(`Finset.sum_range_succ`), and the binary splitting is `N0pair6Aux.SlotPairingSplit6`, whose
hypotheses (`C⁶` + `ℋ⁶` honesty of the two summands and of the datum `f`) are supplied by the
induction hypothesis together with `H6Row6.NS6.hkMem_sum_range`. -/
theorem slotPairing_sum_range_succ {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : Fn}
    (hf6 : Smooth6 f) (hfm : Work.Spaces.HkMem α 6 f) {u : ℕ → Fn} :
    ∀ N : ℕ, (∀ k ≤ N, Smooth6 (u k)) → (∀ k ≤ N, Work.Spaces.HkMem α 6 (u k)) →
      Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => ∑ k ∈ Finset.range (N + 1), u k z θ) f
        = ∑ k ∈ Finset.range (N + 1), Work.FTS.TransportS.slotPairing ρ a b (u k) f := by
  intro N
  induction N with
  | zero =>
      intro _ _
      have h0 : (fun z θ => ∑ k ∈ Finset.range (0 + 1), u k z θ) = u 0 := by
        funext z θ; rw [Finset.sum_range_one]
      rw [h0, Finset.sum_range_one]
  | succ n ih =>
      intro hcd hm
      have hcd' : ∀ k ≤ n, Smooth6 (u k) := fun k hk => hcd k (le_trans hk (Nat.le_succ n))
      have hm' : ∀ k ≤ n, Work.Spaces.HkMem α 6 (u k) :=
        fun k hk => hm k (le_trans hk (Nat.le_succ n))
      obtain ⟨hcdsum, hmsum⟩ :=
        Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range (n + 1) u
          (fun k hk => hcd k (le_of_lt hk))
          (fun k hk => hm k (le_of_lt hk))
      have hsplit : (fun z θ => ∑ k ∈ Finset.range (n + 1 + 1), u k z θ)
          = fun z θ => (∑ k ∈ Finset.range (n + 1), u k z θ) + u (n + 1) z θ := by
        funext z θ; rw [Finset.sum_range_succ]
      rw [hsplit,
        Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotPairingSplit6 (α := α) hα hab hρ
          (u₁ := fun z θ => ∑ k ∈ Finset.range (n + 1), u k z θ) (u₂ := u (n + 1)) (f := f)
          hcdsum (hcd (n + 1) le_rfl) hf6 hmsum (hm (n + 1) le_rfl) hfm,
        ih hcd' hm']
      conv_rhs => rw [Finset.sum_range_succ]

/-- **The assembly of the target bound from the twenty per-piece bounds.**

If every piece of the twenty-term sum satisfies `|slotPairing ρ a b (piece) f| ≤ C·S` with the
same constant and the nonnegative shape factor `S`, then the pairing of the sum — which is the
sum of the pairings, `slotPairing_sum_range_succ` — is at most `(20·C + 1)·S`. -/
theorem abs_slotPairing_sum_le {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : Fn}
    (hf6 : Smooth6 f) (hfm : Work.Spaces.HkMem α 6 f) {u : ℕ → Fn}
    (hcd : ∀ k ≤ 19, Smooth6 (u k)) (hm : ∀ k ≤ 19, Work.Spaces.HkMem α 6 (u k))
    {C S : ℝ} (hC0 : 0 ≤ C) (hS0 : 0 ≤ S)
    (hpiece : ∀ k ≤ 19, |Work.FTS.TransportS.slotPairing ρ a b (u k) f| ≤ C * S) :
    |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => ∑ k ∈ Finset.range 20, u k z θ) f|
      ≤ (20 * C + 1) * S := by
  have hsplit : Work.FTS.TransportS.slotPairing ρ a b
      (fun z θ => ∑ k ∈ Finset.range 20, u k z θ) f
      = ∑ k ∈ Finset.range 20, Work.FTS.TransportS.slotPairing ρ a b (u k) f := by
    have h := slotPairing_sum_range_succ (α := α) hα hab hρ hf6 hfm 19 hcd hm
    simpa using h
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcard : (Finset.range 20).card = 20 := Finset.card_range 20
  have hstep : (∑ k ∈ Finset.range 20,
        |Work.FTS.TransportS.slotPairing ρ a b (u k) f|) ≤ 20 * (C * S) := by
    have h := Finset.sum_le_card_nsmul (Finset.range 20)
      (fun k => |Work.FTS.TransportS.slotPairing ρ a b (u k) f|) (C * S)
      (fun k hk => hpiece k (by have := Finset.mem_range.mp hk; omega))
    rw [hcard] at h
    simpa using h
  have hCS : (0 : ℝ) ≤ C * S := mul_nonneg hC0 hS0
  have : (20 : ℝ) * (C * S) ≤ (20 * C + 1) * S := by nlinarith
  linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux
