import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.loopCombFixedDefs
import Submission.Work.Kernel.loopCombFixed

/-!
# Kernel: the `loop` field of `HvdH.KernelLib`, v2/v3 (bound `(m + 1) * (c + K) + K`)

The combinator is `Work.Kernel.loopCombFixed_comb` (from `loopCombFixedDefs.lean`, where it is also
proved for the `1 ≤ m` variant of the field).  The v2 field has no hypothesis on `m`, but its bound
`(m + 1) * (c + K) + K` is exactly the `1 ≤ m` bound for the parameter `m + 1`, and the hypothesis
with `i + 1 < m` implies the one with `i + 1 < m + 1`.  So the v2 field follows from
`Work.Kernel.loopCombFixed`.

(Do not confuse this with `Submission/Work/Kernel/loopRefute.lean`, which refutes the *v1* text
`m * (c + K) + K`; that file must not be imported anywhere.)
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- `KernelLib.loop` (v2/v3): the do-while, bound `(m + 1) * (c + K) + K`. -/
theorem loopV2 : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ),
    ∀ (main q : HvdH.Cmd) (I : ℕ → List HvdH.Val → Prop) (F : List HvdH.Val → Prop) (c m : ℕ),
      (∀ i vs, I i vs → HvdH.WordR main q (fun w => w = vs)
        (fun _ out => ∃ vs', (out = HvdH.Val.int 0 :: vs' ∧ F vs') ∨
          (out = HvdH.Val.int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < m)) (fun _ => c)) →
      HvdH.WordR main (comb q) (I 0) (fun _ out => F out) (fun _ => (m + 1) * (c + K) + K) := by
  obtain ⟨comb, K, h⟩ := loopCombFixed
  refine ⟨comb, K, ?_⟩
  intro main q I F c m hq
  -- the hypothesis with `i + 1 < m + 1` is weaker than the given one
  have hq' : ∀ i vs, I i vs → WordR main q (fun w => w = vs)
      (fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ F vs') ∨
        (out = .int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < m + 1)) (fun _ => c) := by
    intro i vs hI
    refine WordR_conseq (hq i vs hI) (fun u hu => hu) (fun u out hu hpost => ?_) (fun _ _ => le_rfl)
    rcases hpost with ⟨vs', hh | hh⟩
    · exact ⟨vs', Or.inl hh⟩
    · exact ⟨vs', Or.inr ⟨hh.1, hh.2.1, by omega⟩⟩
  -- `loopCombFixed` at parameter `m + 1` gives exactly the required bound
  have hspec := h main q I F c (m + 1) (by omega) hq'
  simpa using hspec

end Work.Kernel
