import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auRoundAux

/-!
# Parked-stack bookkeeping for `Work.Resample.auCWPark`

The `auCWPark` program rearranges the top `15` values of stack `0`

  `[rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi, CHAIN]`

into

  `[Pv, lr, li, cons rec CHAIN]`

**without ever reading `CHAIN`** (the hypothesis of `auCWPark` bounds the size of the other
fourteen values only, so every operation on `CHAIN` would break the cost bound `K * (S + 1)`).
The strategy is to park the four values that survive on stack `1` (they are all bounded by `S`),
delete the ten unwanted ones, and then rebuild the output on top of the still untouched
`CHAIN.enc`:

* park `Pv`, `lr`, `li`, `rec` on stack `1` in this order (using `KernelLib.roll` to bring each of
  them to the top of stack `0`), so that stack `1` reads `[rec, li, lr, Pv]` from the front and
  popping it returns them in the order in which they must be re-pushed;
* drop the ten unwanted values `zi, zr, M, sh, k, x, y, W, Lor, Loi`;
* pop `rec` back and form `cons rec CHAIN` (the `KernelLib` `consV` only pushes the `cons` glyph,
  at *constant* cost), then pop `li`, `lr`, `Pv`.

This module contains the shared state description (`ParkD`/`PreD`/`PostD`) and the plumbing used
both by the program-specific lemmas and by the final assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## The state description -/

/-- Description of the non-zero stacks: every non-zero stack other than the parking stack `1` is
empty, and the value list of stack `1` is `L1`.  Only the non-zero stacks are described (stack `0`
is described by `vs`, and its raw suffix by the `WordM` frame). -/
def ParkD (L1 : List Val) (a : Stk → List Val) : Prop :=
  ∀ k, k ≠ 0 → a k = if k = 1 then L1 else []

/-- The pre-description of a `WordM` step: the value stack is `V`, the parking stack holds `L1`. -/
def PreD (V L1 : List Val) (vs : List Val) (a : Stk → List Val) : Prop :=
  vs = V ∧ ParkD L1 a

/-- The post-description of a `WordM` step. -/
def PostD (V L1 : List Val) : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop :=
  fun _ _ out b => out = V ∧ ParkD L1 b

theorem ParkD.nil (a : Stk → List Val) (h : a = fun _ => ([] : List Val)) : ParkD [] a := by
  intro k _
  rw [h]
  simp

@[simp] theorem PreD.eq {V L1 : List Val} {vs : List Val} {a : Stk → List Val} :
    PreD V L1 vs a ↔ vs = V ∧ ParkD L1 a := Iff.rfl

/-- A `WordM` step that starts and ends with an empty parking stack is a `WordR` step. -/
theorem WordM.toWordR' {main p : Cmd} {V V' : List Val} {c : ℕ}
    (h : WordM main p (PreD V []) (PostD V' []) (fun _ _ => c)) :
    WordR main p (fun vs => vs = V) (fun _ out => out = V') (fun _ => c) := by
  intro vs hvs s R hR
  obtain ⟨out, b, s', n, ⟨hout, hb⟩, hev, hn, h0, hk⟩ :=
    h vs (fun _ : Stk => ([] : List Val)) ⟨hvs, ParkD.nil _ rfl⟩ s R (fun k => s.stk k) hR
      (fun k _ => rfl)
  refine ⟨out, s', n, hout, hev, hn, h0, fun k hk0 => ?_⟩
  have hbk : b k = ([] : List Val) := by
    have h1 := hb k hk0
    rw [ite_self] at h1
    exact h1
  rw [hk k hk0, hbk]
  rfl

/-- A `WordM` program on a window `A`, with the parking stack empty at both ends, is a `Pipe`. -/
theorem Pipe.ofPark {main p : Cmd} {A B : List Val} {c : ℕ}
    (h : ∀ rest : List Val, WordM main p (PreD (A ++ rest) []) (PostD (B ++ rest) []) (fun _ _ => c)) :
    Pipe main p A B c := by
  intro rest
  exact WordM.toWordR' (h rest)

/-- Composition of two `WordM` steps with determined intermediate description. -/
theorem seqS {main p q : Cmd} {V1 V2 V3 L1 L2 L3 : List Val} {c1 c2 : ℕ}
    (h1 : WordM main p (PreD V1 L1) (PostD V2 L2) (fun _ _ => c1))
    (h2 : WordM main q (PreD V2 L2) (PostD V3 L3) (fun _ _ => c2)) :
    WordM main (.seq p q) (PreD V1 L1) (PostD V3 L3) (fun _ _ => c1 + c2) := by
  refine WordM.conseq (WordM.seq (B := fun _ _ => c2) h1 h2 ?_ ?_) ?_ ?_ ?_
  · intro vs a mid a' h; exact h
  · intro vs a mid a' _; exact le_rfl
  · intro vs a h; exact h
  · intro vs a out b _ hpost
    obtain ⟨mid, a', _, hpost2⟩ := hpost
    exact hpost2
  · intro vs a _; exact le_rfl

/-- Composition of a cost-`c` step with a cost-`d` step, when both are measured as `c * (S + 1)`. -/
theorem seqSc {main p q : Cmd} {V1 V2 V3 L1 L2 L3 : List Val} {c1 c2 S : ℕ}
    (h1 : WordM main p (PreD V1 L1) (PostD V2 L2) (fun _ _ => c1 * (S + 1)))
    (h2 : WordM main q (PreD V2 L2) (PostD V3 L3) (fun _ _ => c2 * (S + 1))) :
    WordM main (.seq p q) (PreD V1 L1) (PostD V3 L3) (fun _ _ => (c1 + c2) * (S + 1)) := by
  refine WordM.mono (seqS h1 h2) (fun _ _ => ?_)
  rw [Nat.add_mul]

/-- Cost monotonicity for the uniform cost shape `c * (S + 1)`. -/
theorem costLe {main p : Cmd} {Pre : List Val → (Stk → List Val) → Prop}
    {Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {c c' S : ℕ} (h : WordM main p Pre Post (fun _ _ => c * (S + 1))) (hc : c ≤ c') :
    WordM main p Pre Post (fun _ _ => c' * (S + 1)) :=
  WordM.mono h (fun _ _ => Nat.mul_le_mul_right _ hc)

end Work.Resample
