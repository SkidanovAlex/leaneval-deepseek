import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `evCarryAdd`: local infrastructure

* `loop_iterate_pred`: iterate a loop along a predicate-indexed family of states;
* `readA`: move the digit bits from `aA` to `aB` (least significant bit on top, `iend`-terminated);
* `postP` / `tailA`: the state and the program for the final carry of the addition phase (push the
  carry onto `aO` if the counter is still positive, else onto `a2`, then drop the `iend`);
* `addLoop_ev`: the addition loop, given one body step as a hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace EvC

open HvdH

/-! ## Iterating a loop along a predicate-indexed family of states -/

/-- `loop_iterate_pred`: if `P k` holds at the states reached after `k` iterations, the loop
register is `cc` while `k < N`, fails at `N`, and one body run moves `P k` to `P (k+1)`, then the
loop runs from any `P k s` (`k ≤ N`) to some `P N s'`, in `(N-k)*(step+1)+1` steps. -/
theorem loop_iterate_pred {main : Cmd} {r : Reg} {cc : Glyph} {body : Cmd} {P : ℕ → State → Prop}
    {N step : ℕ}
    (hstep : ∀ k s, P k s → k < N → ∃ s' n, Work.Layout.Ev main body s s' n ∧ n ≤ step ∧ P (k + 1) s')
    (hgo : ∀ k s, P k s → k < N → s.reg r = cc)
    (hstop : ∀ s, P N s → s.reg r ≠ cc) :
    ∀ k s, P k s → k ≤ N →
      ∃ s' n, Work.Layout.Ev main (.loop r cc body) s s' n ∧
        n ≤ (N - k) * (step + 1) + 1 ∧ P N s' := by
  have aux : ∀ d : ℕ, ∀ k s, N - k ≤ d → P k s → k ≤ N →
      ∃ s' n, Work.Layout.Ev main (.loop r cc body) s s' n ∧
        n ≤ (N - k) * (step + 1) + 1 ∧ P N s' := by
    intro d
    induction d with
    | zero =>
        intro k s _ hP hk
        have hkN : k = N := by omega
        subst hkN
        exact ⟨s, 1, ⟨1, Eval.loopF (hstop s hP), le_rfl⟩, by omega, hP⟩
    | succ d ih =>
        intro k s hd hP hk
        by_cases hkN : k = N
        · subst hkN
          exact ⟨s, 1, ⟨1, Eval.loopF (hstop s hP), le_rfl⟩, by omega, hP⟩
        · have hklt : k < N := by omega
          obtain ⟨s1, n1, he1, hn1, hP1⟩ := hstep k s hP hklt
          obtain ⟨m1, hev1, hm1⟩ := he1
          obtain ⟨s2, n2, he2, hn2, hP2⟩ := ih (k + 1) s1 (by omega) hP1 (by omega)
          obtain ⟨m2, hev2, hm2⟩ := he2
          refine ⟨s2, m1 + m2 + 1, ⟨m1 + m2 + 1,
            Eval.loopT (hgo k s hP hklt) hev1 hev2, le_rfl⟩, ?_, hP2⟩
          have h2 : (N - k) * (step + 1) = (N - (k + 1)) * (step + 1) + (step + 1) := by
            rw [show N - k = (N - (k + 1)) + 1 by omega]
            ring
          rw [h2]
          omega
  intro k s hP hk
  exact aux (N - k) k s le_rfl hP hk

/-! ## Phase 1: read the digit bits from `aA` onto `aB` -/

/-- Move the digit bits from `aA` (reversed value encoding) onto `aB`, least significant bit on
top, `iend`-terminated. -/
def readA : Cmd := Work.Layout.seqs [Shift.drain aA aB (Shift.gmk aA) rGa rLa, .pop aB rGa]

/-! ## The end of the addition phase -/

/-- State after the whole addition phase: the streams are consumed, the low `b` bits of
`addAll W hbits` have been pushed onto `aO`, the rest sits on `a2` (to be moved to `aW`), and the
counter is `b - |addAll|`. -/
def postP (b : ℕ) (W hbits LO : List Bool) (Ws Os Cs A2s Bs : List Glyph) (s : State) : Prop :=
  s.stk aW = Shift.gmk aW :: Ws ∧
  s.stk aB = Shift.gmk aB :: Bs ∧
  s.stk aO = ((addAll W hbits).take b).reverse.map Glyph.bit ++
      LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os ∧
  s.stk a2 = ((addAll W hbits).drop b).reverse.map Glyph.bit ++ Shift.gmk a2 :: A2s ∧
  s.stk aCW = Unary (b - (addAll W hbits).length) (Shift.gmk aCW :: Cs)

/-- The final carry and the removal of the `iend`. -/
def tailA : Cmd := Work.Layout.seqs [carryA, .pop aB rGa]

/-- The addition loop, from `addP 0` to `addP (addN W hbits)`, given one body step. -/
theorem addLoop_ev (main : Cmd) (b : ℕ) (W hbits LO : List Bool) (X : Stk → List Glyph)
    (Ws Os Cs A2s Bs : List Glyph) (s : State)
    (hstep : ∀ (k : ℕ) (t : State), addP b W hbits LO X Ws Os Cs A2s Bs k t → k < addN W hbits →
      ∃ s' n, Work.Layout.Ev main bodyA t s' n ∧ n ≤ 23 ∧
        addP b W hbits LO X Ws Os Cs A2s Bs (k + 1) s')
    (h0 : addP b W hbits LO X Ws Os Cs A2s Bs 0 s) :
    ∃ s' n, Work.Layout.Ev main (.loop rLa Shift.gGo bodyA) s s' n ∧
      n ≤ addN W hbits * 24 + 1 ∧ addP b W hbits LO X Ws Os Cs A2s Bs (addN W hbits) s' := by
  obtain ⟨s', n, hev, hcost, hP⟩ := loop_iterate_pred (r := rLa) (cc := Shift.gGo) (body := bodyA)
    (P := addP b W hbits LO X Ws Os Cs A2s Bs) (N := addN W hbits) (step := 23) hstep
    (by
      intro k t hP hk
      rw [hP.2.2.2.2]
      exact addFlag_of_lt hk)
    (by
      intro t hP
      rw [hP.2.2.2.2, addFlag_of_le (le_refl _)]
      exact Shift.gStop_ne_gGo)
    0 s h0 (Nat.zero_le _)
  refine ⟨s', n, hev, ?_, hP⟩
  calc n ≤ (addN W hbits - 0) * (23 + 1) + 1 := hcost
    _ = addN W hbits * 24 + 1 := by omega

end EvC
end Work.IntLib
