import Mathlib
import Submission.HvdH.Interfaces

/-!
# Sequential composition and cost bookkeeping for the Transform area

The Transform pipeline (paper Theorem 3.1) is the sequential composition of a fixed list
of `WordR` programs.  This file provides the two combinator definitions used for that
(`seqAll`, `csum`) together with their elementary `Eval`/cost lemmas, plus a packaging
lemma for `WordR` conclusions.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- Cost of a sequence of steps: right-nested sum, with a final `skip`. -/
def csum : List ℕ → ℕ
  | [] => 1
  | n :: ns => n + csum ns

/-- Sequential composition of a list of commands. -/
def seqAll : List Cmd → Cmd
  | [] => .skip
  | c :: cs => .seq c (seqAll cs)

theorem csum_nil : csum [] = 1 := rfl

theorem csum_cons (n : ℕ) (ns : List ℕ) : csum (n :: ns) = n + csum ns := rfl

/-- `csum` is the plain list sum plus one. -/
theorem csum_eq_sum_add_one (ns : List ℕ) : csum ns = ns.sum + 1 := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [csum_cons, ih, List.sum_cons]; omega

theorem seqAll_nil (main : Cmd) (s : State) : Eval main (seqAll []) s s (csum []) :=
  Eval.skip s

theorem seqAll_cons (main : Cmd) (c : Cmd) (cs : List Cmd)
    (s s₁ s' : State) (n : ℕ) (ns : List ℕ)
    (h1 : Eval main c s s₁ n) (h2 : Eval main (seqAll cs) s₁ s' (csum ns)) :
    Eval main (seqAll (c :: cs)) s s' (csum (n :: ns)) :=
  Eval.seq h1 h2

/-- Packaging the components of a `WordR` conclusion (keeps unification shallow). -/
theorem wordR_pack {main prog : Cmd} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ}
    (vs out : List Val) (s s' : State) (n : ℕ) (Rg : List Glyph)
    (hpost : Post vs out) (hev : Eval main prog s s' n) (hcost : n ≤ C vs)
    (hstk : s'.stk 0 = encs out ++ Rg) (hfr : ∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) :
    ∃ (out : List Val) (s' : State) (n : ℕ), Post vs out ∧ Eval main prog s s' n ∧
      n ≤ C vs ∧ s'.stk 0 = encs out ++ Rg ∧ ∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k :=
  ⟨out, s', n, hpost, hev, hcost, hstk, hfr⟩

end Work.Transform
