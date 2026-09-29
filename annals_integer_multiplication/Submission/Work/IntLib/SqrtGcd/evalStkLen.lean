import Submission.HvdH.Interfaces

/-!
# Stack lengths grow by at most the cost of a run

Generic fact about the StackLang semantics `HvdH.Eval`: in any run, the length of any stack grows
by at most the number of primitive steps.  This is the tool that lets a *cost bound* of a
sub-program be converted into a *bound on the size of the data it produced*, which is what the
assembly of `sqrtWord` needs (the radicand bit list and the root/remainder regions are produced by
programs whose cost is bounded but whose output size is not part of their statement).
-/

set_option autoImplicit false

namespace Work.IntLib.SqrtGcd

open HvdH

/-- In a run of cost `n`, every stack grows by at most `n` glyphs. -/
theorem Eval.stk_length_le {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) : ∀ k : Stk, (s'.stk k).length ≤ (s.stk k).length + n := by
  induction h with
  | skip s => intro k; simp
  | pop k r s =>
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [Function.update_self]
        rw [List.length_tail]; omega
      · simp only [Function.update_of_ne hj]
        omega
  | peek k r s => intro j; simp
  | push k r s =>
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [Function.update_self, List.length_cons]
        omega
      · simp only [Function.update_of_ne hj]
        omega
  | set r c s => intro k; simp
  | mov dst src s => intro k; simp
  | seq h1 h2 ih1 ih2 =>
      intro k
      have a := ih1 k
      have b := ih2 k
      omega
  | iteT hr hc ih => intro k; have a := ih k; omega
  | iteF hr hc ih => intro k; have a := ih k; omega
  | loopF hr => intro k; simp
  | loopT hr hb hl ihb ihl => intro k; have a := ihb k; have b := ihl k; omega
  | self hh ih => intro k; have a := ih k; omega

/-- If a run leaves, above a marker `T` on stack `k`, the bit list `l` where before there was
nothing above `T`, then `l.length ≤ n`. -/
theorem length_of_region_le_cost {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) (k : Stk) (T : Glyph) (b : List Glyph) (l : List Bool)
    (h0 : s.stk k = T :: b) (h1 : s'.stk k = l.map Glyph.bit ++ T :: b) : l.length ≤ n := by
  have hlen := Eval.stk_length_le h k
  rw [h0, h1] at hlen
  simp only [List.length_append, List.length_map, List.length_cons] at hlen
  omega

/-- If a run leaves, above the marker `T` on stack `k`, the bit list `l` sitting directly on the
*old whole content* of `k` (the situation after a program pushed a region on top of `k`), then
`l.length + 1 ≤ n`. -/
theorem length_of_new_region {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) (k : Stk) (T : Glyph) (l : List Bool)
    (h1 : s'.stk k = l.map Glyph.bit ++ T :: s.stk k) : l.length + 1 ≤ n := by
  have hlen := Eval.stk_length_le h k
  rw [h1] at hlen
  simp only [List.length_append, List.length_map, List.length_cons] at hlen
  omega

end Work.IntLib.SqrtGcd
