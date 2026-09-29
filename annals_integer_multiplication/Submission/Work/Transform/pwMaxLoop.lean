import Mathlib
import Submission.Work.Transform.pwMaxDefs

/-!
# `Work.Transform.pwMaxLoop`: the max-phase loop

Given a per-element word `elem` satisfying `ElemSpec src mx elem Ke` (consume the element
`(Val.int t).enc` on `src`, replace the running maximum `M` on `mx` by `max M t`, restore every
other stack, in time `Ke * (t.size + 1)`), `loopOf elem src` walks the encoding of a list
`ms` of positive integers on `src`, leaves `src` holding just its frame marker, and leaves on `mx`
the bits of `lmax ms` (least significant first) above the marker.

The cost bound is linear in `ms.sum + ms.length` -- in particular it never pays for the *length of
the running maximum*: this is where the sum bound of the paper comes from (`t.size ≤ t` for `t > 0`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel

/-- Loop lemma, without the initial `set mC Glyph.eos`: from a state whose control register already
holds `eos` and whose `src` holds the encoding of `suffix`. -/
theorem pwMaxLoopAux (src mx : HvdH.Stk) (hsm : src ≠ mx) (elem : HvdH.Cmd) (Ke : ℕ)
    (helem : ElemSpec src mx elem Ke) :
    ∀ (main : HvdH.Cmd) (suffix : List ℕ) (M : ℕ) (below mxTail : List HvdH.Glyph)
      (s : HvdH.State),
      s.reg mC = HvdH.Glyph.eos →
      (∀ t ∈ suffix, 0 < t) →
      s.stk src = (HvdH.intList suffix).enc ++ gM :: below →
      s.stk mx = (Computability.encodeNat M).map HvdH.Glyph.bit ++ gM :: mxTail →
      ∃ s' n, HvdH.Eval main (.loop mC HvdH.Glyph.eos (bodyOf elem src)) s s' n ∧
        n ≤ (Ke + 5) * (suffix.sum + suffix.length + 2) ∧
        s'.stk src = gM :: below ∧
        s'.stk mx = (Computability.encodeNat (max M (HvdH.lmax suffix))).map HvdH.Glyph.bit
          ++ gM :: mxTail ∧
        (∀ j : HvdH.Stk, j ≠ src → j ≠ mx → s'.stk j = s.stk j) := by
  intro main suffix
  induction suffix with
  | nil =>
    intro M below mxTail s hreg _ hsrc hmx
    have hsrc' : s.stk src = HvdH.Glyph.nil :: gM :: below := by
      rw [hsrc, mx_intList_nil]; rfl
    set s1 : HvdH.State := HvdH.State.tPop s src mC with hs1
    have e1 : HvdH.Eval main (.pop src mC) s s1 1 := by
      rw [hs1]; exact eval_pop main src mC s
    have hs1src : s1.stk src = gM :: below := by
      rw [hs1, tPop_stk, if_pos rfl, hsrc']; rfl
    have hs1reg : s1.reg mC = HvdH.Glyph.nil := by
      rw [hs1, tPop_reg, if_pos rfl, hsrc']; rfl
    set s2 : HvdH.State := HvdH.State.tSet s1 mC HvdH.Glyph.iend with hs2
    have e2 : HvdH.Eval main (.set mC HvdH.Glyph.iend) s1 s2 1 := by
      rw [hs2]; exact eval_set main mC HvdH.Glyph.iend s1
    have hs2reg : s2.reg mC = HvdH.Glyph.iend := by
      rw [hs2, tSet_reg, if_pos rfl]
    have hcons : HvdH.Glyph.nil ≠ HvdH.Glyph.cons := by decide
    have ebody : HvdH.Eval main (bodyOf elem src) s s2 (1 + (1 + 1)) := by
      show HvdH.Eval main
        (.seq (.pop src mC)
          (.ite mC HvdH.Glyph.cons (.seq elem (.set mC HvdH.Glyph.eos))
            (.set mC HvdH.Glyph.iend))) s s2 (1 + (1 + 1))
      exact Eval.seq e1 (Eval.iteF (by rw [hs1reg]; exact hcons) e2)
    have eend : HvdH.Eval main (.loop mC HvdH.Glyph.eos (bodyOf elem src)) s2 s2 1 :=
      Eval.loopF (by rw [hs2reg]; decide)
    refine ⟨s2, _, Eval.loopT hreg ebody eend, ?_, ?_, ?_, ?_⟩
    · show (1 + (1 + 1)) + 1 + 1 ≤ (Ke + 5) * ((0 : ℕ) + 0 + 2)
      omega
    · rw [hs2, tSet_stk, hs1src]
    · rw [hs2, tSet_stk, hs1, tPop_stk, if_neg (Ne.symm hsm)]
      rw [show HvdH.lmax ([] : List ℕ) = 0 from rfl, max_eq_left (Nat.zero_le M)]
      exact hmx
    · intro j hj1 _
      rw [hs2, tSet_stk, hs1, tPop_stk, if_neg hj1]
  | cons t ts ih =>
    intro M below mxTail s hreg hpos hsrc hmx
    have ht0 : 0 < t := hpos t (by simp)
    have hts : ∀ u ∈ ts, 0 < u := fun u hu => hpos u (by simp [hu])
    have hsrc' : s.stk src =
        HvdH.Glyph.cons :: ((HvdH.Val.int (t : ℤ)).enc ++ ((HvdH.intList ts).enc ++ gM :: below)) := by
      rw [hsrc, mx_intList_cons]
      simp only [List.cons_append, List.append_assoc]
    set s1 : HvdH.State := HvdH.State.tPop s src mC with hs1
    have e1 : HvdH.Eval main (.pop src mC) s s1 1 := by
      rw [hs1]; exact eval_pop main src mC s
    have hs1src : s1.stk src =
        (HvdH.Val.int (t : ℤ)).enc ++ ((HvdH.intList ts).enc ++ gM :: below) := by
      rw [hs1, tPop_stk, if_pos rfl, hsrc']; rfl
    have hs1reg : s1.reg mC = HvdH.Glyph.cons := by
      rw [hs1, tPop_reg, if_pos rfl, hsrc']; rfl
    have hs1mx : s1.stk mx = (Computability.encodeNat M).map HvdH.Glyph.bit ++ gM :: mxTail := by
      rw [hs1, tPop_stk, if_neg (Ne.symm hsm)]
      exact hmx
    obtain ⟨s2, n2, e2, hn2, hs2src, hs2mx, hs2fr⟩ :=
      helem main t M ((HvdH.intList ts).enc ++ gM :: below) mxTail s1 ht0 hs1src hs1mx
    set s3 : HvdH.State := HvdH.State.tSet s2 mC HvdH.Glyph.eos with hs3
    have e3 : HvdH.Eval main (.set mC HvdH.Glyph.eos) s2 s3 1 := by
      rw [hs3]; exact eval_set main mC HvdH.Glyph.eos s2
    have hs3reg : s3.reg mC = HvdH.Glyph.eos := by rw [hs3, tSet_reg, if_pos rfl]
    have hs3src : s3.stk src = (HvdH.intList ts).enc ++ gM :: below := by
      rw [hs3, tSet_stk, hs2src]
    have hs3mx : s3.stk mx =
        (Computability.encodeNat (max M t)).map HvdH.Glyph.bit ++ gM :: mxTail := by
      rw [hs3, tSet_stk, hs2mx]
    have ebody : HvdH.Eval main (bodyOf elem src) s s3 (1 + ((n2 + 1) + 1)) := by
      show HvdH.Eval main
        (.seq (.pop src mC)
          (.ite mC HvdH.Glyph.cons (.seq elem (.set mC HvdH.Glyph.eos))
            (.set mC HvdH.Glyph.iend))) s s3 (1 + ((n2 + 1) + 1))
      exact Eval.seq e1 (Eval.iteT hs1reg (Eval.seq e2 e3))
    obtain ⟨s4, n4, e4, hn4, hs4src, hs4mx, hs4fr⟩ :=
      ih (max M t) below mxTail s3 hs3reg hts hs3src hs3mx
    refine ⟨s4, _, Eval.loopT hreg ebody e4, ?_, ?_, ?_, ?_⟩
    · have h1 : n2 ≤ Ke * (t + 1) :=
        le_trans hn2 (Nat.mul_le_mul_left Ke (by have := mx_size_le_self t ht0; omega))
      have h3 : Ke * (t + 1) + 4 ≤ (Ke + 5) * (t + 1) := by
        rw [Nat.add_mul]; omega
      have hcost : (1 + ((n2 + 1) + 1)) + n4 + 1 = n2 + n4 + 4 := by ring
      rw [hcost, List.sum_cons, List.length_cons]
      have hgoal : (t + ts.sum) + (ts.length + 1) + 2 = (ts.sum + ts.length + 2) + (t + 1) := by
        ring
      rw [hgoal, Nat.mul_add]
      omega
    · rw [hs4src]
    · rw [hs4mx, mx_lmax_cons, max_assoc]
    · intro j hj1 hj2
      rw [hs4fr j hj1 hj2, hs3, tSet_stk, hs2fr j hj1 hj2, hs1, tPop_stk, if_neg hj1]

/-- The max-phase loop, including the initial `set mC Glyph.eos`. -/
theorem pwMaxLoop (src mx : HvdH.Stk) (hsm : src ≠ mx) (elem : HvdH.Cmd) (Ke : ℕ)
    (helem : ElemSpec src mx elem Ke) :
    ∃ K, ∀ (main : HvdH.Cmd) (suffix : List ℕ) (M : ℕ) (below mxTail : List HvdH.Glyph)
      (s : HvdH.State),
      (∀ t ∈ suffix, 0 < t) →
      s.stk src = (HvdH.intList suffix).enc ++ gM :: below →
      s.stk mx = (Computability.encodeNat M).map HvdH.Glyph.bit ++ gM :: mxTail →
      ∃ s' n, HvdH.Eval main (loopOf elem src) s s' n ∧
        n ≤ K * (suffix.sum + suffix.length + 2) ∧
        s'.stk src = gM :: below ∧
        s'.stk mx = (Computability.encodeNat (max M (HvdH.lmax suffix))).map HvdH.Glyph.bit
          ++ gM :: mxTail ∧
        (∀ j : HvdH.Stk, j ≠ src → j ≠ mx → s'.stk j = s.stk j) := by
  refine ⟨Ke + 6, ?_⟩
  intro main suffix M below mxTail s hpos hsrc hmx
  set s0 : HvdH.State := HvdH.State.tSet s mC HvdH.Glyph.eos with hs0
  have e0 : HvdH.Eval main (.set mC HvdH.Glyph.eos) s s0 1 := by
    rw [hs0]; exact eval_set main mC HvdH.Glyph.eos s
  have hs0reg : s0.reg mC = HvdH.Glyph.eos := by rw [hs0, tSet_reg, if_pos rfl]
  have hs0src : s0.stk src = (HvdH.intList suffix).enc ++ gM :: below := by
    rw [hs0, tSet_stk]; exact hsrc
  have hs0mx : s0.stk mx = (Computability.encodeNat M).map HvdH.Glyph.bit ++ gM :: mxTail := by
    rw [hs0, tSet_stk]; exact hmx
  obtain ⟨s', n', e', hn', hsrc', hmx', hfr'⟩ :=
    pwMaxLoopAux src mx hsm elem Ke helem main suffix M below mxTail s0 hs0reg hpos hs0src hs0mx
  refine ⟨s', _, Eval.seq e0 e', ?_, hsrc', hmx', hfr'⟩
  have hX : 1 ≤ suffix.sum + suffix.length + 2 := by omega
  have hkey : (Ke + 5) * (suffix.sum + suffix.length + 2) + 1
      ≤ (Ke + 6) * (suffix.sum + suffix.length + 2) := by
    have h : (Ke + 6) * (suffix.sum + suffix.length + 2)
        = (Ke + 5) * (suffix.sum + suffix.length + 2)
          + (suffix.sum + suffix.length + 2) := by ring
    rw [h]; omega
  omega

end Work.Transform.Pw
