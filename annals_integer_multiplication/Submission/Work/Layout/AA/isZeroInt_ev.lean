import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `isZeroInt`: `Ev`-level specification

`Work.Layout.isZeroInt a rr rf rs` pops the sign glyph of the integer value on top of stack `a`,
peeks at the following glyph and sets the flag register `rf` to `cons` exactly when it is `iend`
(i.e. exactly when the integer is `0`), then puts the sign glyph back.  The whole value is
restored, every other stack is untouched, and the cost is `5`.

The characterisation of the flag is `Work.Layout.AA.headD_encodeNat_bits`: the head of
`(encodeNat k).map bit ++ [iend] ++ A` is `iend` iff `k = 0` (the encoding of `0` is empty, that of
every positive `k` starts with a bit).
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH

/-- `Computability.encodeNat` is empty exactly at `0`. -/
theorem encodeNat_nil_iff (k : ℕ) : Computability.encodeNat k = [] ↔ k = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  have h2 : Computability.decodeNat (Computability.encodeNat k) = k :=
    Computability.decode_encodeNat k
  rw [h] at h2
  exact h2.symm

/-- The head of the bit encoding of `k` (terminated by `iend` and with tail `A`) is `iend` exactly
when `k = 0`. -/
theorem headD_encodeNat_bits (k : ℕ) (A : List Glyph) :
    ((Computability.encodeNat k).map Glyph.bit ++ [Glyph.iend] ++ A).headD Glyph.eos =
      Glyph.iend ↔ k = 0 := by
  rcases h : Computability.encodeNat k with _ | ⟨b, bs⟩
  · simp only [List.map_nil, List.nil_append, List.cons_append, List.headD_cons]
    exact ⟨fun _ => (encodeNat_nil_iff k).mp h, fun _ => trivial⟩
  · simp only [List.map_cons, List.cons_append, List.headD_cons]
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · cases hh
    · exact absurd hh (fun h0 => by
        have hz := (encodeNat_nil_iff k).mpr h0
        rw [h] at hz
        exact List.cons_ne_nil b bs hz)

/-- `seqs [.set rf c, .push a rs]` restores a glyph on the top of `a` and writes `c` into `rf`,
in two steps.  It is the common shape of the two branches of the `ite` inside `isZeroInt`. -/
theorem isZeroInt_body (main : HvdH.Cmd) (a : HvdH.Stk) (rf rs : HvdH.Reg)
    (g2 : HvdH.Reg → HvdH.Glyph) (X1 : HvdH.Stk → List HvdH.Glyph) (c : HvdH.Glyph)
    (hpos : (Function.update g2 rf c) rs = HvdH.Glyph.pos) :
    Work.Layout.Ev main (Work.Layout.seqs [.set rf c, .push a rs]) ⟨g2, X1⟩
      ⟨Function.update g2 rf c, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 2 := by
  have hset : Work.Layout.Ev main (.set rf c) ⟨g2, X1⟩ ⟨Function.update g2 rf c, X1⟩ 1 :=
    Work.Layout.ev_set' main rf c g2 X1
  have hpush : Work.Layout.Ev main (.push a rs) ⟨Function.update g2 rf c, X1⟩
      ⟨Function.update g2 rf c, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 1 := by
    have h := Work.Layout.ev_push' main a rs (Function.update g2 rf c) X1
    rw [hpos] at h
    exact h
  show Work.Layout.Ev main (.seq (.set rf c) (.push a rs)) _ _ 2
  exact Work.Layout.Ev.seq' hset hpush (by omega)

/-- **Main workhorse.**  With the sign glyph already exposed on top of `a` (so that the remaining
content of `a` is the bit encoding of `k` followed by `A`), `isZeroInt` restores `a`,
sets `rf = cons` exactly when `k = 0`, and leaves all other stacks alone; cost `≤ 5`. -/
theorem isZeroInt_gen (main : HvdH.Cmd) (a : HvdH.Stk) (rr rf rs : HvdH.Reg)
    (h2 : rr ≠ rs) (h3 : rf ≠ rs)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (A : List HvdH.Glyph) (k : ℕ)
    (hb : X a = HvdH.Glyph.pos ::
      ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A)) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.isZeroInt a rr rf rs) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk a = HvdH.Glyph.pos ::
        ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) ∧
      (∀ j, j ≠ a → s'.stk j = X j) ∧
      (k = 0 ↔ s'.reg rf = HvdH.Glyph.cons) := by
  have hXa_head : (X a).headD HvdH.Glyph.eos = HvdH.Glyph.pos := by rw [hb]; rfl
  have hXa_tail : (X a).tail =
      (Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A := by
    rw [hb]; rfl
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g rs HvdH.Glyph.pos
  let X1 : HvdH.Stk → List HvdH.Glyph := Function.update X a (X a).tail
  have hpop : Work.Layout.Ev main (.pop a rs) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rs g X
    rw [hXa_head] at h
    exact h
  have hX1a : X1 a =
      (Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A := by
    simp only [X1, Work.Layout.stkFn_same]
    exact hXa_tail
  let g2 : HvdH.Reg → HvdH.Glyph := Function.update g1 rr ((X1 a).headD HvdH.Glyph.eos)
  have hpeek : Work.Layout.Ev main (.peek a rr) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 :=
    Work.Layout.ev_peek' main a rr g1 X1
  have hrs_g2 : g2 rs = HvdH.Glyph.pos := by
    show Function.update g1 rr ((X1 a).headD HvdH.Glyph.eos) rs = HvdH.Glyph.pos
    rw [Function.update_of_ne (Ne.symm h2)]
    show Function.update g rs HvdH.Glyph.pos rs = HvdH.Glyph.pos
    exact Function.update_self rs HvdH.Glyph.pos g
  have hbodyT : Work.Layout.Ev main (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rs])
      ⟨g2, X1⟩
      ⟨Function.update g2 rf HvdH.Glyph.cons, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 2 :=
    isZeroInt_body main a rf rs g2 X1 HvdH.Glyph.cons (by
      rw [Function.update_of_ne (Ne.symm h3)]; exact hrs_g2)
  have hbodyF : Work.Layout.Ev main (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rs])
      ⟨g2, X1⟩
      ⟨Function.update g2 rf HvdH.Glyph.eos, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 2 :=
    isZeroInt_body main a rf rs g2 X1 HvdH.Glyph.eos (by
      rw [Function.update_of_ne (Ne.symm h3)]; exact hrs_g2)
  by_cases hk : k = 0
  · have hcond : g2 rr = HvdH.Glyph.iend := by
      show Function.update g1 rr ((X1 a).headD HvdH.Glyph.eos) rr = HvdH.Glyph.iend
      rw [Function.update_self, hX1a]
      exact (headD_encodeNat_bits k A).mpr hk
    have hit : Work.Layout.Ev main (.ite rr HvdH.Glyph.iend
        (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rs])
        (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rs])) ⟨g2, X1⟩
        ⟨Function.update g2 rf HvdH.Glyph.cons, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 3 :=
      Work.Layout.Ev.iteT hcond hbodyT
    have h12 : Work.Layout.Ev main (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
        (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rs])
        (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rs]))) ⟨g1, X1⟩
        ⟨Function.update g2 rf HvdH.Glyph.cons, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 4 :=
      Work.Layout.Ev.seq' hpeek hit (by omega)
    have htot : Work.Layout.Ev main (Work.Layout.isZeroInt a rr rf rs) ⟨g, X⟩
        ⟨Function.update g2 rf HvdH.Glyph.cons, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 5 := by
      show Work.Layout.Ev main (.seq (.pop a rs) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend _ _))) _ _ 5
      exact Work.Layout.Ev.seq' hpop h12 (by omega)
    refine ⟨_, _, htot, by omega, ?_, ?_, ?_⟩
    · show (Function.update X1 a (HvdH.Glyph.pos :: X1 a)) a =
        HvdH.Glyph.pos :: (List.map HvdH.Glyph.bit (Computability.encodeNat k) ++ [HvdH.Glyph.iend] ++ A)
      rw [Work.Layout.stkFn_same, hX1a]
    · intro j hj
      show (Function.update X1 a (HvdH.Glyph.pos :: X1 a)) j = X j
      rw [Work.Layout.stkFn_ne X1 hj (HvdH.Glyph.pos :: X1 a)]
      exact Work.Layout.stkFn_ne X hj (X a).tail
    · refine ⟨fun _ => ?_, fun _ => hk⟩
      exact Work.Layout.regUpd_same g2 rf HvdH.Glyph.cons
  · have hcond : g2 rr ≠ HvdH.Glyph.iend := by
      show Function.update g1 rr ((X1 a).headD HvdH.Glyph.eos) rr ≠ HvdH.Glyph.iend
      rw [Function.update_self, hX1a]
      intro hh
      exact hk ((headD_encodeNat_bits k A).mp hh)
    have hit : Work.Layout.Ev main (.ite rr HvdH.Glyph.iend
        (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rs])
        (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rs])) ⟨g2, X1⟩
        ⟨Function.update g2 rf HvdH.Glyph.eos, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 3 :=
      Work.Layout.Ev.iteF hcond hbodyF
    have h12 : Work.Layout.Ev main (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
        (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rs])
        (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rs]))) ⟨g1, X1⟩
        ⟨Function.update g2 rf HvdH.Glyph.eos, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 4 :=
      Work.Layout.Ev.seq' hpeek hit (by omega)
    have htot : Work.Layout.Ev main (Work.Layout.isZeroInt a rr rf rs) ⟨g, X⟩
        ⟨Function.update g2 rf HvdH.Glyph.eos, Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ 5 := by
      show Work.Layout.Ev main (.seq (.pop a rs) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend _ _))) _ _ 5
      exact Work.Layout.Ev.seq' hpop h12 (by omega)
    refine ⟨_, _, htot, by omega, ?_, ?_, ?_⟩
    · show (Function.update X1 a (HvdH.Glyph.pos :: X1 a)) a =
        HvdH.Glyph.pos :: (List.map HvdH.Glyph.bit (Computability.encodeNat k) ++ [HvdH.Glyph.iend] ++ A)
      rw [Work.Layout.stkFn_same, hX1a]
    · intro j hj
      show (Function.update X1 a (HvdH.Glyph.pos :: X1 a)) j = X j
      rw [Work.Layout.stkFn_ne X1 hj (HvdH.Glyph.pos :: X1 a)]
      exact Work.Layout.stkFn_ne X hj (X a).tail
    · have hrf : (⟨Function.update g2 rf HvdH.Glyph.eos,
            Function.update X1 a (HvdH.Glyph.pos :: X1 a)⟩ : HvdH.State).reg rf = HvdH.Glyph.eos :=
        Work.Layout.regUpd_same g2 rf HvdH.Glyph.eos
      refine ⟨fun h0 => absurd h0 hk, fun h => ?_⟩
      rw [hrf] at h
      exact absurd h (fun hh => by cases hh)

/-- **Main specification.**  `isZeroInt a rr rf rs` tests whether the integer value on top of
stack `a` is zero: it sets `rf` to `cons` exactly when `k = 0`, restores stack `a` completely,
leaves every other stack unchanged, and costs at most `10` steps. -/
theorem isZeroInt_ev (main : HvdH.Cmd) (a : HvdH.Stk) (rr rf rs : HvdH.Reg)
    (h1 : rr ≠ rf) (h2 : rr ≠ rs) (h3 : rf ≠ rs)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ) (A : List HvdH.Glyph)
    (ha : X a = (HvdH.Val.int k).enc ++ A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.isZeroInt a rr rf rs) ⟨g, X⟩ s' n ∧ n ≤ 10 ∧
      s'.stk a = (HvdH.Val.int k).enc ++ A ∧ (∀ j, j ≠ a → s'.stk j = X j) ∧
      (k = 0 ↔ s'.reg rf = HvdH.Glyph.cons) := by
  have henc : (HvdH.Val.int (k : ℤ)).enc =
      HvdH.Glyph.pos ::
        ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    simp [HvdH.Val.enc]
  have hb : X a = HvdH.Glyph.pos ::
      ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) := by
    rw [ha, henc]
    simp only [List.cons_append]
  obtain ⟨s', n, hev, hn, hstk, hframe, hrf⟩ :=
    isZeroInt_gen main a rr rf rs h2 h3 g X A k hb
  refine ⟨s', n, hev, by omega, ?_, hframe, hrf⟩
  rw [hstk, henc]
  simp only [List.cons_append]

end Work.Layout.AA
