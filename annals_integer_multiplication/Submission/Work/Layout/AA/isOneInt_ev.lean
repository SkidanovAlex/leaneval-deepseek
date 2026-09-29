import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.isZeroInt_ev
import Submission.Work.Kernel.encodeNatBits

/-!
# `isOneInt`: `Ev`-level specification

`Work.Layout.isOneInt a rr rf rs rt` tests whether the (positive) integer on top of stack `a`
equals one.  It pops the sign glyph (`rs`) and the first bit (`rt`), peeks at the glyph that
follows (`rr`), and sets the flag register `rf` to `cons` exactly when that glyph is `iend`,
i.e. exactly when the bit encoding of the counter has length one, i.e. exactly when the
counter is `1`.  The two glyphs popped are pushed back in the reverse order, so the whole
value is restored; every other stack is untouched and the cost is `7`.

The characterisation of the flag is `Work.Layout.AA.headD_map_bit_append_iend` (the head of
`(l.map bit) ++ [iend] ++ A` is `iend` exactly when the bit list `l` is empty, here applied
to the tail of `encodeNat k`) together with `Work.Layout.AA.encodeNat_tail_eq_nil_iff`
(`(encodeNat k).tail = []` iff `k ≤ 1`, using `encodeNat = Nat.bits` and
`Nat.size_eq_bits_len` / `Nat.size_le`).
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH

/-! ## Auxiliary facts about bit encodings -/

/-- The head of `(l.map bit) ++ [iend] ++ A` is `iend` exactly when `l` is empty. -/
theorem headD_map_bit_append_iend (l : List Bool) (A : List Glyph) :
    ((l.map Glyph.bit) ++ [Glyph.iend] ++ A).headD Glyph.eos = Glyph.iend ↔ l = [] := by
  cases l with
  | nil => simp
  | cons b bs => simp

/-- The bit encoding of `k` has at most one bit iff `k ≤ 1`. -/
theorem encodeNat_tail_eq_nil_iff (k : ℕ) : (Computability.encodeNat k).tail = [] ↔ k ≤ 1 := by
  rw [Work.Kernel.encodeNatBits k, List.tail_eq_nil_iff, Nat.size_eq_bits_len, Nat.size_le]
  norm_num

/-! ## The common shape of the two branches of the `ite` -/

/-- Both branches of the `ite` inside `isOneInt` have the shape
`seqs [.set rf c, .push a rt, .push a rs]`: write `c` into `rf`, then push back the two glyphs
popped from `a` (the first bit, then the sign), using registers `rt` and `rs` for the pushes.
`hrt`/`hrs` give the glyphs these registers currently hold, and distinctness of `rf` from `rt`
and `rs` ensures they are not clobbered by the `set`. -/
theorem isOneInt_body (main : HvdH.Cmd) (a : HvdH.Stk) (rf rs rt : HvdH.Reg)
    (hft : rf ≠ rt) (hfs : rf ≠ rs)
    (g3 : HvdH.Reg → HvdH.Glyph) (X2 : HvdH.Stk → List HvdH.Glyph) (c hrtv hrsv : HvdH.Glyph)
    (hrt : g3 rt = hrtv) (hrs : g3 rs = hrsv) :
    Work.Layout.Ev main (Work.Layout.seqs [.set rf c, .push a rt, .push a rs]) ⟨g3, X2⟩
      ⟨Function.update g3 rf c,
       Function.update (Function.update X2 a (hrtv :: X2 a)) a (hrsv :: hrtv :: X2 a)⟩ 3 := by
  have hset : Work.Layout.Ev main (.set rf c) ⟨g3, X2⟩ ⟨Function.update g3 rf c, X2⟩ 1 :=
    Work.Layout.ev_set' main rf c g3 X2
  have hp1 : Work.Layout.Ev main (.push a rt) ⟨Function.update g3 rf c, X2⟩
      ⟨Function.update g3 rf c, Function.update X2 a (hrtv :: X2 a)⟩ 1 := by
    have h := Work.Layout.ev_push' main a rt (Function.update g3 rf c) X2
    rw [show (Function.update g3 rf c) rt = hrtv by
      rw [Function.update_of_ne (Ne.symm hft)]; exact hrt] at h
    exact h
  have hp2 : Work.Layout.Ev main (.push a rs) ⟨Function.update g3 rf c, Function.update X2 a (hrtv :: X2 a)⟩
      ⟨Function.update g3 rf c,
        Function.update (Function.update X2 a (hrtv :: X2 a)) a (hrsv :: hrtv :: X2 a)⟩ 1 := by
    have h := Work.Layout.ev_push' main a rs (Function.update g3 rf c) (Function.update X2 a (hrtv :: X2 a))
    rw [show (Function.update g3 rf c) rs = hrsv by
      rw [Function.update_of_ne (Ne.symm hfs)]; exact hrs] at h
    simpa using h
  have hb : Work.Layout.Ev main (.seq (.push a rt) (.push a rs)) ⟨Function.update g3 rf c, X2⟩
      ⟨Function.update g3 rf c,
        Function.update (Function.update X2 a (hrtv :: X2 a)) a (hrsv :: hrtv :: X2 a)⟩ 2 :=
    Work.Layout.Ev.seq' hp1 hp2 (by omega)
  have h12 : Work.Layout.Ev main (.seq (.set rf c) (.seq (.push a rt) (.push a rs))) ⟨g3, X2⟩
      ⟨Function.update g3 rf c,
        Function.update (Function.update X2 a (hrtv :: X2 a)) a (hrsv :: hrtv :: X2 a)⟩ 3 :=
    Work.Layout.Ev.seq' hset hb (by omega)
  simpa only [Work.Layout.seqs] using h12

/-! ## Main specification -/

theorem isOneInt_ev (main : HvdH.Cmd) (a : HvdH.Stk) (rr rf rs rt : HvdH.Reg)
    (hrr : rr ≠ rf) (hrs : rs ≠ rr) (hfs : rf ≠ rs) (hrt : rt ≠ rr) (hft : rf ≠ rt) (hst : rs ≠ rt)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ) (hk : 1 ≤ k)
    (A : List HvdH.Glyph) (ha : X a = (HvdH.Val.int k).enc ++ A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.isOneInt a rr rf rs rt) ⟨g, X⟩ s' n ∧ n ≤ 14 ∧
      s'.stk a = (HvdH.Val.int k).enc ++ A ∧ (∀ j, j ≠ a → s'.stk j = X j) ∧
      (k = 1 ↔ s'.reg rf = HvdH.Glyph.cons) := by
  have hk0 : k ≠ 0 := by omega
  have henc : (HvdH.Val.int (k : ℤ)).enc =
      HvdH.Glyph.pos :: ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    simp [HvdH.Val.enc]
  obtain ⟨b, bs, hbits⟩ : ∃ b bs, Computability.encodeNat k = b :: bs := by
    rcases hs : Computability.encodeNat k with _ | ⟨b, bs⟩
    · exact absurd ((encodeNat_nil_iff k).mp hs) hk0
    · exact ⟨b, bs, rfl⟩
  have hXa : X a = HvdH.Glyph.pos ::
      ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) := by
    rw [ha, henc]; simp
  have hbitsmap : (Computability.encodeNat k).map HvdH.Glyph.bit =
      HvdH.Glyph.bit b :: bs.map HvdH.Glyph.bit := by rw [hbits]; rfl
  have htarget : (HvdH.Val.int k).enc ++ A = HvdH.Glyph.pos ::
      ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) := by
    rw [henc]; simp
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g rs HvdH.Glyph.pos
  let X1 : HvdH.Stk → List HvdH.Glyph := Function.update X a (X a).tail
  have hhead_a : (X a).headD HvdH.Glyph.eos = HvdH.Glyph.pos := by rw [hXa]; rfl
  have htail_a : (X a).tail =
      HvdH.Glyph.bit b :: (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) := by
    rw [hXa, hbitsmap]; rfl
  have hpop1 : Work.Layout.Ev main (.pop a rs) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rs g X
    rw [hhead_a] at h
    exact h
  have hX1a : X1 a = HvdH.Glyph.bit b :: (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A) := by
    show Function.update X a (X a).tail a = _
    rw [stkFn_same]; exact htail_a
  have hhead_1 : (X1 a).headD HvdH.Glyph.eos = HvdH.Glyph.bit b := by rw [hX1a]; rfl
  have htail_1 : (X1 a).tail = bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A := by rw [hX1a]; rfl
  let g2 : HvdH.Reg → HvdH.Glyph := Function.update g1 rt (HvdH.Glyph.bit b)
  let X2 : HvdH.Stk → List HvdH.Glyph := Function.update X1 a (X1 a).tail
  have hpop2 : Work.Layout.Ev main (.pop a rt) ⟨g1, X1⟩ ⟨g2, X2⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rt g1 X1
    rw [hhead_1] at h
    exact h
  have hX2a : X2 a = bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A := by
    show Function.update X1 a (X1 a).tail a = _
    rw [stkFn_same]; exact htail_1
  let g3 : HvdH.Reg → HvdH.Glyph := Function.update g2 rr ((X2 a).headD HvdH.Glyph.eos)
  have hpeek : Work.Layout.Ev main (.peek a rr) ⟨g2, X2⟩ ⟨g3, X2⟩ 1 :=
    Work.Layout.ev_peek' main a rr g2 X2
  have hg3rr : g3 rr = (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A).headD HvdH.Glyph.eos := by
    show Function.update g2 rr ((X2 a).headD HvdH.Glyph.eos) rr = _
    rw [Function.update_self, hX2a]
  have hcond : g3 rr = HvdH.Glyph.iend ↔ k = 1 := by
    rw [hg3rr, headD_map_bit_append_iend]
    have hbs : (bs : List Bool) = (Computability.encodeNat k).tail := by rw [hbits]; rfl
    rw [hbs, encodeNat_tail_eq_nil_iff]
    constructor <;> omega
  have hrtv : g3 rt = HvdH.Glyph.bit b := by
    show Function.update g2 rr ((X2 a).headD HvdH.Glyph.eos) rt = HvdH.Glyph.bit b
    rw [Function.update_of_ne hrt]
    show Function.update g1 rt (HvdH.Glyph.bit b) rt = HvdH.Glyph.bit b
    rw [Function.update_self]
  have hrsv : g3 rs = HvdH.Glyph.pos := by
    show Function.update g2 rr ((X2 a).headD HvdH.Glyph.eos) rs = HvdH.Glyph.pos
    rw [Function.update_of_ne hrs]
    show Function.update g1 rt (HvdH.Glyph.bit b) rs = HvdH.Glyph.pos
    rw [Function.update_of_ne hst]
    show Function.update g rs HvdH.Glyph.pos rs = HvdH.Glyph.pos
    rw [Function.update_self]
  have hbody : ∀ c : HvdH.Glyph, Work.Layout.Ev main
      (Work.Layout.seqs [.set rf c, .push a rt, .push a rs]) ⟨g3, X2⟩
      ⟨Function.update g3 rf c,
        Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
          (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a)⟩ 3 := fun c =>
    isOneInt_body main a rf rs rt hft hfs g3 X2 c (HvdH.Glyph.bit b) HvdH.Glyph.pos hrtv hrsv
  by_cases hk1 : k = 1
  · have hcondT : g3 rr = HvdH.Glyph.iend := hcond.mpr hk1
    let sT : HvdH.State := ⟨Function.update g3 rf HvdH.Glyph.cons,
      Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
        (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a)⟩
    have hite : Work.Layout.Ev main
        (.ite rr HvdH.Glyph.iend (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs])) ⟨g3, X2⟩ sT 4 :=
      Work.Layout.Ev.iteT hcondT (hbody HvdH.Glyph.cons)
    have h12 : Work.Layout.Ev main
        (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs]))) ⟨g2, X2⟩ sT 5 :=
      Work.Layout.Ev.seq' hpeek hite (by omega)
    have h23 : Work.Layout.Ev main
        (.seq (.pop a rt) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs])))) ⟨g1, X1⟩ sT 6 :=
      Work.Layout.Ev.seq' hpop2 h12 (by omega)
    have htot : Work.Layout.Ev main (Work.Layout.isOneInt a rr rf rs rt) ⟨g, X⟩ sT 7 := by
      show Work.Layout.Ev main
        (.seq (.pop a rs) (.seq (.pop a rt) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs]))))) ⟨g, X⟩ sT 7
      exact Work.Layout.Ev.seq' hpop1 h23 (by omega)
    refine ⟨sT, 7, htot, by omega, ?_, ?_, ?_⟩
    · rw [htarget]
      show Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
          (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a) a = _
      rw [stkFn_same, hX2a, hbitsmap]
      simp only [List.append_assoc, List.cons_append]
    · intro j hj
      show Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
          (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a) j = X j
      rw [stkFn_ne (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) hj
            (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a),
          stkFn_ne X2 hj (HvdH.Glyph.bit b :: X2 a)]
      exact (stkFn_ne X1 hj (X1 a).tail).trans (stkFn_ne X hj (X a).tail)
    · exact ⟨fun _ => regUpd_same g3 rf HvdH.Glyph.cons, fun _ => hk1⟩
  · have hcondF : g3 rr ≠ HvdH.Glyph.iend := fun h => hk1 (hcond.mp h)
    let sT : HvdH.State := ⟨Function.update g3 rf HvdH.Glyph.eos,
      Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
        (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a)⟩
    have hite : Work.Layout.Ev main
        (.ite rr HvdH.Glyph.iend (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs])) ⟨g3, X2⟩ sT 4 :=
      Work.Layout.Ev.iteF hcondF (hbody HvdH.Glyph.eos)
    have h12 : Work.Layout.Ev main
        (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs]))) ⟨g2, X2⟩ sT 5 :=
      Work.Layout.Ev.seq' hpeek hite (by omega)
    have h23 : Work.Layout.Ev main
        (.seq (.pop a rt) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs])))) ⟨g1, X1⟩ sT 6 :=
      Work.Layout.Ev.seq' hpop2 h12 (by omega)
    have htot : Work.Layout.Ev main (Work.Layout.isOneInt a rr rf rs rt) ⟨g, X⟩ sT 7 := by
      show Work.Layout.Ev main
        (.seq (.pop a rs) (.seq (.pop a rt) (.seq (.peek a rr) (.ite rr HvdH.Glyph.iend
          (Work.Layout.seqs [.set rf HvdH.Glyph.cons, .push a rt, .push a rs])
          (Work.Layout.seqs [.set rf HvdH.Glyph.eos, .push a rt, .push a rs]))))) ⟨g, X⟩ sT 7
      exact Work.Layout.Ev.seq' hpop1 h23 (by omega)
    refine ⟨sT, 7, htot, by omega, ?_, ?_, ?_⟩
    · rw [htarget]
      show Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
          (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a) a = _
      rw [stkFn_same, hX2a, hbitsmap]
      simp only [List.append_assoc, List.cons_append]
    · intro j hj
      show Function.update (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) a
          (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a) j = X j
      rw [stkFn_ne (Function.update X2 a (HvdH.Glyph.bit b :: X2 a)) hj
            (HvdH.Glyph.pos :: HvdH.Glyph.bit b :: X2 a),
          stkFn_ne X2 hj (HvdH.Glyph.bit b :: X2 a)]
      exact (stkFn_ne X1 hj (X1 a).tail).trans (stkFn_ne X hj (X a).tail)
    · refine ⟨fun h => absurd h hk1, fun h => ?_⟩
      have hrf : sT.reg rf = HvdH.Glyph.eos := regUpd_same g3 rf HvdH.Glyph.eos
      rw [hrf] at h
      exact absurd h (by decide)

end Work.Layout.AA
