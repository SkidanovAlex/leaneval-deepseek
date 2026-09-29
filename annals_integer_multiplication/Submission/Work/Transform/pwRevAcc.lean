import Mathlib
import Submission.Work.Transform.pwRevAccDefs

/-!
# `Work.Transform.pwRevAcc`: reversal accumulation

`pwRevAcc` traverses the `cons`-list `ofList xs` (all of whose elements are integer values) sitting
above the frame marker `Pw.gM` on stack `src`, and rebuilds the *reversed* list `ofList xs.reverse`
above a freshly pushed `Pw.gM` on stack `dst` in time linear in `(ofList xs).enc.length`, restoring
every stack but `src` and `dst` (in particular the scratch stacks `sp` and `ds`).

The program `pwRaProg` (`Submission.Work.Transform.pwRevAccDefs`):
* the prologue pushes `gM` and `nil` on `dst`;
* the loop `pwRaBody` pops the leading glyph of `src`: a `cons` runs the one-element block
  `pwRaElem` (`pwRaElemEvalAux` below) and continues, a `nil` stops;
* each iteration pushes the block `pwRaBlock (Val.int z) = cons :: (Val.int z).enc` on `dst`, so
  after all iterations `dst` holds `pwRaBlocks xs ++ [nil] ++ gM :: dst`, which is
  `(ofList xs.reverse).enc ++ gM :: dst` (`pwRaBlocks_append_nil`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH
open Work.Kernel

/-- The "one element" block of the reversal loop (implementation of the lemma delegated as
`Work.Transform.pwRaElemEval`): `Pw.storeMag` pops the sign glyph of the integer on top of `src`
onto `ds` and moves its bits (most significant first) above a fresh `gM` on `sp`; then `dst`
receives `iend`, the bits (moved back from `sp`, which is restored by `Pw.dropMarked`), the sign
(returned from `ds`) and finally the leading `cons`. -/
theorem pwRaElemEvalAux (main : Cmd) (src dst sp ds : Stk)
    (h1 : src ≠ dst) (h2 : sp ≠ src) (h3 : sp ≠ dst) (h4 : ds ≠ src) (h5 : ds ≠ dst)
    (h6 : ds ≠ sp) (z : ℤ) (tail : List Glyph) (s : State)
    (hsrc : s.stk src = (Val.int z).enc ++ tail) :
    ∃ s' n, Eval main (pwRaElem src dst sp ds) s s' n ∧ n ≤ 10 * z.natAbs.size + 40 ∧
      s'.stk src = tail ∧
      s'.stk dst = pwRaBlock (Val.int z) ++ s.stk dst ∧
      (∀ j : Stk, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  have h1' : dst ≠ src := Ne.symm h1
  have h3' : dst ≠ sp := Ne.symm h3
  have h5' : dst ≠ ds := Ne.symm h5
  have h4' : src ≠ ds := Ne.symm h4
  have h6' : sp ≠ ds := Ne.symm h6
  set sign : Glyph := (if z < 0 then Glyph.neg else Glyph.pos) with hsign
  set bits : List Bool := Computability.encodeNat z.natAbs with hbits
  have hbl : bits.length = z.natAbs.size := by rw [hbits, Work.IntLib.encodeNat_length]
  have hstkm : s.stk src = sign :: (bits.map Glyph.bit ++ Glyph.iend :: tail) := by
    rw [hsrc, enc_int_eq, hsign, hbits]
    simp [List.cons_append, List.append_assoc]
  obtain ⟨s1, n1, e1, hn1, hs1src, hs1sp, hs1ds, hs1fr⟩ :=
    Pw.storeMag_eval main src sp ds pwrA pwrB h2 h4 h6 sign bits tail s hstkm
  have hs1dst : s1.stk dst = s.stk dst := hs1fr dst h1' h3' h5'
  -- (2) set pwrA iend
  set s2 : State := State.tSet s1 pwrA Glyph.iend with hs2
  have e2 : Eval main (.set pwrA Glyph.iend) s1 s2 1 := by
    rw [hs2]; exact eval_set main pwrA Glyph.iend s1
  -- (3) push dst pwrA
  set s3 : State := State.tPush s2 dst pwrA with hs3
  have e3 : Eval main (.push dst pwrA) s2 s3 1 := by
    rw [hs3]; exact eval_push main dst pwrA s2
  have hs3dst : s3.stk dst = Glyph.iend :: s.stk dst := by
    rw [hs3, Pw.tPush_stk, if_pos rfl, hs2, Pw.tSet_reg, if_pos rfl, Pw.tSet_stk, hs1dst]
  have hs3sp : s3.stk sp = bits.reverse.map Glyph.bit ++ Pw.gM :: s.stk sp := by
    rw [hs3, Pw.tPush_stk, if_neg h3, hs2, Pw.tSet_stk]; exact hs1sp
  -- (4) tLoop sp gM dst pwrB
  have hbits_ne : ∀ g ∈ bits.reverse.map Glyph.bit, g ≠ Pw.gM := Pw.map_bit_ne_gM bits.reverse
  have e4 : Eval main (Pw.tLoop sp Pw.gM dst pwrB) s3
      (Pw.tSt sp Pw.gM dst pwrB (bits.reverse.map Glyph.bit) (s.stk sp) s3)
      (5 * (bits.reverse.map Glyph.bit).length + 7) :=
    Pw.tLoop_eval main sp Pw.gM dst pwrB h3' Pw.gM_ne_eos
      (bits.reverse.map Glyph.bit) (s.stk sp) s3 hs3sp hbits_ne
  set s4 : State := Pw.tSt sp Pw.gM dst pwrB (bits.reverse.map Glyph.bit) (s.stk sp) s3 with hs4
  have hs4sp : s4.stk sp = Pw.gM :: s.stk sp := by
    rw [hs4, Pw.tSt_stk_k _ _ _ _ _ _ _ h3']
  have hs4dst : s4.stk dst = bits.map Glyph.bit ++ (Glyph.iend :: s.stk dst) := by
    rw [hs4, Pw.tSt_stk_dst, hs3dst, List.map_reverse, List.reverse_reverse]
  have hs4fr : ∀ j, j ≠ sp → j ≠ dst → s4.stk j = s3.stk j := by
    intro j hj1 hj2; rw [hs4, Pw.tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj2]
  -- (5) dropMarked sp pwrA pwrB
  obtain ⟨s5, n5, e5, hn5, hs5sp, hs5fr, hs5reg⟩ :=
    Pw.dropMarked_eval main sp pwrA pwrB [] (s.stk sp) (by simp) s4 (by rw [hs4sp]; rfl)
  have hs5ds : s5.stk ds = sign :: s.stk ds := by
    rw [hs5fr ds h6, hs4fr ds h6 h5, hs3, Pw.tPush_stk, if_neg h5, hs2, Pw.tSet_stk, hs1ds]
  -- (6) pop ds pwrA
  set s6 : State := State.tPop s5 ds pwrA with hs6
  have e6 : Eval main (.pop ds pwrA) s5 s6 1 := by rw [hs6]; exact eval_pop main ds pwrA s5
  have hs6ds : s6.stk ds = s.stk ds := by
    rw [hs6, Pw.tPop_stk, if_pos rfl, hs5ds]; rfl
  have hs6reg : s6.reg pwrA = sign := by
    rw [hs6, Pw.tPop_reg, if_pos rfl, hs5ds]; rfl
  -- (7) push dst pwrA
  set s7 : State := State.tPush s6 dst pwrA with hs7
  have e7 : Eval main (.push dst pwrA) s6 s7 1 := by rw [hs7]; exact eval_push main dst pwrA s6
  have hs7dst : s7.stk dst = sign :: (bits.map Glyph.bit ++ (Glyph.iend :: s.stk dst)) := by
    rw [hs7, Pw.tPush_stk, if_pos rfl, hs6reg, hs6, Pw.tPop_stk, if_neg h5',
      hs5fr dst h3', hs4dst]
  -- (8) set pwrA cons
  set s8 : State := State.tSet s7 pwrA Glyph.cons with hs8
  have e8 : Eval main (.set pwrA Glyph.cons) s7 s8 1 := by
    rw [hs8]; exact eval_set main pwrA Glyph.cons s7
  -- (9) push dst pwrA
  set s9 : State := State.tPush s8 dst pwrA with hs9
  have e9 : Eval main (.push dst pwrA) s8 s9 1 := by rw [hs9]; exact eval_push main dst pwrA s8
  have hs9dst : s9.stk dst = pwRaBlock (Val.int z) ++ s.stk dst := by
    rw [hs9, Pw.tPush_stk, if_pos rfl, hs8, Pw.tSet_reg, if_pos rfl, Pw.tSet_stk, hs7dst]
    rw [pwRaBlock, enc_int_eq, hsign, hbits]
    simp [List.cons_append, List.append_assoc]
  have hs9src : s9.stk src = tail := by
    rw [hs9, Pw.tPush_stk, if_neg h1, hs8, Pw.tSet_stk, hs7, Pw.tPush_stk, if_neg h1,
      hs6, Pw.tPop_stk, if_neg h4', hs5fr src (Ne.symm h2), hs4fr src (Ne.symm h2) h1,
      hs3, Pw.tPush_stk, if_neg h1, hs2, Pw.tSet_stk]
    exact hs1src
  have hs9sp : s9.stk sp = s.stk sp := by
    rw [hs9, Pw.tPush_stk, if_neg h3, hs8, Pw.tSet_stk, hs7, Pw.tPush_stk, if_neg h3,
      hs6, Pw.tPop_stk, if_neg h6', hs5sp]
  have hs9ds : s9.stk ds = s.stk ds := by
    rw [hs9, Pw.tPush_stk, if_neg h5, hs8, Pw.tSet_stk, hs7, Pw.tPush_stk, if_neg h5,
      hs6ds]
  have hgen : ∀ j, j ≠ src → j ≠ dst → j ≠ sp → j ≠ ds → s9.stk j = s.stk j := by
    intro j hj1 hj2 hj3 hj4
    rw [hs9, Pw.tPush_stk, if_neg hj2, hs8, Pw.tSet_stk, hs7, Pw.tPush_stk, if_neg hj2,
      hs6, Pw.tPop_stk, if_neg hj4, hs5fr j hj3, hs4fr j hj3 hj2, hs3, Pw.tPush_stk, if_neg hj2,
      hs2, Pw.tSet_stk, hs1fr j hj1 hj3 hj4]
  have hframe : ∀ j : Stk, j ≠ src → j ≠ dst → s9.stk j = s.stk j := by
    intro j hj1 hj2
    by_cases hjs : j = sp
    · subst hjs; exact hs9sp
    by_cases hjd : j = ds
    · subst hjd; exact hs9ds
    · exact hgen j hj1 hj2 hjs hjd
  have eall : Eval main (pwRaElem src dst sp ds) s s9
      (n1 + (1 + (1 + ((5 * (bits.reverse.map Glyph.bit).length + 7) +
        (n5 + (1 + (1 + (1 + 1)))))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
      (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 e9)))))))
  refine ⟨s9, _, eall, ?_, hs9src, hs9dst, hframe⟩
  simp only [List.length_map, List.length_reverse, List.length_nil] at hn1 hn5 ⊢
  omega

/-- Loop lemma. -/
theorem pwRaLoop (main : Cmd) (src dst sp ds : Stk)
    (h1 : src ≠ dst) (h2 : sp ≠ src) (h3 : sp ≠ dst) (h4 : ds ≠ src) (h5 : ds ≠ dst)
    (h6 : ds ≠ sp) :
    ∀ (suf : List Val), (∀ x ∈ suf, ∃ z : ℤ, x = Val.int z) →
    ∀ (pre : List Val) (below old : List Glyph) (s : State),
      s.stk src = (ofList suf).enc ++ Pw.gM :: below →
      s.stk dst = pwRaBlocks pre ++ Glyph.nil :: Pw.gM :: old →
      s.reg pwrC = Glyph.eos →
      ∃ s' n, Eval main (.loop pwrC Glyph.eos (pwRaBody src dst sp ds)) s s' n ∧
        n ≤ 40 * ((ofList suf).enc.length + 1) ∧
        s'.stk src = Pw.gM :: below ∧
        s'.stk dst = pwRaBlocks (pre ++ suf) ++ Glyph.nil :: Pw.gM :: old ∧
        s'.reg pwrC = Glyph.iend ∧
        (∀ j : Stk, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  intro suf
  induction suf with
  | nil =>
    intro _ pre below old s hsrc hdst hreg
    have hsrc' : s.stk src = Glyph.nil :: Pw.gM :: below := by
      rw [hsrc, enc_ofList_nil_eq]; rfl
    set s1 : State := State.tPop s src pwrC with hs1
    have e1 : Eval main (.pop src pwrC) s s1 1 := by rw [hs1]; exact eval_pop main src pwrC s
    have hs1src : s1.stk src = Pw.gM :: below := by
      rw [hs1, Pw.tPop_stk, if_pos rfl, hsrc']; rfl
    have hs1reg : s1.reg pwrC = Glyph.nil := by
      rw [hs1, Pw.tPop_reg, if_pos rfl, hsrc']; rfl
    have hs1dst : s1.stk dst = pwRaBlocks pre ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs1, Pw.tPop_stk, if_neg (Ne.symm h1)]; exact hdst
    have hne : s1.reg pwrC ≠ Glyph.cons := by rw [hs1reg]; decide
    set s2 : State := State.tSet s1 pwrC Glyph.iend with hs2
    have e3 : Eval main (.set pwrC Glyph.iend) s1 s2 1 := by
      rw [hs2]; exact eval_set main pwrC Glyph.iend s1
    have e2 : Eval main (.ite pwrC Glyph.cons
        (.seq (pwRaElem src dst sp ds) (.set pwrC Glyph.eos)) (.set pwrC Glyph.iend)) s1 s2 2 :=
      Eval.iteF hne e3
    have hbody : Eval main (pwRaBody src dst sp ds) s s2 3 := Eval.seq e1 e2
    have hs2reg : s2.reg pwrC = Glyph.iend := by rw [hs2, Pw.tSet_reg, if_pos rfl]
    have hstop : s2.reg pwrC ≠ Glyph.eos := by rw [hs2reg]; decide
    have hrec : Eval main (.loop pwrC Glyph.eos (pwRaBody src dst sp ds)) s2 s2 1 :=
      Eval.loopF hstop
    have hloop : Eval main (.loop pwrC Glyph.eos (pwRaBody src dst sp ds)) s s2 (3 + 1 + 1) :=
      Eval.loopT hreg hbody hrec
    have hs2src : s2.stk src = Pw.gM :: below := by rw [hs2, Pw.tSet_stk]; exact hs1src
    have hs2dst : s2.stk dst = pwRaBlocks (pre ++ ([] : List Val)) ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs2, Pw.tSet_stk, List.append_nil]; exact hs1dst
    have hs2frame : ∀ j : Stk, j ≠ src → j ≠ dst → s2.stk j = s.stk j := by
      intro j hj1 hj2
      rw [hs2, Pw.tSet_stk, hs1, Pw.tPop_stk, if_neg hj1]
    refine ⟨s2, 5, ?_, ?_, hs2src, hs2dst, hs2reg, hs2frame⟩
    · exact hloop
    · rw [enc_ofList_nil_eq]; norm_num
  | cons v vs ih =>
    intro hsuf pre below old s hsrc hdst hreg
    obtain ⟨z, rfl⟩ := hsuf v (by simp)
    have hvs : ∀ x ∈ vs, ∃ z : ℤ, x = Val.int z := fun x hx => hsuf x (by simp [hx])
    have hsrc1 : s.stk src =
        Glyph.cons :: ((Val.int z).enc ++ ((ofList vs).enc ++ Pw.gM :: below)) := by
      rw [hsrc, enc_ofList_cons_eq, pwRaBlock]
      simp [List.cons_append, List.append_assoc]
    set s1 : State := State.tPop s src pwrC with hs1
    have e1 : Eval main (.pop src pwrC) s s1 1 := by rw [hs1]; exact eval_pop main src pwrC s
    have hs1src : s1.stk src = (Val.int z).enc ++ ((ofList vs).enc ++ Pw.gM :: below) := by
      rw [hs1, Pw.tPop_stk, if_pos rfl, hsrc1]; rfl
    have hs1reg : s1.reg pwrC = Glyph.cons := by
      rw [hs1, Pw.tPop_reg, if_pos rfl, hsrc1]; rfl
    have hs1dst : s1.stk dst = pwRaBlocks pre ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs1, Pw.tPop_stk, if_neg (Ne.symm h1)]; exact hdst
    obtain ⟨s2, n2, e2, hn2, hs2src, hs2dst, hs2frame⟩ :=
      pwRaElemEvalAux main src dst sp ds h1 h2 h3 h4 h5 h6 z
        ((ofList vs).enc ++ Pw.gM :: below) s1 hs1src
    have hs2dst' : s2.stk dst = pwRaBlocks (pre ++ [Val.int z]) ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs2dst, hs1dst, pwRaBlocks_concat, List.append_assoc]
    set s3 : State := State.tSet s2 pwrC Glyph.eos with hs3
    have e3 : Eval main (.set pwrC Glyph.eos) s2 s3 1 := by
      rw [hs3]; exact eval_set main pwrC Glyph.eos s2
    have hs3reg : s3.reg pwrC = Glyph.eos := by rw [hs3, Pw.tSet_reg, if_pos rfl]
    have hs3src : s3.stk src = (ofList vs).enc ++ Pw.gM :: below := by
      rw [hs3, Pw.tSet_stk]; exact hs2src
    have hs3dst : s3.stk dst = pwRaBlocks (pre ++ [Val.int z]) ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs3, Pw.tSet_stk]; exact hs2dst'
    have ebranch : Eval main (.seq (pwRaElem src dst sp ds) (.set pwrC Glyph.eos)) s1 s3 (n2 + 1) :=
      Eval.seq e2 e3
    have eite : Eval main (.ite pwrC Glyph.cons
        (.seq (pwRaElem src dst sp ds) (.set pwrC Glyph.eos)) (.set pwrC Glyph.iend)) s1 s3
        (n2 + 1 + 1) := Eval.iteT hs1reg ebranch
    have ebody : Eval main (pwRaBody src dst sp ds) s s3 (1 + (n2 + 1 + 1)) := Eval.seq e1 eite
    obtain ⟨s4, n4, e4, hn4, hs4src, hs4dst, hs4reg, hs4frame⟩ :=
      ih hvs (pre ++ [Val.int z]) below old s3 hs3src hs3dst hs3reg
    have hcat : (pre ++ [Val.int z]) ++ vs = pre ++ (Val.int z :: vs) := List.append_assoc _ _ _
    have hdst4 : s4.stk dst = pwRaBlocks (pre ++ (Val.int z :: vs)) ++ Glyph.nil :: Pw.gM :: old := by
      rw [hs4dst, hcat]
    have hloop : Eval main (.loop pwrC Glyph.eos (pwRaBody src dst sp ds)) s s4
        ((1 + (n2 + 1 + 1)) + n4 + 1) := Eval.loopT hreg ebody e4
    have hframe : ∀ j : Stk, j ≠ src → j ≠ dst → s4.stk j = s.stk j := by
      intro j hj1 hj2
      rw [hs4frame j hj1 hj2, hs3, Pw.tSet_stk, hs2frame j hj1 hj2, hs1, Pw.tPop_stk, if_neg hj1]
    refine ⟨s4, (1 + (n2 + 1 + 1)) + n4 + 1, hloop, ?_, hs4src, hdst4, hs4reg, hframe⟩
    have hlen := enc_ofList_cons_length (Val.int z) vs
    have hb := enc_int_length z
    omega


/-- Reversal-accumulation: traverse the `cons`-list `ofList xs` sitting above the frame marker
`Work.Transform.Pw.gM` on stack `src`, and rebuild the *reversed* list `ofList xs.reverse` above a
fresh `gM` on stack `dst` (the fresh marker is pushed by the program, as in
`Work.Transform.Pw.copyMarked2_eval`).

Intended implementation, one element per iteration (the elements are integer values, so the leading
`cons` glyph is popped, `Work.Transform.Pw.storeMag src sp ds rA rB` pops the sign (onto `ds`) and
moves the bits of the element (most significant first) above a fresh `gM` onto `sp`, consuming the
element's encoding up to its `iend`; then on `dst` one pushes `iend`, moves the bits from `sp`, pops
the sign glyph from `ds` and pushes it, and finally pushes a `cons` glyph; `sp` is reset with
`Work.Transform.Pw.dropMarked`; `dst` must first receive a `nil` glyph, which terminates the encoding
of the reversed list).  The loop ends when the top of `src` is `nil`, which is then popped.

The cost is linear in `(ofList xs).enc.length`, and everything except `src` and `dst` (including the
scratch stacks `sp`, `ds`) is restored. -/
theorem pwRevAcc (src dst sp ds : HvdH.Stk) :
    src ≠ dst → sp ≠ src → sp ≠ dst → ds ≠ src → ds ≠ dst → ds ≠ sp →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (xs : List HvdH.Val) (below : List HvdH.Glyph) (s : HvdH.State),
      (∀ x ∈ xs, ∃ z : ℤ, x = HvdH.Val.int z) →
      s.stk src = (HvdH.ofList xs).enc ++ Work.Transform.Pw.gM :: below →
      ∃ s' n, HvdH.Eval main prog s s' n ∧
        n ≤ K * ((HvdH.ofList xs).enc.length + 1) ∧
        s'.stk src = Work.Transform.Pw.gM :: below ∧
        s'.stk dst = (HvdH.ofList xs.reverse).enc ++ Work.Transform.Pw.gM :: s.stk dst ∧
        (∀ j : HvdH.Stk, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  intro h1 h2 h3 h4 h5 h6
  refine ⟨pwRaProg src dst sp ds, 45, ?_⟩
  intro main xs below s hxs hsrc
  set t0 : State := State.tSet s pwrA Pw.gM with ht0
  have e0 : Eval main (.set pwrA Pw.gM) s t0 1 := by rw [ht0]; exact eval_set main pwrA Pw.gM s
  set t1 : State := State.tPush t0 dst pwrA with ht1
  have e1 : Eval main (.push dst pwrA) t0 t1 1 := by rw [ht1]; exact eval_push main dst pwrA t0
  set t2 : State := State.tSet t1 pwrA Glyph.nil with ht2
  have e2 : Eval main (.set pwrA Glyph.nil) t1 t2 1 := by
    rw [ht2]; exact eval_set main pwrA Glyph.nil t1
  set t3 : State := State.tPush t2 dst pwrA with ht3
  have e3 : Eval main (.push dst pwrA) t2 t3 1 := by rw [ht3]; exact eval_push main dst pwrA t2
  set t4 : State := State.tSet t3 pwrC Glyph.eos with ht4
  have e4 : Eval main (.set pwrC Glyph.eos) t3 t4 1 := by
    rw [ht4]; exact eval_set main pwrC Glyph.eos t3
  have ht1dst : t1.stk dst = Pw.gM :: s.stk dst := by
    rw [ht1, Pw.tPush_stk, if_pos rfl, ht0, Pw.tSet_reg, if_pos rfl, Pw.tSet_stk]
  have ht3dst : t3.stk dst = Glyph.nil :: t1.stk dst := by
    rw [ht3, Pw.tPush_stk, if_pos rfl, ht2, Pw.tSet_reg, if_pos rfl, Pw.tSet_stk]
  have ht4dst : t4.stk dst = Glyph.nil :: Pw.gM :: s.stk dst := by
    rw [ht4, Pw.tSet_stk, ht3dst, ht1dst]
  have hframe : ∀ j : Stk, j ≠ dst → t4.stk j = s.stk j := by
    intro j hj
    rw [ht4, Pw.tSet_stk, ht3, Pw.tPush_stk, if_neg hj, ht2, Pw.tSet_stk, ht1,
      Pw.tPush_stk, if_neg hj, ht0, Pw.tSet_stk]
  have ht4reg : t4.reg pwrC = Glyph.eos := by rw [ht4, Pw.tSet_reg, if_pos rfl]
  have hsrc4 : t4.stk src = (ofList xs).enc ++ Pw.gM :: below := by
    rw [hframe src h1]; exact hsrc
  have hdst4 : t4.stk dst = pwRaBlocks ([] : List Val) ++ Glyph.nil :: Pw.gM :: s.stk dst := by
    rw [ht4dst, pwRaBlocks_nil, List.nil_append]
  obtain ⟨s5, n5, e5, hn5, hs5src, hs5dst, -, hs5frame⟩ :=
    pwRaLoop main src dst sp ds h1 h2 h3 h4 h5 h6 xs hxs [] below (s.stk dst) t4 hsrc4 hdst4 ht4reg
  have hs5dst' : s5.stk dst = (ofList xs.reverse).enc ++ Pw.gM :: s.stk dst := by
    rw [hs5dst, List.nil_append]
    rw [show pwRaBlocks xs ++ (Glyph.nil :: Pw.gM :: s.stk dst)
        = (pwRaBlocks xs ++ [Glyph.nil]) ++ (Pw.gM :: s.stk dst) from (List.append_assoc (pwRaBlocks xs) [Glyph.nil] (Pw.gM :: s.stk dst)).symm,
      pwRaBlocks_append_nil]
  have hframe5 : ∀ j : Stk, j ≠ src → j ≠ dst → s5.stk j = s.stk j := by
    intro j hj1 hj2
    rw [hs5frame j hj1 hj2, hframe j hj2]
  have eall : Eval main (pwRaProg src dst sp ds) s s5 (1 + (1 + (1 + (1 + (1 + n5))))) :=
    Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))))
  refine ⟨s5, 1 + (1 + (1 + (1 + (1 + n5)))), eall, ?_, hs5src, hs5dst', hframe5⟩
  omega

end Work.Transform
