import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.intDivAPI
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.mulSArith
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.eval_mvRev
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.incBitsListAPI
import Submission.Work.IntLib.mvRevOntoTight
import Submission.Work.IntLib.cleanupSpec
import Submission.Work.IntLib.incBitsSpec

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.IntLib
open HvdH
open Work.IntLib.Div


/-! ## list facts -/

theorem app_sing_app {α : Type*} (a : List α) (x : α) (b : List α) :
    a ++ [x] ++ b = a ++ x :: b := by rw [List.append_assoc, List.singleton_append]

theorem bitsG_reverse (l : List Bool) : (bitsG l).reverse = bitsG l.reverse :=
  List.map_reverse.symm

theorem dropWhile_false_bitsG (l : List Bool) :
    (bitsG l).dropWhile (fun g => g = Glyph.bit false) =
      bitsG (l.dropWhile (fun b => b = false)) := by
  have hp : ((fun g => decide (g = Glyph.bit false)) ∘ Glyph.bit)
      = (fun b : Bool => decide (b = false)) := by
    funext b; cases b <;> rfl
  rw [bitsG, List.dropWhile_map, bitsG, hp]

theorem stripHigh_eq_dropWhile (l : List Bool) :
    (l.reverse.dropWhile (fun b => b = false)).reverse = MulS.stripHigh l := by
  rw [MulS.stripHigh]
  have hp : (fun b : Bool => decide (b = false)) = (fun b : Bool => !b) := by
    funext b; cases b <;> rfl
  rw [hp]

theorem emit_bits_reverse (l : List Bool) :
    ((bitsG l).reverse.dropWhile (fun g => g = Glyph.bit false)).reverse =
      bitsG (Computability.encodeNat (ofBits l)) := by
  rw [← List.map_reverse]
  rw [dropWhile_false_bitsG]
  rw [← List.map_reverse]
  rw [stripHigh_eq_dropWhile, MulS.stripHigh_eq_bits, ← encodeNat_eq_bits]

theorem ofBits_eq_zero_iff (l : List Bool) : ofBits l = 0 ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp [ofBits]
  | cons x xs ih =>
    rw [ofBits_cons]
    constructor
    · intro h
      have hx0 : x.toNat = 0 := by omega
      have hxs : ofBits xs = 0 := by omega
      intro b hb
      rcases List.mem_cons.mp hb with hbx | hb
      · rw [hbx]; cases x <;> simp_all
      · exact (ih.mp hxs) b hb
    · intro h
      have hx0 : x.toNat = 0 := by
        have := h x (by simp); cases x <;> simp_all
      have hxs : ofBits xs = 0 := ih.mpr (fun b hb => h b (List.mem_cons_of_mem x hb))
      rw [hxs]; omega

theorem padBits_zero (L : ℕ) : padBits 0 L = List.replicate L false := by
  simp [padBits, List.map_const']

theorem padBits_dropWhile_eq_nil_iff (n L : ℕ) (hn : n < 2 ^ L) :
    (padBits n L).dropWhile (fun b => b = false) = [] ↔ n = 0 := by
  rw [List.dropWhile_eq_nil_iff]
  constructor
  · intro h
    have h0 : ofBits (padBits n L) = 0 :=
      ofBits_eq_zero_iff _ |>.mpr (fun b hb => of_decide_eq_true (h b hb))
    rw [ofBits_padBits, Nat.mod_eq_of_lt hn] at h0
    exact h0
  · intro hn0
    subst hn0
    rw [padBits_zero]
    intro b hb
    rw [List.mem_replicate] at hb
    exact decide_eq_true_eq.mpr hb.2

/-! ## glyph facts -/

theorem bit_ne_gX (b : Bool) : Glyph.bit b ≠ gX := by intro h; cases h
theorem bit_ne_gQ (b : Bool) : Glyph.bit b ≠ gQ := by intro h; cases h
theorem bit_ne_gD (b : Bool) : Glyph.bit b ≠ gD := by intro h; cases h
theorem bit_ne_gR (b : Bool) : Glyph.bit b ≠ gR := by intro h; cases h
theorem bit_ne_gB (b : Bool) : Glyph.bit b ≠ gB := by intro h; cases h
theorem bit_ne_gP (b : Bool) : Glyph.bit b ≠ gP := by intro h; cases h
theorem bit_ne_gS (b : Bool) : Glyph.bit b ≠ gS := by intro h; cases h
theorem bit_ne_gC (b : Bool) : Glyph.bit b ≠ gC := by intro h; cases h
theorem bit_ne_gY (b : Bool) : Glyph.bit b ≠ gY := by intro h; cases h
theorem gX_ne_eos : gX ≠ Glyph.eos := by intro h; cases h
theorem gD_ne_eos : gD ≠ Glyph.eos := by intro h; cases h
theorem gQ_ne_eos : gQ ≠ Glyph.eos := by intro h; cases h
theorem gD_ne_gX : gD ≠ gX := by decide
theorem gQ_ne_gX : gQ ≠ gX := by decide
theorem stX_ne_zero : Div.stX ≠ 0 := by decide
theorem stX_ne_stQ : Div.stX ≠ Div.stQ := by decide
theorem stX_ne_stD : Div.stX ≠ Div.stD := by decide
theorem stX_ne_stR : Div.stX ≠ Div.stR := by decide
theorem stR_ne_stD : Div.stR ≠ Div.stD := by decide
theorem rgT_ne_rgV : rgT ≠ rgV := by decide
theorem rgW_ne_rgT : rgW ≠ rgT := by decide
theorem bit_ne_eos' (b : Bool) : Glyph.bit b ≠ Glyph.eos := by intro h; cases h

/-! ## register frame -/

def writesOnly (R : Reg → Prop) : Cmd → Prop
  | .skip => True
  | .pop _ r => R r
  | .peek _ r => R r
  | .push _ _ => True
  | .set r _ => R r
  | .mov d _ => R d
  | .seq a b => writesOnly R a ∧ writesOnly R b
  | .ite _ _ a b => writesOnly R a ∧ writesOnly R b
  | .loop _ _ b => writesOnly R b
  | .self => False

theorem Eval_reg_frame {main : Cmd} {p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) :
    ∀ {R : Reg → Prop}, writesOnly R p → ∀ r, ¬ R r → s'.reg r = s.reg r := by
  induction h with
  | skip => intro R hf r hr; rfl
  | pop k r' s =>
    intro R hf r hr
    simp only [writesOnly] at hf
    show Function.update s.reg r' ((s.stk k).headD .eos) r = s.reg r
    rw [Function.update_apply]
    by_cases h : r = r'
    · subst h; exact absurd hf hr
    · simp [h]
  | peek k r' s =>
    intro R hf r hr
    simp only [writesOnly] at hf
    show Function.update s.reg r' ((s.stk k).headD .eos) r = s.reg r
    rw [Function.update_apply]
    by_cases h : r = r'
    · subst h; exact absurd hf hr
    · simp [h]
  | push k r' s => intro R hf r hr; rfl
  | set r' c s =>
    intro R hf r hr
    simp only [writesOnly] at hf
    show Function.update s.reg r' c r = s.reg r
    rw [Function.update_apply]
    by_cases h : r = r'
    · subst h; exact absurd hf hr
    · simp [h]
  | mov d src s =>
    intro R hf r hr
    simp only [writesOnly] at hf
    show Function.update s.reg d (s.reg src) r = s.reg r
    rw [Function.update_apply]
    by_cases h : r = d
    · subst h; exact absurd hf hr
    · simp [h]
  | seq h1 h2 ih1 ih2 =>
    intro R hf r hr
    exact (ih2 (R := R) hf.2 r hr).trans (ih1 (R := R) hf.1 r hr)
  | iteT hrc hev ih => intro R hf r hr; exact ih (R := R) hf.1 r hr
  | iteF hrc hev ih => intro R hf r hr; exact ih (R := R) hf.2 r hr
  | loopF hrc => intro R hf r hr; rfl
  | loopT hrc hbody hloop ihbody ihloop =>
    intro R hf r hr
    exact (ihloop (R := R) hf r hr).trans (ihbody (R := R) hf r hr)
  | self hev ih => intro R hf r hr; exact hf.elim

def usesOnly (S : Stk → Prop) : Cmd → Prop
  | .skip => True
  | .pop k _ => S k
  | .peek k _ => S k
  | .push k _ => S k
  | .set _ _ => True
  | .mov _ _ => True
  | .seq a b => usesOnly S a ∧ usesOnly S b
  | .ite _ _ a b => usesOnly S a ∧ usesOnly S b
  | .loop _ _ b => usesOnly S b
  | .self => False

theorem Eval_stk_frame {main : Cmd} {p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) :
    ∀ {S : Stk → Prop}, usesOnly S p → ∀ k, ¬ S k → s'.stk k = s.stk k := by
  induction h with
  | skip => intro S hf k hk; rfl
  | pop k' r s =>
    intro S hf k hk
    simp only [usesOnly] at hf
    show Function.update s.stk k' (s.stk k').tail k = s.stk k
    rw [Function.update_apply]
    by_cases h : k = k'
    · subst h; exact absurd hf hk
    · simp [h]
  | peek k' r s => intro S hf k hk; rfl
  | push k' r s =>
    intro S hf k hk
    simp only [usesOnly] at hf
    show Function.update s.stk k' (s.reg r :: s.stk k') k = s.stk k
    rw [Function.update_apply]
    by_cases h : k = k'
    · subst h; exact absurd hf hk
    · simp [h]
  | set r c s => intro S hf k hk; rfl
  | mov d src s => intro S hf k hk; rfl
  | seq h1 h2 ih1 ih2 =>
    intro S hf k hk
    exact (ih2 (S := S) hf.2 k hk).trans (ih1 (S := S) hf.1 k hk)
  | iteT hrc hev ih => intro S hf k hk; exact ih (S := S) hf.1 k hk
  | iteF hrc hev ih => intro S hf k hk; exact ih (S := S) hf.2 k hk
  | loopF hrc => intro S hf k hk; rfl
  | loopT hrc hbody hloop ihbody ihloop =>
    intro S hf k hk
    exact (ihloop (S := S) hf k hk).trans (ihbody (S := S) hf k hk)
  | self hev ih => intro S hf k hk; exact hf.elim

theorem writesOnly_mkG (k : Stk) (m : Glyph) : writesOnly (fun r => r = rgT) (mkG k m) := by
  simp [writesOnly, mkG]

theorem writesOnly_mvRevOnto (k : Stk) (T : Glyph) (k' : Stk) (r : Reg) :
    writesOnly (fun r' => r' = r) (mvRevOnto k T k' r) := by
  simp [writesOnly, mvRevOnto, consume, consumeLoop, consumeStep]

/-! ## mvRev with a tight bound -/

theorem eval_mvRevTight (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (k' : HvdH.Stk)
    (T' : HvdH.Glyph) (r : HvdH.Reg) (l bk bk' : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ T) (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk')
    (hne : k ≠ k') :
    ∃ s' n, HvdH.Eval main (mvRev k T k' T' r) s s' n ∧ n ≤ 5 * l.length + 11 ∧
      s'.stk k = bk ∧ s'.stk k' = l.reverse ++ T' :: bk' ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  set s0 : State := (s.updReg r T').updStk k' (T' :: s.stk k') with hs0
  have h0k : s0.stk k = l ++ T :: bk := by
    rw [hs0, State.updStk_apply]
    rw [if_neg hne, State.updReg_stk]
    exact hk
  have h0k' : s0.stk k' = T' :: bk' := by
    rw [hs0, State.updStk_same, hk']
  obtain ⟨s1, n1, he1, hn1, h1k, h1k', h1fr⟩ :=
    mvRevOntoTight main k T k' r l bk (T' :: bk') s0 hT h0k h0k' hne
  have h1fr' : ∀ j, j ≠ k → j ≠ k' → s1.stk j = s.stk j := by
    intro j hj hjk
    rw [h1fr j hj hjk]
    show s0.stk j = s.stk j
    rw [hs0, State.updStk_apply]
    rw [if_neg hjk, State.updReg_stk]
  have e1 : Eval main (.set r T') s (s.updReg r T') 1 := Eval.set_eq (r := r) (s := s) (c := T')
  have e2 : Eval main (.push k' r) (s.updReg r T') s0 1 := by
    rw [hs0]
    have hr : (s.updReg r T').reg r = T' := by simp
    simpa [State.updStk] using
      (Eval.push_eq (main := main) (k := k') (r := r) (s := s.updReg r T') hr)
  have hev : Eval main (mvRev k T k' T' r) s s1 (1 + (1 + n1)) := by
    have h := Eval.seq e1 (Eval.seq e2 he1)
    simpa [mvRev, mvRevOnto] using h
  exact ⟨s1, 1 + (1 + n1), hev, by omega, h1k, h1k', h1fr'⟩

theorem eval_mkG' (main : HvdH.Cmd) (k : HvdH.Stk) (m : HvdH.Glyph) (S : HvdH.State) :
    Eval main (mkG k m) S ((S.updReg rgT m).updStk k (m :: S.stk k)) 2 := by
  have h1 : Eval main (.set rgT m) S (S.updReg rgT m) 1 := Eval.set rgT m S
  have h2 : Eval main (.push k rgT) (S.updReg rgT m)
      ((S.updReg rgT m).updStk k (m :: S.stk k)) 1 := by
    have hr : (S.updReg rgT m).reg rgT = m := by simp
    simpa [State.updStk] using
      (Eval.push_eq (main := main) (k := k) (r := rgT) (s := S.updReg rgT m) hr)
  have h := Eval.seq h1 h2
  simpa [mkG, State.updStk] using h

/-! ## `prep` -/

theorem eval_prep (main : HvdH.Cmd) (src : HvdH.Stk) (msrc : HvdH.Glyph) (l : List Bool)
    (bsrc bX : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ b : Bool, Glyph.bit b ≠ msrc) (hX : ∀ b : Bool, Glyph.bit b ≠ gX)
    (hne : src ≠ Div.stX) (hk : s.stk src = bitsG l ++ msrc :: bsrc)
    (hX' : s.stk Div.stX = [gX] ++ bX) :
    ∃ s' n, HvdH.Eval main (prep src msrc) s s' n ∧ n ≤ 7 * l.length + 20 ∧
      s'.stk src = msrc :: bsrc ∧
      s'.stk Div.stX = ((bitsG l).reverse).dropWhile (fun g => g = Glyph.bit false)
        ++ [gX] ++ bX ∧
      ∀ j : HvdH.Stk, j ≠ src → j ≠ Div.stX → s'.stk j = s.stk j := by
  have hTl : ∀ g ∈ bitsG l, g ≠ msrc := by
    intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg; exact hT b
  obtain ⟨s1, n1, he1, hn1, h1src, h1X, h1fr⟩ :=
    mvRevOntoTight main src msrc Div.stX rgT (bitsG l) bsrc ([gX] ++ bX) s hTl hk hX' hne
  have hX1 : s1.stk Div.stX = bitsG l.reverse ++ gX :: bX := by
    rw [h1X, bitsG_reverse]
    rfl
  obtain ⟨s2, n2, he2, hn2, h2X, h2fr⟩ :=
    eval_stripZeros main Div.stX gX rgT l.reverse bX s1 gX_ne_eos hX hX1
  set s3 : State := (s2.updReg rgT msrc).updStk src (msrc :: s2.stk src) with hs3
  have h2src : s2.stk src = bsrc := by rw [h2fr src hne]; exact h1src
  have e3 : Eval main (mkG src msrc) s2 s3 2 := by rw [hs3]; exact eval_mkG' main src msrc s2
  have h3src : s3.stk src = msrc :: bsrc := by
    rw [hs3, State.updStk_same, h2src]
  have h3X : s3.stk Div.stX = ((bitsG l).reverse).dropWhile (fun g => g = Glyph.bit false)
      ++ [gX] ++ bX := by
    rw [hs3, State.updStk_apply]
    rw [if_neg (Ne.symm hne), State.updReg_stk]
    rw [h2X, bitsG_reverse, app_sing_app]
  have h3fr : ∀ j : HvdH.Stk, j ≠ src → j ≠ Div.stX → s3.stk j = s.stk j := by
    intro j hj hjk
    rw [hs3, State.updStk_apply]
    rw [if_neg hj, State.updReg_stk]
    rw [h2fr j hjk, h1fr j hj hjk]
  have hev : Eval main (prep src msrc) s s3 (n1 + (n2 + (2 + 1))) := by
    have h := eval_seqs_cons he1 (eval_seqs_cons he2 (eval_seqs_cons e3
      (by rw [seqs_nil]; exact Eval.skip s3)))
    simpa [prep] using h
  refine ⟨s3, n1 + (n2 + (2 + 1)), hev, ?_, h3src, h3X, h3fr⟩
  have hbg : (bitsG l).length = l.length := by simp [bitsG]
  have hrl : l.reverse.length = l.length := List.length_reverse
  omega

/-! ## `emit` -/

theorem eval_emit (main : HvdH.Cmd) (sg : HvdH.Reg) (A : List HvdH.Glyph) (Z bX : List HvdH.Glyph)
    (s : HvdH.State) (hT : ∀ g ∈ A, g ≠ gX) (hX : s.stk Div.stX = A ++ [gX] ++ bX)
    (h0 : s.stk 0 = Z) (hne : Div.stX ≠ 0) (hsg : sg ≠ rgT) :
    ∃ s' n, HvdH.Eval main (emit sg) s s' n ∧ n ≤ 5 * A.length + 17 ∧
      s'.stk 0 = s.reg sg :: A.reverse ++ [Glyph.iend] ++ Z ∧
      s'.stk Div.stX = [gX] ++ bX ∧
      ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stX → s'.stk j = s.stk j := by
  set s1 : State := s.updReg rgT Glyph.iend with hs1
  have e1 : Eval main (.set rgT Glyph.iend) s s1 1 := by
    rw [hs1]; exact Eval.set_eq (r := rgT) (s := s) (c := Glyph.iend)
  set s2 : State := s1.updStk 0 (Glyph.iend :: s1.stk 0) with hs2
  have hr1 : s1.reg rgT = Glyph.iend := by rw [hs1]; simp
  have e2 : Eval main (.push 0 rgT) s1 s2 1 := by
    rw [hs2]
    simpa [State.updStk] using
      (Eval.push_eq (main := main) (k := 0) (r := rgT) (s := s1) hr1)
  have hX2 : s2.stk Div.stX = A ++ gX :: bX := by
    rw [hs2, State.updStk_apply]
    rw [if_neg stX_ne_zero, State.updReg_stk, hX, app_sing_app]
  have h02 : s2.stk 0 = Glyph.iend :: Z := by
    rw [hs2, State.updStk_same, hs1, State.updReg_stk, h0]
  obtain ⟨s3, n3, he3, hn3, h3X, h30, h3fr⟩ :=
    mvRevOntoTight main Div.stX gX 0 rgT A bX (Glyph.iend :: Z) s2 hT hX2 h02 hne
  set s4 : State := (s3.updReg rgT gX).updStk Div.stX (gX :: s3.stk Div.stX) with hs4
  have e4 : Eval main (mkG Div.stX gX) s3 s4 2 := by rw [hs4]; exact eval_mkG' main Div.stX gX s3
  have h4X : s4.stk Div.stX = [gX] ++ bX := by
    rw [hs4, State.updStk_same, h3X]
    rfl
  have hEval4 : Eval main (Cmd.seq (.set rgT Glyph.iend)
      (Cmd.seq (.push 0 rgT) (Cmd.seq (mvRevOnto Div.stX gX 0 rgT) (mkG Div.stX gX))))
      s s4 (1 + (1 + (n3 + 2))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq he3 e4))
  have hf4 : writesOnly (fun r => r = rgT) (Cmd.seq (.set rgT Glyph.iend)
      (Cmd.seq (.push 0 rgT) (Cmd.seq (mvRevOnto Div.stX gX 0 rgT) (mkG Div.stX gX)))) := by
    simp [writesOnly, writesOnly_mvRevOnto, writesOnly_mkG]
  have h4reg : s4.reg sg = s.reg sg :=
    Eval_reg_frame hEval4 hf4 sg (by simpa using hsg)
  set s5 : State := s4.updReg rgT (s4.reg sg) with hs5
  have e5 : Eval main (.mov rgT sg) s4 s5 1 := by rw [hs5]; exact Eval.mov rgT sg s4
  have hr5 : s5.reg rgT = s.reg sg := by
    rw [hs5]; simp [h4reg]
  set s6 : State := s5.updStk 0 (s5.reg rgT :: s5.stk 0) with hs6
  have e6 : Eval main (.push 0 rgT) s5 s6 1 := by
    rw [hs6, hr5]
    simpa [State.updStk] using
      (Eval.push_eq (main := main) (k := 0) (r := rgT) (s := s5) hr5)
  have h60 : s6.stk 0 = s.reg sg :: A.reverse ++ [Glyph.iend] ++ Z := by
    rw [hs6, State.updStk_same, hr5]
    congr 1
    rw [hs5, State.updReg_stk]
    show s4.stk 0 = A.reverse ++ [Glyph.iend] ++ Z
    rw [hs4, State.updStk_apply]
    rw [if_neg (Ne.symm stX_ne_zero), State.updReg_stk, h30, app_sing_app]
  have h6X : s6.stk Div.stX = [gX] ++ bX := by
    rw [hs6, State.updStk_apply]
    rw [if_neg stX_ne_zero, hs5, State.updReg_stk]
    exact h4X
  have h6fr : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stX → s6.stk j = s.stk j := by
    intro j hj hjk
    rw [hs6, State.updStk_apply]
    rw [if_neg hj, hs5, State.updReg_stk]
    have h4j : s4.stk j = s.stk j := by
      rw [hs4, State.updStk_apply]
      rw [if_neg hjk, State.updReg_stk]
      rw [h3fr j hjk hj]
      show s2.stk j = s.stk j
      rw [hs2, State.updStk_apply]
      rw [if_neg hj, hs1, State.updReg_stk]
    exact h4j
  have hev : Eval main (emit sg) s s6 (1 + (1 + (n3 + (2 + (1 + (1 + 1)))))) := by
    have h := eval_seqs_cons e1 (eval_seqs_cons e2 (eval_seqs_cons he3 (eval_seqs_cons e4
      (eval_seqs_cons e5 (eval_seqs_cons e6 (by rw [seqs_nil]; exact Eval.skip s6))))))
    simpa [emit] using h
  exact ⟨s6, 1 + (1 + (n3 + (2 + (1 + (1 + 1))))), hev, by omega, h60, h6X, h6fr⟩

theorem bitsG_ne_marker (l : List Bool) (m : Glyph) (h : ∀ b : Bool, Glyph.bit b ≠ m) :
    ∀ g ∈ bitsG l, g ≠ m := by
  intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg; exact h b

theorem headD_append_of_ne (l m : List Glyph) (d : Glyph) (h : l ≠ []) :
    (l ++ m).headD d = l.headD d := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-! ## The shared negative tail: restore the remainder, prep+emit the quotient, clean up -/

theorem fdiv_neg_tail (main : HvdH.Cmd) (b0 : HvdH.State) (Z : List HvdH.Glyph) (u : HvdH.State)
    (bv rv qv L j : ℕ) (Br : List HvdH.Glyph) (A' : List Bool)
    (hBrD : ∀ g ∈ Br, g ≠ gD) (hBrR : ∀ g ∈ Br, g ≠ gR)
    (hlenBr : Br.length ≤ L) (hlenA : A'.length ≤ j + 1)
    (h0 : u.stk 0 = Z)
    (hP : u.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : u.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB)
    (hR : u.stk Div.stR = b0.stk Div.stR)
    (hQ : u.stk Div.stQ = bitsG A' ++ gQ :: b0.stk Div.stQ)
    (hS5 : u.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : u.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : u.stk Div.stD = Br ++ gD :: b0.stk Div.stD)
    (hS8 : u.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hS9 : u.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → u.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main (seqs [mvRev Div.stD gD Div.stR gR rgT, mkG Div.stD gD,
        prep Div.stQ gQ, .set rgW Glyph.neg, emit rgW, cleanup]) u s' n ∧
      n ≤ 15 * L + 12 * j + 185 ∧
      s'.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat (Work.IntLib.ofBits A')) ++
        [Glyph.iend] ++ Z ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k := by
  obtain ⟨v1, n1, he1, hn1, h1D, h1R, h1fr⟩ :=
    eval_mvRevTight main Div.stD gD Div.stR gR rgT Br (b0.stk Div.stD) (b0.stk Div.stR) u
      hBrD hS7 hR (by decide)
  set v2 : State := (v1.updReg rgT gD).updStk Div.stD (gD :: v1.stk Div.stD) with hv2
  have e2 : Eval main (mkG Div.stD gD) v1 v2 2 := by rw [hv2]; exact eval_mkG' main Div.stD gD v1
  have h2D : v2.stk Div.stD = gD :: b0.stk Div.stD := by rw [hv2, State.updStk_same, h1D]
  have hX2 : v2.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    rw [hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stX = Div.stD)), State.updReg_stk]
    rw [h1fr Div.stX (by decide) (by decide), hS8]
  have hQ2 : v2.stk Div.stQ = bitsG A' ++ gQ :: b0.stk Div.stQ := by
    rw [hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stQ = Div.stD)), State.updReg_stk]
    rw [h1fr Div.stQ (by decide) (by decide), hQ]
  obtain ⟨v3, n3, he3, hn3, h3Q, h3X, h3fr⟩ :=
    eval_prep main Div.stQ gQ A' (b0.stk Div.stQ) (b0.stk Div.stX) v2
      bit_ne_gQ bit_ne_gX (by decide) hQ2 hX2
  set Aem : List HvdH.Glyph := ((bitsG A').reverse).dropWhile (fun g => g = Glyph.bit false)
    with hAem
  have hAemlen : Aem.length ≤ j + 1 := by
    rw [hAem]
    calc (((bitsG A').reverse).dropWhile (fun g => g = Glyph.bit false)).length
        ≤ ((bitsG A').reverse).length := List.length_dropWhile_le _ _
      _ = A'.length := by simp [bitsG]
      _ ≤ j + 1 := hlenA
  have hTem : ∀ g ∈ Aem, g ≠ gX := by
    intro g hg
    rw [hAem] at hg
    have hmem : g ∈ (bitsG A').reverse :=
      List.Sublist.mem hg (List.dropWhile_sublist (l := (bitsG A').reverse)
        (fun g => g = Glyph.bit false))
    rw [bitsG_reverse] at hmem
    exact bitsG_ne_marker A'.reverse gX bit_ne_gX g hmem
  set v4 : State := v3.updReg rgW Glyph.neg with hv4
  have e4 : Eval main (.set rgW Glyph.neg) v3 v4 1 := by
    rw [hv4]; exact Eval.set_eq (r := rgW) (s := v3) (c := Glyph.neg)
  have hr4 : v4.reg rgW = Glyph.neg := by rw [hv4]; simp
  have hX4 : v4.stk Div.stX = Aem ++ [gX] ++ b0.stk Div.stX := by
    rw [hv4, State.updReg_stk, h3X, hAem]
  have h04 : v4.stk 0 = Z := by
    rw [hv4, State.updReg_stk]
    rw [h3fr 0 (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ ((0 : HvdH.Stk) = Div.stD)), State.updReg_stk]
    rw [h1fr 0 (by decide) (by decide)]
    exact h0
  obtain ⟨v5, n5, he5, hn5, h50, h5X, h5fr⟩ :=
    eval_emit main rgW Aem Z (b0.stk Div.stX) v4 hTem hX4 h04 (by decide) (by decide)
  have hAemrev : Aem.reverse = bitsG (Computability.encodeNat (ofBits A')) := by
    rw [hAem]; exact emit_bits_reverse A'
  have h50' : v5.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat (ofBits A')) ++
      [Glyph.iend] ++ Z := by rw [h50, hr4, hAemrev]
  -- stack contents at v5
  have hP5 : v5.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [h5fr Div.stP (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stP (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stP = Div.stD)), State.updReg_stk,
      h1fr Div.stP (by decide) (by decide)]
    exact hP
  have hB5 : v5.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB := by
    rw [h5fr Div.stB (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stB (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stB = Div.stD)), State.updReg_stk,
      h1fr Div.stB (by decide) (by decide)]
    exact hB
  have hR5 : v5.stk Div.stR = Br.reverse ++ [gR] ++ b0.stk Div.stR := by
    rw [h5fr Div.stR (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stR (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stR = Div.stD)), State.updReg_stk, h1R, app_sing_app]
  have hQ5 : v5.stk Div.stQ = gQ :: b0.stk Div.stQ := by
    rw [h5fr Div.stQ (by decide) (by decide), hv4, State.updReg_stk,
      h3Q]
  have hS55 : v5.stk Div.stS = [gS] ++ b0.stk Div.stS := by
    rw [h5fr Div.stS (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stS (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stS = Div.stD)), State.updReg_stk,
      h1fr Div.stS (by decide) (by decide)]
    exact hS5
  have hS65 : v5.stk Div.stC = [gC] ++ b0.stk Div.stC := by
    rw [h5fr Div.stC (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stC (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stC = Div.stD)), State.updReg_stk,
      h1fr Div.stC (by decide) (by decide)]
    exact hS6
  have hS75 : v5.stk Div.stD = gD :: b0.stk Div.stD := by
    rw [h5fr Div.stD (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stD (by decide) (by decide), h2D]
  have hS85 : v5.stk Div.stX = [gX] ++ b0.stk Div.stX := h5X
  have hS95 : v5.stk Div.stY = [gY] ++ b0.stk Div.stY := by
    rw [h5fr Div.stY (by decide) (by decide), hv4, State.updReg_stk,
      h3fr Div.stY (by decide) (by decide), hv2, State.updStk_apply]
    rw [if_neg (by decide : ¬ (Div.stY = Div.stD)), State.updReg_stk,
      h1fr Div.stY (by decide) (by decide)]
    exact hS9
  have hoth5 : ∀ k : HvdH.Stk, 10 ≤ k.val → v5.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hkX : k ≠ Div.stX := by rintro rfl; simp at hk
    have hkD : k ≠ Div.stD := by rintro rfl; simp at hk
    have hkQ : k ≠ Div.stQ := by rintro rfl; simp at hk
    have hkR : k ≠ Div.stR := by rintro rfl; simp at hk
    rw [h5fr k hk0 hkX, hv4, State.updReg_stk, h3fr k hkQ hkX, hv2,
      State.updStk_apply, if_neg hkD, State.updReg_stk, h1fr k hkD hkR]
    exact hoth k hk
  obtain ⟨v6, n6, he6, hn6, hfr6⟩ :=
    cleanupSpec main b0 v5 [] (bitsG (padBits bv L)) Br.reverse [] [] [] [] [] []
      hP5 hB5 hR5 hQ5 hS55 hS65 hS75 hS85 hS95
      (by intro g hg; simp at hg) (bitsG_ne_marker _ gB bit_ne_gB)
      (by intro g hg; rw [List.mem_reverse] at hg; exact hBrR g hg)
      (by intro g hg; simp at hg) (by intro g hg; simp at hg) (by intro g hg; simp at hg)
      (by intro g hg; simp at hg) (by intro g hg; simp at hg) (by intro g hg; simp at hg)
      hoth5
  have hev : Eval main (seqs [mvRev Div.stD gD Div.stR gR rgT, mkG Div.stD gD,
      prep Div.stQ gQ, .set rgW Glyph.neg, emit rgW, cleanup]) u v6
      (n1 + (2 + (n3 + (1 + (n5 + (n6 + 1)))))) := by
    have h := eval_seqs_cons he1 (eval_seqs_cons e2 (eval_seqs_cons he3 (eval_seqs_cons e4
      (eval_seqs_cons he5 (eval_seqs_cons he6 (by rw [seqs_nil]; exact Eval.skip v6))))))
    simpa using h
  have hf6 : usesOnly (fun k : HvdH.Stk => k ≠ 0) cleanup := by
    simp (config := {decide := true}) [usesOnly, cleanup, dropRgn, consume, consumeLoop,
      consumeStep, seqs]
  have h60 : v6.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat (ofBits A')) ++
      [Glyph.iend] ++ Z := by
    rw [Eval_stk_frame he6 hf6 0 (by decide)]
    exact h50'
  refine ⟨v6, n1 + (2 + (n3 + (1 + (n5 + (n6 + 1))))), hev, ?_, h60, hfr6⟩
  have hn6' : n6 ≤ 10 * L + 117 := by
    have hsum : ([] : List Glyph).length + (bitsG (padBits bv L)).length +
        (Br.reverse).length + ([] : List Glyph).length + ([] : List Glyph).length +
        ([] : List Glyph).length + ([] : List Glyph).length + ([] : List Glyph).length +
        ([] : List Glyph).length ≤ 2 * L := by
      have hb : (bitsG (padBits bv L)).length = L := by simp [bitsG, padBits_length]
      have hr : (Br.reverse).length = Br.length := List.length_reverse
      simp only [List.length_nil, List.length_reverse, hb]
      omega
    omega
  omega

/-! ## The negative branch of `fixFdiv` -/

def negBranch : Cmd := seqs [mvRevOnto Div.stR gR Div.stD rgT, stripZeros Div.stD gD rgT,
  .peek Div.stD rgV, .ite rgV gD .skip (incBits Div.stQ gQ Div.stX gX rgT rgV),
  mvRev Div.stD gD Div.stR gR rgT, mkG Div.stD gD, prep Div.stQ gQ, .set rgW Glyph.neg,
  emit rgW, cleanup]

def posBranch : Cmd := seqs [prep Div.stQ gQ, .set rgW Glyph.pos, emit rgW, cleanup]

theorem fixFdiv_eq : Div.fixFdiv = seqs [readSigns, .ite rgU Glyph.neg negBranch posBranch] := rfl

theorem fdiv_neg_branch (main : HvdH.Cmd) (b0 : HvdH.State) (Z : List HvdH.Glyph)
    (t : HvdH.State) (bv rv qv L j : ℕ) (hrvL : rv < 2 ^ L) (hqvj : qv < 2 ^ j)
    (h0 : t.stk 0 = Z)
    (hP : t.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : t.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB)
    (hR : t.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : t.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : t.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : t.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : t.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : t.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hS9 : t.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → t.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main negBranch t s' n ∧ n ≤ 22 * L + 32 * j + 270 ∧
      s'.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat (qv + (if rv = 0 then 0 else 1))) ++
        [Glyph.iend] ++ Z ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k := by
  set Ar : List Bool := padBits rv L with hAr
  set Aq : List Bool := padBits qv j with hAq
  have hR' : t.stk Div.stR = bitsG Ar ++ gR :: b0.stk Div.stR := by
    simpa [app_sing_app] using hR
  obtain ⟨t1, n1, he1, hn1, h1R, h1D, h1fr⟩ :=
    mvRevOntoTight main Div.stR gR Div.stD rgT (bitsG Ar) (b0.stk Div.stR)
      (gD :: b0.stk Div.stD) t (bitsG_ne_marker Ar gR bit_ne_gR) hR' hS7 (by decide)
  have hD1 : t1.stk Div.stD = bitsG Ar.reverse ++ gD :: b0.stk Div.stD := by
    rw [h1D, bitsG_reverse]
  obtain ⟨t2, n2, he2, hn2, h2D, h2fr⟩ :=
    eval_stripZeros main Div.stD gD rgT Ar.reverse (b0.stk Div.stD) t1 gD_ne_eos bit_ne_gD hD1
  set Br : List HvdH.Glyph := (bitsG Ar.reverse).dropWhile (fun g => g = Glyph.bit false) with hBr
  have h2D' : t2.stk Div.stD = Br ++ gD :: b0.stk Div.stD := by rw [h2D, hBr]
  set t3 : State := t2.updReg rgV ((t2.stk Div.stD).headD Glyph.eos) with ht3
  have he3 : Eval main (.peek Div.stD rgV) t2 t3 1 := by rw [ht3]; exact Eval.peek Div.stD rgV t2
  have hrgv : t3.reg rgV = (Br ++ gD :: b0.stk Div.stD).headD Glyph.eos := by
    rw [ht3]; simp [h2D']
  -- Br facts
  have hBr_eq : Br = bitsG (Ar.reverse.dropWhile (fun b => b = false)) := by
    rw [hBr]; exact dropWhile_false_bitsG Ar.reverse
  have hBrD : ∀ g ∈ Br, g ≠ gD := by
    intro g hg; rw [hBr] at hg
    exact bitsG_ne_marker Ar.reverse gD bit_ne_gD g
      (List.Sublist.mem hg (List.dropWhile_sublist (l := (bitsG Ar.reverse))
        (fun g => g = Glyph.bit false)))
  have hBrR : ∀ g ∈ Br, g ≠ gR := by
    intro g hg; rw [hBr] at hg
    exact bitsG_ne_marker Ar.reverse gR bit_ne_gR g
      (List.Sublist.mem hg (List.dropWhile_sublist (l := (bitsG Ar.reverse))
        (fun g => g = Glyph.bit false)))
  have hlenBr : Br.length ≤ L := by
    rw [hBr, hAr]
    calc (((bitsG (padBits rv L).reverse).dropWhile (fun g => g = Glyph.bit false)).length)
        ≤ ((bitsG (padBits rv L).reverse).length) := List.length_dropWhile_le _ _
      _ = (padBits rv L).length := by simp [bitsG]
      _ = L := padBits_length rv L
  have hBrnil : Br = [] ↔ rv = 0 := by
    rw [hBr_eq, List.map_eq_nil_iff, List.dropWhile_eq_nil_iff]
    constructor
    · intro h
      have h0' : ofBits Ar = 0 :=
        ofBits_eq_zero_iff _ |>.mpr (fun b hb =>
          of_decide_eq_true (h b (by rw [List.mem_reverse]; exact hb)))
      rw [hAr, ofBits_padBits, Nat.mod_eq_of_lt hrvL] at h0'
      exact h0'
    · intro h0' b hb
      rw [hAr, h0', padBits_zero, List.mem_reverse, List.mem_replicate] at hb
      exact decide_eq_true_eq.mpr hb.2
  have hBrbits : Br ≠ [] → ∃ b : Bool, Br.headD Glyph.eos = Glyph.bit b := by
    intro hne
    have heq := hBr_eq
    rw [heq] at hne ⊢
    have hm : Ar.reverse.dropWhile (fun b => b = false) ≠ [] := by
      intro hnil; rw [hnil] at hne; simp at hne
    cases hm' : Ar.reverse.dropWhile (fun b => b = false) with
    | nil => exact absurd hm' hm
    | cons b bs => exact ⟨b, rfl⟩
  -- frames at t3
  have hfr32 : ∀ k : HvdH.Stk, k ≠ Div.stD → t3.stk k = t1.stk k := by
    intro k hk; rw [ht3, State.updReg_stk, h2fr k hk]
  have hfr31 : ∀ k : HvdH.Stk, k ≠ Div.stR → k ≠ Div.stD → t3.stk k = t.stk k := by
    intro k hk hkD; rw [hfr32 k hkD, h1fr k hk hkD]
  have hQ3 : t3.stk Div.stQ = bitsG Aq ++ gQ :: b0.stk Div.stQ := by
    rw [hfr31 Div.stQ (by decide) (by decide), hAq]
    simpa [app_sing_app] using hQ
  have hR3 : t3.stk Div.stR = b0.stk Div.stR := by rw [hfr32 Div.stR (by decide)]; exact h1R
  have hoth3 : ∀ k : HvdH.Stk, 10 ≤ k.val → t3.stk k = b0.stk k := by
    intro k hk
    have hkR : k ≠ Div.stR := by rintro rfl; simp at hk
    have hkD : k ≠ Div.stD := by rintro rfl; simp at hk
    rw [hfr31 k hkR hkD]; exact hoth k hk
  have hlenAq : Aq.length ≤ j + 1 := by rw [hAq, padBits_length]; omega
  have hofAq : ofBits Aq = qv := by
    rw [hAq, ofBits_padBits, Nat.mod_eq_of_lt hqvj]
  rcases eq_or_ne rv 0 with hrv0 | hrvne
  · have hBr0 : Br = [] := hBrnil.mpr hrv0
    have hhead : (Br ++ gD :: b0.stk Div.stD).headD Glyph.eos = gD := by rw [hBr0]; rfl
    have hrgv' : t3.reg rgV = gD := by rw [hrgv, hhead]
    have he4 : Eval main (.ite rgV gD .skip (incBits Div.stQ gQ Div.stX gX rgT rgV))
        t3 t3 2 := Eval.iteT hrgv' (Eval.skip t3)
    obtain ⟨s', n5, he5, hn5, h5val, h5fr⟩ :=
      fdiv_neg_tail main b0 Z t3 bv rv qv L j Br Aq hBrD hBrR hlenBr hlenAq
        (by rw [hfr31 0 (by decide) (by decide)]; exact h0)
        (by rw [hfr31 Div.stP (by decide) (by decide)]; exact hP)
        (by rw [hfr31 Div.stB (by decide) (by decide)]; exact hB)
        hR3 hQ3
        (by rw [hfr31 Div.stS (by decide) (by decide)]; exact hS5)
        (by rw [hfr31 Div.stC (by decide) (by decide)]; exact hS6)
        (by rw [ht3, State.updReg_stk]; exact h2D')
        (by rw [hfr31 Div.stX (by decide) (by decide)]; exact hS8)
        (by rw [hfr31 Div.stY (by decide) (by decide)]; exact hS9)
        hoth3
    have hval : s'.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat
        (qv + (if rv = 0 then 0 else 1))) ++ [Glyph.iend] ++ Z := by
      rw [h5val, hofAq, if_pos hrv0, Nat.add_zero]
    have hev : Eval main negBranch t s' (n1 + (n2 + (1 + (2 + n5)))) := by
      have h := eval_seqs_cons he1 (eval_seqs_cons he2 (eval_seqs_cons he3 (eval_seqs_cons he4 he5)))
      simpa [negBranch] using h
    refine ⟨s', _, hev, ?_, hval, h5fr⟩
    have hArlen : (bitsG Ar).length = L := by rw [hAr]; simp [bitsG, padBits_length]
    have hrl : Ar.reverse.length = L := by rw [hAr, List.length_reverse]; exact padBits_length rv L
    omega
  · have hBrne : Br ≠ [] := fun h => hrvne (hBrnil.mp h)
    obtain ⟨b, hb⟩ := hBrbits hBrne
    have hhead : (Br ++ gD :: b0.stk Div.stD).headD Glyph.eos = Glyph.bit b := by
      rw [headD_append_of_ne Br _ _ hBrne, hb]
    have hrgv' : t3.reg rgV ≠ gD := by rw [hrgv, hhead]; exact bit_ne_gD b
    have hS83 : t3.stk Div.stX = [gX] ++ b0.stk Div.stX := by
      rw [hfr31 Div.stX (by decide) (by decide)]; exact hS8
    obtain ⟨t4, n4, he4b, hn4, h4Q, h4X, h4fr⟩ :=
      incBitsSpec main Div.stQ gQ Div.stX gX rgT rgV Aq (b0.stk Div.stQ)
        ([gX] ++ b0.stk Div.stX) t3 bit_ne_gQ bit_ne_gX rgT_ne_rgV hQ3 rfl hS83 (by decide)
    have he4 : Eval main (.ite rgV gD .skip (incBits Div.stQ gQ Div.stX gX rgT rgV))
        t3 t4 (n4 + 1) := Eval.iteF hrgv' he4b
    have hlenA' : (incBitsList Aq).length ≤ j + 1 := by
      have := length_incBitsList Aq
      have h2 : Aq.length = j := by rw [hAq, padBits_length]
      omega
    have hofA' : ofBits (incBitsList Aq) = qv + 1 := by
      rw [ofBits_incBitsList, hofAq]
    have hfr43 : ∀ k : HvdH.Stk, k ≠ Div.stQ → k ≠ Div.stX → t4.stk k = t3.stk k := h4fr
    obtain ⟨s', n5, he5, hn5, h5val, h5fr⟩ :=
      fdiv_neg_tail main b0 Z t4 bv rv qv L j Br (incBitsList Aq) hBrD hBrR hlenBr hlenA'
        (by rw [hfr43 0 (by decide) (by decide), hfr31 0 (by decide) (by decide)]; exact h0)
        (by rw [hfr43 Div.stP (by decide) (by decide), hfr31 Div.stP (by decide) (by decide)]; exact hP)
        (by rw [hfr43 Div.stB (by decide) (by decide), hfr31 Div.stB (by decide) (by decide)]; exact hB)
        (by rw [hfr43 Div.stR (by decide) (by decide), hfr32 Div.stR (by decide)]; exact h1R)
        h4Q
        (by rw [hfr43 Div.stS (by decide) (by decide), hfr31 Div.stS (by decide) (by decide)]; exact hS5)
        (by rw [hfr43 Div.stC (by decide) (by decide), hfr31 Div.stC (by decide) (by decide)]; exact hS6)
        (by rw [hfr43 Div.stD (by decide) (by decide), ht3, State.updReg_stk]; exact h2D')
        h4X
        (by rw [hfr43 Div.stY (by decide) (by decide), hfr31 Div.stY (by decide) (by decide)]; exact hS9)
        (by intro k hk
            have hkR : k ≠ Div.stR := by rintro rfl; simp at hk
            have hkD : k ≠ Div.stD := by rintro rfl; simp at hk
            have hkQ : k ≠ Div.stQ := by rintro rfl; simp at hk
            have hkX : k ≠ Div.stX := by rintro rfl; simp at hk
            rw [hfr43 k hkQ hkX, hfr31 k hkR hkD]; exact hoth k hk)
    have hval : s'.stk 0 = Glyph.neg :: bitsG (Computability.encodeNat
        (qv + (if rv = 0 then 0 else 1))) ++ [Glyph.iend] ++ Z := by
      rw [h5val, hofA', if_neg hrvne]
    have hev : Eval main negBranch t s' (n1 + (n2 + (1 + ((n4 + 1) + n5)))) := by
      have h := eval_seqs_cons he1 (eval_seqs_cons he2 (eval_seqs_cons he3 (eval_seqs_cons he4 he5)))
      simpa [negBranch] using h
    refine ⟨s', _, hev, ?_, hval, h5fr⟩
    have hArlen : (bitsG Ar).length = L := by rw [hAr]; simp [bitsG, padBits_length]
    have hrl : Ar.reverse.length = L := by rw [hAr, List.length_reverse]; exact padBits_length rv L
    have hAqj : Aq.length = j := by rw [hAq, padBits_length]
    have h4n : n4 ≤ 20 * (j + 1) + 40 := by rw [← hAqj]; exact hn4
    omega

theorem fdiv_pos_branch (main : HvdH.Cmd) (b0 : HvdH.State) (Z : List HvdH.Glyph)
    (t : HvdH.State) (bv rv qv L j : ℕ) (hqvj : qv < 2 ^ j)
    (h0 : t.stk 0 = Z)
    (hP : t.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : t.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB)
    (hR : t.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : t.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : t.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : t.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : t.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : t.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hS9 : t.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → t.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main posBranch t s' n ∧ n ≤ 10 * L + 12 * j + 165 ∧
      s'.stk 0 = Glyph.pos :: bitsG (Computability.encodeNat qv) ++ [Glyph.iend] ++ Z ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k := by
  have hQ' : t.stk Div.stQ = bitsG (padBits qv j) ++ gQ :: b0.stk Div.stQ := by
    simpa [app_sing_app] using hQ
  obtain ⟨v1, n1, he1, hn1, h1Q, h1X, h1fr⟩ :=
    eval_prep main Div.stQ gQ (padBits qv j) (b0.stk Div.stQ) (b0.stk Div.stX) t
      bit_ne_gQ bit_ne_gX (by decide) hQ' hS8
  set Aem : List HvdH.Glyph := ((bitsG (padBits qv j)).reverse).dropWhile
    (fun g => g = Glyph.bit false) with hAem
  have hAemlen : Aem.length ≤ j := by
    rw [hAem]
    calc (((bitsG (padBits qv j)).reverse).dropWhile (fun g => g = Glyph.bit false)).length
        ≤ ((bitsG (padBits qv j)).reverse).length := List.length_dropWhile_le _ _
      _ = (padBits qv j).length := by simp [bitsG]
      _ = j := padBits_length qv j
  have hTem : ∀ g ∈ Aem, g ≠ gX := by
    intro g hg
    rw [hAem] at hg
    have hmem : g ∈ (bitsG (padBits qv j)).reverse :=
      List.Sublist.mem hg (List.dropWhile_sublist (l := (bitsG (padBits qv j)).reverse)
        (fun g => g = Glyph.bit false))
    rw [bitsG_reverse] at hmem
    exact bitsG_ne_marker (padBits qv j).reverse gX bit_ne_gX g hmem
  set v2 : State := v1.updReg rgW Glyph.pos with hv2
  have e2 : Eval main (.set rgW Glyph.pos) v1 v2 1 := by
    rw [hv2]; exact Eval.set_eq (r := rgW) (s := v1) (c := Glyph.pos)
  have hr2 : v2.reg rgW = Glyph.pos := by rw [hv2]; simp
  have hX2 : v2.stk Div.stX = Aem ++ [gX] ++ b0.stk Div.stX := by
    rw [hv2, State.updReg_stk, h1X, hAem]
  have h02 : v2.stk 0 = Z := by
    rw [hv2, State.updReg_stk, h1fr 0 (by decide) (by decide)]; exact h0
  obtain ⟨v3, n3, he3, hn3, h30, h3X, h3fr⟩ :=
    eval_emit main rgW Aem Z (b0.stk Div.stX) v2 hTem hX2 h02 (by decide) (by decide)
  have hAemrev : Aem.reverse = bitsG (Computability.encodeNat (ofBits (padBits qv j))) := by
    rw [hAem]; exact emit_bits_reverse (padBits qv j)
  have h30' : v3.stk 0 = Glyph.pos :: bitsG (Computability.encodeNat qv) ++ [Glyph.iend] ++ Z := by
    rw [h30, hr2, hAemrev, ofBits_padBits, Nat.mod_eq_of_lt hqvj]
  -- cleanup
  have hP3 : v3.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [h3fr Div.stP (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stP (by decide) (by decide)]
    exact hP
  have hB3 : v3.stk Div.stB = bitsG (padBits bv L) ++ [gB] ++ b0.stk Div.stB := by
    rw [h3fr Div.stB (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stB (by decide) (by decide)]
    exact hB
  have hR3 : v3.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR := by
    rw [h3fr Div.stR (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stR (by decide) (by decide)]
    exact hR
  have hQ3 : v3.stk Div.stQ = gQ :: b0.stk Div.stQ := by
    rw [h3fr Div.stQ (by decide) (by decide), hv2, State.updReg_stk, h1Q]
  have hS53 : v3.stk Div.stS = [gS] ++ b0.stk Div.stS := by
    rw [h3fr Div.stS (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stS (by decide) (by decide)]
    exact hS5
  have hS63 : v3.stk Div.stC = [gC] ++ b0.stk Div.stC := by
    rw [h3fr Div.stC (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stC (by decide) (by decide)]
    exact hS6
  have hS73 : v3.stk Div.stD = [gD] ++ b0.stk Div.stD := by
    rw [h3fr Div.stD (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stD (by decide) (by decide)]
    exact hS7
  have hS83 : v3.stk Div.stX = [gX] ++ b0.stk Div.stX := h3X
  have hS93 : v3.stk Div.stY = [gY] ++ b0.stk Div.stY := by
    rw [h3fr Div.stY (by decide) (by decide), hv2, State.updReg_stk,
      h1fr Div.stY (by decide) (by decide)]
    exact hS9
  have hoth3 : ∀ k : HvdH.Stk, 10 ≤ k.val → v3.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hkX : k ≠ Div.stX := by rintro rfl; simp at hk
    rw [h3fr k hk0 hkX, hv2, State.updReg_stk, h1fr k (by rintro rfl; simp at hk)
      (by rintro rfl; simp at hk)]
    exact hoth k hk
  obtain ⟨v4, n4, he4, hn4, hfr4⟩ :=
    cleanupSpec main b0 v3 [] (bitsG (padBits bv L)) (bitsG (padBits rv L)) [] [] [] [] [] []
      hP3 hB3 hR3 hQ3 hS53 hS63 hS73 hS83 hS93
      (by intro g hg; simp at hg) (bitsG_ne_marker _ gB bit_ne_gB)
      (bitsG_ne_marker _ gR bit_ne_gR)
      (by intro g hg; simp at hg) (by intro g hg; simp at hg) (by intro g hg; simp at hg)
      (by intro g hg; simp at hg) (by intro g hg; simp at hg) (by intro g hg; simp at hg)
      hoth3
  have hf4 : usesOnly (fun k : HvdH.Stk => k ≠ 0) cleanup := by
    simp (config := {decide := true}) [usesOnly, cleanup, dropRgn, consume, consumeLoop,
      consumeStep, seqs]
  have h40 : v4.stk 0 = Glyph.pos :: bitsG (Computability.encodeNat qv) ++ [Glyph.iend] ++ Z := by
    rw [Eval_stk_frame he4 hf4 0 (by decide)]; exact h30'
  have hev : Eval main posBranch t v4 (n1 + (1 + (n3 + (n4 + 1)))) := by
    have h := eval_seqs_cons he1 (eval_seqs_cons e2 (eval_seqs_cons he3 (eval_seqs_cons he4
      (by rw [seqs_nil]; exact Eval.skip v4))))
    simpa [posBranch] using h
  refine ⟨v4, _, hev, ?_, h40, hfr4⟩
  have hlen1 : n1 ≤ 7 * (padBits qv j).length + 20 := hn1
  have hlen3 : n3 ≤ 5 * Aem.length + 17 := hn3
  have hlen4 : n4 ≤ 10 * L + 117 := by
    have hsum : ([] : List Glyph).length + (bitsG (padBits bv L)).length +
        (bitsG (padBits rv L)).length + ([] : List Glyph).length + ([] : List Glyph).length +
        ([] : List Glyph).length + ([] : List Glyph).length + ([] : List Glyph).length +
        ([] : List Glyph).length ≤ 2 * L := by
      simp only [List.length_nil]
      rw [show (bitsG (padBits bv L)).length = L from by simp [bitsG, padBits_length],
        show (bitsG (padBits rv L)).length = L from by simp [bitsG, padBits_length]]
      omega
    omega
  have h2 : (padBits qv j).length = j := padBits_length qv j
  omega

theorem div_fixFdiv (main : HvdH.Cmd) (b0 : HvdH.State) (a b : ℤ) (Z : List HvdH.Glyph)
    (S : HvdH.State) (hb : 0 < b) (L j : ℕ) (hL : L = b.natAbs.size + 1) (rv qv : ℕ)
    (hrv : rv = a.natAbs % b.natAbs) (hqv : qv = a.natAbs / b.natAbs) (hvj : qv + 1 < 2 ^ j)
    (h0 : S.stk 0 = Z)
    (hP : S.stk Work.IntLib.Div.stP = [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP)
    (hB : S.stk Work.IntLib.Div.stB = Work.IntLib.bitsG (Work.IntLib.padBits b.natAbs L) ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hR : S.stk Work.IntLib.Div.stR = Work.IntLib.bitsG (Work.IntLib.padBits rv L) ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hQ : S.stk Work.IntLib.Div.stQ = Work.IntLib.bitsG (Work.IntLib.padBits qv j) ++ [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ)
    (hS5 : S.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hS6 : S.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hS7 : S.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
    (hS8 : S.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hS9 : S.stk Work.IntLib.Div.stY =
      [if b < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos,
        if a < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos] ++ [Work.IntLib.gY] ++ b0.stk Work.IntLib.Div.stY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → S.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.fixFdiv S s' n ∧
      n ≤ 60 * (j + L + 2) + 60 ∧
      s'.stk 0 = (HvdH.Val.int (a.fdiv b)).enc ++ Z ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by

  have hbne : b ≠ 0 := ne_of_gt hb
  have hL2 : 2 ≤ L := by
    rw [hL]
    have hsz : 0 < b.natAbs.size := by
      rcases Nat.eq_zero_or_pos b.natAbs.size with h | h
      · rw [Nat.size_eq_zero] at h; omega
      · exact h
    omega
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h] at hvj; simp at hvj
    · exact h
  have hqvj : qv < 2 ^ j := by omega
  have hrvL : rv < 2 ^ L := by
    rw [hrv]
    have hm : a.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ (Int.natAbs_pos.mpr hbne)
    have hbp : b.natAbs < 2 ^ L := Nat.size_le.mp (by rw [hL]; omega)
    omega
  -- readSigns
  set S1 : State := (S.updReg rgT ((S.stk Div.stY).headD Glyph.eos)).updStk Div.stY
    ((S.stk Div.stY).tail) with hS1
  have ht1 : Eval main (.pop Div.stY rgT) S S1 1 := by rw [hS1]; exact Eval.pop Div.stY rgT S
  set t : State := (S1.updReg rgU ((S1.stk Div.stY).headD Glyph.eos)).updStk Div.stY
    ((S1.stk Div.stY).tail) with ht
  have ht2 : Eval main (.pop Div.stY rgU) S1 t 1 := by rw [ht]; exact Eval.pop Div.stY rgU S1
  have he_read : Eval main readSigns S t (1 + (1 + 1)) := by
    have h := Eval.seq ht1 (Eval.seq ht2 (Eval.skip t))
    simpa [readSigns, seqs] using h
  have hS1Y : S1.stk Div.stY = (S.stk Div.stY).tail := by rw [hS1]; simp
  have ht_stk : ∀ k : HvdH.Stk, k ≠ Div.stY → t.stk k = S.stk k := by
    intro k hk
    rw [ht]; simp only [State.updStk_apply]
    rw [if_neg hk, State.updReg_stk]
    rw [hS1]; simp only [State.updStk_apply]
    rw [if_neg hk, State.updReg_stk]
  have htY : t.stk Div.stY = [gY] ++ b0.stk Div.stY := by
    rw [ht]; simp only [State.updStk_same]
    rw [hS1Y, hS9]; rfl
  have htrgU : t.reg rgU = (if a < 0 then Glyph.neg else Glyph.pos) := by
    rw [ht, State.updStk_reg, State.updReg_apply, if_pos rfl, hS1Y, hS9]
    rfl
  have hoth_t : ∀ k : HvdH.Stk, 10 ≤ k.val → t.stk k = b0.stk k := by
    intro k hk
    rw [ht_stk k (by rintro rfl; simp at hk)]
    exact hoth k hk
  rcases lt_or_ge a 0 with ha | ha
  · -- negative
    have hrgU : t.reg rgU = Glyph.neg := by rw [htrgU, if_pos ha]
    obtain ⟨s', nb, heb, hcb, hvb, hfb⟩ :=
      fdiv_neg_branch main b0 Z t b.natAbs rv qv L j hrvL hqvj
        (ht_stk 0 (by decide) ▸ h0)
        (ht_stk Div.stP (by decide) ▸ hP)
        (by rw [ht_stk Div.stB (by decide)]; exact hB)
        (by rw [ht_stk Div.stR (by decide)]; exact hR)
        (by rw [ht_stk Div.stQ (by decide)]; exact hQ)
        (by rw [ht_stk Div.stS (by decide)]; exact hS5)
        (by rw [ht_stk Div.stC (by decide)]; exact hS6)
        (by rw [ht_stk Div.stD (by decide)]; exact hS7)
        (by rw [ht_stk Div.stX (by decide)]; exact hS8)
        htY hoth_t
    have he_ite : Eval main (.ite rgU Glyph.neg negBranch posBranch) t s' (nb + 1) :=
      Eval.iteT hrgU heb
    have hev : Eval main Div.fixFdiv S s' (3 + ((nb + 1) + 1)) := by
      have h := Eval.seq he_read (Eval.seq he_ite (Eval.skip s'))
      simpa [fixFdiv_eq] using h
    have hfdiv : a.fdiv b = -((qv : ℤ) + (if rv = 0 then (0 : ℤ) else 1)) := by
      have h1 := intDivAPI.2.2.1 a b hb
      rw [if_neg (by omega : ¬ (0 ≤ a))] at h1
      rw [h1, ← hqv, ← hrv]
    have hpos : 0 < qv + (if rv = 0 then 0 else 1) := by
      have hbase : b.natAbs * qv + rv = a.natAbs := by rw [hqv, hrv]; exact Nat.div_add_mod _ _
      have haneg : a.natAbs ≠ 0 := by intro h; rw [Int.natAbs_eq_zero] at h; omega
      by_cases hq : qv = 0
      · have hrvne : rv ≠ 0 := by
          intro hrv0
          have : a.natAbs = 0 := by rw [← hbase, hq, hrv0, Nat.mul_zero, Nat.zero_add]
          exact haneg this
        simp [hq, hrvne]
      · have hq1 : 1 ≤ qv := Nat.one_le_iff_ne_zero.mpr hq
        by_cases h : rv = 0 <;> simp [h] <;> omega
    have hnat : (-((qv : ℤ) + (if rv = 0 then (0 : ℤ) else 1))).natAbs
        = qv + (if rv = 0 then 0 else 1) := by
      have hcast : (↑(qv + (if rv = 0 then 0 else 1)) : ℤ)
          = (qv : ℤ) + (if rv = 0 then (0 : ℤ) else 1) := by
        by_cases h : rv = 0 <;> simp [h]
      rw [← hcast, Int.natAbs_neg, Int.natAbs_natCast]
    have hval : s'.stk 0 = (HvdH.Val.int (a.fdiv b)).enc ++ Z := by
      rw [hvb, hfdiv, enc_int]
      rw [if_pos (by omega : (-((qv : ℤ) + (if rv = 0 then (0:ℤ) else 1))) < 0), hnat]
      rw [List.cons_append]
    exact ⟨s', 3 + ((nb + 1) + 1), hev, by omega, hval, hfb⟩
  · -- positive
    have hrgU : t.reg rgU ≠ Glyph.neg := by
      rw [htrgU, if_neg (not_lt.mpr ha)]
      exact (by decide : Glyph.pos ≠ Glyph.neg)
    obtain ⟨s', nb, heb, hcb, hvb, hfb⟩ :=
      fdiv_pos_branch main b0 Z t b.natAbs rv qv L j hqvj
        (ht_stk 0 (by decide) ▸ h0)
        (by rw [ht_stk Div.stP (by decide)]; exact hP)
        (by rw [ht_stk Div.stB (by decide)]; exact hB)
        (by rw [ht_stk Div.stR (by decide)]; exact hR)
        (by rw [ht_stk Div.stQ (by decide)]; exact hQ)
        (by rw [ht_stk Div.stS (by decide)]; exact hS5)
        (by rw [ht_stk Div.stC (by decide)]; exact hS6)
        (by rw [ht_stk Div.stD (by decide)]; exact hS7)
        (by rw [ht_stk Div.stX (by decide)]; exact hS8)
        htY hoth_t
    have he_ite : Eval main (.ite rgU Glyph.neg negBranch posBranch) t s' (nb + 1) :=
      Eval.iteF hrgU heb
    have hev : Eval main Div.fixFdiv S s' (3 + ((nb + 1) + 1)) := by
      have h := Eval.seq he_read (Eval.seq he_ite (Eval.skip s'))
      simpa [fixFdiv_eq] using h
    have hfdiv : a.fdiv b = (qv : ℤ) := by
      have h1 := intDivAPI.2.2.1 a b hb
      rw [if_pos ha] at h1
      rw [h1, ← hqv]
    have hval : s'.stk 0 = (HvdH.Val.int (a.fdiv b)).enc ++ Z := by
      rw [hvb, hfdiv, enc_int]
      rw [if_neg (by omega : ¬ ((qv : ℤ) < 0)), Int.natAbs_natCast]
      rw [List.cons_append]
    exact ⟨s', 3 + ((nb + 1) + 1), hev, by omega, hval, hfb⟩

end Work.IntLib
