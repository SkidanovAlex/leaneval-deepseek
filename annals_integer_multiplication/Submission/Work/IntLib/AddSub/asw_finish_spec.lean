import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.mulSArith
import Submission.Work.IntLib.UR.Main
import Submission.Work.IntLib.AddSub.asw_stripLoop_tight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## Two list facts about `headD` of a reversed glyph-coded bit list -/

/-- If `e` is nonempty, the head of `(e.map bit).reverse ++ A` is a `bit` glyph, so it is not
any glyph `M` which is never a `bit` glyph. -/
theorem headD_map_rev_ne (M : HvdH.Glyph) (hM : ∀ b : Bool, M ≠ HvdH.Glyph.bit b) :
    ∀ (e : List Bool), e ≠ [] → ∀ (A : List HvdH.Glyph),
      ((e.map HvdH.Glyph.bit).reverse ++ A).headD HvdH.Glyph.eos ≠ M := by
  intro e
  induction e with
  | nil => intro h; exact absurd rfl h
  | cons b t ih =>
      intro _ A
      cases t with
      | nil =>
        have hA : ((b :: []).map HvdH.Glyph.bit).reverse ++ A = HvdH.Glyph.bit b :: A := by
          simp
        rw [hA, List.headD_cons]
        exact fun h => hM b h.symm
      | cons b' t' =>
        have hsplit : ((b :: b' :: t').map HvdH.Glyph.bit).reverse ++ A
            = ((b' :: t').map HvdH.Glyph.bit).reverse ++ (HvdH.Glyph.bit b :: A) := by
          simp only [List.map_cons, List.reverse_cons, List.singleton_append,
            List.cons_append, List.nil_append, List.append_assoc]
        rw [hsplit]
        exact ih (List.cons_ne_nil b' t') (HvdH.Glyph.bit b :: A)

/-- `headD` of `(e.map bit).reverse ++ M :: C` is the marker `M` exactly when `e` is empty. -/
theorem headD_map_rev_eq_iff (e : List Bool) (M : HvdH.Glyph) (C : List HvdH.Glyph)
    (hM : ∀ b : Bool, M ≠ HvdH.Glyph.bit b) :
    ((e.map HvdH.Glyph.bit).reverse ++ M :: C).headD HvdH.Glyph.eos = M ↔ e = [] := by
  constructor
  · intro h
    by_contra hne
    exact headD_map_rev_ne M hM e hne (M :: C) h
  · rintro rfl
    simp

/-- `gmk i` is never a `bit` glyph. -/
theorem gmk_ne_bit (i : HvdH.Stk) (b : Bool) : gmk i ≠ HvdH.Glyph.bit b := by
  intro h; cases h

/-! ## The tail of `asw_finish`

After `asw_stripLoop out` has removed the leading zero glyphs of the magnitude on `out`, the rest
of `asw_finish sg out` writes the `iend` terminator, reads the sign glyph off `sg`, replaces it by
`pos` if the magnitude is empty, drains the magnitude onto stack 0 and pushes the sign. -/

theorem asw_finish_tail {main : HvdH.Cmd} (sg out : HvdH.Stk) (hsg : sg ≠ out) (hout0 : out ≠ 0)
    (hsg0 : sg ≠ 0) :
    ∀ (e : List Bool) (sgg : HvdH.Glyph) (C D R : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X out = (e.map HvdH.Glyph.bit).reverse ++ gmk out :: C →
      X sg = sgg :: gmk sg :: D →
      X 0 = R →
      ∃ s' n, Ev main (seqs [.set rS .iend, .push 0 rS, .pop sg rU, .peek out rT,
          .ite rT (gmk out) (.set rU .pos) .skip, asw_drain out 0 (gmk out) rA rF, .push 0 rU])
          ⟨g, X⟩ s' n ∧
        n ≤ 5 * (e.length + 1) + 12 ∧
        s'.stk out = gmk out :: C ∧ s'.stk sg = gmk sg :: D ∧
        s'.stk 0 = (if e = [] then HvdH.Glyph.pos else sgg) ::
          (e.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) := by
  intro e sgg C D R g X hXout hXsg hX0
  -- after `set rS iend`
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g rS HvdH.Glyph.iend
  let X1 : HvdH.Stk → List HvdH.Glyph := X
  let s1 : State := ⟨g1, X1⟩
  have he1 : Ev main (.set rS HvdH.Glyph.iend) ⟨g, X⟩ s1 1 :=
    ev_set' main rS HvdH.Glyph.iend g X
  -- after `push 0 rS`
  let X2 : HvdH.Stk → List HvdH.Glyph := Function.update X1 0 (g1 rS :: X1 0)
  let s2 : State := ⟨g1, X2⟩
  have he2 : Ev main (.push 0 rS) s1 s2 1 := ev_push' main 0 rS g1 X1
  -- after `pop sg rU`
  let g3 : HvdH.Reg → HvdH.Glyph := Function.update g1 rU ((X2 sg).headD HvdH.Glyph.eos)
  let X3 : HvdH.Stk → List HvdH.Glyph := Function.update X2 sg (X2 sg).tail
  let s3 : State := ⟨g3, X3⟩
  have he3 : Ev main (.pop sg rU) s2 s3 1 := ev_pop' main sg rU g1 X2
  -- after `peek out rT`
  let g4 : HvdH.Reg → HvdH.Glyph := Function.update g3 rT ((X3 out).headD HvdH.Glyph.eos)
  let s4 : State := ⟨g4, X3⟩
  have he4 : Ev main (.peek out rT) s3 s4 1 := ev_peek' main out rT g3 X3
  -- contents of the working stacks
  have hg1 : g1 rS = HvdH.Glyph.iend := by simp [g1]
  have hX2_0 : X2 0 = HvdH.Glyph.iend :: R := by
    show (Function.update X 0 (g1 rS :: X 0)) 0 = HvdH.Glyph.iend :: R
    rw [upStk_same, hg1, hX0]
  have hX2_sg : X2 sg = sgg :: gmk sg :: D := by
    show (Function.update X 0 (g1 rS :: X 0)) sg = sgg :: gmk sg :: D
    rw [upStk_ne hsg0, hXsg]
  have hg3_rU : g3 rU = sgg := by
    show (Function.update g1 rU ((X2 sg).headD HvdH.Glyph.eos)) rU = sgg
    rw [upReg_same, hX2_sg, List.headD_cons]
  have hX3_out : X3 out = (e.map HvdH.Glyph.bit).reverse ++ gmk out :: C := by
    show (Function.update X2 sg (X2 sg).tail) out = (e.map HvdH.Glyph.bit).reverse ++ gmk out :: C
    rw [upStk_ne hsg.symm]
    show (Function.update X 0 (g1 rS :: X 0)) out = _
    rw [upStk_ne hout0, hXout]
  have hX3_0 : X3 0 = HvdH.Glyph.iend :: R := by
    show (Function.update X2 sg (X2 sg).tail) 0 = HvdH.Glyph.iend :: R
    rw [upStk_ne hsg0.symm, hX2_0]
  have hX3_sg : X3 sg = gmk sg :: D := by
    show (Function.update X2 sg (X2 sg).tail) sg = gmk sg :: D
    rw [upStk_same, hX2_sg]
    rfl
  -- the decision `ite rT (gmk out) (set rU pos) skip`
  have hite : ∃ g5 : HvdH.Reg → HvdH.Glyph,
      Ev main (.ite rT (gmk out) (.set rU .pos) .skip) s4 ⟨g5, X3⟩ 2 ∧
      g5 rU = (if e = [] then HvdH.Glyph.pos else sgg) := by
    rcases eq_or_ne e [] with rfl | hne
    · refine ⟨Function.update g4 rU HvdH.Glyph.pos, ?_, ?_⟩
      · refine Ev.iteT ?_ (ev_set' main rU HvdH.Glyph.pos g4 X3)
        show g4 rT = gmk out
        show (Function.update g3 rT ((X3 out).headD HvdH.Glyph.eos)) rT = gmk out
        rw [upReg_same, hX3_out]
        simp
      · simp
    · refine ⟨g4, ?_, ?_⟩
      · refine Ev.iteF ?_ (ev_skip' main g4 X3)
        show g4 rT ≠ gmk out
        show (Function.update g3 rT ((X3 out).headD HvdH.Glyph.eos)) rT ≠ gmk out
        rw [upReg_same, hX3_out]
        exact fun hc => headD_map_rev_ne (gmk out) (fun b => gmk_ne_bit out b) e hne
          (gmk out :: C) hc
      · show g4 rU = (if e = [] then HvdH.Glyph.pos else sgg)
        show (Function.update g3 rT ((X3 out).headD HvdH.Glyph.eos)) rU = _
        rw [upReg_ne (by decide : rU ≠ rT), hg3_rU]
        simp [hne]
  obtain ⟨g5, he5, hg5rU⟩ := hite
  let s5 : State := ⟨g5, X3⟩
  -- the drain
  have hGne : ∀ h ∈ (e.map HvdH.Glyph.bit).reverse, h ≠ gmk out := by
    intro h hh
    rw [List.mem_reverse] at hh
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hh
    intro hc
    cases hc
  obtain ⟨s6, nd, he6, hnd, hout6, h06, _⟩ :=
    asw_drain_ev (main := main) out 0 (gmk out) rA rF hout0 (by decide)
      ((e.map HvdH.Glyph.bit).reverse) C (HvdH.Glyph.iend :: R) g5 X3 hGne hX3_out hX3_0
  have h06' : s6.stk 0 = e.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: R := by
    rw [h06, List.reverse_reverse]
  have hk_sg : sg ∉ ({out, 0} : Finset HvdH.Stk) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hsg, hsg0⟩
  have hframe_drain : cmdTouches (asw_drain out 0 (gmk out) rA rF) ⊆
      ({out, 0} : Finset HvdH.Stk) := by
    intro j hj
    simp only [asw_drain, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert, Finset.notMem_empty] at hj ⊢
    tauto
  have hs6_sg : s6.stk sg = gmk sg :: D := by
    have hfr := Ev.frame he6 hframe_drain hk_sg
    rw [hfr]
    exact hX3_sg
  -- registers other than `rA`, `rF` survive the drain
  have hrU : rU ∉ UR.cmdWrites (asw_drain out 0 (gmk out) rA rF) := by
    simp only [UR.cmdWrites, asw_drain, seqs, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, not_or]
    repeat' first | apply And.intro | decide
  have hreg : s6.reg rU = g5 rU := by
    obtain ⟨m6, he6ev, _⟩ := he6
    exact UR.Eval_reg_frame he6ev hrU
  -- the final push
  let X7 : HvdH.Stk → List HvdH.Glyph := Function.update s6.stk 0 (s6.reg rU :: s6.stk 0)
  let s7 : State := ⟨s6.reg, X7⟩
  have he7 : Ev main (.push 0 rU) s6 s7 1 := ev_push' main 0 rU s6.reg s6.stk
  have hlen : (e.map HvdH.Glyph.bit).reverse.length = e.length := by simp
  have hX7_0 : s7.stk 0 = (if e = [] then HvdH.Glyph.pos else sgg) ::
      (e.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) := by
    show (Function.update s6.stk 0 (s6.reg rU :: s6.stk 0)) 0 = _
    rw [upStk_same, hreg, hg5rU, h06']
    simp
  have hout7 : s7.stk out = gmk out :: C := by
    show (Function.update s6.stk 0 (s6.reg rU :: s6.stk 0)) out = gmk out :: C
    rw [upStk_ne hout0]
    exact hout6
  have hsg7 : s7.stk sg = gmk sg :: D := by
    show (Function.update s6.stk 0 (s6.reg rU :: s6.stk 0)) sg = gmk sg :: D
    rw [upStk_ne hsg0]
    exact hs6_sg
  -- assemble the sequence
  have hc67 : Ev main (seqs [asw_drain out 0 (gmk out) rA rF, .push 0 rU]) s5 s7 (nd + 1) :=
    Ev.seqs_cons he6 he7
  have hc567 : Ev main (seqs [.ite rT (gmk out) (.set rU .pos) .skip,
      asw_drain out 0 (gmk out) rA rF, .push 0 rU]) s4 s7 (2 + (nd + 1)) :=
    Ev.seqs_cons he5 hc67
  have hc4567 : Ev main (seqs [.peek out rT, .ite rT (gmk out) (.set rU .pos) .skip,
      asw_drain out 0 (gmk out) rA rF, .push 0 rU]) s3 s7 (1 + (2 + (nd + 1))) :=
    Ev.seqs_cons he4 hc567
  have hc34567 : Ev main (seqs [.pop sg rU, .peek out rT, .ite rT (gmk out) (.set rU .pos) .skip,
      asw_drain out 0 (gmk out) rA rF, .push 0 rU]) s2 s7 (1 + (1 + (2 + (nd + 1)))) :=
    Ev.seqs_cons he3 hc4567
  have hc234567 : Ev main (seqs [.push 0 rS, .pop sg rU, .peek out rT,
      .ite rT (gmk out) (.set rU .pos) .skip, asw_drain out 0 (gmk out) rA rF,
      .push 0 rU]) s1 s7 (1 + (1 + (1 + (2 + (nd + 1))))) :=
    Ev.seqs_cons he2 hc34567
  have hall : Ev main (seqs [.set rS .iend, .push 0 rS, .pop sg rU, .peek out rT,
      .ite rT (gmk out) (.set rU .pos) .skip, asw_drain out 0 (gmk out) rA rF, .push 0 rU])
      ⟨g, X⟩ s7 (1 + (1 + (1 + (1 + (2 + (nd + 1)))))) :=
    Ev.seqs_cons he1 hc234567
  exact ⟨s7, 1 + (1 + (1 + (1 + (2 + (nd + 1))))), hall, by omega, hout7, hsg7, hX7_0⟩

/-! ## The specification of `asw_finish` -/

theorem asw_finish_spec {main : HvdH.Cmd} (sg out : HvdH.Stk) (hsg : sg ≠ out) (hout0 : out ≠ 0)
    (hsg0 : sg ≠ 0) :
    ∀ (em : List Bool) (sgg : HvdH.Glyph) (C D R : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X out = (em.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C →
      X sg = sgg :: Work.IntLib.AddSub.gmk sg :: D →
      X 0 = R → (sgg = HvdH.Glyph.pos ∨ sgg = HvdH.Glyph.neg) →
      ∃ s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_finish sg out) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (em.length + 1) + 60 ∧
        s'.stk out = Work.IntLib.AddSub.gmk out :: C ∧
        s'.stk sg = Work.IntLib.AddSub.gmk sg :: D ∧
        ∃ em' : List Bool, Work.IntLib.IsBits em' ∧
          Work.IntLib.ofBits em' = Work.IntLib.ofBits em ∧
          s'.stk 0 = (if em' = [] then HvdH.Glyph.pos else sgg) ::
            (em'.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) := by
  intro em sgg C D R g X hXout hXsg hX0 _
  -- Step 1: strip the leading zeros of the magnitude on `out`
  obtain ⟨kk, s1, n1, hev1, hn1, hlen1, hout1, _⟩ :=
    asw_stripLoop_tight (main := main) out em C g X hXout
  have hS1 : cmdTouches (asw_stripLoop out) ⊆ ({out} : Finset HvdH.Stk) := by
    intro j hj
    simp only [asw_stripLoop, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert, Finset.notMem_empty] at hj ⊢
    tauto
  have h01 : s1.stk 0 = R := by
    rw [← hX0]
    exact Ev.frame hev1 hS1 (k := 0) (by
      simp only [Finset.mem_singleton]
      exact fun h => hout0 h.symm)
  have hsg1 : s1.stk sg = sgg :: gmk sg :: D := by
    rw [← hXsg]
    exact Ev.frame hev1 hS1 (k := sg) (by
      simp only [Finset.mem_singleton]
      exact hsg)
  -- Step 2: the rest of the program
  obtain ⟨s2, n2, hev2, hn2, hout2, hsg2, h02⟩ :=
    asw_finish_tail (main := main) sg out hsg hout0 hsg0 (MulS.stripHigh em) sgg C D R
      s1.reg s1.stk hout1 hsg1 h01
  refine ⟨s2, n1 + n2, ?_, ?_, hout2, hsg2,
    ⟨MulS.stripHigh em, MulS.isBits_stripHigh em, MulS.ofBits_stripHigh em, h02⟩⟩
  · exact Ev.seqs_cons hev1 hev2
  · omega

end AddSub
end Work.IntLib
