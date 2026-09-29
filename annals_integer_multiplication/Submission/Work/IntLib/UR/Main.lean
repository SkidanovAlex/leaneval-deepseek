import Mathlib
import Submission.Work.IntLib.UR.Defs
import Submission.Work.IntLib.UR.phase1_eval
import Submission.Work.IntLib.UR.phase2_eval

set_option autoImplicit false

namespace Work.IntLib
namespace UR

open HvdH
open Work.Layout

/-! ## Register distinctness (symmetrised) -/

theorem rT_ne_rD : rT ≠ rD := rD_ne_rT.symm
theorem rT_ne_rScr : rT ≠ rScr := rScr_ne_rT.symm
theorem rTok_ne_rScr : rTok ≠ rScr := rScr_ne_rTok.symm
theorem rTok_ne_rB : rTok ≠ rB := rB_ne_rTok.symm
theorem rTok_ne_rPos : rTok ≠ rPos := rPos_ne_rTok.symm
theorem rTok_ne_rIend : rTok ≠ rIend := rIend_ne_rTok.symm
/-! ## Register frames of `Eval` -/

/-- The set of registers a program may write. -/
def cmdWrites : Cmd → Finset Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov dst _ => {dst}
  | .seq a b => cmdWrites a ∪ cmdWrites b
  | .ite _ _ a b => cmdWrites a ∪ cmdWrites b
  | .loop _ _ a => cmdWrites a
  | .self => Finset.univ

theorem Eval_reg_frame {main c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n) :
    ∀ {r : Reg}, r ∉ cmdWrites c → s'.reg r = s.reg r := by
  induction h with
  | skip s => intro r hr; rfl
  | pop k r' s =>
      intro r hr
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | peek k r' s =>
      intro r hr
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | push k r' s => intro r hr; rfl
  | set r' c s =>
      intro r hr
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | mov dst src s =>
      intro r hr
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | seq h1 h2 ih1 ih2 =>
      intro r hr
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      rw [ih2 hr.2, ih1 hr.1]
  | iteT _ _ ih =>
      intro r hr
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | iteF _ _ ih =>
      intro r hr
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopF _ => intro r hr; rfl
  | loopT _ _ _ ih1 ih2 =>
      intro r hr
      simp only [cmdWrites] at hr
      rw [ih2 hr, ih1 hr]
  | self h ih => intro r hr; exact absurd (Finset.mem_univ r) hr

theorem Ev_reg_frame {main p : Cmd} {s s' : State} {C : ℕ} (h : Ev main p s s' C) :
    ∀ {r : Reg}, r ∉ cmdWrites p → s'.reg r = s.reg r := by
  intro r hr
  obtain ⟨n, he, _⟩ := h
  exact Eval_reg_frame he hr

theorem rTok_not_mem_phase1 (c tr : Stk) : rTok ∉ cmdWrites (urPhase1Loop c tr) := by
  simp [cmdWrites, urPhase1Loop, urPhase1Body, rTok_ne_rD]

theorem rT_not_mem_double (c tr : Stk) : rT ∉ cmdWrites (urDouble c tr) := by
  simp [cmdWrites, urDouble, urPhase1Loop, urPhase1Body, urPhase2Loop, urPhase2Body,
    rT_ne_rD, rT_ne_rScr]

theorem rB_not_mem_double (c tr : Stk) : rB ∉ cmdWrites (urDouble c tr) := by
  simp [cmdWrites, urDouble, urPhase1Loop, urPhase1Body, urPhase2Loop, urPhase2Body,
    rB_ne_rD, rB_ne_rScr]

theorem rTok_not_mem_double (c tr : Stk) : rTok ∉ cmdWrites (urDouble c tr) := by
  simp [cmdWrites, urDouble, urPhase1Loop, urPhase1Body, urPhase2Loop, urPhase2Body,
    rTok_ne_rD, rTok_ne_rScr]

/-! ## The numeric step of the main-loop cost recurrence -/

theorem ur_bound_step2 (A b B m : ℕ) :
    9 * A + 17 + (9 * (b + 2 * A) * (2 ^ m - 1) + 18 * B + 18 * m + 5) ≤
      9 * A * (2 ^ (m + 1) - 1) + 18 * (2 ^ m * b + B) + 18 * (m + 1) + 5 := by
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  set u : ℕ := 2 ^ m - 1 with hu
  have h2m : 2 ^ m = u + 1 := by omega
  have h2m1 : 2 ^ (m + 1) - 1 = 2 * u + 1 := by
    have h : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    omega
  rw [h2m1, h2m]
  nlinarith

/-! ## The doubling gadget -/

theorem double_eval (main : Cmd) (c tr : Stk) (hct : c ≠ tr) (v : ℕ)
    (Gc Tr : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (hc : X c = Unary v Gc) (htr : X tr = Tr) (hrTok : g rTok = gTok) :
    ∃ (g' : Reg → Glyph) (X' : Stk → List Glyph) (n : ℕ),
      Ev main (urDouble c tr) ⟨g, X⟩ ⟨g', X'⟩ n ∧ n ≤ 9 * v + 9 ∧
      X' c = Unary (2 * v) Gc ∧ X' tr = Tr ∧
      g' rT = g rT ∧ g' rB = g rB ∧ g' rTok = g rTok ∧
      (∀ k : Stk, k ≠ c → k ≠ tr → X' k = X k) := by
  have htrc : tr ≠ c := fun h => hct h.symm
  set g1 : Reg → Glyph := Function.update g rD gEnd with hg1
  set X2 : Stk → List Glyph := Function.update X tr (gEnd :: X tr) with hX2
  set g3 : Reg → Glyph := Function.update g1 rD ((X2 c).headD .eos) with hg3
  have h1 : Ev main (.set rD gEnd) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    rw [hg1]; exact ev_set' main rD gEnd g X
  have hg1rD : g1 rD = gEnd := by
    rw [hg1]; exact Function.update_self rD gEnd g
  have h2 : Ev main (.push tr rD) ⟨g1, X⟩ ⟨g1, X2⟩ 1 := by
    have h := ev_push' main tr rD g1 X
    rw [hg1rD] at h
    rw [hX2]
    exact h
  have h3 : Ev main (.peek c rD) ⟨g1, X2⟩ ⟨g3, X2⟩ 1 := by
    rw [hg3]; exact ev_peek' main c rD g1 X2
  have hX2c : X2 c = Unary v Gc := by
    rw [hX2, Function.update_of_ne hct (gEnd :: X tr) X, hc]
  have hX2tr : X2 tr = Unary 0 Tr := by
    rw [hX2, Function.update_self tr (gEnd :: X tr) X, htr, Unary_zero]
  have hr3 : g3 rD = (Unary v Gc).headD .eos := by
    rw [hg3, Function.update_self rD ((X2 c).headD .eos) g1, hX2c]
  obtain ⟨g4, X4, n4, h4ev, h4n, h4c, h4tr, h4fr⟩ :=
    phase1_eval main c tr hct v 0 Gc Tr g3 X2 hX2c hX2tr hr3
  have hX4tr : X4 tr = Unary v Tr := by simpa using h4tr
  set g5 : Reg → Glyph := Function.update g4 rD ((X4 tr).headD .eos) with hg5
  have h5 : Ev main (.peek tr rD) ⟨g4, X4⟩ ⟨g5, X4⟩ 1 := by
    rw [hg5]; exact ev_peek' main tr rD g4 X4
  have hr5 : g5 rD = (Unary v Tr).headD .eos := by
    rw [hg5, Function.update_self rD ((X4 tr).headD .eos) g4, hX4tr]
  have hg4rTok : g4 rTok = g3 rTok := Ev_reg_frame h4ev (rTok_not_mem_phase1 c tr)
  have hg3rTok : g3 rTok = gTok := by
    rw [hg3, Function.update_of_ne rTok_ne_rD ((X2 c).headD .eos) g1, hg1,
      Function.update_of_ne rTok_ne_rD gEnd g, hrTok]
  have hrTok5 : g5 rTok = gTok := by
    rw [hg5, Function.update_of_ne rTok_ne_rD ((X4 tr).headD .eos) g4, hg4rTok, hg3rTok]
  obtain ⟨g6, X6, n6, h6ev, h6n, h6tr, h6c, h6fr⟩ :=
    phase2_eval main c tr hct v 0 Gc Tr g5 X4 hX4tr h4c hr5 hrTok5
  have hX6tr : X6 tr = gEnd :: Tr := by
    rw [h6tr, Unary_zero]
  set g7 : Reg → Glyph := Function.update g6 rScr ((X6 tr).headD .eos) with hg7
  set X7 : Stk → List Glyph := Function.update X6 tr (X6 tr).tail with hX7
  have h7 : Ev main (.pop tr rScr) ⟨g6, X6⟩ ⟨g7, X7⟩ 1 := by
    rw [hg7, hX7]; exact ev_pop' main tr rScr g6 X6
  have hmain : Ev main (urDouble c tr) ⟨g, X⟩ ⟨g7, X7⟩
      (1 + (1 + (1 + (n4 + (1 + (n6 + 1)))))) :=
    Ev.seq h1 (Ev.seq h2 (Ev.seq h3 (Ev.seq h4ev (Ev.seq h5 (Ev.seq h6ev h7)))))
  have hX7c : X7 c = Unary (2 * v) Gc := by
    rw [hX7]
    exact (Function.update_of_ne hct (X6 tr).tail X6).trans (by simpa using h6c)
  have hX7tr : X7 tr = Tr := by
    rw [hX7, Function.update_self tr (X6 tr).tail X6, hX6tr, List.tail_cons]
  refine ⟨g7, X7, _, hmain, ?_, hX7c, hX7tr, ?_, ?_, ?_, ?_⟩
  · omega
  · exact Ev_reg_frame hmain (rT_not_mem_double c tr)
  · exact Ev_reg_frame hmain (rB_not_mem_double c tr)
  · exact Ev_reg_frame hmain (rTok_not_mem_double c tr)
  · intro k hkc hktr
    have h1k : X7 k = X6 k :=
      Function.update_of_ne (fun h : k = tr => hktr h) (X6 tr).tail X6
    have h2k : X6 k = X4 k := h6fr k hkc hktr
    have h3k : X4 k = X2 k := h4fr k hkc hktr
    have h4k : X2 k = X k :=
      Function.update_of_ne (fun h : k = tr => hktr h) (gEnd :: X tr) X
    exact h1k.trans (h2k.trans (h3k.trans h4k))


/-! ## One iteration of the main loop -/

theorem loopBody_bit_eval (main : Cmd) (a tgt c tr : Stk) (hat : a ≠ tgt) (hac : a ≠ c)
    (hac' : a ≠ tr) (htc : tgt ≠ c) (htt : tgt ≠ tr) (hct : c ≠ tr)
    (b : Bool) (tl p : List Bool) (Gs Gt Gc Tr : List Glyph)
    (g : Reg → Glyph) (X : Stk → List Glyph)
    (ha : X a = Glyph.bit b :: (tl.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs))
    (hc : X c = Unary (urW p) Gc) (htgt : X tgt = Gt) (htr : X tr = Tr)
    (hrT : g rT = gTok) (hrTok : g rTok = gTok) :
    ∃ (g' : Reg → Glyph) (X' : Stk → List Glyph) (n : ℕ),
      Ev main (urLoopBody a tgt c tr) ⟨g, X⟩ ⟨g', X'⟩ n ∧ n ≤ 9 * urW p + 16 ∧
      X' a = tl.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs ∧
      X' c = Unary (2 * urW p + b.toNat) Gc ∧
      X' tgt = Glyph.bit b :: Gt ∧ X' tr = Tr ∧
      g' rT = gTok ∧ g' rTok = gTok ∧
      (∀ k : Stk, k ≠ a → k ≠ tgt → k ≠ c → k ≠ tr → X' k = X k) := by
  have hca : c ≠ a := fun h => hac h.symm
  have hctg : c ≠ tgt := fun h => htc h.symm
  have hta : tgt ≠ a := fun h => hat h.symm
  have httgt : tr ≠ tgt := fun h => htt h.symm
  have htra : tr ≠ a := fun h => hac' h.symm
  have htrc : tr ≠ c := fun h => hct h.symm
  set gA : Reg → Glyph := Function.update g rT ((X a).headD .eos) with hgA
  set XA : Stk → List Glyph := Function.update X a (X a).tail with hXA
  have hpop : Ev main (.pop a rT) ⟨g, X⟩ ⟨gA, XA⟩ 1 := by
    rw [hgA, hXA]; exact ev_pop' main a rT g X
  have hgArT : gA rT = Glyph.bit b := by
    rw [hgA, Function.update_self rT ((X a).headD .eos) g, ha, List.headD_cons]
  have hXAa : XA a = tl.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs := by
    rw [hXA, Function.update_self a (X a).tail X, ha, List.tail_cons]
  have hgAne : gA rT ≠ Glyph.pos := by rw [hgArT]; exact bit_ne_pos b
  set gB : Reg → Glyph := Function.update gA rB (gA rT) with hgB
  have hmov : Ev main (.mov rB rT) ⟨gA, XA⟩ ⟨gB, XA⟩ 1 := by
    rw [hgB]; exact ev_mov' main rB rT gA XA
  set gC : Reg → Glyph := Function.update gB rT gTok with hgC
  have hset : Ev main (.set rT gTok) ⟨gB, XA⟩ ⟨gC, XA⟩ 1 := by
    rw [hgC]; exact ev_set' main rT gTok gB XA
  have hgCrB : gC rB = Glyph.bit b := by
    rw [hgC, Function.update_of_ne rB_ne_rT gTok gB, hgB,
      Function.update_self rB (gA rT) gA, hgArT]
  have hgCrT : gC rT = gTok := by
    rw [hgC, Function.update_self rT gTok gB]
  have hgCrTok : gC rTok = gTok := by
    rw [hgC, Function.update_of_ne rTok_ne_rT gTok gB, hgB,
      Function.update_of_ne rTok_ne_rB (gA rT) gA, hgA,
      Function.update_of_ne rTok_ne_rT ((X a).headD .eos) g, hrTok]
  set XD : Stk → List Glyph := Function.update XA tgt (gC rB :: XA tgt) with hXD
  have hpush : Ev main (.push tgt rB) ⟨gC, XA⟩ ⟨gC, XD⟩ 1 := by
    rw [hXD]; exact ev_push' main tgt rB gC XA
  have hXDc : XD c = Unary (urW p) Gc := by
    rw [hXD, Function.update_of_ne hctg (gC rB :: XA tgt) XA, hXA,
      Function.update_of_ne hca (X a).tail X, hc]
  have hXDtr : XD tr = Tr := by
    rw [hXD, Function.update_of_ne httgt (gC rB :: XA tgt) XA, hXA,
      Function.update_of_ne htra (X a).tail X, htr]
  have hXDtgt : XD tgt = Glyph.bit b :: Gt := by
    rw [hXD, Function.update_self tgt (gC rB :: XA tgt) XA, hgCrB, hXA,
      Function.update_of_ne hta (X a).tail X, htgt]
  obtain ⟨g5, X5, n5, h5ev, h5n, h5c, h5tr, h5rT, h5rB, h5rTok, h5fr⟩ :=
    double_eval main c tr hct (urW p) Gc Tr gC XD hXDc hXDtr hgCrTok
  have hg5rT : g5 rT = gTok := h5rT.trans hgCrT
  have hrTok5 : g5 rTok = gTok := h5rTok.trans hgCrTok
  have hfrX : ∀ k : Stk, k ≠ a → k ≠ tgt → k ≠ c → k ≠ tr → XD k = X k := by
    intro k h1 h2 h3 h4
    exact (Function.update_of_ne h2 (gC rB :: XA tgt) XA).trans
      (Function.update_of_ne h1 (X a).tail X)
  cases b with
  | true =>
    have hbit : g5 rB = Glyph.bit true := h5rB.trans hgCrB
    set XE : Stk → List Glyph := Function.update X5 c (gTok :: X5 c) with hXE
    have hita : Ev main (.push c rTok) ⟨g5, X5⟩ ⟨g5, XE⟩ 1 := by
      have h := ev_push' main c rTok g5 X5
      rw [hrTok5] at h
      rw [hXE]; exact h
    have hite : Ev main (.ite rB (Glyph.bit true) (.push c rTok) .skip) ⟨g5, X5⟩ ⟨g5, XE⟩ 2 :=
      Ev.iteT hbit hita
    have helse : Ev main (.seq (.mov rB rT)
        (.seq (.set rT gTok)
          (.seq (.push tgt rB)
            (.seq (urDouble c tr) (.ite rB (Glyph.bit true) (.push c rTok) .skip)))))
        ⟨gA, XA⟩ ⟨g5, XE⟩ _ :=
      Ev.seq hmov (Ev.seq hset (Ev.seq hpush (Ev.seq h5ev hite)))
    have hbody : Ev main (urLoopBody a tgt c tr) ⟨g, X⟩ ⟨g5, XE⟩ _ :=
      Ev.seq hpop (Ev.iteF hgAne helse)
    refine ⟨g5, XE, _, hbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · refine (Function.update_of_ne hac (gTok :: X5 c) X5).trans ?_
      exact (h5fr a hac hac').trans
        ((Function.update_of_ne hat (gC rB :: XA tgt) XA).trans hXAa)
    · refine (Function.update_self c (gTok :: X5 c) X5).trans ?_
      rw [h5c]
      exact (Unary_succ (2 * urW p) Gc).symm
    · refine (Function.update_of_ne htc (gTok :: X5 c) X5).trans ?_
      exact (h5fr tgt htc htt).trans hXDtgt
    · refine (Function.update_of_ne htrc (gTok :: X5 c) X5).trans ?_
      exact h5tr
    · exact hg5rT
    · exact hrTok5
    · intro k h1 h2 h3 h4
      rw [hXE]
      exact (Function.update_of_ne h3 (gTok :: X5 c) X5).trans
        ((h5fr k h3 h4).trans (hfrX k h1 h2 h3 h4))
  | false =>
    have hbit : g5 rB ≠ Glyph.bit true := by
      rw [h5rB.trans hgCrB]; exact fun h => bit_true_ne_false h.symm
    have hite : Ev main (.ite rB (Glyph.bit true) (.push c rTok) .skip) ⟨g5, X5⟩ ⟨g5, X5⟩ 2 :=
      Ev.iteF hbit (ev_skip' main g5 X5)
    have helse : Ev main (.seq (.mov rB rT)
        (.seq (.set rT gTok)
          (.seq (.push tgt rB)
            (.seq (urDouble c tr) (.ite rB (Glyph.bit true) (.push c rTok) .skip)))))
        ⟨gA, XA⟩ ⟨g5, X5⟩ _ :=
      Ev.seq hmov (Ev.seq hset (Ev.seq hpush (Ev.seq h5ev hite)))
    have hbody : Ev main (urLoopBody a tgt c tr) ⟨g, X⟩ ⟨g5, X5⟩ _ :=
      Ev.seq hpop (Ev.iteF hgAne helse)
    refine ⟨g5, X5, _, hbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · exact (h5fr a hac hac').trans
        ((Function.update_of_ne hat (gC rB :: XA tgt) XA).trans hXAa)
    · exact h5c
    · exact (h5fr tgt htc htt).trans hXDtgt
    · exact h5tr
    · exact hg5rT
    · exact hrTok5
    · intro k h1 h2 h3 h4
      exact (h5fr k h3 h4).trans (hfrX k h1 h2 h3 h4)

/-! ## The main loop -/

theorem loop_eval (main : Cmd) (a tgt c tr : Stk) (hat : a ≠ tgt) (hac : a ≠ c)
    (hac' : a ≠ tr) (htc : tgt ≠ c) (htt : tgt ≠ tr) (hct : c ≠ tr)
    (bl p : List Bool) (Gs Gt Gc Tr : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (ha : X a = bl.map Glyph.bit ++ Glyph.pos :: Glyph.mk a :: Gs)
    (hc : X c = Unary (urW p) Gc) (htgt : X tgt = p.reverse.map Glyph.bit ++ Gt)
    (htr : X tr = Tr) (hrT : g rT = gTok) (hrTok : g rTok = gTok) :
    ∃ (g' : Reg → Glyph) (X' : Stk → List Glyph) (n : ℕ),
      Ev main (urLoop a tgt c tr) ⟨g, X⟩ ⟨g', X'⟩ n ∧
      n ≤ 9 * urW p * (2 ^ bl.length - 1) + 18 * urW bl + 18 * bl.length + 5 ∧
      X' a = Glyph.mk a :: Gs ∧
      X' c = Unary (urW (p ++ bl)) Gc ∧
      X' tgt = (p ++ bl).reverse.map Glyph.bit ++ Gt ∧
      X' tr = Tr ∧
      (∀ k : Stk, k ≠ a → k ≠ tgt → k ≠ c → k ≠ tr → X' k = X k) := by
  induction bl generalizing p g X with
  | nil =>
    have hca : c ≠ a := fun h => hac h.symm
    have hta : tgt ≠ a := fun h => hat h.symm
    have htra : tr ≠ a := fun h => hac' h.symm
    set gA : Reg → Glyph := Function.update g rT ((X a).headD .eos) with hgA
    set XA : Stk → List Glyph := Function.update X a (X a).tail with hXA
    have hpop : Ev main (.pop a rT) ⟨g, X⟩ ⟨gA, XA⟩ 1 := by
      rw [hgA, hXA]; exact ev_pop' main a rT g X
    have hgApos : gA rT = Glyph.pos := by
      rw [hgA, Function.update_self rT ((X a).headD .eos) g, ha]
      simp
    have hXAa : XA a = Glyph.mk a :: Gs := by
      rw [hXA, Function.update_self a (X a).tail X, ha]
      simp
    set gB : Reg → Glyph := Function.update gA rT gEnd with hgB
    have hset : Ev main (.set rT gEnd) ⟨gA, XA⟩ ⟨gB, XA⟩ 1 := by
      rw [hgB]; exact ev_set' main rT gEnd gA XA
    have hloopF : Ev main (urLoop a tgt c tr) ⟨gB, XA⟩ ⟨gB, XA⟩ 1 :=
      Ev.loopF (by
        rw [hgB]
        show (Function.update gA rT gEnd) rT ≠ gTok
        rw [Function.update_self rT gEnd gA]
        exact gEnd_ne_gTok)
    have hbody : Ev main (urLoopBody a tgt c tr) ⟨g, X⟩ ⟨gB, XA⟩ 3 :=
      Ev.seq hpop (Ev.iteT hgApos hset)
    have hmain : Ev main (urLoop a tgt c tr) ⟨g, X⟩ ⟨gB, XA⟩ 5 :=
      Ev.loopT hrT hbody hloopF
    refine ⟨gB, XA, 5, hmain, ?_, hXAa, ?_, ?_, ?_, ?_⟩
    · simp [urW_nil]
    · rw [List.append_nil, hXA]
      exact (Function.update_of_ne hca (X a).tail X).trans hc
    · rw [List.append_nil, hXA]
      exact (Function.update_of_ne hta (X a).tail X).trans htgt
    · rw [hXA]
      exact (Function.update_of_ne htra (X a).tail X).trans htr
    · intro k h1 h2 h3 h4
      rw [hXA]
      exact Function.update_of_ne h1 (X a).tail X
  | cons b tl ih =>
    obtain ⟨g1, X1, n1, hev1, hn1, ha1, hc1, htgt1, htr1, hrT1, hrTok1, hfr1⟩ :=
      loopBody_bit_eval main a tgt c tr hat hac hac' htc htt hct b tl p Gs _ Gc Tr
        g X ha hc htgt htr hrT hrTok
    have hc1' : X1 c = Unary (urW (p ++ [b])) Gc := by
      have h : (2 * urW p + b.toNat) = urW (p ++ [b]) := by rw [urW_snoc]; ring
      rw [hc1, h]
    have htgt1' : X1 tgt = (p ++ [b]).reverse.map Glyph.bit ++ Gt := by
      have h : (p ++ [b]).reverse = b :: p.reverse := by simp
      simp [htgt1, h]
    obtain ⟨g2, X2, n2, hev2, hn2, ha2, hc2, htgt2, htr2, hfr2⟩ :=
      ih (p ++ [b]) g1 X1 ha1 hc1' htgt1' htr1 hrT1 hrTok1
    refine ⟨g2, X2, _, Ev.loopT hrT hev1 hev2, ?_, ha2, ?_, ?_, htr2, ?_⟩
    · have h2 := hn2
      rw [urW_snoc] at h2
      have h3 := ur_bound_step2 (urW p) b.toNat (urW tl) tl.length
      have h1' : n1 ≤ 9 * urW p + 16 := hn1
      rw [urW_cons, List.length_cons]
      omega
    · have h : (p ++ [b]) ++ tl = p ++ (b :: tl) := by simp
      rw [← h]
      exact hc2
    · have h : (p ++ [b]) ++ tl = p ++ (b :: tl) := by simp
      rw [← h]
      exact htgt2
    · intro k h1 h2 h3 h4
      exact (hfr2 k h1 h2 h3 h4).trans (hfr1 k h1 h2 h3 h4)

end UR
end Work.IntLib
