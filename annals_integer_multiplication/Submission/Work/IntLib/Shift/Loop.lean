import Mathlib
import Submission.Work.IntLib.Shift.Defs

/-!
# `IntLib` / shift words: the `shl` main loop

`Eval` specifications of the `shl` main loop and its pieces.  Every straight-line piece comes with
*state functions* (`pst1`, `pst2`, …) defined on the whole state, so that its `Eval` lemma is
proved by composing the primitive `Ev` steps (whose states match definitionally); the stack
contents of the resulting states are then read off with `simp`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

/-! ## Frame bookkeeping and concrete distinctness facts -/

/-- All stacks outside `S` are unchanged. -/
def SameOn (s s' : State) (S : Finset Stk) : Prop := ∀ j : Stk, j ∉ S → s'.stk j = s.stk j

theorem SameOn.trans {s s' s'' : State} {S S' : Finset Stk} (h1 : SameOn s s' S)
    (h2 : SameOn s' s'' S') : SameOn s s'' (S ∪ S') := by
  intro j hj
  rw [h2 j (fun h => hj (Finset.mem_union_right S h)), h1 j (fun h => hj (Finset.mem_union_left S' h))]

theorem SameOn.union {s s' : State} {S S' : Finset Stk} (h : SameOn s s' S) : SameOn s s' (S ∪ S') :=
  fun j hj => h j (fun h' => hj (Finset.mem_union_left S' h'))

theorem SameOn.of_pair {s s' : State} {a b : Stk}
    (h : ∀ j, j ≠ a → j ≠ b → s'.stk j = s.stk j) : SameOn s s' ({a, b} : Finset Stk) := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  exact h j hj.1 hj.2

theorem SameOn.refl' (s : State) (S : Finset Stk) : SameOn s s S := fun _ _ => rfl

theorem SameOn.mono {s s' : State} {S S' : Finset Stk} (h : SameOn s s' S) (hSS : S ⊆ S') :
    SameOn s s' S' := fun j hj => h j (fun h' => hj (hSS h'))

theorem SameOn.union_self {s s' : State} {S : Finset Stk} (h : SameOn s s' (S ∪ S)) :
    SameOn s s' S := fun j hj => h j (by simp [hj])

theorem SameOn.of_triple {s s' : State} {a b c : Stk}
    (h : ∀ j, j ≠ a → j ≠ b → j ≠ c → s'.stk j = s.stk j) : SameOn s s' ({a, b, c} : Finset Stk) := by
  intro j hj
  exact h j (fun h1 => hj (by simp [h1])) (fun h2 => hj (by simp [h2]))
    (fun h3 => hj (by simp [h3]))

@[simp] theorem ne_sP_sA : sP ≠ sA := by decide
@[simp] theorem ne_sP_sT2 : sP ≠ sT2 := by decide
@[simp] theorem ne_sA_sP : sA ≠ sP := by decide
@[simp] theorem ne_sA_sT2 : sA ≠ sT2 := by decide
@[simp] theorem ne_sT2_sP : sT2 ≠ sP := by decide
@[simp] theorem ne_sT2_sA : sT2 ≠ sA := by decide
@[simp] theorem ne_sK_sP : sK ≠ sP := by decide
@[simp] theorem ne_sK_sA : sK ≠ sA := by decide
@[simp] theorem ne_sK_sT2 : sK ≠ sT2 := by decide
@[simp] theorem ne_sK_sM : sK ≠ sM := by decide
@[simp] theorem ne_sK_sSg : sK ≠ sSg := by decide
@[simp] theorem ne_sP_sK : sP ≠ sK := by decide
@[simp] theorem ne_sA_sK : sA ≠ sK := by decide
@[simp] theorem ne_sT2_sK : sT2 ≠ sK := by decide
@[simp] theorem ne_sM_sP : sM ≠ sP := by decide
@[simp] theorem ne_sM_sA : sM ≠ sA := by decide
@[simp] theorem ne_sM_sT2 : sM ≠ sT2 := by decide
@[simp] theorem ne_sM_sK : sM ≠ sK := by decide
@[simp] theorem ne_sM_sSg : sM ≠ sSg := by decide
@[simp] theorem ne_sM_sT : sM ≠ sT := by decide
@[simp] theorem ne_sP_sM : sP ≠ sM := by decide
@[simp] theorem ne_sA_sM : sA ≠ sM := by decide
@[simp] theorem ne_sT2_sM : sT2 ≠ sM := by decide
@[simp] theorem ne_sSg_sM : sSg ≠ sM := by decide
@[simp] theorem ne_sSg_sP : sSg ≠ sP := by decide
@[simp] theorem ne_sSg_sA : sSg ≠ sA := by decide
@[simp] theorem ne_sSg_sT2 : sSg ≠ sT2 := by decide
@[simp] theorem ne_sSg_sK : sSg ≠ sK := by decide
@[simp] theorem ne_sP_sSg : sP ≠ sSg := by decide
@[simp] theorem ne_sA_sSg : sA ≠ sSg := by decide
@[simp] theorem ne_sT2_sSg : sT2 ≠ sSg := by decide
@[simp] theorem ne_sT_sM : sT ≠ sM := by decide
@[simp] theorem ne_sT_sT2 : sT ≠ sT2 := by decide
@[simp] theorem ne_sT2_sT : sT2 ≠ sT := by decide
@[simp] theorem ne_sT_sP : sT ≠ sP := by decide
@[simp] theorem ne_sT_sA : sT ≠ sA := by decide
@[simp] theorem ne_rI_rY : rI ≠ rY := by decide
@[simp] theorem ne_rI_rX : rI ≠ rX := by decide
@[simp] theorem ne_rY_rI : rY ≠ rI := by decide
@[simp] theorem ne_rY_rX : rY ≠ rX := by decide
@[simp] theorem ne_rX_rY : rX ≠ rY := by decide
@[simp] theorem ne_rX_rI : rX ≠ rI := by decide
@[simp] theorem ne_rW_rY : rW ≠ rY := by decide
@[simp] theorem ne_rW_rX : rW ≠ rX := by decide
@[simp] theorem ne_rW_rI : rW ≠ rI := by decide
@[simp] theorem ne_rI_rW : rI ≠ rW := by decide
@[simp] theorem ne_rO_rX : rO ≠ rX := by decide
@[simp] theorem ne_rO_rW : rO ≠ rW := by decide
@[simp] theorem ne_rE_rI : rE ≠ rI := by decide
@[simp] theorem ne_rE_rX : rE ≠ rX := by decide
@[simp] theorem ne_rD_rI : rD ≠ rI := by decide
@[simp] theorem ne_rD_rX : rD ≠ rX := by decide
@[simp] theorem ne_rZ_rJ : rZ ≠ rJ := by decide
@[simp] theorem ne_rJ_rZ : rJ ≠ rZ := by decide

@[simp] theorem upReg_same {g : Reg → Glyph} (r : Reg) (c : Glyph) :
    (Function.update g r c) r = c := Function.update_self r c g

@[simp] theorem upReg_ne {g : Reg → Glyph} {r r' : Reg} (h : r ≠ r') (c : Glyph) :
    (Function.update g r' c) r = g r := Function.update_of_ne h c g

theorem unit_ne_markerP : gUnit ≠ gmk sP := by decide
theorem unit_ne_markerT2 : gUnit ≠ gmk sT2 := by decide
theorem unit_ne_markerK : gUnit ≠ gmk sK := by decide
theorem unit_ne_markerM : gUnit ≠ gmk sM := by decide
theorem unit_ne_markerA : gUnit ≠ gmk sA := by decide
theorem zero_ne_markerA : gZero ≠ gmk sA := by decide
theorem bit_ne_marker (b : Bool) (k : Stk) : (Glyph.bit b : Glyph) ≠ gmk k := fun h => by cases h
theorem marker_ne_bit (b : Bool) (k : Stk) : gmk k ≠ (Glyph.bit b : Glyph) := fun h => by cases h

/-- A region all of whose glyphs are equal to `a`. -/
def AllEq (a : Glyph) (l : List Glyph) : Prop := ∀ g ∈ l, g = a

/-- A region all of whose glyphs are `gUnit`. -/
def AllUnit (l : List Glyph) : Prop := AllEq gUnit l

/-- A region all of whose glyphs are `gZero` (the accumulator of `shl`). -/
def AllZero (l : List Glyph) : Prop := AllEq gZero l

theorem AllEq.cons {a : Glyph} {l : List Glyph} (h : AllEq a l) : AllEq a (a :: l) :=
  fun g hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · rfl
    · exact h g hg

theorem AllEq.append {a : Glyph} {l l' : List Glyph} (h : AllEq a l) (h' : AllEq a l') :
    AllEq a (l ++ l') := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact h' g hg

theorem AllEq.reverse {a : Glyph} {l : List Glyph} (h : AllEq a l) : AllEq a l.reverse :=
  fun g hg => h g (List.mem_reverse.mp hg)

theorem allEq_replicate (a : Glyph) (n : ℕ) : AllEq a (List.replicate n a) :=
  fun g hg => List.eq_of_mem_replicate hg

theorem AllEq.eq_replicate {a : Glyph} {l : List Glyph} (h : AllEq a l) :
    l = List.replicate l.length a := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have hb : b = a := h b (List.mem_cons_self ..)
    have ht : AllEq a t := fun g hg => h g (List.mem_cons_of_mem b hg)
    rw [hb, ih ht, List.length_cons, List.replicate_succ, List.length_replicate]

theorem allUnit_replicate (n : ℕ) : AllUnit (List.replicate n gUnit) := allEq_replicate gUnit n

theorem allZero_replicate (n : ℕ) : AllZero (List.replicate n gZero) := allEq_replicate gZero n

theorem AllUnit.nil : AllUnit ([] : List Glyph) := fun _ hg => absurd hg (List.not_mem_nil)

theorem AllUnit.cons {l : List Glyph} (h : AllUnit l) : AllUnit (gUnit :: l) :=
  AllEq.cons h

theorem AllZero.cons {l : List Glyph} (h : AllZero l) : AllZero (gZero :: l) := AllEq.cons h

/-- `a` prepended to `p` copies of `a` and a list `A`. -/
theorem replicate_append_cons (p : ℕ) (a : Glyph) (A : List Glyph) :
    List.replicate p a ++ (a :: A) = List.replicate (p + 1) a ++ A := by
  induction p with
  | zero => simp
  | succ p ih =>
    show (a :: List.replicate p a) ++ (a :: A) = (a :: List.replicate (p + 1) a) ++ A
    rw [List.cons_append, List.cons_append, ih]

/-! ## State-based primitive lemmas -/

theorem ev_pop_st (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.pop k r) s ⟨Function.update s.reg r ((s.stk k).headD .eos),
      Function.update s.stk k (s.stk k).tail⟩ 1 :=
  ⟨1, Eval.pop k r s, le_rfl⟩

theorem ev_peek_st (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.peek k r) s ⟨Function.update s.reg r ((s.stk k).headD .eos), s.stk⟩ 1 :=
  ⟨1, Eval.peek k r s, le_rfl⟩

theorem ev_push_st (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Ev main (.push k r) s ⟨s.reg, Function.update s.stk k (s.reg r :: s.stk k)⟩ 1 :=
  ⟨1, Eval.push k r s, le_rfl⟩

theorem ev_push_glyph_st (main : Cmd) (k : Stk) (r : Reg) (s : State) (gd : Glyph)
    (h : s.reg r = gd) :
    Ev main (.push k r) s ⟨s.reg, Function.update s.stk k (gd :: s.stk k)⟩ 1 := by
  rw [← h]
  exact ev_push_st main k r s

theorem ev_set_st (main : Cmd) (r : Reg) (c : Glyph) (s : State) :
    Ev main (.set r c) s ⟨Function.update s.reg r c, s.stk⟩ 1 :=
  ⟨1, Eval.set r c s, le_rfl⟩

theorem ev_mov_st (main : Cmd) (dst src : Reg) (s : State) :
    Ev main (.mov dst src) s ⟨Function.update s.reg dst (s.reg src), s.stk⟩ 1 :=
  ⟨1, Eval.mov dst src s, le_rfl⟩

theorem ev_pushC_st (main : Cmd) (k : Stk) (gd : Glyph) (r : Reg) (s : State) :
    Ev main (pushC k gd r) s ⟨Function.update s.reg r gd, Function.update s.stk k (gd :: s.stk k)⟩ 2 := by
  have h1 : Ev main (.set r gd) s ⟨Function.update s.reg r gd, s.stk⟩ 1 := ev_set_st main r gd s
  have h2 : Ev main (.push k r) ⟨Function.update s.reg r gd, s.stk⟩
      ⟨Function.update s.reg r gd, Function.update s.stk k (gd :: s.stk k)⟩ 1 :=
    ev_push_glyph_st main k r ⟨Function.update s.reg r gd, s.stk⟩ gd (Function.update_self r gd s.reg)
  rw [pushC, seqs_pair]
  exact Ev.seq' h1 h2 (le_rfl)

/-! ## `shl`: the block pass -/

def pst1 (s : State) : State :=
  ⟨Function.update s.reg rX ((s.stk sP).headD .eos), Function.update s.stk sP (s.stk sP).tail⟩

def pst2 (s : State) : State :=
  ⟨Function.update (pst1 s).reg rY gUnit, Function.update (pst1 s).stk sT2 (gUnit :: (pst1 s).stk sT2)⟩

def pst3 (s : State) : State :=
  ⟨Function.update (pst2 s).reg rY gUnit, Function.update (pst2 s).stk sT2 (gUnit :: (pst2 s).stk sT2)⟩

def pst4 (s : State) : State :=
  ⟨Function.update (pst3 s).reg rY gZero, Function.update (pst3 s).stk sA (gZero :: (pst3 s).stk sA)⟩

/-- State after the push of one "hit" iteration of the `shl` pass. -/
def pstH1 (s : State) : State :=
  ⟨(pst1 s).reg, Function.update (pst1 s).stk sP ((pst1 s).reg rX :: (pst1 s).stk sP)⟩

/-- State after one "hit" iteration of the `shl` pass. -/
def pstH (s : State) : State :=
  ⟨Function.update (pstH1 s).reg rI gStop, (pstH1 s).stk⟩

theorem pst4_stk_sP (s : State) : (pst4 s).stk sP = (s.stk sP).tail := by simp [pst4, pst3, pst2, pst1]
theorem pst4_stk_sA (s : State) : (pst4 s).stk sA = gZero :: (s.stk sA) := by
  simp [pst4, pst3, pst2, pst1]
theorem pst4_stk_sT2 (s : State) : (pst4 s).stk sT2 = gUnit :: gUnit :: (s.stk sT2) := by
  simp [pst4, pst3, pst2, pst1]
theorem pst4_reg_rI (s : State) : (pst4 s).reg rI = s.reg rI := by simp [pst4, pst3, pst2, pst1]
theorem pst4_stk_other (s : State) {j : Stk} (h1 : j ≠ sP) (h2 : j ≠ sA) (h3 : j ≠ sT2) :
    (pst4 s).stk j = s.stk j := by simp [pst4, pst3, pst2, pst1, h1, h2, h3]

theorem pstH_stk_sP (s : State) : (pstH s).stk sP = (s.stk sP).headD .eos :: (s.stk sP).tail := by
  simp [pstH, pstH1, pst1]
theorem pstH_reg (s : State) : (pstH s).reg rI = gStop := by simp [pstH, pstH1, pst1]
theorem pstH_stk_other (s : State) {j : Stk} (h1 : j ≠ sP) : (pstH s).stk j = s.stk j := by
  simp [pstH, pstH1, pst1, h1]

theorem ev_shlPassBody_go (main : Cmd) (s : State) (h : s.stk sP = gUnit :: (s.stk sP).tail) :
    Ev main shlPassBody s (pst4 s) 8 := by
  have hhead : (s.stk sP).headD .eos = gUnit := by rw [h]; rfl
  have hne : (s.stk sP).headD .eos ≠ gmk sP := by rw [hhead]; exact unit_ne_markerP
  have h1 : Ev main (.pop sP rX) s (pst1 s) 1 := ev_pop_st main sP rX s
  have h2 : Ev main (pushC sT2 gUnit rY) (pst1 s) (pst2 s) 2 :=
    ev_pushC_st main sT2 gUnit rY (pst1 s)
  have h3 : Ev main (pushC sT2 gUnit rY) (pst2 s) (pst3 s) 2 :=
    ev_pushC_st main sT2 gUnit rY (pst2 s)
  have h4 : Ev main (pushC sA gZero rY) (pst3 s) (pst4 s) 2 :=
    ev_pushC_st main sA gZero rY (pst3 s)
  have hseq : Ev main (seqs [pushC sT2 gUnit rY, pushC sT2 gUnit rY, pushC sA gZero rY])
      (pst1 s) (pst4 s) 6 :=
    Ev.seq' h2 (Ev.seq' h3 h4 (le_rfl)) (by omega)
  have hite : Ev main (seqs [.pop sP rX,
      .ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
        (seqs [pushC sT2 gUnit rY, pushC sT2 gUnit rY, pushC sA gZero rY])])
      s (pst4 s) 8 := Ev.seq' h1 (Ev.iteF hne hseq) (le_rfl)
  exact hite

theorem ev_shlPassBody_hit (main : Cmd) (s : State) (h : s.stk sP = gmk sP :: (s.stk sP).tail) :
    Ev main shlPassBody s (pstH s) 4 := by
  have hhead : (s.stk sP).headD .eos = gmk sP := by rw [h]; rfl
  have h1 : Ev main (.pop sP rX) s (pst1 s) 1 := ev_pop_st main sP rX s
  have h2 : Ev main (.push sP rX) (pst1 s) (pstH1 s) 1 := ev_push_st main sP rX (pst1 s)
  have h3 : Ev main (.set rI gStop) (pstH1 s) (pstH s) 1 := ev_set_st main rI gStop (pstH1 s)
  have hseq : Ev main (seqs [.push sP rX, .set rI gStop]) (pst1 s) (pstH s) 2 :=
    Ev.seq' h2 h3 (le_rfl)
  have hite : Ev main (seqs [.pop sP rX,
      .ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
        (seqs [pushC sT2 gUnit rY, pushC sT2 gUnit rY, pushC sA gZero rY])])
      s (pstH s) 4 := Ev.seq' h1 (Ev.iteT hhead hseq) (le_rfl)
  exact hite

theorem shlPassBody_go_ev (main : Cmd) (s : State) (L : List Glyph) (hL : s.stk sP = gUnit :: L) :
    ∃ (s' : State) (n : ℕ), Eval main shlPassBody s s' n ∧ n ≤ 8 ∧ s'.reg rI = s.reg rI ∧
      s'.stk sP = L ∧ s'.stk sA = gZero :: (s.stk sA) ∧ s'.stk sT2 = gUnit :: gUnit :: (s.stk sT2) ∧
      SameOn s s' {sP, sA, sT2} := by
  have htail : (s.stk sP).tail = L := by rw [hL]; rfl
  obtain ⟨n, he, hn⟩ := ev_shlPassBody_go main s (by rw [hL]; rfl)
  refine ⟨pst4 s, n, he, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pst4_reg_rI]
  · rw [pst4_stk_sP, htail]
  · rw [pst4_stk_sA]
  · rw [pst4_stk_sT2]
  · exact SameOn.of_triple (fun j hj1 hj2 hj3 => pst4_stk_other s hj1 hj2 hj3)

theorem shlPassBody_hit_ev (main : Cmd) (s : State) (JP : List Glyph) (hP : s.stk sP = gmk sP :: JP) :
    ∃ (s' : State) (n : ℕ), Eval main shlPassBody s s' n ∧ n ≤ 4 ∧
      s'.reg rI = gStop ∧ s'.stk sP = gmk sP :: JP ∧ SameOn s s' ({sP} : Finset Stk) := by
  obtain ⟨n, he, hn⟩ := ev_shlPassBody_hit main s (by rw [hP]; rfl)
  refine ⟨pstH s, n, he, by omega, pstH_reg s, ?_, ?_⟩
  · rw [pstH_stk_sP, hP]; rfl
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    exact pstH_stk_other s hj

/-- The `shl` block pass. -/
theorem shlPass_ev (main : Cmd) (p : ℕ) :
    ∀ (A JA JP T0 JT2 : List Glyph) (s : State), AllUnit T0 →
      s.stk sP = List.replicate p gUnit ++ gmk sP :: JP → s.stk sA = A ++ gmk sA :: JA →
      s.stk sT2 = T0 ++ gmk sT2 :: JT2 → s.reg rI = gGo →
      ∃ (s' : State) (n : ℕ) (T' : List Glyph), Eval main (.loop rI gGo shlPassBody) s s' n ∧
        n ≤ 10 * p + 6 ∧ s'.reg rI ≠ gGo ∧
        s'.stk sP = gmk sP :: JP ∧
        s'.stk sA = List.replicate p gZero ++ A ++ gmk sA :: JA ∧
        s'.stk sT2 = T' ++ gmk sT2 :: JT2 ∧ AllUnit T' ∧ T'.length = T0.length + 2 * p ∧
        SameOn s s' {sP, sA, sT2} := by
  intro A JA JP T0 JT2 s
  induction p generalizing A T0 s with
  | zero =>
      intro hU0 hP hA hT hgo
      simp only [List.replicate_zero, List.nil_append] at hP
      obtain ⟨s1, n1, he1, hn1, hr1, hP1, ho1⟩ := shlPassBody_hit_ev main s JP hP
      have hne : s1.reg rI ≠ gGo := by rw [hr1]; exact gStop_ne_gGo
      have hloop : Ev main (.loop rI gGo shlPassBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩ (Ev.loopF (main := main) (s := s1) hne)
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s1, m, T0, hm, ?_, hne, hP1, ?_, ?_, hU0, by omega, ?_⟩
      · omega
      · have h1 := ho1 sA (by simp)
        rw [h1, hA]; simp
      · have h1 := ho1 sT2 (by simp)
        rw [h1, hT]
      · exact ho1.mono (by decide)
  | succ p ih =>
      intro hU0 hP hA hT hgo
      rw [List.replicate_succ] at hP
      obtain ⟨s1, n1, he1, hn1, hreg1, hPs, hAs, hTs, ho1⟩ :=
        shlPassBody_go_ev main s (List.replicate p gUnit ++ gmk sP :: JP) hP
      have hgo1 : s1.reg rI = gGo := by rw [hreg1]; exact hgo
      have hA1 : s1.stk sA = (gZero :: A) ++ gmk sA :: JA := by rw [hAs, hA, List.cons_append]
      have hT1 : s1.stk sT2 = (gUnit :: gUnit :: T0) ++ gmk sT2 :: JT2 := by
        rw [hTs, hT, ← List.cons_append, ← List.cons_append]
      have hU1 : AllUnit (gUnit :: gUnit :: T0) :=
        AllUnit.cons (AllUnit.cons hU0)
      obtain ⟨s2, n2, T', he2, hn2, hr2, hP2, hA2, hT2', hUT', hlen, ho2⟩ :=
        ih (gZero :: A) (gUnit :: gUnit :: T0) s1 hU1 hPs hA1 hT1 hgo1
      have hloop : Ev main (.loop rI gGo shlPassBody) s s2 (n1 + n2 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩ ⟨n2, he2, le_rfl⟩
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s2, m, T', hm, ?_, hr2, hP2, ?_, ?_, hUT', ?_, ?_⟩
      · omega
      · show s2.stk sA = List.replicate (p + 1) gZero ++ A ++ gmk sA :: JA
        rw [hA2, replicate_append_cons]
      · exact hT2'
      · simp only [List.length_cons] at *
        omega
      · exact (ho1.trans ho2).union_self


/-! ## Register frames -/

/-- The set of registers a program may write. -/
def cmdRegs : Cmd → Finset Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov d _ => {d}
  | .seq a b => cmdRegs a ∪ cmdRegs b
  | .ite r _ a b => insert r (cmdRegs a ∪ cmdRegs b)
  | .loop r _ a => insert r (cmdRegs a)
  | .self => Finset.univ

/-- A program never writes a register outside `cmdRegs`. -/
theorem Eval_reg_frame {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) :
    ∀ {r : Reg}, r ∉ cmdRegs c → s'.reg r = s.reg r := by
  induction h with
  | skip s => intro r _; rfl
  | pop k r' s =>
      intro r hr
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | peek k r' s =>
      intro r hr
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | push k r' s => intro r _; rfl
  | set r' c s =>
      intro r hr
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | mov dst src s =>
      intro r hr
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | seq h1 h2 ih1 ih2 =>
      intro r hr
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      rw [ih2 hr.2, ih1 hr.1]
  | iteT hr' h ih =>
      intro r hr
      simp only [cmdRegs, Finset.mem_insert, Finset.mem_union, not_or] at hr
      exact ih hr.2.1
  | iteF hr' h ih =>
      intro r hr
      simp only [cmdRegs, Finset.mem_insert, Finset.mem_union, not_or] at hr
      exact ih hr.2.2
  | loopF hr' => intro r _; rfl
  | loopT hr' h1 h2 ih1 ih2 =>
      intro r hr
      refine (ih2 hr).trans (ih1 (fun hc => hr ?_))
      simp only [cmdRegs]
      exact Finset.mem_insert_of_mem hc
  | self h ih =>
      intro r hr
      simp only [cmdRegs] at hr
      exact absurd (Finset.mem_univ r) hr

/-- `SameOn` for the registers: the registers outside `S` are unchanged. -/
def SameReg (s s' : State) (S : Finset Reg) : Prop := ∀ r : Reg, r ∉ S → s'.reg r = s.reg r

theorem SameReg.of_frame {main : Cmd} {s s' : State} {c : Cmd} {n : ℕ} (h : Eval main c s s' n)
    {S : Finset Reg} (hS : cmdRegs c ⊆ S) : SameReg s s' S :=
  fun r hr => Eval_reg_frame h (fun hc => hr (hS hc))

theorem SameReg.mono {s s' : State} {S S' : Finset Reg} (h : SameReg s s' S) (hSS : S ⊆ S') :
    SameReg s s' S' := fun r hr => h r (fun h' => hr (hSS h'))

theorem SameReg.trans {s s' s'' : State} {S S' : Finset Reg} (h1 : SameReg s s' S)
    (h2 : SameReg s' s'' S') : SameReg s s'' (S ∪ S') := by
  intro r hr
  rw [h2 r (fun h => hr (Finset.mem_union_right S h)), h1 r (fun h => hr (Finset.mem_union_left S' h))]

theorem SameReg.refl' (s : State) (S : Finset Reg) : SameReg s s S := fun _ _ => rfl

end Shift
end Work.IntLib
