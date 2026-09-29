import Mathlib
import Submission.Work.IntLib.Shift.ShlLoop
import Submission.Work.IntLib.Shift.shrPass_ev

/-! # `IntLib` / shift words: the `shr` outer loop -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH


/-! ## Helpers -/

theorem ev_pop_eq (main : Cmd) (k : Stk) (r : Reg) (s : State) (g : Glyph) (l : List Glyph)
    (h : s.stk k = g :: l) :
    Ev main (.pop k r) s ⟨Function.update s.reg r g, Function.update s.stk k l⟩ 1 := by
  have h1 : (s.stk k).headD .eos = g := by rw [h]; rfl
  have h2 : (s.stk k).tail = l := by rw [h]; rfl
  have h' := ev_pop_st main k r s
  rwa [h1, h2] at h'

theorem mst3_reg_rE (s : State) : (mst3 s).reg rE = s.reg rE := by
  rw [mst3_reg_other (by decide : rE ≠ rI), mst2_reg_other (by decide : rE ≠ rW),
    mst1_reg_other (by decide : rE ≠ rX)]

theorem mst3_reg_rD (s : State) : (mst3 s).reg rD = s.reg rD := by
  rw [mst3_reg_other (by decide : rD ≠ rI), mst2_reg_other (by decide : rD ≠ rW),
    mst1_reg_other (by decide : rD ≠ rX)]

theorem take_add' {α : Type} (l : List α) (n m : ℕ) :
    l.take (n + m) = l.take n ++ (l.drop n).take m := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [show n + 1 + m = (n + m) + 1 by omega]
          simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
          rw [ih n]

theorem mem_take_add {l : List Bool} {n m : ℕ} :
    true ∈ l.take (n + m) ↔ true ∈ l.take n ∨ true ∈ (l.drop n).take m := by
  rw [take_add' l n m, List.mem_append]

theorem drop_two (bs : List Bool) (p : ℕ) : (bs.drop p).drop p = bs.drop (2 * p) := by
  rw [List.drop_drop, two_mul]

theorem mem_take_two (bs : List Bool) (p : ℕ) :
    true ∈ bs.take (2 * p) ↔ true ∈ bs.take p ∨ true ∈ (bs.drop p).take p := by
  rw [two_mul]; exact mem_take_add

theorem mem_split (bs : List Bool) (p : ℕ) :
    true ∈ bs ↔ true ∈ bs.take p ∨ true ∈ bs.drop p := by
  conv_lhs => rw [← List.take_append_drop p bs]
  rw [List.mem_append]

theorem take_one_cons (b : Bool) (t : List Bool) : true ∈ (b :: t).take 1 ↔ b = true := by
  cases b <;> simp

theorem allUnit_nil' : ∀ h ∈ ([] : List Glyph), h = gUnit := AllUnit.nil

/-- Cost of the `shr` main loop, mirroring the program: the block length `p`, the remaining bits
`m`, and the list `R` of the bits of `k` that are still to be read. -/
def shrLoopCost : ℕ → List Bool → ℕ → ℕ
  | _, [], _ => 12
  | p, b :: bs, m => 121 * (min p m + 1) + shrLoopCost (2 * p + b.toNat) bs (m - (p + b.toNat))

theorem shrLoopCost_ge (p : ℕ) (R : List Bool) (m : ℕ) : 12 ≤ shrLoopCost p R m := by
  cases R with
  | nil => simp only [shrLoopCost]; omega
  | cons b bs => simp only [shrLoopCost]; omega

theorem shrLoopCost_le (p : ℕ) (R : List Bool) (m : ℕ) :
    shrLoopCost p R m ≤ 400 * (m + R.length + 2) := by
  induction R generalizing p m with
  | nil => simp only [shrLoopCost, List.length_nil]; omega
  | cons b bs ih =>
      simp only [shrLoopCost, List.length_cons]
      by_cases h : p + b.toNat ≤ m
      · have h2 : min p m = p := Nat.min_eq_left (by omega)
        rw [h2]
        have := ih (2 * p + b.toNat) (m - (p + b.toNat))
        omega
      · have h1 : m - (p + b.toNat) = 0 := by omega
        rw [h1]
        have := ih (2 * p + b.toNat) 0
        have hmin : min p m ≤ m := Nat.min_le_right p m
        omega

/-! ## The extra unit -/

theorem shrExtra_ev (main : Cmd) (s : State) (bs : List Bool) (T0 JM JT2 : List Glyph)
    (hTg : ∀ h ∈ T0, h = gUnit)
    (hM : s.stk sM = bs.map Glyph.bit ++ gmk sM :: JM)
    (hT : s.stk sT2 = T0 ++ gmk sT2 :: JT2) :
    ∃ (s' : State) (n : ℕ), Eval main shrExtraBody s s' n ∧ n ≤ 8 ∧
      s'.stk sM = (bs.drop 1).map Glyph.bit ++ gmk sM :: JM ∧
      s'.stk sT2 = (if bs = [] then T0 else gUnit :: T0) ++ gmk sT2 :: JT2 ∧
      ((s'.reg rD = gAny) ↔ (s.reg rD = gAny ∨ true ∈ bs.take 1)) ∧
      (bs = [] → s'.reg rE = gStop) ∧ (bs ≠ [] → s'.reg rE = s.reg rE) ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = s.stk j) := by
  cases bs with
  | nil =>
      have hM' : s.stk sM = gmk sM :: JM := by simpa using hM
      have hpop : Ev main (.pop sM rX) s
          ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM JM⟩ 1 :=
        ev_pop_eq main sM rX s (gmk sM) JM hM'
      have hreg : (⟨Function.update s.reg rX (gmk sM),
          Function.update s.stk sM JM⟩ : State).reg rX = gmk sM :=
        Function.update_self rX (gmk sM) s.reg
      have hpush : Ev main (.push sM rX)
          ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM JM⟩
          ⟨Function.update s.reg rX (gmk sM),
            Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)⟩ 1 :=
        ev_push_st main sM rX _
      have hset : Ev main (.set rE gStop)
          ⟨Function.update s.reg rX (gmk sM),
            Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)⟩
          ⟨Function.update (Function.update s.reg rX (gmk sM)) rE gStop,
            Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)⟩ 1 :=
        ev_set_st main rE gStop _
      have hbr : Ev main (seqs [.push sM rX, .set rE gStop])
          ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM JM⟩
          ⟨Function.update (Function.update s.reg rX (gmk sM)) rE gStop,
            Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)⟩ 2 := by
        rw [seqs_pair]; exact Ev.seq' hpush hset (le_rfl)
      have hbody : Ev main shrExtraBody s
          ⟨Function.update (Function.update s.reg rX (gmk sM)) rE gStop,
            Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)⟩ 4 := by
        rw [shrExtraBody, seqs_pair]
        exact Ev.seq' hpop (Ev.iteT hreg hbr) (le_rfl)
      obtain ⟨n, he, hn⟩ := hbody
      refine ⟨_, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)) sM = gmk sM :: JM
        rw [upStk_same]
      · show (Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)) sT2
            = (if ([] : List Bool) = [] then T0 else gUnit :: T0) ++ gmk sT2 :: JT2
        rw [upStk_ne (by decide : sT2 ≠ sM), upStk_ne (by decide : sT2 ≠ sM), hT]
        simp
      · show (Function.update (Function.update s.reg rX (gmk sM)) rE gStop) rD = gAny ↔
            (s.reg rD = gAny ∨ true ∈ ([] : List Bool).take 1)
        rw [upReg_ne (by decide : rD ≠ rE), upReg_ne (by decide : rD ≠ rX)]
        simp
      · intro _
        show (Function.update (Function.update s.reg rX (gmk sM)) rE gStop) rE = gStop
        rw [upReg_same]
      · intro h; exact absurd rfl h
      · intro j hj1 hj2
        show (Function.update (Function.update s.stk sM JM) sM (gmk sM :: JM)) j = s.stk j
        rw [upStk_ne hj1, upStk_ne hj1]
  | cons b t =>
      have hM' : s.stk sM = Glyph.bit b :: t.map Glyph.bit ++ gmk sM :: JM := by
        rw [hM]; rfl
      have hpop : Ev main (.pop sM rX) s
          ⟨Function.update s.reg rX (Glyph.bit b),
            Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ 1 :=
        ev_pop_eq main sM rX s (Glyph.bit b) (t.map Glyph.bit ++ gmk sM :: JM) hM'
      have hne_out : (⟨Function.update s.reg rX (Glyph.bit b),
          Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ : State).reg rX ≠ gmk sM := by
        show Function.update s.reg rX (Glyph.bit b) rX ≠ gmk sM
        rw [Function.update_self]
        exact bit_ne_marker b sM
      cases b with
      | false =>
          have hne_in : (⟨Function.update s.reg rX (Glyph.bit false),
              Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ : State).reg rX
              ≠ Glyph.bit true := by
            show Function.update s.reg rX (Glyph.bit false) rX ≠ Glyph.bit true
            rw [Function.update_self]; decide
          have hskip : Ev main (.ite rX (Glyph.bit true) (.set rD gAny) .skip)
              ⟨Function.update s.reg rX (Glyph.bit false),
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩
              ⟨Function.update s.reg rX (Glyph.bit false),
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ 2 :=
            Ev.iteF hne_in (ev_skip_st main _)
          have hpush : Ev main (pushC sT2 gUnit rY)
              ⟨Function.update s.reg rX (Glyph.bit false),
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩
              ⟨Function.update (Function.update s.reg rX (Glyph.bit false)) rY gUnit,
                Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                  (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)⟩ 2 :=
            ev_pushC_st main sT2 gUnit rY _
          have hbody : Ev main shrExtraBody s
              ⟨Function.update (Function.update s.reg rX (Glyph.bit false)) rY gUnit,
                Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                  (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)⟩ 6 := by
            rw [shrExtraBody, seqs_pair]
            have hseq : Ev main (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
                pushC sT2 gUnit rY]) _ _ 4 := Ev.seq' hskip hpush (le_rfl)
            have hite : Ev main (.ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop])
                (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip, pushC sT2 gUnit rY])) _ _ 5 :=
              Ev.iteF hne_out hseq
            exact Ev.seq' hpop hite (by omega)
          obtain ⟨n, he, hn⟩ := hbody
          have hsT2 : (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
              = T0 ++ gmk sT2 :: JT2 := by
            rw [upStk_ne (by decide : sT2 ≠ sM), hT]
          refine ⟨_, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) sM
                = ((false :: t).drop 1).map Glyph.bit ++ gmk sM :: JM
            rw [upStk_ne (by decide : sM ≠ sT2), upStk_same]
            rfl
          · show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) sT2
                = (if (false :: t) = [] then T0 else gUnit :: T0) ++ gmk sT2 :: JT2
            rw [upStk_same, hsT2]
            simp
          · show (Function.update (Function.update s.reg rX (Glyph.bit false)) rY gUnit) rD = gAny ↔
                (s.reg rD = gAny ∨ true ∈ (false :: t).take 1)
            rw [upReg_ne (by decide : rD ≠ rY), upReg_ne (by decide : rD ≠ rX)]
            simp [take_one_cons false t]
          · intro h; exact absurd h (List.cons_ne_nil false t)
          · intro _
            show (Function.update (Function.update s.reg rX (Glyph.bit false)) rY gUnit) rE = s.reg rE
            rw [upReg_ne (by decide : rE ≠ rY), upReg_ne (by decide : rE ≠ rX)]
          · intro j hj1 hj2
            show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
              (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) j = s.stk j
            rw [upStk_ne hj2, upStk_ne hj1]
      | true =>
          have hgt : (⟨Function.update s.reg rX (Glyph.bit true),
              Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ : State).reg rX
              = Glyph.bit true := by
            show Function.update s.reg rX (Glyph.bit true) rX = Glyph.bit true
            rw [Function.update_self]
          have hset : Ev main (.set rD gAny)
              ⟨Function.update s.reg rX (Glyph.bit true),
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩
              ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny,
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩ 1 :=
            ev_set_st main rD gAny _
          have hpush : Ev main (pushC sT2 gUnit rY)
              ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny,
                Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)⟩
              ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny)
                  rY gUnit,
                Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                  (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)⟩ 2 :=
            ev_pushC_st main sT2 gUnit rY _
          have hbody : Ev main shrExtraBody s
              ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny)
                  rY gUnit,
                Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                  (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)⟩ 6 := by
            rw [shrExtraBody, seqs_pair]
            have hseq : Ev main (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
                pushC sT2 gUnit rY]) _ _ 4 := Ev.seq' (Ev.iteT hgt hset) hpush (le_rfl)
            have hite : Ev main (.ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop])
                (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip, pushC sT2 gUnit rY])) _ _ 5 :=
              Ev.iteF hne_out hseq
            exact Ev.seq' hpop hite (by omega)
          obtain ⟨n, he, hn⟩ := hbody
          have hsT2 : (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
              = T0 ++ gmk sT2 :: JT2 := by
            rw [upStk_ne (by decide : sT2 ≠ sM), hT]
          refine ⟨_, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) sM
                = ((true :: t).drop 1).map Glyph.bit ++ gmk sM :: JM
            rw [upStk_ne (by decide : sM ≠ sT2), upStk_same]
            rfl
          · show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
                (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) sT2
                = (if (true :: t) = [] then T0 else gUnit :: T0) ++ gmk sT2 :: JT2
            rw [upStk_same, hsT2]
            simp
          · show (Function.update (Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny)
                rY gUnit) rD = gAny ↔ (s.reg rD = gAny ∨ true ∈ (true :: t).take 1)
            rw [upReg_ne (by decide : rD ≠ rY), upReg_same]
            simp [take_one_cons true t]
          · intro h; exact absurd h (List.cons_ne_nil true t)
          · intro _
            show (Function.update (Function.update (Function.update s.reg rX (Glyph.bit true)) rD gAny)
                rY gUnit) rE = s.reg rE
            rw [upReg_ne (by decide : rE ≠ rY), upReg_ne (by decide : rE ≠ rD),
              upReg_ne (by decide : rE ≠ rX)]
          · intro j hj1 hj2
            show (Function.update (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2
              (gUnit :: (Function.update s.stk sM (t.map Glyph.bit ++ gmk sM :: JM)) sT2)) j = s.stk j
            rw [upStk_ne hj2, upStk_ne hj1]

/-! ## The stop branch of the outer loop -/

theorem shrStop_ev (main : Cmd) (s : State) (JK : List Glyph) (hK : s.stk sK = gmk sK :: JK) :
    ∃ (s' : State) (n : ℕ), Eval main shrOuterBody s s' n ∧ n ≤ 6 ∧ s'.reg rO = gStop ∧
      s'.stk sK = gmk sK :: JK ∧ s'.stk sP = s.stk sP ∧ s'.stk sM = s.stk sM ∧
      s'.stk sT2 = s.stk sT2 ∧ s'.reg rD = s.reg rD ∧
      SameOn s s' ({sK, sP, sM, sT2} : Finset Stk) := by
  have hhead : (s.stk sK).headD .eos = gmk sK := by rw [hK]; rfl
  have hpop : Ev main (.pop sK rX) s (mst1 s) 1 := ev_pop_st main sK rX s
  have hmov : Ev main (.mov rW rX) (mst1 s) (mst2 s) 1 := ev_mov_st main rW rX (mst1 s)
  have htest : (mst2 s).reg rW = gmk sK := by rw [mst2_reg_rW, hhead]
  have hpush : Ev main (.push sK rW) (mst2 s)
      ⟨(mst2 s).reg, Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)⟩ 1 :=
    ev_push_st main sK rW (mst2 s)
  have hset : Ev main (.set rO gStop)
      ⟨(mst2 s).reg, Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)⟩
      ⟨Function.update (mst2 s).reg rO gStop,
        Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)⟩ 1 :=
    ev_set_st main rO gStop _
  have hpush2 : Ev main (seqs [.push sK rW, .set rO gStop]) (mst2 s) _ 2 :=
    Ev.seq' hpush hset (le_rfl)
  have hite : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
      (seqs [.set rI gGo, .loop rI gGo shrPassBody,
        .ite rE gStop (seqs [.set rO gStop])
          (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                 .ite rE gStop (seqs [.set rO gStop])
                   (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])) (mst2 s) _ 3 :=
    Ev.iteT htest hpush2
  have eAll : Ev main (seqs [.pop sK rX, .mov rW rX,
      .ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
        (seqs [.set rI gGo, .loop rI gGo shrPassBody,
          .ite rE gStop (seqs [.set rO gStop])
            (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                   .ite rE gStop (seqs [.set rO gStop])
                     (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])]) s _ 5 :=
    Ev.seq' hpop (Ev.seq' hmov hite (le_rfl)) (le_rfl)
  obtain ⟨n, he, hn⟩ := eAll
  have hr : (Function.update (mst2 s).reg rO gStop) rO = gStop := upReg_same rO gStop
  have hsp : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sK
      = gmk sK :: JK := by rw [upStk_same, mst2_reg_rW, hhead, mst2_stk_sK, hK]; rfl
  have h1 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sP
      = s.stk sP := by rw [upStk_ne (by decide : sP ≠ sK), mst2_stk_other (by decide : sP ≠ sK)]
  have h2 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sM
      = s.stk sM := by rw [upStk_ne (by decide : sM ≠ sK), mst2_stk_other (by decide : sM ≠ sK)]
  have h3 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sT2
      = s.stk sT2 := by rw [upStk_ne (by decide : sT2 ≠ sK), mst2_stk_other (by decide : sT2 ≠ sK)]
  have h4 : SameOn s ⟨Function.update (mst2 s).reg rO gStop,
      Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)⟩
      ({sK, sP, sM, sT2} : Finset Stk) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hj
    show (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) j = s.stk j
    rw [upStk_ne hj1, mst2_stk_other hj1]
  have hrd : (Function.update (mst2 s).reg rO gStop) rD = s.reg rD := by
    rw [upReg_ne (by decide : rD ≠ rO), mst2_reg_other (by decide : rD ≠ rW),
      mst1_reg_other (by decide : rD ≠ rX)]
  exact ⟨_, n, he, by omega, hr, hsp, h1, h2, h3, hrd, h4⟩

/-! ## One iteration of the outer loop -/

theorem shrStep_ev (main : Cmd) (R' : List Bool) (b : Bool) (p : ℕ) (bs : List Bool) (s : State)
    (JK JP JM JT2 : List Glyph)
    (hK : s.stk sK = (b :: R').map Glyph.bit ++ gmk sK :: JK)
    (hP : s.stk sP = List.replicate p gUnit ++ gmk sP :: JP)
    (hM : s.stk sM = (bs.drop p).map Glyph.bit ++ gmk sM :: JM)
    (hT : s.stk sT2 = gmk sT2 :: JT2)
    (hO : s.reg rO = gGo) (hE : s.reg rE = gNo)
    (hD : (s.reg rD = gAny) ↔ (true ∈ bs.take p))
    (hle : p ≤ bs.length) :
    ∃ (s' : State) (n : ℕ), Eval main shrOuterBody s s' n ∧
      n ≤ 120 * (min p ((bs.drop p).length) + 1) ∧
      s'.stk sK = R'.map Glyph.bit ++ gmk sK :: JK ∧
      SameOn s s' ({sK, sP, sM, sT2} : Finset Stk) ∧
      ( (s'.reg rO = gGo ∧ s'.reg rE = gNo ∧ 2 * p + b.toNat ≤ bs.length ∧
         s'.stk sP = List.replicate (2 * p + b.toNat) gUnit ++ gmk sP :: JP ∧
         s'.stk sM = (bs.drop (2 * p + b.toNat)).map Glyph.bit ++ gmk sM :: JM ∧
         s'.stk sT2 = gmk sT2 :: JT2 ∧
         ((s'.reg rD = gAny) ↔ (true ∈ bs.take (2 * p + b.toNat))))
        ∨ (s'.reg rO = gStop ∧ s'.reg rE = gStop ∧ s'.stk sM = gmk sM :: JM ∧
         ((s'.reg rD = gAny) ↔ (true ∈ bs)) ∧ bs.length ≤ 2 * p ∧
         ∃ (P' T2' : List Glyph), s'.stk sP = P' ++ gmk sP :: JP ∧
           s'.stk sT2 = T2' ++ gmk sT2 :: JT2 ∧ (∀ h ∈ P', h = gUnit) ∧
           (∀ h ∈ T2', h = gUnit) ∧ P'.length + T2'.length ≤ bs.length + 2) ) := by
  have hK' : s.stk sK = Glyph.bit b :: (R'.map Glyph.bit ++ gmk sK :: JK) := by rw [hK]; rfl
  have hpop : Ev main (.pop sK rX) s (mst1 s) 1 := ev_pop_st main sK rX s
  have hmov : Ev main (.mov rW rX) (mst1 s) (mst2 s) 1 := ev_mov_st main rW rX (mst1 s)
  have hset : Ev main (.set rI gGo) (mst2 s) (mst3 s) 1 := ev_set_st main rI gGo (mst2 s)
  have hW2 : (mst2 s).reg rW = Glyph.bit b := by rw [mst2_reg_rW, hK']; rfl
  have htest : (mst2 s).reg rW ≠ gmk sK := by rw [hW2]; exact bit_ne_marker b sK
  have hs3K : (mst3 s).stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by rw [mst3_stk_sK, hK']; rfl
  have hs3P : (mst3 s).stk sP = List.replicate p gUnit ++ gmk sP :: JP := by
    rw [mst3_stk_other (by decide : sP ≠ sK)]; exact hP
  have hs3M : (mst3 s).stk sM = (bs.drop p).map Glyph.bit ++ gmk sM :: JM := by
    rw [mst3_stk_other (by decide : sM ≠ sK)]; exact hM
  have hs3T : (mst3 s).stk sT2 = ([] : List Glyph) ++ gmk sT2 :: JT2 := by
    rw [mst3_stk_other (by decide : sT2 ≠ sK)]; exact hT
  have hs3E : (mst3 s).reg rE = gNo := by rw [mst3_reg_rE]; exact hE
  have hs3D : ((mst3 s).reg rD = gAny) ↔ (true ∈ bs.take p) := by rw [mst3_reg_rD]; exact hD
  have hs3O : (mst3 s).reg rO = gGo := by rw [mst3_reg_rO]; exact hO
  obtain ⟨s4, n4, he4, hn4, hrI4, hP4, hM4, hT4, hE4a, hE4b, hD4, ho4⟩ :=
    shrPass_ev main p (bs.drop p) ([] : List Glyph) JP JM JT2 (mst3 s) allUnit_nil' hs3P hs3M
      hs3T mst3_reg_rI
  have hlen : (bs.drop p).length = bs.length - p := List.length_drop ..
  rcases lt_or_ge (bs.drop p).length p with hlt | hge
  · -- Case A: the bits of `a` run out inside the block pass
    have hE4stop : s4.reg rE = gStop := hE4b hlt
    have hmin : min p (bs.drop p).length = (bs.drop p).length := Nat.min_eq_right (le_of_lt hlt)
    have hif : (if p ≤ (bs.drop p).length then 0 else 1) = 1 := if_neg (not_le.mpr hlt)
    have hP4' : s4.stk sP = List.replicate (p - ((bs.drop p).length + 1)) gUnit ++ gmk sP :: JP := by
      rw [hP4, hmin, hif]
    have hT4' : s4.stk sT2 = List.replicate (2 * ((bs.drop p).length)) gUnit ++ gmk sT2 :: JT2 := by
      rw [hT4, hmin, List.nil_append]
    have hM4' : s4.stk sM = gmk sM :: JM := by
      rw [hM4, hmin, List.drop_eq_nil_of_le (le_refl (bs.drop p).length)]
      rfl
    have hD4' : (s4.reg rD = gAny) ↔ (true ∈ bs) := by
      have h2 : (s4.reg rD = gAny) ↔ ((mst3 s).reg rD = gAny ∨ true ∈ bs.drop p) := by
        rw [hD4, hmin, List.take_length]
      rw [h2, hs3D, mem_split bs p]
    have eSetO : Ev main (.set rO gStop) s4 ⟨Function.update s4.reg rO gStop, s4.stk⟩ 1 :=
      ev_set_st main rO gStop s4
    have eIteA : Ev main (.ite rE gStop (seqs [.set rO gStop])
        (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
               .ite rE gStop (seqs [.set rO gStop])
                 (seqs [drain sT2 sP (gmk sT2) rZ rJ])])) s4
        ⟨Function.update s4.reg rO gStop, s4.stk⟩ 2 := Ev.iteT hE4stop eSetO
    have eLoop4 : Ev main (.loop rI gGo shrPassBody) (mst3 s) s4 n4 := ⟨n4, he4, le_rfl⟩
    have eInnerA : Ev main (seqs [.set rI gGo, .loop rI gGo shrPassBody,
        .ite rE gStop (seqs [.set rO gStop])
          (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                 .ite rE gStop (seqs [.set rO gStop])
                   (seqs [drain sT2 sP (gmk sT2) rZ rJ])])]) (mst2 s)
        ⟨Function.update s4.reg rO gStop, s4.stk⟩ (1 + (n4 + 2)) :=
      Ev.seq' hset (Ev.seq' eLoop4 eIteA (le_rfl)) (le_rfl)
    have eIteA2 : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
        (seqs [.set rI gGo, .loop rI gGo shrPassBody,
          .ite rE gStop (seqs [.set rO gStop])
            (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                   .ite rE gStop (seqs [.set rO gStop])
                     (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])) (mst2 s)
        ⟨Function.update s4.reg rO gStop, s4.stk⟩ ((1 + (n4 + 2)) + 1) := Ev.iteF htest eInnerA
    have eAllA : Ev main shrOuterBody s ⟨Function.update s4.reg rO gStop, s4.stk⟩
        (1 + (1 + ((1 + (n4 + 2)) + 1))) :=
      Ev.seq' hpop (Ev.seq' hmov eIteA2 (le_rfl)) (le_rfl)
    obtain ⟨nn, hev, hnle⟩ := eAllA
    have hK3 : (⟨Function.update s4.reg rO gStop, s4.stk⟩ : State).stk sK
        = R'.map Glyph.bit ++ gmk sK :: JK := by
      show s4.stk sK = _
      rw [ho4 sK (by decide : sK ≠ sP) (by decide : sK ≠ sM) (by decide : sK ≠ sT2)]
      exact hs3K
    have hframe : SameOn s ⟨Function.update s4.reg rO gStop, s4.stk⟩
        ({sK, sP, sM, sT2} : Finset Stk) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      obtain ⟨h1, h2, h3, h4⟩ := hj
      show s4.stk j = s.stk j
      rw [ho4 j h2 h3 h4, (SameOn.mst3 s) j (by simpa using h1)]
    refine ⟨_, nn, hev, by omega, hK3, hframe, Or.inr ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_,
      List.replicate (p - ((bs.drop p).length + 1)) gUnit,
      List.replicate (2 * ((bs.drop p).length)) gUnit, ?_, ?_,
      allUnit_replicate _, allUnit_replicate _, ?_⟩
    · show (Function.update s4.reg rO gStop) rO = gStop
      rw [upReg_same]
    · show (Function.update s4.reg rO gStop) rE = gStop
      rw [upReg_ne (by decide : rE ≠ rO)]; exact hE4stop
    · show s4.stk sM = gmk sM :: JM; exact hM4'
    · show ((Function.update s4.reg rO gStop) rD = gAny) ↔ (true ∈ bs)
      rw [upReg_ne (by decide : rD ≠ rO)]; exact hD4'
    · omega
    · exact hP4'
    · exact hT4'
    · simp only [List.length_replicate]
      omega
  · -- Case B: the whole block is consumed
    have hmin : min p (bs.drop p).length = p := Nat.min_eq_left hge
    have hif : (if p ≤ (bs.drop p).length then 0 else 1) = 0 := if_pos hge
    have hE4gno : s4.reg rE = gNo := by rw [hE4a hge]; exact hs3E
    have hP4e : s4.stk sP = gmk sP :: JP := by
      rw [hP4, hmin, hif]; simp
    have hM4e : s4.stk sM = (bs.drop (2 * p)).map Glyph.bit ++ gmk sM :: JM := by
      rw [hM4, hmin, drop_two]
    have hT4e : s4.stk sT2 = List.replicate (2 * p) gUnit ++ gmk sT2 :: JT2 := by
      rw [hT4, hmin, List.nil_append]
    have hD4e : (s4.reg rD = gAny) ↔ (true ∈ bs.take (2 * p)) := by
      have h2 : (s4.reg rD = gAny) ↔ (true ∈ bs.take p ∨ true ∈ (bs.drop p).take p) := by
        rw [hD4, hmin, hs3D]
      rw [h2, ← mem_take_two bs p]
    have hE4ne : s4.reg rE ≠ gStop := by rw [hE4gno]; decide
    have hW4 : s4.reg rW = Glyph.bit b := by
      rw [Eval_reg_frame he4 (by decide : rW ∉ cmdRegs (Cmd.loop rI gGo shrPassBody)),
        mst3_reg_rW, hK']; rfl
    have hK4 : s4.stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by
      rw [ho4 sK (by decide : sK ≠ sP) (by decide : sK ≠ sM) (by decide : sK ≠ sT2)]
      exact hs3K
    have hframe4 : SameOn s s4 ({sK, sP, sM, sT2} : Finset Stk) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      obtain ⟨h1, h2, h3, h4⟩ := hj
      rw [ho4 j h2 h3 h4, (SameOn.mst3 s) j (by simpa using h1)]
    cases b with
    | false =>
        have hne' : s4.reg rW ≠ Glyph.bit true := by rw [hW4]; decide
        have eSkip : Ev main (.ite rW (Glyph.bit true) shrExtraBody .skip) s4 s4 2 :=
          Ev.iteF hne' (ev_skip_st main s4)
        obtain ⟨s6, n6, he6, hn6, hT6, hP6, ho6⟩ :=
          shlDrain_ev main s4 (List.replicate (2 * p) gUnit) JP JT2
            (allUnit_replicate (2 * p)) hT4e hP4e
        have eIte2 : Ev main (.ite rE gStop (seqs [.set rO gStop])
            (seqs [drain sT2 sP (gmk sT2) rZ rJ])) s4 s6 (n6 + 1) :=
          Ev.iteF hE4ne ⟨n6, he6, le_rfl⟩
        have eB : Ev main (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
            .ite rE gStop (seqs [.set rO gStop])
              (seqs [drain sT2 sP (gmk sT2) rZ rJ])]) s4 s6 (2 + (n6 + 1)) :=
          Ev.seq' eSkip eIte2 (le_rfl)
        have eOuterIte : Ev main (.ite rE gStop (seqs [.set rO gStop])
            (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                   .ite rE gStop (seqs [.set rO gStop])
                     (seqs [drain sT2 sP (gmk sT2) rZ rJ])])) s4 s6 ((2 + (n6 + 1)) + 1) :=
          Ev.iteF hE4ne eB
        have eInnerB : Ev main (seqs [.set rI gGo, .loop rI gGo shrPassBody,
            .ite rE gStop (seqs [.set rO gStop])
              (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                     .ite rE gStop (seqs [.set rO gStop])
                       (seqs [drain sT2 sP (gmk sT2) rZ rJ])])]) (mst2 s) s6
            (1 + (n4 + ((2 + (n6 + 1)) + 1))) :=
          Ev.seq' hset (Ev.seq' (⟨n4, he4, le_rfl⟩ : Ev main (.loop rI gGo shrPassBody)
            (mst3 s) s4 n4) eOuterIte (le_rfl)) (le_rfl)
        have eIteB : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
            (seqs [.set rI gGo, .loop rI gGo shrPassBody,
              .ite rE gStop (seqs [.set rO gStop])
                (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                       .ite rE gStop (seqs [.set rO gStop])
                         (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])) (mst2 s) s6
            (1 + (n4 + ((2 + (n6 + 1)) + 1)) + 1) := Ev.iteF htest eInnerB
        have eAllB : Ev main shrOuterBody s s6
            (1 + (1 + ((1 + (n4 + ((2 + (n6 + 1)) + 1))) + 1))) :=
          Ev.seq' hpop (Ev.seq' hmov eIteB (le_rfl)) (le_rfl)
        obtain ⟨nn, hev, hnle⟩ := eAllB
        have hn6' : n6 ≤ 10 * p + 7 := by rw [List.length_replicate] at hn6; omega
        have hK6 : s6.stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by
          rw [ho6 sK (by decide : sK ∉ ({sT2, sP} : Finset Stk)), hK4]
        have hro6 : s6.reg rO = gGo := by
          rw [Eval_reg_frame he6 (by decide : rO ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ)),
            Eval_reg_frame he4 (by decide : rO ∉ cmdRegs (Cmd.loop rI gGo shrPassBody)), hs3O]
        have hre6 : s6.reg rE = gNo := by
          rw [Eval_reg_frame he6 (by decide : rE ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ)), hE4gno]
        have hrd6 : s6.reg rD = s4.reg rD :=
          Eval_reg_frame he6 (by decide : rD ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ))
        have hframe6 : SameOn s s6 ({sK, sP, sM, sT2} : Finset Stk) :=
          (hframe4.trans ho6).mono (by decide)
        refine ⟨_, nn, hev, by omega, hK6, hframe6, Or.inl ?_⟩
        refine ⟨hro6, hre6, ?_, ?_, ?_, hT6, ?_⟩
        · simp only [Bool.toNat_false, Nat.add_zero]; omega
        · rw [hP6, List.reverse_replicate]; simp
        · rw [ho6 sM (by decide : sM ∉ ({sT2, sP} : Finset Stk)), hM4e]; simp
        · rw [hrd6, hD4e]; simp
    | true =>
        have hgt : s4.reg rW = Glyph.bit true := by rw [hW4]
        have hlen2p : (bs.drop (2 * p)).length = bs.length - 2 * p := List.length_drop ..
        by_cases hemp : bs.drop (2 * p) = []
        · -- the extra unit finds the exhausted magnitude region
          have h2p : 2 * p = bs.length := by
            have h5 : (bs.drop (2 * p)).length = 0 := by rw [hemp]; rfl
            rw [hlen2p] at h5; omega
          have hM4s : s4.stk sM = ([] : List Bool).map Glyph.bit ++ gmk sM :: JM := by
            rw [hM4e, hemp]
          obtain ⟨s5, n5, he5, hn5, h5M, h5T, h5D, h5E, -, h5frame⟩ :=
            shrExtra_ev main s4 (bs.drop (2 * p)) (List.replicate (2 * p) gUnit) JM JT2
              (allUnit_replicate (2 * p)) hM4e hT4e
          have hrg : s5.reg rE = gStop := h5E hemp
          have eSetO5 : Ev main (.set rO gStop) s5 ⟨Function.update s5.reg rO gStop, s5.stk⟩ 1 :=
            ev_set_st main rO gStop s5
          have eIte2 : Ev main (.ite rE gStop (seqs [.set rO gStop])
              (seqs [drain sT2 sP (gmk sT2) rZ rJ])) s5
              ⟨Function.update s5.reg rO gStop, s5.stk⟩ 2 := Ev.iteT hrg eSetO5
          have eExtra : Ev main (.ite rW (Glyph.bit true) shrExtraBody .skip) s4 s5 (n5 + 1) :=
            Ev.iteT hgt ⟨n5, he5, le_rfl⟩
          have eB : Ev main (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
              .ite rE gStop (seqs [.set rO gStop])
                (seqs [drain sT2 sP (gmk sT2) rZ rJ])]) s4
              ⟨Function.update s5.reg rO gStop, s5.stk⟩ ((n5 + 1) + 2) :=
            Ev.seq' eExtra eIte2 (le_rfl)
          have eOuterIte : Ev main (.ite rE gStop (seqs [.set rO gStop])
              (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                     .ite rE gStop (seqs [.set rO gStop])
                       (seqs [drain sT2 sP (gmk sT2) rZ rJ])])) s4
              ⟨Function.update s5.reg rO gStop, s5.stk⟩ (((n5 + 1) + 2) + 1) :=
            Ev.iteF hE4ne eB
          have eInnerB : Ev main (seqs [.set rI gGo, .loop rI gGo shrPassBody,
              .ite rE gStop (seqs [.set rO gStop])
                (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                       .ite rE gStop (seqs [.set rO gStop])
                         (seqs [drain sT2 sP (gmk sT2) rZ rJ])])]) (mst2 s)
              ⟨Function.update s5.reg rO gStop, s5.stk⟩ (1 + (n4 + (((n5 + 1) + 2) + 1))) :=
            Ev.seq' hset (Ev.seq' (⟨n4, he4, le_rfl⟩ : Ev main (.loop rI gGo shrPassBody)
              (mst3 s) s4 n4) eOuterIte (le_rfl)) (le_rfl)
          have eIteB : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
              (seqs [.set rI gGo, .loop rI gGo shrPassBody,
                .ite rE gStop (seqs [.set rO gStop])
                  (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                         .ite rE gStop (seqs [.set rO gStop])
                           (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])) (mst2 s)
              ⟨Function.update s5.reg rO gStop, s5.stk⟩
              (1 + (n4 + (((n5 + 1) + 2) + 1)) + 1) := Ev.iteF htest eInnerB
          have eAllB : Ev main shrOuterBody s ⟨Function.update s5.reg rO gStop, s5.stk⟩
              (1 + (1 + ((1 + (n4 + (((n5 + 1) + 2) + 1))) + 1))) :=
            Ev.seq' hpop (Ev.seq' hmov eIteB (le_rfl)) (le_rfl)
          obtain ⟨nn, hev, hnle⟩ := eAllB
          have hro : (Function.update s5.reg rO gStop) rO = gStop := upReg_same rO gStop
          have hre : (Function.update s5.reg rO gStop) rE = gStop := by
            rw [upReg_ne (by decide : rE ≠ rO)]; exact hrg
          have hsm : s5.stk sM = gmk sM :: JM := by
            rw [h5M, hemp]; rfl
          have hss : ((Function.update s5.reg rO gStop) rD = gAny) ↔ (true ∈ bs) := by
            rw [upReg_ne (by decide : rD ≠ rO), h5D, hemp]
            simp only [List.take_nil, List.not_mem_nil, or_false]
            rw [hD4e, h2p, List.take_length]
          have hK5 : (⟨Function.update s5.reg rO gStop, s5.stk⟩ : State).stk sK
              = R'.map Glyph.bit ++ gmk sK :: JK := by
            show s5.stk sK = _
            rw [h5frame sK (by decide : sK ≠ sM) (by decide : sK ≠ sT2), hK4]
          have hframe5 : SameOn s ⟨Function.update s5.reg rO gStop, s5.stk⟩
              ({sK, sP, sM, sT2} : Finset Stk) := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            obtain ⟨h1, h2, h3, h4⟩ := hj
            show s5.stk j = s.stk j
            rw [h5frame j h3 h4]
            exact hframe4 j (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2, h3, h4⟩)
          refine ⟨_, nn, hev, by omega, hK5, hframe5, Or.inr ?_⟩
          refine ⟨hro, hre, hsm, hss, ?_, ([] : List Glyph),
            List.replicate (2 * p) gUnit, ?_, ?_, ?_, allUnit_replicate _, ?_⟩
          · omega
          · show s5.stk sP = ([] : List Glyph) ++ gmk sP :: JP
            rw [h5frame sP (by decide : sP ≠ sM) (by decide : sP ≠ sT2), hP4e]; rfl
          · show s5.stk sT2 = List.replicate (2 * p) gUnit ++ gmk sT2 :: JT2
            rw [h5T]; simp [hemp]
          · intro h hh; exact absurd hh List.not_mem_nil
          · simp only [List.length_nil, List.length_replicate, Nat.zero_add]; omega
        · -- the extra unit pops one more bit
          obtain ⟨s5, n5, he5, hn5, h5M, h5T, h5D, -, h5Ene, h5frame⟩ :=
            shrExtra_ev main s4 (bs.drop (2 * p)) (List.replicate (2 * p) gUnit) JM JT2
              (allUnit_replicate (2 * p)) hM4e hT4e
          have h5T' : s5.stk sT2 = List.replicate (2 * p + 1) gUnit ++ gmk sT2 :: JT2 := by
            rw [h5T, if_neg hemp, List.replicate_succ]
          have hP5 : s5.stk sP = gmk sP :: JP := by
            rw [h5frame sP (by decide : sP ≠ sM) (by decide : sP ≠ sT2), hP4e]
          obtain ⟨s6, n6, he6, hn6, hT6, hP6, ho6⟩ :=
            shlDrain_ev main s5 (List.replicate (2 * p + 1) gUnit) JP JT2
              (allUnit_replicate (2 * p + 1)) h5T' hP5
          have hE5ne : s5.reg rE ≠ gStop := by rw [h5Ene hemp]; exact hE4ne
          have eIte2 : Ev main (.ite rE gStop (seqs [.set rO gStop])
              (seqs [drain sT2 sP (gmk sT2) rZ rJ])) s5 s6 (n6 + 1) :=
            Ev.iteF hE5ne ⟨n6, he6, le_rfl⟩
          have eExtra : Ev main (.ite rW (Glyph.bit true) shrExtraBody .skip) s4 s5 (n5 + 1) :=
            Ev.iteT hgt ⟨n5, he5, le_rfl⟩
          have eB : Ev main (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
              .ite rE gStop (seqs [.set rO gStop])
                (seqs [drain sT2 sP (gmk sT2) rZ rJ])]) s4 s6 ((n5 + 1) + (n6 + 1)) :=
            Ev.seq' eExtra eIte2 (le_rfl)
          have eOuterIte : Ev main (.ite rE gStop (seqs [.set rO gStop])
              (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                     .ite rE gStop (seqs [.set rO gStop])
                       (seqs [drain sT2 sP (gmk sT2) rZ rJ])])) s4 s6 (((n5 + 1) + (n6 + 1)) + 1) :=
            Ev.iteF hE4ne eB
          have eInnerB : Ev main (seqs [.set rI gGo, .loop rI gGo shrPassBody,
              .ite rE gStop (seqs [.set rO gStop])
                (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                       .ite rE gStop (seqs [.set rO gStop])
                         (seqs [drain sT2 sP (gmk sT2) rZ rJ])])]) (mst2 s) s6
              (1 + (n4 + (((n5 + 1) + (n6 + 1)) + 1))) :=
            Ev.seq' hset (Ev.seq' (⟨n4, he4, le_rfl⟩ : Ev main (.loop rI gGo shrPassBody)
              (mst3 s) s4 n4) eOuterIte (le_rfl)) (le_rfl)
          have eIteB : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
              (seqs [.set rI gGo, .loop rI gGo shrPassBody,
                .ite rE gStop (seqs [.set rO gStop])
                  (seqs [.ite rW (Glyph.bit true) shrExtraBody .skip,
                         .ite rE gStop (seqs [.set rO gStop])
                           (seqs [drain sT2 sP (gmk sT2) rZ rJ])])])) (mst2 s) s6
              (1 + (n4 + (((n5 + 1) + (n6 + 1)) + 1)) + 1) := Ev.iteF htest eInnerB
          have eAllB : Ev main shrOuterBody s s6
              (1 + (1 + ((1 + (n4 + (((n5 + 1) + (n6 + 1)) + 1))) + 1))) :=
            Ev.seq' hpop (Ev.seq' hmov eIteB (le_rfl)) (le_rfl)
          obtain ⟨nn, hev, hnle⟩ := eAllB
          have hn6' : n6 ≤ 10 * p + 15 := by rw [List.length_replicate] at hn6; omega
          have hK6 : s6.stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by
            rw [ho6 sK (by decide : sK ∉ ({sT2, sP} : Finset Stk)),
              h5frame sK (by decide : sK ≠ sM) (by decide : sK ≠ sT2), hK4]
          have hro6 : s6.reg rO = gGo := by
            rw [Eval_reg_frame he6 (by decide : rO ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ)),
              Eval_reg_frame he5 (by decide : rO ∉ cmdRegs shrExtraBody),
              Eval_reg_frame he4 (by decide : rO ∉ cmdRegs (Cmd.loop rI gGo shrPassBody)), hs3O]
          have hre6 : s6.reg rE = gNo := by
            rw [Eval_reg_frame he6 (by decide : rE ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ)),
              h5Ene hemp, hE4gno]
          have hlen2 : 2 * p + 1 ≤ bs.length := by
            have h5 : 0 < (bs.drop (2 * p)).length := by
              rw [List.length_pos_iff]; exact hemp
            rw [hlen2p] at h5; omega
          have hsm6 : s6.stk sM = (bs.drop (2 * p + 1)).map Glyph.bit ++ gmk sM :: JM := by
            rw [ho6 sM (by decide : sM ∉ ({sT2, sP} : Finset Stk)), h5M, List.drop_drop]
          have hrd6' : (s6.reg rD = gAny) ↔ (true ∈ bs.take (2 * p + 1)) := by
            have h2 : s6.reg rD = s5.reg rD :=
              Eval_reg_frame he6 (by decide : rD ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ))
            rw [h2, h5D]
            rw [hD4e]
            exact Iff.symm (mem_take_add (l := bs) (n := 2 * p) (m := 1))
          have hframe6 : SameOn s s6 ({sK, sP, sM, sT2} : Finset Stk) := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            obtain ⟨h1, h2, h3, h4⟩ := hj
            show s6.stk j = s.stk j
            rw [ho6 j (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h4, h2⟩),
              h5frame j h3 h4]
            exact hframe4 j (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2, h3, h4⟩)
          refine ⟨_, nn, hev, by omega, hK6, hframe6, Or.inl ?_⟩
          refine ⟨hro6, hre6, by simp only [Bool.toNat_true]; omega, ?_, ?_, hT6, ?_⟩
          · rw [hP6, List.reverse_replicate]; simp
          · rw [hsm6]; simp
          · rw [hrd6']; simp

theorem le_natOfMSB (q : ℕ) (L : List Bool) : q ≤ natOfMSB q L := by
  induction L generalizing q with
  | nil => simp
  | cons b bs ih =>
      rw [natOfMSB_cons]
      exact le_trans (by omega) (ih (2 * q + b.toNat))

/-! ## The main loop -/

theorem shrLoopBody_ev (main : Cmd) (R : List Bool) (bs : List Bool) (p : ℕ) :
    ∀ (s : State) (JK JP JM JT2 : List Glyph),
      s.stk sK = R.map Glyph.bit ++ gmk sK :: JK →
      s.stk sP = List.replicate p gUnit ++ gmk sP :: JP →
      s.stk sM = (bs.drop p).map Glyph.bit ++ gmk sM :: JM →
      s.stk sT2 = gmk sT2 :: JT2 →
      s.reg rO = gGo → s.reg rE = gNo → ((s.reg rD = gAny) ↔ (true ∈ bs.take p)) →
      p ≤ bs.length →
      ∃ (s' : State) (n : ℕ) (p' : ℕ) (B : List Bool) (SK : List Glyph),
        Eval main (.loop rO gGo shrOuterBody) s s' n ∧ n ≤ shrLoopCost p R (bs.length - p) ∧
        s'.reg rO = gStop ∧ s'.stk sK = SK ++ gmk sK :: JK ∧ (∀ h ∈ SK, h ≠ gmk sK) ∧
        SK.length ≤ R.length ∧
        s'.stk sM = B.map Glyph.bit ++ gmk sM :: JM ∧
        SameOn s s' ({sK, sP, sM, sT2} : Finset Stk) ∧
        ( (p' = natOfMSB p R ∧ B = bs.drop p' ∧ ((s'.reg rD = gAny) ↔ (true ∈ bs.take p')) ∧
            s'.stk sP = List.replicate p' gUnit ++ gmk sP :: JP ∧ s'.stk sT2 = gmk sT2 :: JT2 ∧
            p' ≤ bs.length)
          ∨ (B = [] ∧ ((s'.reg rD = gAny) ↔ (true ∈ bs)) ∧ bs.length ≤ 2 * p' ∧
             2 * p' ≤ natOfMSB p R ∧ R ≠ [] ∧
             ∃ (P' T2' : List Glyph), s'.stk sP = P' ++ gmk sP :: JP ∧
               s'.stk sT2 = T2' ++ gmk sT2 :: JT2 ∧ (∀ h ∈ P', h = gUnit) ∧
               (∀ h ∈ T2', h = gUnit) ∧ P'.length + T2'.length ≤ bs.length + 2) ) := by
  intro s JK JP JM JT2 hK hP hM hT hO hE hD hle
  induction R generalizing p s with
  | nil =>
      obtain ⟨s1, n1, he1, hc1, hO1, hK1, hP1, hM1, hT1, hrD1, ho1⟩ :=
        shrStop_ev main s JK (by rw [hK]; rfl)
      have hloop : Ev main (.loop rO gGo shrOuterBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hO ⟨n1, he1, le_rfl⟩ (Ev.loopF (by rw [hO1]; exact gStop_ne_gGo))
      obtain ⟨m, hm, hmle⟩ := hloop
      have hcost : m ≤ shrLoopCost p [] (bs.length - p) := by
        rw [shrLoopCost]
        omega
      refine ⟨s1, m, p, bs.drop p, [], hm, hcost, hO1, ?_, ?_, ?_, ?_, ho1,
        Or.inl ⟨rfl, rfl, ?_, ?_, ?_, hle⟩⟩
      · show s1.stk sK = ([] : List Glyph) ++ gmk sK :: JK
        exact hK1
      · intro h hh; exact absurd hh List.not_mem_nil
      · simp
      · show s1.stk sM = (bs.drop p).map Glyph.bit ++ gmk sM :: JM
        rw [hM1, hM]
      · rw [hrD1]; exact hD
      · show s1.stk sP = List.replicate p gUnit ++ gmk sP :: JP
        rw [hP1, hP]
      · show s1.stk sT2 = gmk sT2 :: JT2
        rw [hT1, hT]
  | cons b R' ih =>
      obtain ⟨s1, n1, he1, hc1, hK1, ho1, hcase⟩ :=
        shrStep_ev main R' b p bs s JK JP JM JT2 hK hP hM hT hO hE hD hle
      have hlen : (bs.drop p).length = bs.length - p := List.length_drop ..
      have hn1 : n1 ≤ 120 * (min p (bs.length - p) + 1) := by
        rw [hlen] at hc1
        exact hc1
      rcases hcase with ⟨hO1, hE1, hle1, hP1, hM1, hT1, hD1⟩
        | ⟨hO1, hE1, hM1, hD1, hlen1, P2, T2c, hP2, hT2, hP2u, hT2u, hlen2⟩
      · -- continue
        obtain ⟨s2, n2, p2, B2, SK2, he2, hc2, hO2, hK2, hK2u, hK2l, hM2, ho2, hres2⟩ :=
          ih (p := 2 * p + b.toNat) (s := s1) hK1 hP1 hM1 hT1 hO1 hE1 hD1 hle1
        have hloop : Ev main (.loop rO gGo shrOuterBody) s s2 (n1 + n2 + 1) :=
          Ev.loopT hO ⟨n1, he1, le_rfl⟩ ⟨n2, he2, le_rfl⟩
        obtain ⟨m, hm, hmle⟩ := hloop
        have hsub : (bs.length - p) - (p + b.toNat) = bs.length - (2 * p + b.toNat) := by
          rw [Nat.sub_sub]; congr 1; omega
        have hcost : m ≤ shrLoopCost p (b :: R') (bs.length - p) := by
          rw [shrLoopCost, hsub]
          omega
        have hframe : SameOn s s2 ({sK, sP, sM, sT2} : Finset Stk) :=
          (ho1.trans ho2).mono (by decide)
        have hK2u' : ∀ h ∈ SK2, h ≠ gmk sK := hK2u
        have hK2l' : SK2.length ≤ (b :: R').length := by
          have := hK2l; simp only [List.length_cons]; omega
        rcases hres2 with ⟨hp2, hB2, hD2, hP2', hT2', hp2le⟩
          | ⟨hB2, hD2, hlen3, hlen4, -, P3, T3, hP3, hT3, hP3u, hT3u, hlen5⟩
        · refine ⟨s2, m, p2, B2, SK2, hm, hcost, hO2, hK2, hK2u', hK2l', hM2, hframe,
            Or.inl ⟨?_, hB2, hD2, hP2', hT2', hp2le⟩⟩
          rw [hp2]; rfl
        · refine ⟨s2, m, p2, B2, SK2, hm, hcost, hO2, hK2, hK2u', hK2l', hM2, hframe,
            Or.inr ⟨hB2, hD2, hlen3, ?_, List.cons_ne_nil b R', P3, T3, hP3, hT3, hP3u, hT3u,
              hlen5⟩⟩
          rw [natOfMSB_cons]
          exact hlen4
      · -- stop
        have hloop : Ev main (.loop rO gGo shrOuterBody) s s1 (n1 + 1 + 1) :=
          Ev.loopT hO ⟨n1, he1, le_rfl⟩ (Ev.loopF (by rw [hO1]; exact gStop_ne_gGo))
        obtain ⟨m, hm, hmle⟩ := hloop
        have hcost : m ≤ shrLoopCost p (b :: R') (bs.length - p) := by
          rw [shrLoopCost]
          have := shrLoopCost_ge (2 * p + b.toNat) R' (bs.length - p - (p + b.toNat))
          omega
        refine ⟨s1, m, p, [], R'.map Glyph.bit, hm, hcost, hO1, ?_, ?_, ?_, ?_, ho1,
          Or.inr ⟨rfl, hD1, hlen1, ?_, List.cons_ne_nil b R', P2, T2c, hP2, hT2, hP2u, hT2u,
            hlen2⟩⟩
        · show s1.stk sK = R'.map Glyph.bit ++ gmk sK :: JK
          exact hK1
        · intro h hh; exact noMark_bitsG R' h hh sK
        · simp only [List.length_map, List.length_cons]; omega
        · show s1.stk sM = ([] : List Bool).map Glyph.bit ++ gmk sM :: JM
          rw [hM1]; rfl
        · rw [natOfMSB_cons]
          exact le_trans (by omega : 2 * p ≤ 2 * p + b.toNat) (le_natOfMSB (2 * p + b.toNat) R')

/-- The `shr` main loop from the canonical start state (`p = 0`). -/
theorem shrLoop_ev (main : Cmd) (R : List Bool) (bs : List Bool) (s : State)
    (JK JP JM JT2 : List Glyph)
    (hK : s.stk sK = R.map Glyph.bit ++ gmk sK :: JK)
    (hP : s.stk sP = gmk sP :: JP)
    (hM : s.stk sM = bs.map Glyph.bit ++ gmk sM :: JM)
    (hT : s.stk sT2 = gmk sT2 :: JT2) :
    ∃ (s' : State) (n : ℕ) (p' : ℕ) (B : List Bool) (SK : List Glyph),
      Eval main shrLoop s s' n ∧ n ≤ shrLoopCost 0 R bs.length + 3 ∧
      s'.reg rO = gStop ∧ s'.stk sK = SK ++ gmk sK :: JK ∧ (∀ h ∈ SK, h ≠ gmk sK) ∧
      SK.length ≤ R.length ∧
      s'.stk sM = B.map Glyph.bit ++ gmk sM :: JM ∧
      SameOn s s' ({sK, sP, sM, sT2} : Finset Stk) ∧
      ( (p' = natOfMSB 0 R ∧ B = bs.drop p' ∧ ((s'.reg rD = gAny) ↔ (true ∈ bs.take p')) ∧
          s'.stk sP = List.replicate p' gUnit ++ gmk sP :: JP ∧ s'.stk sT2 = gmk sT2 :: JT2 ∧
          p' ≤ bs.length)
        ∨ (B = [] ∧ ((s'.reg rD = gAny) ↔ (true ∈ bs)) ∧ bs.length ≤ 2 * p' ∧
           2 * p' ≤ natOfMSB 0 R ∧ R ≠ [] ∧
           ∃ (P' T2' : List Glyph), s'.stk sP = P' ++ gmk sP :: JP ∧
             s'.stk sT2 = T2' ++ gmk sT2 :: JT2 ∧ (∀ h ∈ P', h = gUnit) ∧
             (∀ h ∈ T2', h = gUnit) ∧ P'.length + T2'.length ≤ bs.length + 2) ) := by
  have e1 : Ev main (.set rE gNo) s ⟨Function.update s.reg rE gNo, s.stk⟩ 1 :=
    ev_set_st main rE gNo s
  have e2 : Ev main (.set rD gNo) ⟨Function.update s.reg rE gNo, s.stk⟩
      ⟨Function.update (Function.update s.reg rE gNo) rD gNo, s.stk⟩ 1 :=
    ev_set_st main rD gNo _
  have e3 : Ev main (.set rO gGo)
      ⟨Function.update (Function.update s.reg rE gNo) rD gNo, s.stk⟩
      ⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo, s.stk⟩ 1 :=
    ev_set_st main rO gGo _
  have hP0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).stk sP = List.replicate 0 gUnit ++ gmk sP :: JP := by
    show s.stk sP = _
    rw [hP]; rfl
  have hM0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).stk sM = (bs.drop 0).map Glyph.bit ++ gmk sM :: JM := by
    show s.stk sM = _
    rw [hM]; rfl
  have hT0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).stk sT2 = gmk sT2 :: JT2 := by
    show s.stk sT2 = _
    exact hT
  have hK0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).stk sK = R.map Glyph.bit ++ gmk sK :: JK := by
    show s.stk sK = _
    exact hK
  have hO0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).reg rO = gGo := by
    show Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo rO = gGo
    rw [Function.update_self]
  have hE0 : (⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).reg rE = gNo := by
    show Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo rE = gNo
    rw [upReg_ne (by decide : rE ≠ rO), upReg_ne (by decide : rE ≠ rD),
      Function.update_self rE gNo s.reg]
  have hD0 : ((⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
      s.stk⟩ : State).reg rD = gAny) ↔ (true ∈ bs.take 0) := by
    show (Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo rD
      = gAny) ↔ (true ∈ bs.take 0)
    rw [upReg_ne (by decide : rD ≠ rO), Function.update_self]
    constructor
    · intro h; exact absurd h gNo_ne_gAny
    · intro h
      have h0 : bs.take 0 = ([] : List Bool) := rfl
      rw [h0] at h
      exact absurd h List.not_mem_nil
  obtain ⟨s', n', p', B, SK, he', hc', hO', hK', hK'u, hK'l, hM', ho', hres'⟩ :=
    shrLoopBody_ev main R bs 0 _ JK JP JM JT2 hK0 hP0 hM0 hT0 hO0 hE0 hD0 (Nat.zero_le _)
  obtain ⟨n0, he0, hn0⟩ : ∃ (n0 : ℕ), Eval main shrLoop s s' n0 ∧ n0 ≤ 3 + n' := by
    have hA : Eval main (.set rE gNo) s ⟨Function.update s.reg rE gNo, s.stk⟩ 1 := Eval.set rE gNo s
    have hB : Eval main (.set rD gNo) ⟨Function.update s.reg rE gNo, s.stk⟩
        ⟨Function.update (Function.update s.reg rE gNo) rD gNo, s.stk⟩ 1 := Eval.set rD gNo _
    have hC : Eval main (.set rO gGo)
        ⟨Function.update (Function.update s.reg rE gNo) rD gNo, s.stk⟩
        ⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo, s.stk⟩ 1 :=
      Eval.set rO gGo _
    have hD : Eval main (.loop rO gGo shrOuterBody)
        ⟨Function.update (Function.update (Function.update s.reg rE gNo) rD gNo) rO gGo,
          s.stk⟩ s' n' := he'
    have hE : Eval main (seqs [.set rE gNo, .set rD gNo, .set rO gGo,
        .loop rO gGo shrOuterBody]) s s' (1 + (1 + (1 + n'))) :=
      Eval.seq hA (Eval.seq hB (Eval.seq hC hD))
    exact ⟨1 + (1 + (1 + n')), hE, by omega⟩
  have hc'' : n' ≤ shrLoopCost 0 R bs.length := by
    rw [Nat.sub_zero] at hc'
    exact hc'
  have h1 : s'.stk sK = SK ++ gmk sK :: JK := hK'
  have h2 : ∀ h ∈ SK, h ≠ gmk sK := hK'u
  have h3 : SK.length ≤ R.length := hK'l
  have h4 : s'.stk sM = B.map Glyph.bit ++ gmk sM :: JM := hM'
  have h5 : SameOn s s' ({sK, sP, sM, sT2} : Finset Stk) := ho'
  have h6 : n0 ≤ shrLoopCost 0 R bs.length + 3 := le_trans hn0 (by omega)
  exact ⟨s', n0, p', B, SK, he0, h6, hO', h1, h2, h3, h4, h5, hres'⟩

end Shift
end Work.IntLib
