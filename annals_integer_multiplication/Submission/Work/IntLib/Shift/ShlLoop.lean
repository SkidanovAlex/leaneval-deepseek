import Mathlib
import Submission.Work.IntLib.Shift.Loop

/-!
# `IntLib` / shift words: the `shl` outer loop

One iteration of the outer loop reads the next bit of `k` from the region of `sK`, runs the block
pass, performs the extra unit when that bit is `1`, and moves the doubled block from `sT2` back
into `sP`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

theorem boolToNat_eq (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl

theorem boolToNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> simp

/-! ## The intermediate states of one iteration -/

/-- State after `pop sK rX`. -/
def mst1 (s : State) : State :=
  ⟨Function.update s.reg rX ((s.stk sK).headD .eos), Function.update s.stk sK (s.stk sK).tail⟩

/-- State after `pop sK rX ; mov rW rX`. -/
def mst2 (s : State) : State :=
  ⟨Function.update (mst1 s).reg rW ((mst1 s).reg rX), (mst1 s).stk⟩

/-- State after `pop sK rX ; mov rW rX ; set rI gGo`. -/
def mst3 (s : State) : State :=
  ⟨Function.update (mst2 s).reg rI gGo, (mst2 s).stk⟩

theorem mst1_stk_sK {s : State} : (mst1 s).stk sK = (s.stk sK).tail := by simp [mst1]
theorem mst1_stk_other {s : State} {j : Stk} (h : j ≠ sK) : (mst1 s).stk j = s.stk j := by
  simp [mst1, h]
theorem mst2_stk_sK {s : State} : (mst2 s).stk sK = (s.stk sK).tail := by simp [mst2, mst1]
theorem mst2_stk_other {s : State} {j : Stk} (h : j ≠ sK) : (mst2 s).stk j = s.stk j := by
  simp [mst2, mst1, h]
theorem mst2_reg_rW {s : State} : (mst2 s).reg rW = (s.stk sK).headD .eos := by
  simp [mst2, mst1]
theorem mst3_stk_sK {s : State} : (mst3 s).stk sK = (s.stk sK).tail := by simp [mst3, mst2, mst1]
theorem mst3_stk_other {s : State} {j : Stk} (h : j ≠ sK) : (mst3 s).stk j = s.stk j := by
  simp [mst3, mst2, mst1, h]
theorem mst3_reg_rW {s : State} : (mst3 s).reg rW = (s.stk sK).headD .eos := by
  simp [mst3, mst2, mst1]
theorem mst3_reg_rI {s : State} : (mst3 s).reg rI = gGo := by simp [mst3]

theorem mst1_reg_other {s : State} {r : Reg} (h : r ≠ rX) : (mst1 s).reg r = s.reg r := by
  simp [mst1, h]
theorem mst2_reg_other {s : State} {r : Reg} (h : r ≠ rW) : (mst2 s).reg r = (mst1 s).reg r := by
  simp [mst2, h]
theorem mst3_reg_other {s : State} {r : Reg} (h : r ≠ rI) : (mst3 s).reg r = (mst2 s).reg r := by
  simp [mst3, h]
theorem mst3_reg_rO {s : State} : (mst3 s).reg rO = s.reg rO := by
  rw [mst3_reg_other (by decide : rO ≠ rI), mst2_reg_other (by decide : rO ≠ rW),
    mst1_reg_other (by decide : rO ≠ rX)]

theorem SameOn.mst3 (s : State) : SameOn s (mst3 s) ({sK} : Finset Stk) := by
  intro j hj
  simp only [Finset.mem_singleton] at hj
  exact mst3_stk_other hj

theorem ev_skip_st (main : Cmd) (s : State) : Ev main .skip s s 1 := ⟨1, Eval.skip s, le_rfl⟩

theorem ev_shlStep_pre (main : Cmd) (s : State) :
    Ev main (seqs [.pop sK rX, .mov rW rX, .set rI gGo]) s (mst3 s) 3 :=
  Ev.seq' (ev_pop_st main sK rX s)
    (Ev.seq' (ev_mov_st main rW rX (mst1 s)) (ev_set_st main rI gGo (mst2 s)) (le_rfl)) (le_rfl)

/-! ## The extra unit -/

theorem ev_shlExtra (main : Cmd) (s : State) :
    Ev main shlExtraBody s
      ⟨Function.update (Function.update s.reg rY gUnit) rY gZero,
        Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA (gZero :: s.stk sA)⟩ 4 := by
  have h1 : Ev main (pushC sT2 gUnit rY) s
      ⟨Function.update s.reg rY gUnit, Function.update s.stk sT2 (gUnit :: s.stk sT2)⟩ 2 :=
    ev_pushC_st main sT2 gUnit rY s
  have h2 : Ev main (pushC sA gZero rY)
      ⟨Function.update s.reg rY gUnit, Function.update s.stk sT2 (gUnit :: s.stk sT2)⟩
      ⟨Function.update (Function.update s.reg rY gUnit) rY gZero,
        Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA (gZero :: s.stk sA)⟩ 2 :=
    ev_pushC_st main sA gZero rY _
  rw [shlExtraBody, seqs_pair]
  exact Ev.seq' h1 h2 (le_rfl)

theorem shlExtra_ev (main : Cmd) (s : State) :
    ∃ (s' : State) (n : ℕ), Eval main shlExtraBody s s' n ∧ n ≤ 4 ∧
      s'.stk sT2 = gUnit :: (s.stk sT2) ∧ s'.stk sA = gZero :: (s.stk sA) ∧
      SameOn s s' ({sT2, sA} : Finset Stk) ∧ s'.reg rW = s.reg rW ∧ s'.reg rO = s.reg rO := by
  obtain ⟨n, he, hn⟩ := ev_shlExtra main s
  have hregs : ∀ r : Reg, r ≠ rY →
      (Function.update (Function.update s.reg rY gUnit) rY gZero) r = s.reg r := by
    intro r hr
    rw [upReg_ne hr, upReg_ne hr]
  have hT : (Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA
      (gZero :: s.stk sA)) sT2 = gUnit :: (s.stk sT2) := by
    rw [upStk_ne (by decide : sT2 ≠ sA), upStk_same]
  have hA : (Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA
      (gZero :: s.stk sA)) sA = gZero :: (s.stk sA) := by rw [upStk_same]
  have hO : SameOn s ⟨Function.update (Function.update s.reg rY gUnit) rY gZero,
      Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA (gZero :: s.stk sA)⟩
      ({sT2, sA} : Finset Stk) := SameOn.of_pair (fun j hj1 hj2 => by
    show (Function.update (Function.update s.stk sT2 (gUnit :: s.stk sT2)) sA
      (gZero :: s.stk sA)) j = s.stk j
    rw [upStk_ne hj2, upStk_ne hj1])
  exact ⟨_, n, he, by omega, hT, hA, hO, hregs rW (by decide), hregs rO (by decide)⟩

/-! ## The middle block: `ite rW (bit true) shlExtraBody skip` -/

theorem shlIteBlock_ev (main : Cmd) (b : Bool) (s : State) (JP JA JT2 T0 Acur : List Glyph)
    (hU : AllUnit T0) (hP : s.stk sP = gmk sP :: JP) (hA : s.stk sA = Acur ++ gmk sA :: JA)
    (hAz : AllZero Acur) (hT : s.stk sT2 = T0 ++ gmk sT2 :: JT2)
    (hW : s.reg rW = Glyph.bit b) :
    ∃ (s' : State) (n : ℕ) (T' A' : List Glyph),
      Eval main (.ite rW (Glyph.bit true) shlExtraBody .skip) s s' n ∧ n ≤ 6 ∧
      s'.stk sT2 = T' ++ gmk sT2 :: JT2 ∧ AllUnit T' ∧ T'.length = T0.length + b.toNat ∧
      s'.stk sA = A' ++ gmk sA :: JA ∧ AllZero A' ∧ A'.length = Acur.length + b.toNat ∧
      SameOn s s' ({sT2, sA} : Finset Stk) ∧ s'.stk sP = s.stk sP ∧ s'.reg rW = s.reg rW := by
  cases b with
  | false =>
      have hnil : T0.length = T0.length + false.toNat := by simp [boolToNat_eq]
      have hnil2 : Acur.length = Acur.length + false.toNat := by simp [boolToNat_eq]
      exact ⟨s, 2, T0, Acur, Eval.iteF (by rw [hW]; decide) (Eval.skip s), by omega, hT, hU, hnil,
        hA, hAz, hnil2, SameOn.refl' s _, rfl, rfl⟩
  | true =>
      obtain ⟨s', n, he, hn, hT2s, hAs, ho, hrW, _⟩ := shlExtra_ev main s
      have hU' : AllUnit (gUnit :: T0) := AllUnit.cons hU
      have hT'' : s'.stk sT2 = (gUnit :: T0) ++ gmk sT2 :: JT2 := by
        rw [hT2s, hT, ← List.cons_append]
      have hTlen : (gUnit :: T0).length = T0.length + true.toNat := by simp [boolToNat_eq]
      have hA'' : s'.stk sA = (gZero :: Acur) ++ gmk sA :: JA := by
        rw [hAs, hA, ← List.cons_append]
      have hA''z : AllZero (gZero :: Acur) := AllZero.cons hAz
      have hAlen : (gZero :: Acur).length = Acur.length + true.toNat := by simp [boolToNat_eq]
      have hsp : s'.stk sP = s.stk sP := ho sP (by decide : sP ∉ ({sT2, sA} : Finset Stk))
      exact ⟨s', n + 1, gUnit :: T0, gZero :: Acur, Eval.iteT (by rw [hW]) he, by omega, hT'', hU',
        hTlen, hA'', hA''z, hAlen, ho, hsp, hrW⟩

/-! ## The final drain of one iteration -/

theorem shlDrain_ev (main : Cmd) (s : State) (T2c JP JT2 : List Glyph) (hU : AllUnit T2c)
    (hT : s.stk sT2 = T2c ++ gmk sT2 :: JT2) (hP : s.stk sP = gmk sP :: JP) :
    ∃ (s' : State) (n : ℕ), Eval main (drain sT2 sP (gmk sT2) rZ rJ) s s' n ∧
      n ≤ 5 * (T2c.length + 1) + 2 ∧ s'.stk sT2 = gmk sT2 :: JT2 ∧
      s'.stk sP = T2c.reverse ++ gmk sP :: JP ∧
      SameOn s s' ({sT2, sP} : Finset Stk) := by
  have hnomk : ∀ h ∈ T2c, h ≠ gmk sT2 := fun h hm => by rw [hU h hm]; exact unit_ne_markerT2
  obtain ⟨g', n, he, hn, hrF, hT', hP', ho⟩ :=
    drain_ev (main := main) sT2 sP (gmk sT2) rZ rJ (by decide) (by decide) T2c JT2
      (gmk sP :: JP) s.reg s.stk hnomk hT (by rw [hP])
  exact ⟨_, n, he, by omega, hT', hP', SameOn.of_pair (fun j hj1 hj2 => ho j hj1 hj2)⟩

/-! ## One iteration of the outer loop -/

theorem shlStep_ev (main : Cmd) (R' : List Bool) (b : Bool) (p : ℕ) (s : State)
    (JK JP JA JT2 Pcur Acur : List Glyph)
    (hK : s.stk sK = (b :: R').map Glyph.bit ++ gmk sK :: JK)
    (hP : s.stk sP = Pcur ++ gmk sP :: JP) (hPU : AllUnit Pcur) (hPlen : Pcur.length = p)
    (hA : s.stk sA = Acur ++ gmk sA :: JA) (hAU : AllZero Acur) (hAlen : Acur.length = p)
    (hT : s.stk sT2 = gmk sT2 :: JT2) (hgo : s.reg rO = gGo) :
    ∃ (s' : State) (n : ℕ) (P' A' : List Glyph), Eval main shlOuterBody s s' n ∧
      n ≤ 100 * (p + 1) ∧ s'.reg rO = gGo ∧ s'.stk sK = R'.map Glyph.bit ++ gmk sK :: JK ∧
      s'.stk sP = P' ++ gmk sP :: JP ∧ AllUnit P' ∧ P'.length = 2 * p + b.toNat ∧
      s'.stk sA = A' ++ gmk sA :: JA ∧ AllZero A' ∧ A'.length = 2 * p + b.toNat ∧
      s'.stk sT2 = gmk sT2 :: JT2 ∧
      SameOn s s' ({sK, sP, sA, sT2} : Finset Stk) := by
  have hb_le : b.toNat ≤ 1 := boolToNat_le_one b
  have hhead : (s.stk sK).headD .eos = Glyph.bit b := by rw [hK]; rfl
  have htail : (s.stk sK).tail = R'.map Glyph.bit ++ gmk sK :: JK := by rw [hK]; rfl
  obtain ⟨m0, hm0, _⟩ := ev_shlStep_pre main s
  have hso0 : SameOn s (mst3 s) ({sK} : Finset Stk) := SameOn.mst3 s
  have hsK : (mst3 s).stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by rw [mst3_stk_sK, htail]
  have hsP : (mst3 s).stk sP = Pcur ++ gmk sP :: JP := by rw [mst3_stk_other (by decide), hP]
  have hsA : (mst3 s).stk sA = Acur ++ gmk sA :: JA := by rw [mst3_stk_other (by decide), hA]
  have hsT : (mst3 s).stk sT2 = List.nil ++ gmk sT2 :: JT2 := by
    rw [mst3_stk_other (by decide), hT]; rfl
  have hPcur : Pcur = List.replicate p gUnit := by rw [AllEq.eq_replicate hPU, hPlen]
  have hregW3 : (mst3 s).reg rW = Glyph.bit b := by rw [mst3_reg_rW, hhead]
  -- the block pass
  obtain ⟨s1, n1, T1, he1, hn1, hr1, hP1, hA1, hT1, hU1, hlen1, ho1⟩ :=
    shlPass_ev main p Acur JA JP List.nil JT2 (mst3 s) AllUnit.nil
      (by rw [hsP, hPcur]) hsA hsT mst3_reg_rI
  have hregW1 : s1.reg rW = Glyph.bit b := by
    rw [Eval_reg_frame he1 (by decide : rW ∉ cmdRegs (.loop rI gGo shlPassBody)), hregW3]
  have hA1z : AllZero (List.replicate p gZero ++ Acur) :=
    AllEq.append (allEq_replicate gZero p) hAU
  -- the extra unit (or nothing)
  obtain ⟨s2, n2, T2c, A2c, he2, hn2, hT2c, hT2cu, hT2clen, hA2c, hA2cz, hA2clen, ho2, hP2, hrW2⟩ :=
    shlIteBlock_ev main b s1 JP JA JT2 T1 (List.replicate p gZero ++ Acur) hU1
      (by rw [hP1]) hA1 hA1z (by rw [hT1]) hregW1
  -- the drain of the doubled block back into `sP`
  obtain ⟨s3, n3, he3, hn3, hT2end, hP3, ho3⟩ :=
    shlDrain_ev main s2 T2c JP JT2 hT2cu hT2c (by rw [hP2, hP1])
  -- the composite evaluation
  have ePop : Ev main (.pop sK rX) s (mst1 s) 1 := ev_pop_st main sK rX s
  have eMov : Ev main (.mov rW rX) (mst1 s) (mst2 s) 1 := ev_mov_st main rW rX (mst1 s)
  have eSet : Ev main (.set rI gGo) (mst2 s) (mst3 s) 1 := ev_set_st main rI gGo (mst2 s)
  have eLoop : Ev main (.loop rI gGo shlPassBody) (mst3 s) s1 n1 := ⟨n1, he1, le_rfl⟩
  have eIte2 : Ev main (.ite rW (Glyph.bit true) shlExtraBody .skip) s1 s2 n2 := ⟨n2, he2, le_rfl⟩
  have eDrain : Ev main (drain sT2 sP (gmk sT2) rZ rJ) s2 s3 n3 := ⟨n3, he3, le_rfl⟩
  have htest : (mst2 s).reg rW ≠ gmk sK := by rw [mst2_reg_rW, hhead]; exact bit_ne_marker b sK
  have eBody : Ev main (seqs [.set rI gGo, .loop rI gGo shlPassBody,
      .ite rW (Glyph.bit true) shlExtraBody .skip, drain sT2 sP (gmk sT2) rZ rJ]) (mst2 s) s3
      (1 + (n1 + (n2 + n3))) :=
    Ev.seq' eSet (Ev.seq' eLoop (Ev.seq' eIte2 eDrain (le_rfl)) (le_rfl)) (le_rfl)
  have eIte : Ev main (.ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
      (seqs [.set rI gGo, .loop rI gGo shlPassBody,
        .ite rW (Glyph.bit true) shlExtraBody .skip, drain sT2 sP (gmk sT2) rZ rJ]))
      (mst2 s) s3 ((1 + (n1 + (n2 + n3))) + 1) := Ev.iteF htest eBody
  have eAll : Ev main (seqs [.pop sK rX, .mov rW rX,
      .ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
        (seqs [.set rI gGo, .loop rI gGo shlPassBody,
          .ite rW (Glyph.bit true) shlExtraBody .skip, drain sT2 sP (gmk sT2) rZ rJ])])
      s s3 (1 + (1 + ((1 + (n1 + (n2 + n3))) + 1))) :=
    Ev.seq' ePop (Ev.seq' eMov eIte (le_rfl)) (le_rfl)
  obtain ⟨nn, hev, hnle⟩ := eAll
  have hK3 : s3.stk sK = R'.map Glyph.bit ++ gmk sK :: JK := by
    rw [ho3 sK (by decide : sK ∉ ({sT2, sP} : Finset Stk)), ho2 sK (by decide), ho1 sK (by decide),
      hsK]
  have hA3 : s3.stk sA = A2c ++ gmk sA :: JA := by
    rw [ho3 sA (by decide : sA ∉ ({sT2, sP} : Finset Stk)), hA2c]
  have hframe : SameOn s s3 ({sK, sP, sA, sT2} : Finset Stk) := by
    have h01 : SameOn s (mst3 s) ({sK, sP, sA, sT2} : Finset Stk) := hso0.mono (by decide)
    have h12 : SameOn (mst3 s) s1 ({sK, sP, sA, sT2} : Finset Stk) := ho1.mono (by decide)
    have h23 : SameOn s1 s2 ({sK, sP, sA, sT2} : Finset Stk) := ho2.mono (by decide)
    have h34 : SameOn s2 s3 ({sK, sP, sA, sT2} : Finset Stk) := ho3.mono (by decide)
    intro j hj
    rw [h34 j hj, h23 j hj, h12 j hj, h01 j hj]
  have hrO1 : s1.reg rO = (mst3 s).reg rO :=
    Eval_reg_frame he1 (by decide : rO ∉ cmdRegs (.loop rI gGo shlPassBody))
  have hrO2 : s2.reg rO = s1.reg rO :=
    Eval_reg_frame he2 (by decide : rO ∉ cmdRegs (.ite rW (Glyph.bit true) shlExtraBody .skip))
  have hrO3 : s3.reg rO = s2.reg rO :=
    Eval_reg_frame he3 (by decide : rO ∉ cmdRegs (drain sT2 sP (gmk sT2) rZ rJ))
  have hrO0 : (mst3 s).reg rO = s.reg rO := mst3_reg_rO
  have hro : s3.reg rO = s.reg rO := by rw [hrO3, hrO2, hrO1, hrO0]
  have hT2clen' : T2c.length = 2 * p + b.toNat := by rw [hT2clen, hlen1]; simp
  have hcost : nn ≤ 100 * (p + 1) := by
    have h3 : n3 ≤ 5 * (2 * p + b.toNat + 1) + 2 := by rw [← hT2clen']; exact hn3
    omega
  exact ⟨s3, nn, T2c.reverse, A2c, hev, hcost, by rw [hro]; exact hgo, hK3, hP3,
    AllEq.reverse hT2cu, by rw [List.length_reverse, hT2clen'], hA3, hA2cz,
    by rw [hA2clen, List.length_append, List.length_replicate, hAlen]; omega,
    hT2end, hframe⟩

/-! ## The stop branch -/

theorem shlStop_ev (main : Cmd) (s : State) (JK : List Glyph) (hK : s.stk sK = gmk sK :: JK) :
    ∃ (s' : State) (n : ℕ), Eval main shlOuterBody s s' n ∧ n ≤ 6 ∧ s'.reg rO = gStop ∧
      s'.stk sK = gmk sK :: JK ∧ s'.stk sP = s.stk sP ∧ s'.stk sA = s.stk sA ∧
      s'.stk sT2 = s.stk sT2 ∧ SameOn s s' ({sK, sP, sA, sT2} : Finset Stk) := by
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
      (seqs [.set rI gGo, .loop rI gGo shlPassBody,
        .ite rW (Glyph.bit true) shlExtraBody .skip, drain sT2 sP (gmk sT2) rZ rJ])) (mst2 s) _ 3 :=
    Ev.iteT htest hpush2
  have eAll : Ev main (seqs [.pop sK rX, .mov rW rX,
      .ite rW (gmk sK) (seqs [.push sK rW, .set rO gStop])
        (seqs [.set rI gGo, .loop rI gGo shlPassBody,
          .ite rW (Glyph.bit true) shlExtraBody .skip, drain sT2 sP (gmk sT2) rZ rJ])]) s _ 5 :=
    Ev.seq' hpop (Ev.seq' hmov hite (le_rfl)) (le_rfl)
  obtain ⟨n, he, hn⟩ := eAll
  have hr : (Function.update (mst2 s).reg rO gStop) rO = gStop := by rw [upReg_same]
  have hsp : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sK
      = gmk sK :: JK := by rw [upStk_same, mst2_reg_rW, hhead, mst2_stk_sK, hK]; rfl
  have h1 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sP
      = s.stk sP := by rw [upStk_ne (by decide : sP ≠ sK), mst2_stk_other (by decide : sP ≠ sK)]
  have h2 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sA
      = s.stk sA := by rw [upStk_ne (by decide : sA ≠ sK), mst2_stk_other (by decide : sA ≠ sK)]
  have h3 : (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) sT2
      = s.stk sT2 := by rw [upStk_ne (by decide : sT2 ≠ sK), mst2_stk_other (by decide : sT2 ≠ sK)]
  have h4 : SameOn s ⟨Function.update (mst2 s).reg rO gStop,
      Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)⟩
      ({sK, sP, sA, sT2} : Finset Stk) := by
    intro j hj
    show (Function.update (mst2 s).stk sK ((mst2 s).reg rW :: (mst2 s).stk sK)) j = s.stk j
    by_cases hjK : j = sK
    · subst hjK
      exact absurd (by decide : sK ∈ ({sK, sP, sA, sT2} : Finset Stk)) hj
    · rw [upStk_ne hjK, mst2_stk_other hjK]
  exact ⟨_, n, he, by omega, hr, hsp, h1, h2, h3, h4⟩

/-! ## The loop -/

theorem shlLoop_ev (main : Cmd) (R : List Bool) (p : ℕ) :
    ∀ (s : State) (JK JP JA JT2 Pcur Acur : List Glyph),
      s.stk sK = R.map Glyph.bit ++ gmk sK :: JK →
      s.stk sP = Pcur ++ gmk sP :: JP → AllUnit Pcur → Pcur.length = p →
      s.stk sA = Acur ++ gmk sA :: JA → AllZero Acur → Acur.length = p →
      s.stk sT2 = gmk sT2 :: JT2 → s.reg rO = gGo →
      ∃ (s' : State) (n : ℕ) (P' A' : List Glyph),
        Eval main (.loop rO gGo shlOuterBody) s s' n ∧ n ≤ 105 * (shlCost p R + 1) ∧
        s'.reg rO = gStop ∧ s'.stk sK = gmk sK :: JK ∧
        s'.stk sP = P' ++ gmk sP :: JP ∧ AllUnit P' ∧ P'.length = natOfMSB p R ∧
        s'.stk sA = A' ++ gmk sA :: JA ∧ AllZero A' ∧ A'.length = natOfMSB p R ∧
        s'.stk sT2 = gmk sT2 :: JT2 ∧ SameOn s s' ({sK, sP, sA, sT2} : Finset Stk) := by
  intro s JK JP JA JT2 Pcur Acur hK hP hPU hPlen hA hAU hAlen hT hgo
  induction R generalizing p Pcur Acur s with
  | nil =>
      obtain ⟨s1, n1, he1, hn1, hr1, hK1, hP1, hA1, hT1, ho1⟩ :=
        shlStop_ev main s JK (by rw [hK]; rfl)
      have hloop : Ev main (.loop rO gGo shlOuterBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩
          (Ev.loopF (main := main) (s := s1) (by rw [hr1]; exact gStop_ne_gGo))
      obtain ⟨m, hm, hmle⟩ := hloop
      have hcost : m ≤ 105 * (shlCost p [] + 1) := by
        simp only [shlCost_nil] at *
        omega
      have hP' : s1.stk sP = Pcur ++ gmk sP :: JP := by rw [hP1, hP]
      have hA' : s1.stk sA = Acur ++ gmk sA :: JA := by rw [hA1, hA]
      have hT' : s1.stk sT2 = gmk sT2 :: JT2 := by rw [hT1, hT]
      exact ⟨s1, m, Pcur, Acur, hm, hcost, hr1, hK1, hP', hPU, hPlen, hA', hAU, hAlen, hT', ho1⟩
  | cons b R' ih =>
      obtain ⟨s1, n1, P1, A1, he1, hn1, hr1, hK1, hP1, hP1u, hP1len, hA1, hA1z, hA1len, hT1, ho1⟩ :=
        shlStep_ev main R' b p s JK JP JA JT2 Pcur Acur hK hP hPU hPlen hA hAU hAlen hT hgo
      have hgo1 : s1.reg rO = gGo := hr1
      obtain ⟨s2, n2, P2, A2, he2, hn2, hr2, hK2, hP2, hP2u, hP2len, hA2, hA2z, hA2len, hT2, ho2⟩ :=
        ih (p := 2 * p + b.toNat) (Pcur := P1) (Acur := A1) (s := s1) hK1 hP1 hP1u hP1len hA1 hA1z
          hA1len hT1 hgo1
      have hloop : Ev main (.loop rO gGo shlOuterBody) s s2 (n1 + n2 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩ ⟨n2, he2, le_rfl⟩
      obtain ⟨m, hm, hmle⟩ := hloop
      have hlen : natOfMSB (2 * p + b.toNat) R' = natOfMSB p (b :: R') := rfl
      have hcost : m ≤ 105 * (shlCost p (b :: R') + 1) := by
        simp only [shlCost_cons] at *
        omega
      have hP' : s2.stk sP = P2 ++ gmk sP :: JP := hP2
      have hA' : s2.stk sA = A2 ++ gmk sA :: JA := hA2
      have hlen2 : P2.length = natOfMSB p (b :: R') := by rw [← hlen, hP2len]
      have hlen3 : A2.length = natOfMSB p (b :: R') := by rw [← hlen, hA2len]
      exact ⟨s2, m, P2, A2, hm, hcost, hr2, hK2, hP', hP2u, hlen2, hA', hA2z, hlen3, hT2,
        (ho1.trans ho2).mono (by decide)⟩

end Shift
end Work.IntLib
