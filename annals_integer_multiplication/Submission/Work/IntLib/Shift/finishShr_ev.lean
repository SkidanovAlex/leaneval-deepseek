import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Shift

open HvdH

/-! ## States of the `finishShr` glue sequence

`finishShr` first peeks `sM` (to decide whether the answer is `0`), then pushes `iend` on stack 0,
moves the magnitude region `sM → sT → 0` (two drains whose composite is the identity on the
region), pops the sign glyph off `sSg` and pushes it on stack 0.  The states of the straight-line
pieces are defined here as functions of the incoming state, so that the primitive `Ev` lemmas
match definitionally. -/

/-- State after `peek sM rY`. -/
def finShr1 (s : State) : State :=
  ⟨Function.update s.reg rY ((s.stk sM).headD .eos), s.stk⟩

/-- State after `peek sM rY ; pushC 0 iend rY`. -/
def finShr2 (s : State) : State :=
  ⟨Function.update (finShr1 s).reg rY Glyph.iend,
    Function.update (finShr1 s).stk 0 (Glyph.iend :: (finShr1 s).stk 0)⟩

/-- State after `... ; pop sSg rY`. -/
def finShr3 (s : State) : State :=
  ⟨Function.update s.reg rY ((s.stk sSg).headD .eos),
    Function.update s.stk sSg (s.stk sSg).tail⟩

/-- State after `... ; pop sSg rY ; push 0 rY`. -/
def finShr4 (s : State) : State :=
  ⟨(finShr3 s).reg, Function.update (finShr3 s).stk 0 ((finShr3 s).reg rY :: (finShr3 s).stk 0)⟩

theorem finShr1_stk (s : State) : (finShr1 s).stk = s.stk := rfl

theorem finShr1_reg_rY (s : State) : (finShr1 s).reg rY = (s.stk sM).headD .eos := by
  simp [finShr1]

theorem finShr2_stk (s : State) :
    (finShr2 s).stk = Function.update s.stk 0 (Glyph.iend :: s.stk 0) := rfl

theorem finShr2_stk_0 (s : State) : (finShr2 s).stk 0 = Glyph.iend :: s.stk 0 := by
  rw [finShr2_stk, upStk_same]

theorem finShr2_stk_ne (s : State) {j : Stk} (h : j ≠ 0) : (finShr2 s).stk j = s.stk j := by
  rw [finShr2_stk, upStk_ne h]

theorem finShr2_reg_rY (s : State) : (finShr2 s).reg rY = Glyph.iend := by
  simp [finShr2, finShr1]

theorem finShr3_stk_sSg (s : State) : (finShr3 s).stk sSg = (s.stk sSg).tail := by
  simp [finShr3]

theorem finShr3_stk_ne (s : State) {j : Stk} (h : j ≠ sSg) : (finShr3 s).stk j = s.stk j := by
  simp [finShr3, h]

theorem finShr3_reg_rY (s : State) : (finShr3 s).reg rY = (s.stk sSg).headD .eos := by
  simp [finShr3]

theorem finShr4_stk_0 (s : State) : (finShr4 s).stk 0 = (finShr3 s).reg rY :: (finShr3 s).stk 0 := by
  simp [finShr4]

theorem finShr4_stk_ne (s : State) {j : Stk} (h : j ≠ 0) : (finShr4 s).stk j = (finShr3 s).stk j := by
  simp [finShr4, h]

theorem finishShr_ev (main : HvdH.Cmd) (sg : HvdH.Glyph) (B T0 Rj JM JSg JT : List HvdH.Glyph) (s : HvdH.State)
    (hB : ∀ h ∈ B, ∀ r : HvdH.Stk, h ≠ Work.IntLib.Shift.gmk r)
    (hM : s.stk Work.IntLib.Shift.sM = B ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM)
    (hSg : s.stk Work.IntLib.Shift.sSg = sg :: Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: JSg)
    (hT : s.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT)
    (h0 : s.stk 0 = T0 ++ Rj) (hne : B ≠ []) :
    ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main Work.IntLib.Shift.finishShr s s' n ∧
      n ≤ 10 * B.length + 40 ∧
      s'.stk 0 = (sg :: (B ++ [HvdH.Glyph.iend])) ++ T0 ++ Rj ∧
      s'.stk Work.IntLib.Shift.sM = Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM ∧
      s'.stk Work.IntLib.Shift.sSg = Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: JSg ∧
      s'.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT ∧
      s'.stk Work.IntLib.Shift.sK = s.stk Work.IntLib.Shift.sK ∧
      s'.stk Work.IntLib.Shift.sP = s.stk Work.IntLib.Shift.sP ∧
      s'.stk Work.IntLib.Shift.sA = s.stk Work.IntLib.Shift.sA ∧
      s'.stk Work.IntLib.Shift.sT2 = s.stk Work.IntLib.Shift.sT2 := by
  cases B with
  | nil => exact absurd rfl hne
  | cons b B' =>
    have hb : b ≠ gmk sM := hB b (List.mem_cons_self ..) sM
    have hhead : (s.stk sM).headD .eos = b := by rw [hM]; rfl
    have hMsM : s.stk sM = (b :: B') ++ gmk sM :: JM := hM
    -- `peek sM rY`
    have hpeek : Ev main (.peek sM rY) s (finShr1 s) 1 := ev_peek_st main sM rY s
    have hrY1 : (finShr1 s).reg rY ≠ gmk sM := by
      rw [finShr1_reg_rY, hhead]; exact hb
    -- `pushC 0 iend rY`
    have hpush : Ev main (pushC 0 Glyph.iend rY) (finShr1 s) (finShr2 s) 2 :=
      ev_pushC_st main 0 Glyph.iend rY (finShr1 s)
    have hMsM2 : (finShr2 s).stk sM = (b :: B') ++ gmk sM :: JM := by
      rw [finShr2_stk_ne s (by decide : sM ≠ 0)]; exact hMsM
    have hTsT2 : (finShr2 s).stk sT = gmk sT :: JT := by
      rw [finShr2_stk_ne s (by decide : sT ≠ 0)]; exact hT
    have hBsm : ∀ h ∈ b :: B', h ≠ gmk sM := fun h hm => hB h hm sM
    -- first drain: `sM → sT`
    obtain ⟨t3, n3, he3, hn3, _, hM3, hT3, ho3⟩ :=
      drain_ev (main := main) sM sT (gmk sM) rZ rJ (by decide) (by decide)
        (b :: B') JM (gmk sT :: JT) (finShr2 s).reg (finShr2 s).stk hBsm hMsM2 hTsT2
    have he3n : Eval main (drain sM sT (gmk sM) rZ rJ) (finShr2 s) t3 n3 := he3
    have hrev : ∀ x ∈ (b :: B').reverse, x ≠ gmk sT := fun x hx =>
      hB x (List.mem_reverse.mp hx) sT
    have h0t3 : t3.stk 0 = Glyph.iend :: (T0 ++ Rj) := by
      rw [ho3 0 (by decide) (by decide), finShr2_stk_0, h0]
    -- second drain: `sT → 0`
    obtain ⟨t4, n4, he4, hn4, _, hT4, h0t4, ho4⟩ :=
      drain_ev (main := main) sT 0 (gmk sT) rZ rJ (by decide) (by decide)
        ((b :: B').reverse) JT (Glyph.iend :: (T0 ++ Rj)) t3.reg t3.stk hrev hT3 h0t3
    have he4n : Eval main (drain sT 0 (gmk sT) rZ rJ) t3 t4 n4 := he4
    have hSg4 : t4.stk sSg = sg :: gmk sSg :: JSg := by
      rw [ho4 sSg (by decide) (by decide), ho3 sSg (by decide) (by decide),
        finShr2_stk_ne s (by decide : sSg ≠ 0)]
      exact hSg
    -- `pop sSg rY ; push 0 rY`
    have hpop : Ev main (.pop sSg rY) t4 (finShr3 t4) 1 := ev_pop_st main sSg rY t4
    have hpush2 : Ev main (.push 0 rY) (finShr3 t4) (finShr4 t4) 1 :=
      ev_push_st main 0 rY (finShr3 t4)
    obtain ⟨m1, hm1, hm1le⟩ := hpeek
    obtain ⟨m2, hm2, hm2le⟩ := hpush
    obtain ⟨m5, hm5, hm5le⟩ := hpop
    obtain ⟨m6, hm6, hm6le⟩ := hpush2
    have e45 : Eval main (.seq (.pop sSg rY) (.push 0 rY)) t4 (finShr4 t4) (m5 + m6) :=
      Eval.seq hm5 hm6
    have e345 : Eval main (.seq (drain sT 0 (gmk sT) rZ rJ) (.seq (.pop sSg rY) (.push 0 rY)))
        t3 (finShr4 t4) (n4 + (m5 + m6)) := Eval.seq he4n e45
    have e2345 : Eval main (.seq (drain sM sT (gmk sM) rZ rJ)
        (.seq (drain sT 0 (gmk sT) rZ rJ) (.seq (.pop sSg rY) (.push 0 rY))))
        (finShr2 s) (finShr4 t4) (n3 + (n4 + (m5 + m6))) := Eval.seq he3n e345
    have e12345 : Eval main (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ,
        drain sT 0 (gmk sT) rZ rJ, .pop sSg rY, .push 0 rY])
        (finShr1 s) (finShr4 t4) (m2 + (n3 + (n4 + (m5 + m6)))) := Eval.seq hm2 e2345
    -- the `ite` (false branch: the magnitude region is non-empty) and the whole sequence
    have hite : Eval main (.ite rY (gmk sM)
        (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY])
        (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ,
          drain sT 0 (gmk sT) rZ rJ, .pop sSg rY, .push 0 rY]))
        (finShr1 s) (finShr4 t4) ((m2 + (n3 + (n4 + (m5 + m6)))) + 1) := Eval.iteF hrY1 e12345
    have hfull : Eval main finishShr s (finShr4 t4)
        (m1 + ((m2 + (n3 + (n4 + (m5 + m6)))) + 1)) := Eval.seq hm1 hite
    have hlenrev : (b :: B').reverse.length = (b :: B').length := List.length_reverse
    refine ⟨finShr4 t4, m1 + ((m2 + (n3 + (n4 + (m5 + m6)))) + 1), hfull, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · -- cost bound
      omega
    · -- stack 0
      rw [finShr4_stk_0]
      have h3r : (finShr3 t4).reg rY = sg := by rw [finShr3_reg_rY, hSg4]; rfl
      have h30 : (finShr3 t4).stk 0 = t4.stk 0 := finShr3_stk_ne t4 (by decide : (0 : Stk) ≠ sSg)
      rw [h3r, h30, h0t4]
      simp only [List.reverse_reverse, List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append]
    · -- sM
      rw [finShr4_stk_ne t4 (by decide : sM ≠ 0), finShr3_stk_ne t4 (by decide : sM ≠ sSg),
        ho4 sM (by decide) (by decide)]
      exact hM3
    · -- sSg
      rw [finShr4_stk_ne t4 (by decide : sSg ≠ 0), finShr3_stk_sSg, hSg4]
      rfl
    · -- sT
      rw [finShr4_stk_ne t4 (by decide : sT ≠ 0), finShr3_stk_ne t4 (by decide : sT ≠ sSg)]
      exact hT4
    · -- sK
      rw [finShr4_stk_ne t4 (by decide : sK ≠ 0), finShr3_stk_ne t4 (by decide : sK ≠ sSg),
        ho4 sK (by decide) (by decide), ho3 sK (by decide) (by decide),
        finShr2_stk_ne s (by decide : sK ≠ 0)]
    · -- sP
      rw [finShr4_stk_ne t4 (by decide : sP ≠ 0), finShr3_stk_ne t4 (by decide : sP ≠ sSg),
        ho4 sP (by decide) (by decide), ho3 sP (by decide) (by decide),
        finShr2_stk_ne s (by decide : sP ≠ 0)]
    · -- sA
      rw [finShr4_stk_ne t4 (by decide : sA ≠ 0), finShr3_stk_ne t4 (by decide : sA ≠ sSg),
        ho4 sA (by decide) (by decide), ho3 sA (by decide) (by decide),
        finShr2_stk_ne s (by decide : sA ≠ 0)]
    · -- sT2
      rw [finShr4_stk_ne t4 (by decide : sT2 ≠ 0), finShr3_stk_ne t4 (by decide : sT2 ≠ sSg),
        ho4 sT2 (by decide) (by decide), ho3 sT2 (by decide) (by decide),
        finShr2_stk_ne s (by decide : sT2 ≠ 0)]

end Work.IntLib.Shift
