import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.intDivAPI
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.eval_mvRev
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.subRippleBits_padBits
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.mvRevOntoTight
import Submission.Work.IntLib.cleanupSpec
import Submission.Work.IntLib.div_prep_eval
import Submission.Work.IntLib.dropWhile_rev_padBits_bits
import Submission.Work.IntLib.div_rippleProgBR_eval

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.IntLib

open HvdH

/-! ## Pure arithmetic and encoding facts -/

/-- The low `L` bits of `b.natAbs + 2^L - rv` are `b.natAbs - rv`. -/
theorem ff_mod_ripple (a b : ℤ) (hb : 0 < b) (L rv : ℕ) (hL : L = b.natAbs.size + 1)
    (hrv : rv = a.natAbs % b.natAbs) :
    (b.natAbs + 2 ^ L - rv) % 2 ^ L = b.natAbs - rv := by
  have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
  have hrvlt : rv < b.natAbs := by rw [hrv]; exact Nat.mod_lt _ hbpos
  have hlt : b.natAbs < 2 ^ L := by
    rw [hL]; exact (Nat.size_le).mp (Nat.le_succ _)
  have hkey : b.natAbs + 2 ^ L - rv = 2 ^ L + (b.natAbs - rv) := by omega
  rw [hkey, Nat.add_comm]
  have h := Nat.add_mul_mod_self_left (b.natAbs - rv) (2 ^ L) 1
  simp only [Nat.mul_one] at h
  rw [h, Nat.mod_eq_of_lt (by omega)]

/-- The ripple of the fixed `fixFmod` computes `b.natAbs - rv`. -/
theorem ff_subRipple (a b : ℤ) (hb : 0 < b) (L rv : ℕ) (hL : L = b.natAbs.size + 1)
    (hrv : rv = a.natAbs % b.natAbs) :
    Work.IntLib.subRippleBits (Work.IntLib.padBits b.natAbs L) (Work.IntLib.padBits rv L) false
      = (false, Work.IntLib.padBits (b.natAbs - rv) L) := by
  have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
  have hrvlt : rv < b.natAbs := by rw [hrv]; exact Nat.mod_lt _ hbpos
  have hlt : b.natAbs < 2 ^ L := by rw [hL]; exact (Nat.size_le).mp (Nat.le_succ _)
  rw [Work.IntLib.subRippleBits_padBits b.natAbs rv L hlt (by omega)]
  have h1 : decide (rv > b.natAbs) = false := by
    simp [decide_eq_false_iff_not, not_lt]; omega
  rw [h1, ff_mod_ripple a b hb L rv hL hrv]

/-- Encoding of a nonnegative integer. -/
theorem ff_enc_nat (v : ℕ) :
    (HvdH.Val.int (v : ℤ)).enc =
      Glyph.pos :: (Work.IntLib.bitsG (Computability.encodeNat v) ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int]
  simp [Int.natAbs_natCast, Work.IntLib.bitsG]

/-- Encoding of `0`. -/
theorem ff_enc_zero : (HvdH.Val.int 0).enc = [Glyph.pos, Glyph.iend] := by
  have h0 : Computability.encodeNat (0 : ℕ) = [] := (Work.IntLib.encodeNat_eq_nil_iff 0).mpr rfl
  rw [Work.IntLib.enc_int]
  simp [Work.IntLib.bitsG, h0]

/-- Basic size facts about the parameters of `fixFmod`. -/
theorem ff_size_facts (a b : ℤ) (hb : 0 < b) (L rv : ℕ) (hL : L = b.natAbs.size + 1)
    (hrv : rv = a.natAbs % b.natAbs) :
    rv < b.natAbs ∧ b.natAbs < 2 ^ L ∧ b.natAbs < 2 ^ (L - 1) ∧ 2 ≤ L ∧ rv < 2 ^ L := by
  have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
  have hrvlt : rv < b.natAbs := by rw [hrv]; exact Nat.mod_lt _ hbpos
  have hlt : b.natAbs < 2 ^ L := by rw [hL]; exact (Nat.size_le).mp (Nat.le_succ _)
  have hlt1 : b.natAbs < 2 ^ (L - 1) := by
    have h := (Nat.size_le (m := b.natAbs) (n := b.natAbs.size)).mp (Nat.le_refl _)
    have hL' : L - 1 = b.natAbs.size := by omega
    rw [hL']
    exact h
  have hL2 : 2 ≤ L := by
    have hne : b.natAbs.size ≠ 0 := by
      intro hh
      exact absurd (Nat.size_eq_zero.mp hh) (ne_of_gt hbpos)
    omega
  exact ⟨hrvlt, hlt, hlt1, hL2, by omega⟩

/-! ## Projection lemmas for the concrete states -/

@[simp] theorem ff_stk_updStk_self (s : State) (k : Stk) (l : List Glyph) :
    (s.updStk k l).stk k = l := by
  simp [State.updStk, Function.update_apply, if_pos rfl]

@[simp] theorem ff_stk_updStk_ne (s : State) (k j : Stk) (l : List Glyph) (h : j ≠ k) :
    (s.updStk k l).stk j = s.stk j := by
  simp [State.updStk, Function.update_apply, if_neg h]

@[simp] theorem ff_stk_updReg (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (s.updReg r g).stk j = s.stk j := rfl

@[simp] theorem ff_reg_updReg_self (s : State) (r : Reg) (g : Glyph) :
    (s.updReg r g).reg r = g := by
  simp [State.updReg, Function.update_apply, if_pos rfl]

@[simp] theorem ff_reg_updReg_ne (s : State) (r r' : Reg) (g : Glyph) (h : r' ≠ r) :
    (s.updReg r g).reg r' = s.reg r' := by
  simp [State.updReg, Function.update_apply, if_neg h]

@[simp] theorem ff_reg_updStk (s : State) (k : Stk) (l : List Glyph) (r : Reg) :
    (s.updStk k l).reg r = s.reg r := rfl

/-! ## Register tracking -/

/-- The registers a program may write. -/
def Writes (r : Reg) : Cmd → Prop
  | .skip => False
  | .pop _ r' => r' = r
  | .peek _ r' => r' = r
  | .push _ _ => False
  | .set r' _ => r' = r
  | .mov dst _ => dst = r
  | .seq a b => Writes r a ∨ Writes r b
  | .ite _ _ a b => Writes r a ∨ Writes r b
  | .loop _ _ b => Writes r b
  | .self => True

/-- A register that a program never writes is preserved. -/
theorem ff_reg_preserved (main : Cmd) (r : Reg) {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) (hw : Writes r c → False) : s'.reg r = s.reg r := by
  induction h with
  | skip => rfl
  | pop k r' =>
      have hr : r' ≠ r := fun hh => hw (by simp [Writes, hh])
      simp [State.tPop, State.updReg, Function.update_apply, if_neg (Ne.symm hr)]
  | peek k r' =>
      have hr : r' ≠ r := fun hh => hw (by simp [Writes, hh])
      simp [State.updReg, Function.update_apply, if_neg (Ne.symm hr)]
  | push k r' => rfl
  | set r' c' =>
      have hr : r' ≠ r := fun hh => hw (by simp [Writes, hh])
      simp [State.updReg, Function.update_apply, if_neg (Ne.symm hr)]
  | mov dst src =>
      have hr : dst ≠ r := fun hh => hw (by simp [Writes, hh])
      simp [State.updReg, Function.update_apply, if_neg (Ne.symm hr)]
  | seq h1 h2 ih1 ih2 =>
      rw [ih2 (fun hh => hw (Or.inr hh)), ih1 (fun hh => hw (Or.inl hh))]
  | iteT hr h1 ih => exact ih (fun hh => hw (Or.inl hh))
  | iteF hr h1 ih => exact ih (fun hh => hw (Or.inr hh))
  | loopF hne => rfl
  | loopT hr hb htl ihb ihtl => rw [ihtl (fun hh => hw hh), ihb (fun hh => hw hh)]
  | self h1 ih => exact absurd trivial hw

/-- `mvRevOnto` writes nothing but its own register. -/
theorem ff_writes_mvRevOnto (sg : Reg) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg) :
    Writes sg (Work.IntLib.mvRevOnto k T k' r) → r = sg := by
  intro hw
  simp [Writes, Work.IntLib.mvRevOnto, Work.IntLib.consume, Work.IntLib.consumeLoop,
    Work.IntLib.consumeStep] at hw
  tauto

/-- `mkG k m` pushes the marker `m` on stack `k`. -/
theorem ff_mkG (main : Cmd) (k : Stk) (m : Glyph) (s : State) :
    Eval main (Div.mkG k m) s ((s.updReg Div.rgT m).updStk k (m :: s.stk k)) 2 := by
  have h1 : Eval main (.set Div.rgT m) s (s.updReg Div.rgT m) 1 := Eval.set Div.rgT m s
  have h2 : Eval main (.push k Div.rgT) (s.updReg Div.rgT m)
      ((s.updReg Div.rgT m).updStk k (m :: (s.updReg Div.rgT m).stk k)) 1 :=
    Eval.push k Div.rgT (s.updReg Div.rgT m)
  have h := Eval.seq h1 h2
  simpa [Div.mkG, State.updReg, State.updStk] using h

/-- `Div.emit` (with its final `skip`): costs `5 * l.length + 16`. -/
theorem ff_emit (main : Cmd) (sg : Reg) (l bkX A : List Glyph) (s : State)
    (hX : s.stk Div.stX = l ++ gX :: bkX) (h0 : s.stk 0 = A)
    (hT : ∀ g ∈ l, g ≠ gX) (hne : Div.stX ≠ 0) (hsg : sg ≠ Div.rgT) :
    ∃ s' n, Eval main (Div.emit sg) s s' n ∧ n ≤ 5 * l.length + 16 ∧
      s'.stk 0 = s.reg sg :: (l.reverse ++ [Glyph.iend] ++ A) ∧
      s'.stk Div.stX = [gX] ++ bkX ∧
      ∀ j : Stk, j ≠ 0 → j ≠ Div.stX → s'.stk j = s.stk j := by
  set s1 : State := ⟨Function.update s.reg Div.rgT Glyph.iend, s.stk⟩ with hs1
  have hev1 : Eval main (.set Div.rgT Glyph.iend) s s1 1 := by
    rw [hs1]; exact Eval.set Div.rgT Glyph.iend s
  have h1sg : s1.reg sg = s.reg sg := by simp [hs1, Function.update_of_ne hsg]
  set s2 : State := ⟨s1.reg, Function.update s1.stk 0 (s1.reg Div.rgT :: s1.stk 0)⟩ with hs2
  have hev2 : Eval main (.push 0 Div.rgT) s1 s2 1 := by
    rw [hs2]; exact Eval.push 0 Div.rgT s1
  have h2sg : s2.reg sg = s1.reg sg := by simp [hs2]
  have h2X : s2.stk Div.stX = l ++ gX :: bkX := by
    simp [hs2, hs1, Function.update_apply,
      if_neg (show ¬ (Div.stX = (0 : Stk)) from by decide)]
    exact hX
  have h20 : s2.stk 0 = Glyph.iend :: A := by
    simp [hs2, hs1, Function.update_apply, h0]
  obtain ⟨s3, n3, hev3, hc3, h3X, h30, hfr3⟩ :=
    mvRevOntoTight main Div.stX gX 0 Div.rgT l bkX (Glyph.iend :: A) s2 hT h2X h20 (by decide)
  have hNW : Writes sg (Work.IntLib.mvRevOnto Div.stX gX 0 Div.rgT) → False :=
    fun hw => hsg (ff_writes_mvRevOnto sg Div.stX gX 0 Div.rgT hw).symm
  have h3sg : s3.reg sg = s2.reg sg := ff_reg_preserved main sg hev3 hNW
  set s4 : State := (s3.updReg Div.rgT gX).updStk Div.stX (gX :: s3.stk Div.stX) with hs4
  have hev4 : Eval main (Div.mkG Div.stX gX) s3 s4 2 := by
    rw [hs4]; exact ff_mkG main Div.stX gX s3
  have h4X : s4.stk Div.stX = [gX] ++ bkX := by
    simp [hs4, State.updStk, State.updReg, Function.update_apply, h3X]
  have h40 : s4.stk 0 = l.reverse ++ Glyph.iend :: A := by
    simp [hs4, State.updStk, State.updReg, Function.update_apply,
      if_neg (show ¬ ((0 : Stk) = Div.stX) from by decide)]
    exact h30
  have h4sg : s4.reg sg = s.reg sg := by
    simp [hs4, State.updStk, State.updReg, Function.update_apply, if_neg hsg]
    rw [h3sg, h2sg, h1sg]
  set s5 : State := ⟨Function.update s4.reg Div.rgT (s4.reg sg), s4.stk⟩ with hs5
  have hev5 : Eval main (.mov Div.rgT sg) s4 s5 1 := by
    rw [hs5]; exact Eval.mov Div.rgT sg s4
  have h5_0 : s5.stk 0 = l.reverse ++ Glyph.iend :: A := by simp [hs5]; exact h40
  have h5reg : s5.reg Div.rgT = s.reg sg := by
    simp [hs5]
    exact h4sg
  set s6 : State := ⟨s5.reg, Function.update s5.stk 0 (s5.reg Div.rgT :: s5.stk 0)⟩ with hs6
  have hev6 : Eval main (.push 0 Div.rgT) s5 s6 1 := by
    rw [hs6]; exact Eval.push 0 Div.rgT s5
  have h6_0 : s6.stk 0 = s.reg sg :: (l.reverse ++ [Glyph.iend] ++ A) := by
    simp [hs6, h5reg, h5_0]
  have h6X : s6.stk Div.stX = [gX] ++ bkX := by
    simp [hs6, Function.update_apply,
      if_neg (show ¬ (Div.stX = (0 : Stk)) from by decide)]
    exact h4X
  have h6fr : ∀ j : Stk, j ≠ 0 → j ≠ Div.stX → s6.stk j = s.stk j := by
    intro j hj0 hjX
    simp only [hs6, hs5, hs4, State.updStk, State.updReg, Function.update_apply,
      if_neg hj0, if_neg hjX]
    rw [hfr3 j hjX hj0]
    simp [hs2, hs1, Function.update_apply, if_neg hj0]
  refine ⟨s6, 1 + (1 + (n3 + (2 + (1 + (1 + 1))))), ?_, by omega, h6_0, h6X, h6fr⟩
  have h := Eval.seq hev1
    (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.seq hev5 (Eval.seq hev6 (Eval.skip s6))))))
  simpa [Div.emit, Div.seqs, Div.seqs_cons, Div.seqs_nil, Div.mkG] using h

/-! ## The branches of `fixFmod` -/

/-- The `rv = 0` inner branch of `fixFmod`. -/
def ffIA : Cmd :=
  Div.seqs [Cmd.set Div.rgV Glyph.iend, Cmd.push 0 Div.rgV, Cmd.set Div.rgT Glyph.pos,
    Cmd.push 0 Div.rgT, Div.cleanup]

/-- The `rv ≠ 0` inner branch of `fixFmod`. -/
def ffIB : Cmd :=
  Div.seqs [Work.IntLib.mvRevOnto Div.stS gS Div.stR Div.rgT, Div.mkG Div.stS gS,
    Div.prep Div.stR gR, Cmd.set Div.rgW Glyph.pos, Div.emit Div.rgW, Div.cleanup]

/-- The `a < 0` branch of `fixFmod`. -/
def ffA : Cmd :=
  Div.seqs [Div.rippleProg Div.stB Div.stR gB gR, Div.mkG Div.stB gB, Div.mkG Div.stR gR,
    Work.IntLib.stripZeros Div.stC gC Div.rgT, Cmd.peek Div.stC Div.rgV,
    Cmd.ite Div.rgV gC ffIA ffIB]

/-- The `a ≥ 0` branch of `fixFmod`. -/
def ffB : Cmd :=
  Div.seqs [Div.prep Div.stR gR, Cmd.set Div.rgW Glyph.pos, Div.emit Div.rgW, Div.cleanup]

/-- `dropWhile` of the reversed low bits of `n` is the encoding of `n`. -/
theorem ff_dropWhile_rev_bitsG (n L : ℕ) (h : n < 2 ^ L) :
    ((bitsG (padBits n L)).reverse).dropWhile (fun g => g = Glyph.bit false)
      = (bitsG (Computability.encodeNat n)).reverse := by
  rw [← List.map_reverse]
  exact dropWhile_rev_padBits_bits n L h

/-- The same, in the argument order produced by `stripZeros`. -/
theorem ff_dropWhile_bitsG_rev (n L : ℕ) (h : n < 2 ^ L) :
    (bitsG ((padBits n L).reverse)).dropWhile (fun g => g = Glyph.bit false)
      = (bitsG (Computability.encodeNat n)).reverse :=
  dropWhile_rev_padBits_bits n L h



/-- A region of bits never contains the marker `gX`. -/
theorem ff_dropWhile_rev_bitsG_mem (rv L : ℕ) :
    ∀ g ∈ ((bitsG (padBits rv L)).reverse).dropWhile (fun g => g = Glyph.bit false), g ≠ gX := by
  intro g hg hcon
  have h1 : g ∈ (bitsG (padBits rv L)).reverse :=
    List.Sublist.mem hg (List.dropWhile_sublist (fun g => g = Glyph.bit false))
  have h1' : g ∈ (padBits rv L).map Glyph.bit := List.mem_reverse.mp h1
  obtain ⟨b', -, hb'⟩ := List.mem_map.mp h1'
  rw [← hb'] at hcon
  cases hcon


/-- The stacks that a program may write. -/
def WStk (j : Stk) : Cmd → Prop
  | .skip => False
  | .pop k _ => k = j
  | .peek k _ => k = j
  | .push k _ => k = j
  | .set _ _ => False
  | .mov _ _ => False
  | .seq a b => WStk j a ∨ WStk j b
  | .ite _ _ a b => WStk j a ∨ WStk j b
  | .loop _ _ b => WStk j b
  | .self => True

/-- A stack that a program never writes is preserved. -/
theorem ff_stk_preserved (main : Cmd) (j : Stk) {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) (hw : WStk j c → False) : s'.stk j = s.stk j := by
  induction h with
  | skip => rfl
  | pop k r =>
      have hk : k ≠ j := fun hh => hw (by simp [WStk, hh])
      simp [State.tPop, Function.update_apply, if_neg (Ne.symm hk)]
  | peek k r =>
      have hk : k ≠ j := fun hh => hw (by simp [WStk, hh])
      simp [State.updReg]
  | push k r =>
      have hk : k ≠ j := fun hh => hw (by simp [WStk, hh])
      simp [Function.update_apply, if_neg (Ne.symm hk)]
  | set r c => rfl
  | mov dst src => rfl
  | seq h1 h2 ih1 ih2 => rw [ih2 (fun hh => hw (Or.inr hh)), ih1 (fun hh => hw (Or.inl hh))]
  | iteT hr h1 ih => exact ih (fun hh => hw (Or.inl hh))
  | iteF hr h1 ih => exact ih (fun hh => hw (Or.inr hh))
  | loopF hne => rfl
  | loopT hr hb htl ihb ihtl => rw [ihtl (fun hh => hw hh), ihb (fun hh => hw hh)]
  | self h1 ih => exact absurd trivial hw

/-- `Div.cleanup` never writes stack 0. -/
theorem ff_cleanup_W0 : WStk (0 : Stk) Div.cleanup → False := by
  intro hh
  have h : Div.cleanup = Div.seqs [Work.IntLib.dropRgn Div.stP gP Div.rgT, Work.IntLib.dropRgn Div.stB gB Div.rgT,
      Work.IntLib.dropRgn Div.stR gR Div.rgT, Work.IntLib.dropRgn Div.stQ gQ Div.rgT,
      Work.IntLib.dropRgn Div.stS gS Div.rgT, Work.IntLib.dropRgn Div.stC gC Div.rgT,
      Work.IntLib.dropRgn Div.stD gD Div.rgT, Work.IntLib.dropRgn Div.stX gX Div.rgT,
      Work.IntLib.dropRgn Div.stY gY Div.rgT] := rfl
  rw [h] at hh
  simp only [Div.seqs_cons, Div.seqs_nil, WStk, Work.IntLib.dropRgn, Work.IntLib.consume,
    Work.IntLib.consumeLoop, Work.IntLib.consumeStep] at hh
  exact absurd hh (by decide)

/-- `Div.cleanup` also leaves stack 0 alone (which `cleanupSpec` does not record). -/
theorem ff_cleanup (main : Cmd) (b0 : State) (s : State)
    (lP lB lR lQ lS lC lD lX lY : List Glyph)
    (hP : s.stk Div.stP = lP ++ [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = lB ++ [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = lR ++ [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = lQ ++ [gQ] ++ b0.stk Div.stQ)
    (hS : s.stk Div.stS = lS ++ [gS] ++ b0.stk Div.stS)
    (hC : s.stk Div.stC = lC ++ [gC] ++ b0.stk Div.stC)
    (hD : s.stk Div.stD = lD ++ [gD] ++ b0.stk Div.stD)
    (hX : s.stk Div.stX = lX ++ [gX] ++ b0.stk Div.stX)
    (hY : s.stk Div.stY = lY ++ [gY] ++ b0.stk Div.stY)
    (nP : ∀ g ∈ lP, g ≠ gP) (nB : ∀ g ∈ lB, g ≠ gB)
    (nR : ∀ g ∈ lR, g ≠ gR) (nQ : ∀ g ∈ lQ, g ≠ gQ)
    (nS : ∀ g ∈ lS, g ≠ gS) (nC : ∀ g ∈ lC, g ≠ gC)
    (nD : ∀ g ∈ lD, g ≠ gD) (nX : ∀ g ∈ lX, g ≠ gX)
    (nY : ∀ g ∈ lY, g ≠ gY)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, Eval main Div.cleanup s s' n ∧
      n ≤ 5 * (lP.length + lB.length + lR.length + lQ.length + lS.length + lC.length +
        lD.length + lX.length + lY.length) + 117 ∧
      s'.stk 0 = s.stk 0 ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  obtain ⟨s', n, hev, hcost, hframe⟩ :=
    cleanupSpec main b0 s lP lB lR lQ lS lC lD lX lY hP hB hR hQ hS hC hD hX hY
      nP nB nR nQ nS nC nD nX nY hoth
  exact ⟨s', n, hev, hcost, ff_stk_preserved main 0 hev ff_cleanup_W0, hframe⟩

/-! ## Branch `a ≥ 0` -/



theorem ff_branchB (main : Cmd) (b0 : State) (Z : List Glyph) (a b : ℤ) (L j rv qv : ℕ)
    (s : State) (hb : 0 < b) (hL : L = b.natAbs.size + 1) (hrv : rv = a.natAbs % b.natAbs)
    (ha : 0 ≤ a) (h0 : s.stk 0 = Z)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = bitsG (padBits b.natAbs L) ++ [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : s.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : s.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : s.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hS9 : s.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, Eval main ffB s s' n ∧ n ≤ 17 * L + 5 * j + 150 ∧
      s'.stk 0 = (Val.int (a.fmod b)).enc ++ Z ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  obtain ⟨hrvlt, hbL, hbL1, hL2, hrvL⟩ := ff_size_facts a b hb L rv hL hrv
  -- ## prep stR gR
  have hR' : s.stk Div.stR = bitsG (padBits rv L) ++ gR :: b0.stk Div.stR := by simpa using hR
  have hS8' : s.stk Div.stX = [gX] ++ b0.stk Div.stX := hS8
  obtain ⟨s1, n1, hev1, hc1, h1R, h1X, h1fr⟩ :=
    div_prep_eval main Div.stR gR (padBits rv L) (b0.stk Div.stR) (b0.stk Div.stX) s
      (fun b' => by intro h; cases h) hR' hS8' (by decide)
  have hc1' : n1 ≤ 7 * L + 19 := by
    rw [Work.IntLib.padBits_length] at hc1
    exact hc1
  -- ## set rgW pos
  set s2 : State := ⟨Function.update s1.reg Div.rgW Glyph.pos, s1.stk⟩ with hs2
  have hev2 : Eval main (.set Div.rgW Glyph.pos) s1 s2 1 := by
    rw [hs2]; exact Eval.set Div.rgW Glyph.pos s1
  have h2fr : ∀ q : Stk, s2.stk q = s1.stk q := by intro q; simp [hs2]
  have h2reg : s2.reg Div.rgW = Glyph.pos := by simp [hs2]
  set l2 : List Glyph := ((bitsG (padBits rv L)).reverse).dropWhile (fun g => g = Glyph.bit false)
    with hl2def
  have h2X : s2.stk Div.stX = l2 ++ gX :: b0.stk Div.stX := by
    rw [h2fr, h1X, hl2def]
    simp
  have h20 : s2.stk 0 = Z := by
    rw [h2fr, h1fr 0 (by decide) (by decide)]
    exact h0
  -- ## emit rgW
  obtain ⟨s3, n3, hev3, hc3, h30, h3X, h3fr⟩ :=
    ff_emit main Div.rgW l2 (b0.stk Div.stX) Z s2 h2X h20
      (ff_dropWhile_rev_bitsG_mem rv L) (by decide) (by decide)
  have hl2 : l2 = (bitsG (Computability.encodeNat rv)).reverse := by
    rw [hl2def]; exact ff_dropWhile_rev_bitsG rv L hrvL
  have hlen2 : l2.length ≤ L - 1 := by
    rw [hl2]
    simp only [Work.IntLib.bitsG, List.length_reverse, List.length_map,
      Work.IntLib.encodeNat_length]
    exact Nat.size_le.mpr (by omega)
  have hc3' : n3 ≤ 5 * L + 11 := by omega
  have hval3 : s3.stk 0 = (Val.int (rv : ℤ)).enc ++ Z := by
    rw [h30, hl2, List.reverse_reverse, ff_enc_nat rv, h2reg]
    simp [List.append_assoc]
  have hfmod : a.fmod b = (rv : ℤ) := by
    have h := (Work.IntLib.intDivAPI).2.2.2 a b hb
    rw [h, if_pos ha, hrv]
  -- ## cleanup
  have h3P : s3.stk Div.stP = [] ++ [gP] ++ b0.stk Div.stP := by
    rw [h3fr Div.stP (by decide) (by decide), h2fr, h1fr Div.stP (by decide) (by decide), hP] <;> simp
  have h3B : s3.stk Div.stB = bitsG (padBits b.natAbs L) ++ [gB] ++ b0.stk Div.stB := by
    rw [h3fr Div.stB (by decide) (by decide), h2fr, h1fr Div.stB (by decide) (by decide), hB] <;> simp
  have h3R : s3.stk Div.stR = [] ++ [gR] ++ b0.stk Div.stR := by
    rw [h3fr Div.stR (by decide) (by decide), h2fr, h1R] <;> simp
  have h3Q : s3.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [h3fr Div.stQ (by decide) (by decide), h2fr, h1fr Div.stQ (by decide) (by decide), hQ] <;> simp
  have h3S : s3.stk Div.stS = [] ++ [gS] ++ b0.stk Div.stS := by
    rw [h3fr Div.stS (by decide) (by decide), h2fr, h1fr Div.stS (by decide) (by decide), hS5] <;> simp
  have h3C : s3.stk Div.stC = [] ++ [gC] ++ b0.stk Div.stC := by
    rw [h3fr Div.stC (by decide) (by decide), h2fr, h1fr Div.stC (by decide) (by decide), hS6] <;> simp
  have h3D : s3.stk Div.stD = [] ++ [gD] ++ b0.stk Div.stD := by
    rw [h3fr Div.stD (by decide) (by decide), h2fr, h1fr Div.stD (by decide) (by decide), hS7] <;> simp
  have h3Xc : s3.stk Div.stX = [] ++ [gX] ++ b0.stk Div.stX := by
    rw [h3X] <;> simp
  have h3Y : s3.stk Div.stY = [] ++ [gY] ++ b0.stk Div.stY := by
    rw [h3fr Div.stY (by decide) (by decide), h2fr, h1fr Div.stY (by decide) (by decide), hS9] <;> simp
  have h3oth : ∀ k : Stk, 10 ≤ k.val → s3.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk
    have hkX : k ≠ Div.stX := by intro h; rw [h] at hk; simp at hk
    have hkR : k ≠ Div.stR := by intro h; rw [h] at hk; simp at hk
    rw [h3fr k hk0 hkX, h2fr, h1fr k hkR hkX]
    exact hoth k hk
  obtain ⟨s4, n4, hev4, hc4, h4_0, h4fr⟩ :=
    ff_cleanup main b0 s3 ([] : List Glyph) (bitsG (padBits b.natAbs L)) ([] : List Glyph)
      (bitsG (padBits qv j)) ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
      ([] : List Glyph) ([] : List Glyph)
      h3P h3B h3R h3Q h3S h3C h3D h3Xc h3Y
      (by intro g hg; cases hg)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; cases hg)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; cases hg) (by intro g hg; cases hg) (by intro g hg; cases hg)
      (by intro g hg; cases hg) (by intro g hg; cases hg) h3oth
  have hc4' : n4 ≤ 5 * L + 5 * j + 117 := by
    have h1 : (bitsG (padBits b.natAbs L)).length = L := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h2 : (bitsG (padBits qv j)).length = j := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h3 := hc4
    rw [h1, h2] at h3
    simp only [List.length_nil, Nat.add_zero] at h3
    omega
  refine ⟨s4, n1 + (1 + (n3 + (n4 + 1))), ?_, ?_, ?_, h4fr⟩
  · have h := Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.skip s4))))
    simpa [ffB, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
  · omega
  · rw [h4_0, hval3, hfmod]

/-! ## Branch `a < 0` -/

/-- The region left on stack 5 (`stS`) by the ripple subtraction: the low `L` bits of
`b.natAbs - rv`, most significant bit first (the order in which the stack holds them). -/
def ffSreg (bN rv L : ℕ) : List Bool :=
  ((Work.IntLib.subRippleBits (Work.IntLib.padBits bN L) (Work.IntLib.padBits rv L) false).2).reverse

theorem ffSreg_length (bN rv L : ℕ) (hb : bN < 2 ^ L) (hrv : rv < 2 ^ L) :
    (ffSreg bN rv L).length = L := by
  rw [ffSreg, List.length_reverse, Work.IntLib.subRippleBits_padBits bN rv L hb hrv]
  exact Work.IntLib.padBits_length _ L

theorem ff_bitsG_reverse (l : List Bool) :
    (Work.IntLib.bitsG l).reverse = Work.IntLib.bitsG l.reverse :=
  List.map_reverse.symm

theorem ff_app_sing_app {α : Type*} (a : List α) (x : α) (b : List α) :
    a ++ [x] ++ b = a ++ x :: b := by rw [List.append_assoc, List.singleton_append]

theorem ff_bit_ne_gP (b : Bool) : Glyph.bit b ≠ gP := by intro h; cases h
theorem ff_bit_ne_gB (b : Bool) : Glyph.bit b ≠ gB := by intro h; cases h
theorem ff_bit_ne_gR (b : Bool) : Glyph.bit b ≠ gR := by intro h; cases h
theorem ff_bit_ne_gQ (b : Bool) : Glyph.bit b ≠ gQ := by intro h; cases h
theorem ff_bit_ne_gS (b : Bool) : Glyph.bit b ≠ gS := by intro h; cases h
theorem ff_bit_ne_gC (b : Bool) : Glyph.bit b ≠ gC := by intro h; cases h
theorem ff_bit_ne_gD (b : Bool) : Glyph.bit b ≠ gD := by intro h; cases h
theorem ff_bit_ne_gX (b : Bool) : Glyph.bit b ≠ gX := by intro h; cases h
theorem ff_bit_ne_gY (b : Bool) : Glyph.bit b ≠ gY := by intro h; cases h
theorem ff_bit_ne_eos (b : Bool) : Glyph.bit b ≠ Glyph.eos := by intro h; cases h

theorem ff_bitsG_ne (l : List Bool) {m : Glyph} (h : ∀ b : Bool, Glyph.bit b ≠ m) :
    ∀ g ∈ Work.IntLib.bitsG l, g ≠ m := by
  intro g hg hcon
  obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg
  exact h b' (hb'.trans hcon)

/-- The first glyph of the stripped remainder region is the marker `gC` exactly when the remainder
region is empty. -/
theorem ff_headD_encC (X : List Bool) (bk : List Glyph) :
    ((Work.IntLib.bitsG X).reverse ++ [gC] ++ bk).headD Glyph.eos = gC ↔ X = [] := by
  constructor
  · intro h
    by_contra hX
    have hne : (Work.IntLib.bitsG X).reverse ≠ [] := by
      intro hnil
      rw [List.reverse_eq_nil_iff] at hnil
      exact hX (List.map_eq_nil_iff.mp hnil)
    cases hrev : (Work.IntLib.bitsG X).reverse with
    | nil => exact absurd hrev hne
    | cons g gs =>
        rw [hrev] at h
        simp only [List.cons_append, List.headD_cons] at h
        have hmem : g ∈ (Work.IntLib.bitsG X).reverse := by rw [hrev]; simp
        obtain ⟨b', -, hb'⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
        rw [← hb'] at h
        cases h
  · intro hX
    rw [hX, Work.IntLib.bitsG, List.map_nil, List.reverse_nil, List.nil_append]
    rfl

/-- The four commands of the `a < 0` branch that follow the ripple: restore the frame markers `gB`
and `gR`, strip the padding of the remainder region and read its first glyph into `rgV`. -/
theorem ff_prefixA_rest (main : Cmd) (b0 : State) (Z : List Glyph) (b : ℤ) (rv qv L j : ℕ)
    (s : State)
    (h0 : s.stk 0 = Z)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = b0.stk Div.stB)
    (hR : s.stk Div.stR = b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS : s.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS)
    (hC : s.stk Div.stC = bitsG (padBits rv L).reverse ++ [gC] ++ b0.stk Div.stC)
    (hD : s.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD)
    (hX : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hY : s.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hrvL : rv < 2 ^ L)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s1 s2 s3 s4 n3,
      Eval main (Div.mkG Div.stB gB) s s1 2 ∧
      Eval main (Div.mkG Div.stR gR) s1 s2 2 ∧
      Eval main (Work.IntLib.stripZeros Div.stC gC Div.rgT) s2 s3 n3 ∧
      Eval main (Cmd.peek Div.stC Div.rgV) s3 s4 1 ∧
      n3 ≤ 2 * L + 8 ∧
      s4.stk 0 = Z ∧
      s4.stk Div.stP = [gP] ++ b0.stk Div.stP ∧
      s4.stk Div.stB = [gB] ++ b0.stk Div.stB ∧
      s4.stk Div.stR = [gR] ++ b0.stk Div.stR ∧
      s4.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ ∧
      s4.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS ∧
      s4.stk Div.stC = (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC ∧
      s4.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD ∧
      s4.stk Div.stX = [gX] ++ b0.stk Div.stX ∧
      s4.stk Div.stY = [gY] ++ b0.stk Div.stY ∧
      (∀ k : Stk, 10 ≤ k.val → s4.stk k = b0.stk k) ∧
      s4.reg Div.rgV =
        ((bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC).headD
          Glyph.eos := by
  -- `mkG stB gB`
  set s1 : State := (s.updReg Div.rgT gB).updStk Div.stB (gB :: s.stk Div.stB) with hs1
  have hev1 : Eval main (Div.mkG Div.stB gB) s s1 2 := by
    rw [hs1]; exact ff_mkG main Div.stB gB s
  have h1B : s1.stk Div.stB = [gB] ++ b0.stk Div.stB := by
    rw [hs1, State.updStk_same, hB]
    rfl
  have h1fr : ∀ k : Stk, k ≠ Div.stB → s1.stk k = s.stk k := by
    intro k hk
    rw [hs1, State.updStk_apply, if_neg hk, State.updReg_stk]
  -- `mkG stR gR`
  set s2 : State := (s1.updReg Div.rgT gR).updStk Div.stR (gR :: s1.stk Div.stR) with hs2
  have hev2 : Eval main (Div.mkG Div.stR gR) s1 s2 2 := by
    rw [hs2]; exact ff_mkG main Div.stR gR s1
  have h2R : s2.stk Div.stR = [gR] ++ b0.stk Div.stR := by
    rw [hs2, State.updStk_same, h1fr Div.stR (by decide), hR]
    rfl
  have h2fr : ∀ k : Stk, k ≠ Div.stR → s2.stk k = s1.stk k := by
    intro k hk
    rw [hs2, State.updStk_apply, if_neg hk, State.updReg_stk]
  -- `stripZeros stC gC rgT`
  have h2C : s2.stk Div.stC = bitsG ((padBits rv L).reverse) ++ gC :: b0.stk Div.stC := by
    rw [h2fr Div.stC (by decide), h1fr Div.stC (by decide), hC, ff_app_sing_app]
  obtain ⟨s3, n3, hev3, hc3, h3C, h3fr⟩ :=
    Work.IntLib.eval_stripZeros main Div.stC gC Div.rgT ((padBits rv L).reverse)
      (b0.stk Div.stC) s2 (by decide) ff_bit_ne_gC h2C
  have h3C' : s3.stk Div.stC =
      (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC := by
    rw [h3C, ff_dropWhile_bitsG_rev rv L hrvL, ff_app_sing_app]
  have hc3' : n3 ≤ 2 * L + 8 := by
    have h := hc3
    rw [List.length_reverse, Work.IntLib.padBits_length] at h
    exact h
  -- `peek stC rgV`
  set s4 : State := s3.updReg Div.rgV ((s3.stk Div.stC).headD Glyph.eos) with hs4
  have hev4 : Eval main (.peek Div.stC Div.rgV) s3 s4 1 := by
    rw [hs4]; exact Eval.peek Div.stC Div.rgV s3
  have h4fr : ∀ k : Stk, s4.stk k = s3.stk k := by
    intro k; rw [hs4, State.updReg_stk]
  have h4fr' : ∀ k : Stk, k ≠ Div.stB → k ≠ Div.stR → k ≠ Div.stC → s4.stk k = s.stk k := by
    intro k h1 h2 h3
    rw [h4fr k, h3fr k h3, h2fr k h2, h1fr k h1]
  have h40 : s4.stk 0 = Z := by
    rw [h4fr' 0 (by decide) (by decide) (by decide)]
    exact h0
  have h4P : s4.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [h4fr' Div.stP (by decide) (by decide) (by decide)]
    exact hP
  have h4B : s4.stk Div.stB = [gB] ++ b0.stk Div.stB := by
    rw [h4fr Div.stB, h3fr Div.stB (by decide), h2fr Div.stB (by decide)]
    exact h1B
  have h4R : s4.stk Div.stR = [gR] ++ b0.stk Div.stR := by
    rw [h4fr Div.stR, h3fr Div.stR (by decide)]
    exact h2R
  have h4Q : s4.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [h4fr' Div.stQ (by decide) (by decide) (by decide)]
    exact hQ
  have h4S : s4.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS := by
    rw [h4fr' Div.stS (by decide) (by decide) (by decide)]
    exact hS
  have h4C : s4.stk Div.stC =
      (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC := by
    rw [h4fr Div.stC]
    exact h3C'
  have h4D : s4.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [h4fr' Div.stD (by decide) (by decide) (by decide)]
    exact hD
  have h4X : s4.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    rw [h4fr' Div.stX (by decide) (by decide) (by decide)]
    exact hX
  have h4Y : s4.stk Div.stY = [gY] ++ b0.stk Div.stY := by
    rw [h4fr' Div.stY (by decide) (by decide) (by decide)]
    exact hY
  have h4oth : ∀ k : Stk, 10 ≤ k.val → s4.stk k = b0.stk k := by
    intro k hk
    have h1 : k ≠ Div.stB := by rintro rfl; simp at hk
    have h2 : k ≠ Div.stR := by rintro rfl; simp at hk
    have h3 : k ≠ Div.stC := by rintro rfl; simp at hk
    rw [h4fr' k h1 h2 h3]
    exact hoth k hk
  have h4reg : s4.reg Div.rgV =
      ((bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC).headD
        Glyph.eos := by
    rw [hs4, State.updReg_apply, if_pos rfl, h3C']
  exact ⟨s1, s2, s3, s4, n3, hev1, hev2, hev3, hev4, hc3', h40, h4P, h4B, h4R, h4Q, h4S, h4C,
    h4D, h4X, h4Y, h4oth, h4reg⟩

/-- The `rv = 0` inner branch of the `a < 0` case: emit the literal `0`. -/
theorem ff_tail0 (main : Cmd) (b0 : State) (Z : List Glyph) (a b : ℤ) (rv qv L j : ℕ) (s : State)
    (hb : 0 < b) (hL : L = b.natAbs.size + 1) (hrv : rv = a.natAbs % b.natAbs)
    (ha : a < 0) (hrv0 : rv = 0)
    (h0 : s.stk 0 = Z)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS : s.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS)
    (hC : s.stk Div.stC = (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC)
    (hD : s.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD)
    (hX : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hY : s.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, Eval main ffIA s s' n ∧ n ≤ 10 * L + 5 * j + 122 ∧
      s'.stk 0 = (Val.int (a.fmod b)).enc ++ Z ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  obtain ⟨hrvlt, hbL, hbL1, hL2, hrvL⟩ := ff_size_facts a b hb L rv hL hrv
  have hmod0 : a.natAbs % b.natAbs = 0 := by rw [← hrv, hrv0]
  have hfmod : a.fmod b = 0 := by
    rw [Work.IntLib.intDivAPI.2.2.2 a b hb]
    rw [if_neg (show ¬ (0 ≤ a) by omega), if_pos hmod0]
  have henc0 : Computability.encodeNat rv = [] := by
    rw [hrv0]; exact (Work.IntLib.encodeNat_eq_nil_iff 0).mpr rfl
  have hC0 : s.stk Div.stC = [] ++ [gC] ++ b0.stk Div.stC := by
    rw [hC, henc0, Work.IntLib.bitsG, List.map_nil, List.reverse_nil, List.nil_append]
  -- the four commands
  set t1 : State := s.updReg Div.rgV Glyph.iend with ht1
  have hev1 : Eval main (.set Div.rgV Glyph.iend) s t1 1 := by rw [ht1]; exact Eval.set_eq
  have hr1 : t1.reg Div.rgV = Glyph.iend := by rw [ht1]; simp
  set t2 : State := t1.updStk 0 (t1.reg Div.rgV :: t1.stk 0) with ht2
  have hev2 : Eval main (.push 0 Div.rgV) t1 t2 1 := by
    rw [ht2]
    exact Eval.push (main := main) (0 : Stk) Div.rgV t1
  have h20 : t2.stk 0 = Glyph.iend :: Z := by
    rw [ht2, State.updStk_same, hr1, ht1, State.updReg_stk, h0]
  set t3 : State := t2.updReg Div.rgT Glyph.pos with ht3
  have hev3 : Eval main (.set Div.rgT Glyph.pos) t2 t3 1 := by rw [ht3]; exact Eval.set_eq
  have hr3 : t3.reg Div.rgT = Glyph.pos := by rw [ht3]; simp
  set t4 : State := t3.updStk 0 (t3.reg Div.rgT :: t3.stk 0) with ht4
  have hev4 : Eval main (.push 0 Div.rgT) t3 t4 1 := by
    rw [ht4]
    exact Eval.push (main := main) (0 : Stk) Div.rgT t3
  have h40 : t4.stk 0 = [Glyph.pos, Glyph.iend] ++ Z := by
    rw [ht4, State.updStk_same, hr3, ht3, State.updReg_stk, h20]
    rfl
  have ht1_stk : ∀ k : Stk, t1.stk k = s.stk k := by intro k; rw [ht1, State.updReg_stk]
  have ht2_stk : ∀ k : Stk, k ≠ 0 → t2.stk k = t1.stk k := by
    intro k hk
    rw [ht2, State.updStk_apply, if_neg hk]
  have ht3_stk : ∀ k : Stk, t3.stk k = t2.stk k := by intro k; rw [ht3, State.updReg_stk]
  have ht4_stk0 : ∀ k : Stk, k ≠ 0 → t4.stk k = t3.stk k := by
    intro k hk
    rw [ht4, State.updStk_apply, if_neg hk]
  have ht4_stk : ∀ k : Stk, k ≠ 0 → t4.stk k = s.stk k := by
    intro k hk
    rw [ht4_stk0 k hk, ht3_stk k, ht2_stk k hk, ht1_stk k]
  -- the cleanup
  have hP4 : t4.stk Div.stP = [] ++ [gP] ++ b0.stk Div.stP := by
    rw [ht4_stk Div.stP (by decide)]; simpa using hP
  have hB4 : t4.stk Div.stB = [] ++ [gB] ++ b0.stk Div.stB := by
    rw [ht4_stk Div.stB (by decide)]; simpa using hB
  have hR4 : t4.stk Div.stR = [] ++ [gR] ++ b0.stk Div.stR := by
    rw [ht4_stk Div.stR (by decide)]; simpa using hR
  have hQ4 : t4.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [ht4_stk Div.stQ (by decide)]; exact hQ
  have hS4 : t4.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS := by
    rw [ht4_stk Div.stS (by decide)]; exact hS
  have hC4 : t4.stk Div.stC = [] ++ [gC] ++ b0.stk Div.stC := by
    rw [ht4_stk Div.stC (by decide)]; exact hC0
  have hD4 : t4.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [ht4_stk Div.stD (by decide)]; exact hD
  have hX4 : t4.stk Div.stX = [] ++ [gX] ++ b0.stk Div.stX := by
    rw [ht4_stk Div.stX (by decide), hX]
    rfl
  have hY4 : t4.stk Div.stY = [] ++ [gY] ++ b0.stk Div.stY := by
    rw [ht4_stk Div.stY (by decide)]; simpa using hY
  have hoth4 : ∀ k : Stk, 10 ≤ k.val → t4.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    rw [ht4_stk k hk0]
    exact hoth k hk
  obtain ⟨u, nu, hevu, hcu, hu0, hufr⟩ :=
    ff_cleanup main b0 t4 [] [] [] (bitsG (padBits qv j)) (bitsG (ffSreg b.natAbs rv L)) []
      (bitsG (padBits b.natAbs L).reverse) [] []
      hP4 hB4 hR4 hQ4 hS4 hC4 hD4 hX4 hY4
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      (ff_bitsG_ne _ ff_bit_ne_gQ)
      (ff_bitsG_ne _ ff_bit_ne_gS)
      (by intro g hg; simp at hg)
      (ff_bitsG_ne _ ff_bit_ne_gD)
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      hoth4
  have hcu' : nu ≤ 10 * L + 5 * j + 117 := by
    have h1 : (bitsG (padBits qv j)).length = j := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h2 : (bitsG (ffSreg b.natAbs rv L)).length = L := by
      simp [Work.IntLib.bitsG, ffSreg_length b.natAbs rv L hbL hrvL]
    have h3 : (bitsG (padBits b.natAbs L).reverse).length = L := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h4 := hcu
    rw [h1, h2, h3] at h4
    simp only [List.length_nil, Nat.add_zero] at h4
    omega
  have hval : u.stk 0 = (Val.int (a.fmod b)).enc ++ Z := by
    rw [hu0, h40, hfmod, ff_enc_zero]
  refine ⟨u, 1 + (1 + (1 + (1 + (nu + 1)))), ?_, by omega, hval, hufr⟩
  have h := Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4
    (Eval.seq hevu (Eval.skip u)))))
  simpa [ffIA, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h

/-- The `rv ≠ 0` inner branch of the `a < 0` case: emit the low `L` bits of `b.natAbs - rv`. -/
theorem ff_tailNE (main : Cmd) (b0 : State) (Z : List Glyph) (a b : ℤ) (rv qv L j : ℕ)
    (s : State)
    (hb : 0 < b) (hL : L = b.natAbs.size + 1) (hrv : rv = a.natAbs % b.natAbs)
    (ha : a < 0) (hrvne : rv ≠ 0)
    (h0 : s.stk 0 = Z)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS : s.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS)
    (hC : s.stk Div.stC = (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++ b0.stk Div.stC)
    (hD : s.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD)
    (hX : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hY : s.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, Eval main ffIB s s' n ∧ n ≤ 27 * L + 5 * j + 160 ∧
      s'.stk 0 = (Val.int (a.fmod b)).enc ++ Z ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  obtain ⟨hrvlt, hbL, hbL1, hL2, hrvL⟩ := ff_size_facts a b hb L rv hL hrv
  have hbsub : b.natAbs - rv < 2 ^ L := by omega
  -- `mvRevOnto stS gS stR rgT`
  have hS' : s.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ gS :: b0.stk Div.stS := by
    rw [hS, ff_app_sing_app]
  obtain ⟨t1, n1, he1, hc1, h1S, h1R, h1fr⟩ :=
    mvRevOntoTight main Div.stS gS Div.stR Div.rgT (bitsG (ffSreg b.natAbs rv L))
      (b0.stk Div.stS) ([gR] ++ b0.stk Div.stR) s (ff_bitsG_ne _ ff_bit_ne_gS) hS' hR
      (by decide)
  have hc1' : n1 ≤ 5 * L + 9 := by
    have h := hc1
    rw [Work.IntLib.bitsG, List.length_map, ffSreg_length b.natAbs rv L hbL hrvL] at h
    exact h
  have h1R' : t1.stk Div.stR =
      bitsG (Work.IntLib.padBits (b.natAbs - rv) L) ++ [gR] ++ b0.stk Div.stR := by
    rw [h1R, ff_bitsG_reverse, ffSreg, ff_subRipple a b hb L rv hL hrv]
    simp
  -- `mkG stS gS`
  set t2 : State := (t1.updReg Div.rgT gS).updStk Div.stS (gS :: t1.stk Div.stS) with ht2
  have he2 : Eval main (Div.mkG Div.stS gS) t1 t2 2 := by
    rw [ht2]; exact ff_mkG main Div.stS gS t1
  have h2S : t2.stk Div.stS = [gS] ++ b0.stk Div.stS := by
    rw [ht2, State.updStk_same, h1S]
    rfl
  have h2R : t2.stk Div.stR =
      bitsG (Work.IntLib.padBits (b.natAbs - rv) L) ++ gR :: b0.stk Div.stR := by
    rw [ht2, State.updStk_apply, if_neg (by decide : ¬ (Div.stR = Div.stS)), State.updReg_stk,
      h1R', ff_app_sing_app]
  have h2fr : ∀ k : Stk, k ≠ Div.stS → t2.stk k = t1.stk k := by
    intro k hk
    rw [ht2, State.updStk_apply, if_neg hk, State.updReg_stk]
  have h2X : t2.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    rw [h2fr Div.stX (by decide), h1fr Div.stX (by decide) (by decide)]
    exact hX
  -- `prep stR gR`
  obtain ⟨t3, n3, he3, hc3, h3R, h3X, h3fr⟩ :=
    div_prep_eval main Div.stR gR (Work.IntLib.padBits (b.natAbs - rv) L) (b0.stk Div.stR)
      (b0.stk Div.stX) t2 (fun b' => by intro h; cases h) h2R h2X (by decide)
  have hc3' : n3 ≤ 7 * L + 19 := by
    have h := hc3
    rw [Work.IntLib.padBits_length] at h
    exact h
  have h3R' : t3.stk Div.stR = [gR] ++ b0.stk Div.stR := by
    rw [h3R]
    rfl
  -- the stripped region on `stX`
  set Aem : List Glyph := ((bitsG (Work.IntLib.padBits (b.natAbs - rv) L)).reverse).dropWhile
    (fun g => g = Glyph.bit false) with hAem
  have h3X' : t3.stk Div.stX = Aem ++ [gX] ++ b0.stk Div.stX := by rw [h3X, hAem]
  have hAemrev : Aem.reverse = bitsG (Computability.encodeNat (b.natAbs - rv)) := by
    rw [hAem, ff_dropWhile_rev_bitsG (b.natAbs - rv) L hbsub, List.reverse_reverse]
  have hAemlen : Aem.length ≤ L - 1 := by
    rw [← List.length_reverse, hAemrev, Work.IntLib.bitsG, List.length_map,
      Work.IntLib.encodeNat_length]
    exact Nat.size_le.mpr (by omega)
  have hAemne : ∀ g ∈ Aem, g ≠ gX := by
    intro g hg
    rw [hAem] at hg
    have hmem : g ∈ (bitsG (Work.IntLib.padBits (b.natAbs - rv) L)).reverse :=
      List.Sublist.mem hg (List.dropWhile_sublist (l := (bitsG (Work.IntLib.padBits (b.natAbs - rv) L)).reverse) (fun g => g = Glyph.bit false))
    rw [ff_bitsG_reverse] at hmem
    exact ff_bitsG_ne _ ff_bit_ne_gX g hmem
  -- `set rgW pos`
  set t4 : State := t3.updReg Div.rgW Glyph.pos with ht4
  have he4 : Eval main (.set Div.rgW Glyph.pos) t3 t4 1 := by rw [ht4]; exact Eval.set_eq
  have hr4 : t4.reg Div.rgW = Glyph.pos := by rw [ht4]; simp
  have h4X : t4.stk Div.stX = Aem ++ gX :: b0.stk Div.stX := by
    rw [ht4, State.updReg_stk, h3X', ff_app_sing_app]
  have h40 : t4.stk 0 = Z := by
    rw [ht4, State.updReg_stk, h3fr 0 (by decide) (by decide), h2fr 0 (by decide),
      h1fr 0 (by decide) (by decide)]
    exact h0
  -- `emit rgW`
  obtain ⟨t5, n5, he5, hc5, h50, h5X, h5fr⟩ :=
    ff_emit main Div.rgW Aem (b0.stk Div.stX) Z t4 h4X h40 hAemne (by decide) (by decide)
  have hc5' : n5 ≤ 5 * L + 11 := by omega
  have hfmod : a.fmod b = ((b.natAbs - rv : ℕ) : ℤ) := by
    have h := (Work.IntLib.intDivAPI).2.2.2 a b hb
    have hmod : a.natAbs % b.natAbs = rv := hrv.symm
    rw [h, if_neg (show ¬ (0 ≤ a) by omega), if_neg (by rw [hmod]; exact hrvne), hmod]
    exact (Nat.cast_sub (le_of_lt hrvlt)).symm
  have hval5 : t5.stk 0 = (Val.int (a.fmod b)).enc ++ Z := by
    rw [h50, hr4, hAemrev, hfmod, ff_enc_nat]
    simp [List.append_assoc]
  -- the shapes before the cleanup
  have h5fr' : ∀ k : Stk, k ≠ 0 → k ≠ Div.stX → k ≠ Div.stR → k ≠ Div.stS →
      t5.stk k = s.stk k := by
    intro k hk0 hkX hkR hkS
    rw [h5fr k hk0 hkX, ht4, State.updReg_stk, h3fr k hkR hkX, ht2, State.updStk_apply,
      if_neg hkS, State.updReg_stk, h1fr k hkS hkR]
  have h5P : t5.stk Div.stP = [] ++ [gP] ++ b0.stk Div.stP := by
    rw [h5fr' Div.stP (by decide) (by decide) (by decide) (by decide)]
    simpa using hP
  have h5B : t5.stk Div.stB = [] ++ [gB] ++ b0.stk Div.stB := by
    rw [h5fr' Div.stB (by decide) (by decide) (by decide) (by decide)]
    simpa using hB
  have h5R : t5.stk Div.stR = [] ++ [gR] ++ b0.stk Div.stR := by
    rw [h5fr Div.stR (by decide) (by decide), ht4, State.updReg_stk, h3R']
    rfl
  have h5Q : t5.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [h5fr' Div.stQ (by decide) (by decide) (by decide) (by decide)]
    exact hQ
  have h5S : t5.stk Div.stS = [] ++ [gS] ++ b0.stk Div.stS := by
    rw [h5fr Div.stS (by decide) (by decide), ht4, State.updReg_stk,
      h3fr Div.stS (by decide) (by decide), h2S]
    rfl
  have h5C : t5.stk Div.stC = (bitsG (Computability.encodeNat rv)).reverse ++ [gC] ++
      b0.stk Div.stC := by
    rw [h5fr' Div.stC (by decide) (by decide) (by decide) (by decide)]
    exact hC
  have h5D : t5.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [h5fr' Div.stD (by decide) (by decide) (by decide) (by decide)]
    exact hD
  have h5X' : t5.stk Div.stX = [] ++ [gX] ++ b0.stk Div.stX := by
    rw [h5X]
    rfl
  have h5Y : t5.stk Div.stY = [] ++ [gY] ++ b0.stk Div.stY := by
    rw [h5fr' Div.stY (by decide) (by decide) (by decide) (by decide)]
    simpa using hY
  have hoth5 : ∀ k : Stk, 10 ≤ k.val → t5.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hkX : k ≠ Div.stX := by rintro rfl; simp at hk
    have hkR : k ≠ Div.stR := by rintro rfl; simp at hk
    have hkS : k ≠ Div.stS := by rintro rfl; simp at hk
    rw [h5fr' k hk0 hkX hkR hkS]
    exact hoth k hk
  -- the cleanup
  obtain ⟨u, nu, hevu, hcu, hu0, hufr⟩ :=
    ff_cleanup main b0 t5 [] [] [] (bitsG (padBits qv j)) []
      ((bitsG (Computability.encodeNat rv)).reverse) (bitsG (padBits b.natAbs L).reverse) [] []
      h5P h5B h5R h5Q h5S h5C h5D h5X' h5Y
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      (ff_bitsG_ne _ ff_bit_ne_gQ)
      (by intro g hg; simp at hg)
      (by
        intro g hg
        rw [ff_bitsG_reverse] at hg
        exact ff_bitsG_ne _ ff_bit_ne_gC g hg)
      (ff_bitsG_ne _ ff_bit_ne_gD)
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      hoth5
  have hcu' : nu ≤ 10 * L + 5 * j + 112 := by
    have h1 : (bitsG (padBits qv j)).length = j := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h2 : ((bitsG (Computability.encodeNat rv)).reverse).length ≤ L - 1 := by
      rw [List.length_reverse, Work.IntLib.bitsG, List.length_map, Work.IntLib.encodeNat_length]
      exact Nat.size_le.mpr (by omega)
    have h3 : (bitsG (padBits b.natAbs L).reverse).length = L := by
      simp [Work.IntLib.bitsG, Work.IntLib.padBits_length]
    have h4 := hcu
    rw [h1, h3] at h4
    simp only [List.length_nil, Nat.add_zero] at h4
    omega
  have hval : u.stk 0 = (Val.int (a.fmod b)).enc ++ Z := by rw [hu0]; exact hval5
  refine ⟨u, n1 + (2 + (n3 + (1 + (n5 + (nu + 1))))), ?_, by omega, hval, hufr⟩
  have h := Eval.seq he1 (Eval.seq he2 (Eval.seq he3 (Eval.seq he4 (Eval.seq he5
    (Eval.seq hevu (Eval.skip u))))))
  simpa [ffIB, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h

/-- The `a < 0` branch of `fixFmod`: ripple the divisor out of the remainder, strip the padding of
the remainder, and dispatch on whether it vanished. -/
theorem ff_branchA (main : Cmd) (b0 : State) (Z : List Glyph) (a b : ℤ) (L j rv qv : ℕ)
    (s : State) (hb : 0 < b) (hL : L = b.natAbs.size + 1) (hrv : rv = a.natAbs % b.natAbs)
    (ha : a < 0) (h0 : s.stk 0 = Z)
    (hP : s.stk Div.stP = [gP] ++ b0.stk Div.stP)
    (hB : s.stk Div.stB = bitsG (padBits b.natAbs L) ++ [gB] ++ b0.stk Div.stB)
    (hR : s.stk Div.stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk Div.stR)
    (hQ : s.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ)
    (hS5 : s.stk Div.stS = [gS] ++ b0.stk Div.stS)
    (hS6 : s.stk Div.stC = [gC] ++ b0.stk Div.stC)
    (hS7 : s.stk Div.stD = [gD] ++ b0.stk Div.stD)
    (hS8 : s.stk Div.stX = [gX] ++ b0.stk Div.stX)
    (hS9 : s.stk Div.stY = [gY] ++ b0.stk Div.stY)
    (hoth : ∀ k : Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, Eval main ffA s s' n ∧
      n ≤ (if rv = 0 then 27 * L + 5 * j + 176 else 43 * L + 5 * j + 212) ∧
      s'.stk 0 = (Val.int (a.fmod b)).enc ++ Z ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  obtain ⟨hrvlt, hbL, hbL1, hL2, hrvL⟩ := ff_size_facts a b hb L rv hL hrv
  have hXY : (padBits b.natAbs L).length = (padBits rv L).length := by
    rw [Work.IntLib.padBits_length, Work.IntLib.padBits_length]
  have hB' : s.stk Div.stB = bitsG (padBits b.natAbs L) ++ gB :: b0.stk Div.stB := by
    rw [hB, ff_app_sing_app]
  have hR' : s.stk Div.stR = bitsG (padBits rv L) ++ gR :: b0.stk Div.stR := by
    rw [hR, ff_app_sing_app]
  have hripple : ∃ (s1 : State) (n1 : ℕ),
      Eval main (Div.rippleProg Div.stB Div.stR gB gR) s s1 n1 ∧
      n1 ≤ 14 * ((padBits b.natAbs L).length + 2) + 6 ∧
      s1.stk Div.stB = b0.stk Div.stB ∧
      s1.stk Div.stR = b0.stk Div.stR ∧
      s1.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS ∧
      s1.stk Div.stC = bitsG (padBits rv L).reverse ++ [gC] ++ b0.stk Div.stC ∧
      s1.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD ∧
      (∀ k : Stk, k ≠ Div.stB → k ≠ Div.stR → k ≠ Div.stS → k ≠ Div.stC →
        k ≠ Div.stD → s1.stk k = s.stk k) ∧
      s1.stk 0 = s.stk 0 ∧
      s1.stk Div.stP = s.stk Div.stP ∧
      s1.stk Div.stQ = s.stk Div.stQ ∧
      s1.stk Div.stX = s.stk Div.stX ∧
      s1.stk Div.stY = s.stk Div.stY ∧
      (∀ k : Stk, 10 ≤ k.val → s1.stk k = s.stk k) := by
    obtain ⟨s1, n1, hev, hn, hb1, hr1, hs1, hc1, hd1, hfr⟩ :=
      rippleProgBR_eval_gen main s (b0.stk Div.stB) (b0.stk Div.stR) (b0.stk Div.stC)
        (b0.stk Div.stD) (b0.stk Div.stS) (padBits b.natAbs L) (padBits rv L) hXY
        hB hR hS6 hS7 hS5
    refine ⟨s1, n1, hev, hn, hb1, hr1, ?_, ?_, ?_, hfr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs1, ← List.map_reverse]
      rfl
    · rw [hc1, ← List.map_reverse]
    · rw [hd1, ← List.map_reverse]
    · exact hfr 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hfr Div.stP (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hfr Div.stQ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hfr Div.stX (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hfr Div.stY (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro k hk
      exact hfr k (by rintro rfl; simp at hk) (by rintro rfl; simp at hk)
        (by rintro rfl; simp at hk) (by rintro rfl; simp at hk) (by rintro rfl; simp at hk)
  obtain ⟨r1, m1, hevR, hcR, hRB, hRR, hRS, hRC, hRD, hRfr, hR0, hRP, hRQ, hRX, hRY,
    hRoth⟩ := hripple
  have hcR' : m1 ≤ 14 * (L + 2) + 6 := by
    rw [Work.IntLib.padBits_length] at hcR
    exact hcR
  have hRP' : r1.stk Div.stP = [gP] ++ b0.stk Div.stP := by rw [hRP]; exact hP
  have hRQ' : r1.stk Div.stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk Div.stQ := by
    rw [hRQ]; exact hQ
  have hRX' : r1.stk Div.stX = [gX] ++ b0.stk Div.stX := by rw [hRX]; exact hS8
  have hRY' : r1.stk Div.stY = [gY] ++ b0.stk Div.stY := by rw [hRY]; exact hS9
  have hR0' : r1.stk 0 = Z := by rw [hR0]; exact h0
  have hRS' : r1.stk Div.stS = bitsG (ffSreg b.natAbs rv L) ++ [gS] ++ b0.stk Div.stS := hRS
  have hRC' : r1.stk Div.stC = bitsG (padBits rv L).reverse ++ [gC] ++ b0.stk Div.stC := hRC
  have hRD' : r1.stk Div.stD = bitsG (padBits b.natAbs L).reverse ++ [gD] ++ b0.stk Div.stD := hRD
  -- the four commands after the ripple
  obtain ⟨p1, p2, p3, p4, m3, hevA, hevB, hevC, hevD, hc3, h40, h4P, h4B, h4R, h4Q, h4S, h4C,
    h4D, h4X, h4Y, h4oth, h4reg⟩ :=
    ff_prefixA_rest main b0 Z b rv qv L j r1 hR0' hRP' hRB hRR hRQ' hRS' hRC' hRD' hRX' hRY'
      hrvL (fun k hk => (hRoth k hk).trans (hoth k hk))
  by_cases hrv0 : rv = 0
  · -- ### `rv = 0`: emit the literal `0`
    have hreg : p4.reg Div.rgV = gC := by
      rw [h4reg]
      exact (ff_headD_encC (Computability.encodeNat rv) (b0.stk Div.stC)).mpr
        ((Work.IntLib.encodeNat_eq_nil_iff rv).mpr hrv0)
    obtain ⟨u, nu, hevu, hcu, hu0, hufr⟩ :=
      ff_tail0 main b0 Z a b rv qv L j p4 hb hL hrv ha hrv0 h40 h4P h4B h4R h4Q h4S h4C h4D
        h4X h4Y h4oth
    have hite : Eval main (Cmd.ite Div.rgV gC ffIA ffIB) p4 u (nu + 1) := Eval.iteT hreg hevu
    refine ⟨u, m1 + (2 + (2 + (m3 + (1 + (nu + 1 + 1))))), ?_, ?_, hu0, hufr⟩
    · have h := Eval.seq hevR (Eval.seq hevA (Eval.seq hevB (Eval.seq hevC (Eval.seq hevD
        (Eval.seq hite (Eval.skip u))))))
      simpa [ffA, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
    · rw [if_pos hrv0]
      omega
  · -- ### `rv ≠ 0`: emit the low bits of `b.natAbs - rv`
    have hreg : p4.reg Div.rgV ≠ gC := by
      rw [h4reg]
      exact (ff_headD_encC (Computability.encodeNat rv) (b0.stk Div.stC)).not.mpr
        (fun hX => hrv0 ((Work.IntLib.encodeNat_eq_nil_iff rv).mp hX))
    obtain ⟨u, nu, hevu, hcu, hu0, hufr⟩ :=
      ff_tailNE main b0 Z a b rv qv L j p4 hb hL hrv ha hrv0 h40 h4P h4B h4R h4Q h4S h4C h4D
        h4X h4Y h4oth
    have hite : Eval main (Cmd.ite Div.rgV gC ffIA ffIB) p4 u (nu + 1) := Eval.iteF hreg hevu
    refine ⟨u, m1 + (2 + (2 + (m3 + (1 + (nu + 1 + 1))))), ?_, ?_, hu0, hufr⟩
    · have h := Eval.seq hevR (Eval.seq hevA (Eval.seq hevB (Eval.seq hevC (Eval.seq hevD
        (Eval.seq hite (Eval.skip u))))))
      simpa [ffA, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
    · rw [if_neg hrv0]
      omega

/-- **The requested lemma**: `Div.fixFmod` computes `a.fmod b` and restores all stacks. -/
theorem div_fixFmod (main : HvdH.Cmd) (b0 : HvdH.State) (a b : ℤ) (Z : List HvdH.Glyph)
    (S : HvdH.State) (hb : 0 < b) (L j : ℕ) (hL : L = b.natAbs.size + 1) (rv qv : ℕ)
    (hrv : rv = a.natAbs % b.natAbs) (hqv : qv = a.natAbs / b.natAbs)
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
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.fixFmod S s' n ∧
      n ≤ 60 * (j + L + 2) + 60 ∧
      s'.stk 0 = (HvdH.Val.int (a.fmod b)).enc ++ Z ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  have hL2 : 2 ≤ L := (ff_size_facts a b hb L rv hL hrv).2.2.2.1
  have hrvL : rv < 2 ^ L := (ff_size_facts a b hb L rv hL hrv).2.2.2.2
  -- `readSigns`: pop the two sign glyphs of `stY`
  set S1 : State := (S.updReg Div.rgT ((S.stk Div.stY).headD Glyph.eos)).updStk Div.stY
    ((S.stk Div.stY).tail) with hS1
  have ht1 : Eval main (.pop Div.stY Div.rgT) S S1 1 := by rw [hS1]; exact Eval.pop Div.stY Div.rgT S
  set t : State := (S1.updReg Div.rgU ((S1.stk Div.stY).headD Glyph.eos)).updStk Div.stY
    ((S1.stk Div.stY).tail) with ht
  have ht2 : Eval main (.pop Div.stY Div.rgU) S1 t 1 := by rw [ht]; exact Eval.pop Div.stY Div.rgU S1
  have he_read : Eval main Div.readSigns S t (1 + (1 + 1)) := by
    have h := Eval.seq ht1 (Eval.seq ht2 (Eval.skip t))
    simpa [Div.readSigns, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
  have hS1Y : S1.stk Div.stY = (S.stk Div.stY).tail := by rw [hS1]; simp
  have ht_stk : ∀ k : Stk, k ≠ Div.stY → t.stk k = S.stk k := by
    intro k hk
    rw [ht]; simp only [State.updStk_apply]
    rw [if_neg hk, State.updReg_stk]
    rw [hS1]; simp only [State.updStk_apply]
    rw [if_neg hk, State.updReg_stk]
  have htY : t.stk Div.stY = [gY] ++ b0.stk Div.stY := by
    rw [ht]; simp only [State.updStk_same]
    rw [hS1Y, hS9]; rfl
  have htrgU : t.reg Div.rgU = (if a < 0 then Glyph.neg else Glyph.pos) := by
    rw [ht, State.updStk_reg, State.updReg_apply, if_pos rfl, hS1Y, hS9]
    rfl
  have hoth_t : ∀ k : Stk, 10 ≤ k.val → t.stk k = b0.stk k := by
    intro k hk
    rw [ht_stk k (by rintro rfl; simp at hk)]
    exact hoth k hk
  have hfixFmod : Div.fixFmod = Div.seqs [Div.readSigns, .ite Div.rgU Glyph.neg ffA ffB] := rfl
  rcases lt_or_ge a 0 with ha | ha
  · -- negative dividend: the `ffA` branch
    have hrgU : t.reg Div.rgU = Glyph.neg := by rw [htrgU, if_pos ha]
    obtain ⟨s', nb, heb, hcb, hvb, hfb⟩ :=
      ff_branchA main b0 Z a b L j rv qv t hb hL hrv ha
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
    have he_ite : Eval main (.ite Div.rgU Glyph.neg ffA ffB) t s' (nb + 1) := Eval.iteT hrgU heb
    have hev : Eval main Div.fixFmod S s' (3 + ((nb + 1) + 1)) := by
      have h := Eval.seq he_read (Eval.seq he_ite (Eval.skip s'))
      simpa [hfixFmod, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
    refine ⟨s', 3 + ((nb + 1) + 1), hev, ?_, hvb, hfb⟩
    by_cases hrv0 : rv = 0
    · rw [if_pos hrv0] at hcb
      omega
    · rw [if_neg hrv0] at hcb
      have hb2 : 2 ≤ b.natAbs := by
        by_contra hcon
        have h1 : b.natAbs ≤ 1 := by omega
        have hb1 : b.natAbs = 1 := by omega
        exact hrv0 (by rw [hrv, hb1, Nat.mod_one])
      have hs2 : 2 ≤ b.natAbs.size := by
        by_contra hcon
        have h1 : b.natAbs.size ≤ 1 := by omega
        have h2 : b.natAbs < 2 := Nat.size_le.mp h1
        omega
      have hL3 : 3 ≤ L := by omega
      omega
  · -- nonnegative dividend: the `ffB` branch
    have hrgU : t.reg Div.rgU ≠ Glyph.neg := by
      rw [htrgU, if_neg (not_lt.mpr ha)]
      exact (by decide : Glyph.pos ≠ Glyph.neg)
    obtain ⟨s', nb, heb, hcb, hvb, hfb⟩ :=
      ff_branchB main b0 Z a b L j rv qv t hb hL hrv ha
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
    have he_ite : Eval main (.ite Div.rgU Glyph.neg ffA ffB) t s' (nb + 1) := Eval.iteF hrgU heb
    have hev : Eval main Div.fixFmod S s' (3 + ((nb + 1) + 1)) := by
      have h := Eval.seq he_read (Eval.seq he_ite (Eval.skip s'))
      simpa [hfixFmod, Div.seqs, Div.seqs_cons, Div.seqs_nil] using h
    refine ⟨s', 3 + ((nb + 1) + 1), hev, by omega, hvb, hfb⟩

end Work.IntLib
