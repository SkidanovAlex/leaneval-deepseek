import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divPush
import Submission.Work.IntLib.intDivAPI
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.divFoldAPI
import Submission.Work.IntLib.div_shiftR
import Submission.Work.IntLib.div_fixTmod
import Submission.Work.IntLib.div_fixFdiv
import Submission.Work.IntLib.div_fixFmod
import Submission.Work.IntLib.div_extract
import Submission.Work.IntLib.div_mainLoop
import Submission.Work.IntLib.div_fixTdiv

/-!
# IntLib division: assembly of the four `BinOp`s

Combines the prologue (`pushMarkers`, `extract`), one padding bit on the pending-dividend stack,
the long-division loop (`mainLoopProg`) and one of the four fix-ups (`fixTdiv`, `fixTmod`,
`fixFdiv`, `fixFmod`) into the four words of `Work.IntLib.divWord`.

The padding bit on stack 1 (a leading `false`, i.e. a zero most significant bit, of the dividend)
lengthens the quotient region by one bit, so that the quotient `qv` of the division satisfies
`qv + 1 < 2^j` for `j` the length of the quotient region: this is the side condition of
`div_fixFdiv`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.IntLib.Div

open HvdH

/-! ## Elementary list and state facts -/

theorem encs_cons_int (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs, List.map_cons, List.flatten_cons]

theorem bval_false_cons (A : List Bool) : bval (false :: A) = bval A := by
  simp [bval, List.foldl_cons]

theorem padBits_zero_asm (j : ℕ) : padBits 0 j = List.replicate j false := by
  simp [padBits, List.map_const']

theorem size_padP (n : ℕ) : (false :: n.bits.reverse).length = n.size + 1 := by
  simp [List.length_cons, List.length_reverse, Nat.size_eq_bits_len]

theorem bval_padP (n : ℕ) : bval (false :: n.bits.reverse) = n := by
  rw [bval_false_cons]; exact divFoldBvalBridge.2 n

/-- Uniqueness of the division with remainder: `qv` and `rv` with `bv * qv + rv = a`, `rv < bv`
are the quotient and the remainder of `a` by `bv`. -/
theorem divmod_unique {a bv qv rv : ℕ} (hbv : 0 < bv) (h : bv * qv + rv = a) (hr : rv < bv) :
    qv = a / bv ∧ rv = a % bv := by
  have h1 : qv * bv ≤ a := by rw [Nat.mul_comm]; omega
  have h2 : a < (qv + 1) * bv := by
    have : a = bv * qv + rv := h.symm
    nlinarith
  have hd : a / bv = qv := Nat.div_eq_of_lt_le h1 h2
  refine ⟨hd.symm, ?_⟩
  have hdm := Nat.div_add_mod a bv
  rw [hd] at hdm
  omega

theorem pmAux_stk_of_ne (b0 : State) (l : List (Stk × Glyph)) (k : Stk)
    (h : ∀ km ∈ l, km.1 ≠ k) : (pmAux b0 l).stk k = b0.stk k := by
  induction l generalizing b0 with
  | nil => simp [pmAux]
  | cons km rest ih =>
    rw [pmAux_cons]
    rw [ih ((b0.updReg rgT km.2).updStk km.1 (km.2 :: b0.stk km.1))
      (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp only [State.updStk_apply, State.updReg_stk]
    rw [if_neg (fun hc => h km List.mem_cons_self hc.symm)]

theorem pushedSt_stk_hi (b0 : State) (k : Stk) (hk : 10 ≤ k.val) :
    (pushedSt b0).stk k = b0.stk k := by
  rw [pushedSt]
  refine pmAux_stk_of_ne b0 markerList k ?_
  intro km hkm
  obtain ⟨j, m⟩ := km
  simp only [markerList, List.mem_cons, List.not_mem_nil, or_false] at hkm
  rcases hkm with h | h | h | h | h | h | h | h | h
  all_goals { obtain ⟨rfl, -⟩ := h; rintro rfl; simp at hk }

/-- From `k ≠ g` for all nine markers `g`, conclude `10 ≤ k.val` (the remaining six stacks). -/
theorem ge_ten_of_ne {j : Stk} (h0 : j ≠ 0) (h1 : j ≠ stP) (h2 : j ≠ stB) (h3 : j ≠ stR)
    (h4 : j ≠ stQ) (h5 : j ≠ stS) (h6 : j ≠ stC) (h7 : j ≠ stD) (h8 : j ≠ stX)
    (h9 : j ≠ stY) : 10 ≤ j.val := by
  fin_cases j <;> simp_all [stP, stB, stR, stQ, stS, stC, stD, stX, stY]

theorem not_marker_of_ge_ten {k : Stk} (hk : 10 ≤ k.val) :
    k ≠ 0 ∧ k ≠ stP ∧ k ≠ stB ∧ k ≠ stR ∧ k ≠ stQ ∧ k ≠ stS ∧ k ≠ stC ∧ k ≠ stD ∧
      k ≠ stX ∧ k ≠ stY :=
  ⟨by rintro rfl; simp at hk, by rintro rfl; simp at hk, by rintro rfl; simp at hk,
   by rintro rfl; simp at hk, by rintro rfl; simp at hk, by rintro rfl; simp at hk,
   by rintro rfl; simp at hk, by rintro rfl; simp at hk, by rintro rfl; simp at hk,
   by rintro rfl; simp at hk⟩

/-! ## The state carrying the two signs -/

/-- `s` with the two sign glyphs of the operands pushed onto stack 9 (divisor sign on top). -/
def withSigns (s : State) (a b : ℤ) : State :=
  s.updStk stY ([if b < 0 then Glyph.neg else Glyph.pos,
    if a < 0 then Glyph.neg else Glyph.pos] ++ [gY] ++ s.stk stY)

theorem withSigns_stkY (s : State) (a b : ℤ) : (withSigns s a b).stk stY =
    [if b < 0 then Glyph.neg else Glyph.pos, if a < 0 then Glyph.neg else Glyph.pos] ++ [gY] ++
      s.stk stY := by
  simp [withSigns]

theorem withSigns_stk_ne (s : State) (a b : ℤ) (k : Stk) (hk : k ≠ stY) :
    (withSigns s a b).stk k = s.stk k := by
  simp [withSigns, hk]

/-! ## The programs -/

/-- Push one `false` bit (a leading zero) onto the pending-dividend stack. -/
def padP : Cmd := seqs [.set rgS (Glyph.bit false), .push stP rgS]

/-- The common core: markers, extraction, one padding bit on stack 1, a reset of the loop
register, and the long-division loop. -/
def coreRun : Cmd := seqs [pushMarkers, extract, padP, .set rLoop Glyph.eos, mainLoopProg]

/-! ## The core run -/

theorem div_core_run (main : Cmd) (s : State) (a b : ℤ) (R : List Glyph)
    (h : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ R) (hb : b ≠ 0) :
    ∃ s' n rv qv, Eval main coreRun s s' n ∧
      s'.stk 0 = R ∧
      s'.stk stP = [gP] ++ s.stk stP ∧
      s'.stk stB = bitsG (padBits b.natAbs (b.natAbs.size + 1)) ++ [gB] ++ s.stk stB ∧
      s'.stk stR = bitsG (padBits rv (b.natAbs.size + 1)) ++ [gR] ++ s.stk stR ∧
      s'.stk stQ = bitsG (padBits qv (a.natAbs.size + 1)) ++ [gQ] ++ s.stk stQ ∧
      b.natAbs * qv + rv = a.natAbs ∧ rv < b.natAbs ∧
      s'.stk stS = [gS] ++ s.stk stS ∧
      s'.stk stC = [gC] ++ s.stk stC ∧
      s'.stk stD = [gD] ++ s.stk stD ∧
      s'.stk stX = [gX] ++ s.stk stX ∧
      s'.stk stY = [if b < 0 then Glyph.neg else Glyph.pos,
        if a < 0 then Glyph.neg else Glyph.pos] ++ [gY] ++ s.stk stY ∧
      (∀ j : Stk, j ≠ 0 → j ≠ stP → j ≠ stB → j ≠ stR → j ≠ stQ → j ≠ stS → j ≠ stC →
        j ≠ stD → j ≠ stX → j ≠ stY → s'.stk j = s.stk j) ∧
      n ≤ 24 + 40 * (isz a + isz b + 1) +
          (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := by
  have h1 : Eval main pushMarkers s (pushedSt s) 19 := eval_pushMarkers main s
  obtain ⟨s2, n2, he2, hn2, h20, h2P, h2B, h2R, h2Q, h2S, h2C, h2D, h2X, h2Y, h2fr⟩ :=
    div_extract main s a b R hb (pushedSt s)
      (by rw [pushedSt_stk0]; exact h)
      (pushedSt_stk1 s) (pushedSt_stk2 s) (pushedSt_stk3 s) (pushedSt_stk4 s) (pushedSt_stk5 s)
      (pushedSt_stk6 s) (pushedSt_stk7 s) (pushedSt_stk8 s) (pushedSt_stk9 s)
      (fun k hk => pushedSt_stk_hi s k hk)
  -- one padding zero bit on stack 1
  set s3 : State := ⟨Function.update s2.reg rgS (Glyph.bit false),
    Function.update s2.stk stP (Glyph.bit false :: s2.stk stP)⟩ with hs3
  have h3a : Eval main (.set rgS (Glyph.bit false)) s2
      ⟨Function.update s2.reg rgS (Glyph.bit false), s2.stk⟩ 1 := Eval.set_eq
  have h3b : Eval main (.push stP rgS)
      ⟨Function.update s2.reg rgS (Glyph.bit false), s2.stk⟩ s3 1 := by
    have h' := Eval.push (main := main) stP rgS
      (⟨Function.update s2.reg rgS (Glyph.bit false), s2.stk⟩ : State)
    rw [hs3]; simpa using h'
  have h3 : Eval main padP s2 s3 3 := by
    have h' := eval_seqs_cons h3a (eval_seqs_cons h3b (by rw [seqs_nil]; exact Eval.skip s3))
    simpa [padP] using h'
  have h3P : s3.stk stP = bitsG (false :: a.natAbs.bits.reverse) ++ [gP] ++ s.stk stP := by
    rw [hs3]
    show Function.update s2.stk stP (Glyph.bit false :: s2.stk stP) stP = _
    rw [Function.update_self, h2P]
    simp [bitsG]
  have h3fr : ∀ k : Stk, k ≠ stP → s3.stk k = s2.stk k := by
    intro k hk
    rw [hs3]
    show Function.update s2.stk stP (Glyph.bit false :: s2.stk stP) k = s2.stk k
    rw [Function.update_of_ne hk]
  -- reset of the loop register
  set s4 : State := ⟨Function.update s3.reg rLoop Glyph.eos, s3.stk⟩ with hs4
  have hset4 : Eval main (.set rLoop Glyph.eos) s3 s4 1 := by rw [hs4]; exact Eval.set_eq
  have h4rl : s4.reg rLoop = Glyph.eos := by rw [hs4]; simp
  have h4stk : ∀ k : Stk, s4.stk k = s3.stk k := by intro k; simp [hs4]
  -- the long division loop
  have hAdef : (false :: a.natAbs.bits.reverse).length = a.natAbs.size + 1 := size_padP a.natAbs
  have hval : bval (false :: a.natAbs.bits.reverse) = a.natAbs := bval_padP a.natAbs
  have hP4 : s4.stk stP = bitsG ((false :: a.natAbs.bits.reverse).drop 0) ++ [gP] ++
      (withSigns s a b).stk stP := by
    rw [h4stk, h3P, withSigns_stk_ne s a b stP (by decide)]
    simp
  have hB4 : s4.stk stB = bitsG (padBits b.natAbs ((b.natAbs.size + 1))) ++ [gB] ++
      (withSigns s a b).stk stB := by
    rw [h4stk, h3fr stB (by decide), h2B, withSigns_stk_ne s a b stB (by decide)]
  have hR4 : s4.stk stR = bitsG (padBits 0 (b.natAbs.size + 1)) ++ [gR] ++
      (withSigns s a b).stk stR := by
    rw [h4stk, h3fr stR (by decide), h2R, withSigns_stk_ne s a b stR (by decide)]
  have hQ4 : s4.stk stQ = bitsG (padBits 0 0) ++ [gQ] ++ (withSigns s a b).stk stQ := by
    rw [h4stk, h3fr stQ (by decide), h2Q, withSigns_stk_ne s a b stQ (by decide)]
    simp [padBits]
  have hS54 : s4.stk stS = [gS] ++ (withSigns s a b).stk stS := by
    rw [h4stk, h3fr stS (by decide), h2S, withSigns_stk_ne s a b stS (by decide)]
  have hS64 : s4.stk stC = [gC] ++ (withSigns s a b).stk stC := by
    rw [h4stk, h3fr stC (by decide), h2C, withSigns_stk_ne s a b stC (by decide)]
  have hS74 : s4.stk stD = [gD] ++ (withSigns s a b).stk stD := by
    rw [h4stk, h3fr stD (by decide), h2D, withSigns_stk_ne s a b stD (by decide)]
  have hS84 : s4.stk stX = [gX] ++ (withSigns s a b).stk stX := by
    rw [h4stk, h3fr stX (by decide), h2X, withSigns_stk_ne s a b stX (by decide)]
  have hS94 : s4.stk stY = (withSigns s a b).stk stY := by
    rw [h4stk, h3fr stY (by decide), h2Y, withSigns_stkY s a b]
  obtain ⟨s5, n5, rv, qv, he5, hn5, h5P, h5B, h5R, h5Q, h5eq, h5rlt, h5S, h5C, h5D, h5X, h5Y,
    h5fr⟩ :=
    div_mainLoop main (withSigns s a b) (false :: a.natAbs.bits.reverse) b.natAbs 0 0 0
      (a.natAbs.size + 1) (b.natAbs.size + 1)
      (Int.natAbs_pos.mpr hb) (by omega) rfl hAdef (by simp [bval]) (Nat.zero_le _) s4
      hP4 hB4 hR4 hQ4 hS54 hS64 hS74 hS84 hS94 h4rl
  -- assemble
  have hP5 : s5.stk stP = [gP] ++ s.stk stP := by
    rw [h5P, withSigns_stk_ne s a b stP (by decide)]
  have hB5 : s5.stk stB = bitsG (padBits b.natAbs (b.natAbs.size + 1)) ++ [gB] ++ s.stk stB := by
    rw [h5B, withSigns_stk_ne s a b stB (by decide)]
  have hR5 : s5.stk stR = bitsG (padBits rv (b.natAbs.size + 1)) ++ [gR] ++ s.stk stR := by
    rw [h5R, withSigns_stk_ne s a b stR (by decide)]
  have hQ5 : s5.stk stQ = bitsG (padBits qv (a.natAbs.size + 1)) ++ [gQ] ++ s.stk stQ := by
    rw [h5Q, withSigns_stk_ne s a b stQ (by decide)]
  have hS5 : s5.stk stS = [gS] ++ s.stk stS := by
    rw [h5S, withSigns_stk_ne s a b stS (by decide)]
  have hC5 : s5.stk stC = [gC] ++ s.stk stC := by
    rw [h5C, withSigns_stk_ne s a b stC (by decide)]
  have hD5 : s5.stk stD = [gD] ++ s.stk stD := by
    rw [h5D, withSigns_stk_ne s a b stD (by decide)]
  have hX5 : s5.stk stX = [gX] ++ s.stk stX := by
    rw [h5X, withSigns_stk_ne s a b stX (by decide)]
  have hY5 : s5.stk stY = [if b < 0 then Glyph.neg else Glyph.pos,
      if a < 0 then Glyph.neg else Glyph.pos] ++ [gY] ++ s.stk stY := by
    rw [h5Y, withSigns_stkY s a b]
  have heq5 : b.natAbs * qv + rv = a.natAbs := by rw [h5eq, hval]
  have h05 : s5.stk 0 = R := by
    have := h5fr 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [this, h4stk, h3fr 0 (by decide), h20]
  have hfr5 : ∀ j : Stk, j ≠ 0 → j ≠ stP → j ≠ stB → j ≠ stR → j ≠ stQ → j ≠ stS →
      j ≠ stC → j ≠ stD → j ≠ stX → j ≠ stY → s5.stk j = s.stk j := by
    intro j h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hj10 := ge_ten_of_ne h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [h5fr j h1 h2 h3 h4 h5 h6 h7 h8 h9, h4stk, h3fr j h1,
      h2fr j h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, pushedSt_stk_hi s j hj10]
  have h5b : n5 ≤ (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := by
    have h' := hn5
    simp only [Nat.sub_zero] at h'
    have e1 : (a.natAbs.size + 1) + 1 = a.natAbs.size + 2 := by omega
    have e2 : ((b.natAbs.size + 1) + 1) = b.natAbs.size + 2 := by omega
    rw [e1, e2] at h'
    exact h'
  have hcore : Eval main coreRun s s5 (24 + (n2 + n5)) := by
    have htail : Eval main (seqs [.set rLoop Glyph.eos, mainLoopProg]) s3 s5 (1 + (n5 + 1)) :=
      eval_seqs_cons hset4 (eval_seqs_cons he5 (by rw [seqs_nil]; exact Eval.skip s5))
    have hpad : Eval main (seqs [padP, .set rLoop Glyph.eos, mainLoopProg]) s2 s5
        (3 + (1 + (n5 + 1))) := eval_seqs_cons h3 htail
    have hex : Eval main (seqs [extract, padP, .set rLoop Glyph.eos, mainLoopProg]) (pushedSt s) s5
        (n2 + (3 + (1 + (n5 + 1)))) := eval_seqs_cons he2 hpad
    have hall := eval_seqs_cons h1 hex
    have : 19 + (n2 + (3 + (1 + (n5 + 1)))) = 24 + (n2 + n5) := by omega
    rw [← this]
    simpa [coreRun] using hall
  refine ⟨s5, 24 + (n2 + n5), rv, qv, hcore, h05, hP5, hB5, hR5, hQ5, heq5, h5rlt, hS5, hC5,
    hD5, hX5, hY5, hfr5, ?_⟩
  have h2b : n2 ≤ 40 * (isz a + isz b + 1) := hn2
  rw [isz_eq, isz_eq] at h2b ⊢
  omega

/-! ## The four programs -/

def divProgTdiv : Cmd := seqs [coreRun, fixTdiv]
def divProgTmod : Cmd := seqs [coreRun, fixTmod]
def divProgFdiv : Cmd := seqs [coreRun, fixFdiv]
def divProgFmod : Cmd := seqs [coreRun, fixFmod]

/-! ## The four words -/

theorem div_tdiv_word (main : Cmd) :
    WordR main divProgTdiv (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ b ≠ 0)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a.tdiv b) :: rest)
      (binCost (fun a b => 1000 * isz a * isz b)) := by
  intro vs hv s R h0
  obtain ⟨a, b, rest, rfl, hb⟩ := hv
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    rw [h0, encs_cons_int, encs_cons_int]
    simp only [List.append_assoc]
  obtain ⟨s2, n2, rv, qv, he2, h20, h2P, h2B, h2R, h2Q, h2eq, h2rlt, h2S, h2C, h2D, h2X, h2Y,
    h2fr, hn2⟩ := div_core_run main s a b (encs rest ++ R) h0' hb
  obtain ⟨hdv, hmv⟩ := divmod_unique (Int.natAbs_pos.mpr hb) h2eq h2rlt
  have hqvj : qv < 2 ^ (a.natAbs.size + 1) := by
    have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb
    have hle : qv ≤ b.natAbs * qv := by simpa using Nat.mul_le_mul_right qv hb1
    have h1 : qv ≤ a.natAbs := by omega
    have h2 : a.natAbs < 2 ^ a.natAbs.size :=
      (Nat.size_le (m := a.natAbs) (n := a.natAbs.size)).mp le_rfl
    have hpow : (2 : ℕ) ^ (a.natAbs.size + 1) = 2 ^ a.natAbs.size * 2 := by rw [pow_succ]
    have hpos : 1 ≤ 2 ^ a.natAbs.size := Nat.one_le_two_pow
    omega
  obtain ⟨s3, n3, he3, hn3, h30, h3fr⟩ :=
    div_fixTdiv main s a b (encs rest ++ R) s2 hb (b.natAbs.size + 1) (a.natAbs.size + 1)
      rfl rv qv hmv hdv hqvj h20 h2P h2B h2R h2Q h2S h2C h2D h2X h2Y
      (fun k hk => by
        obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := not_marker_of_ge_ten hk
        exact h2fr k g0 g1 g2 g3 g4 g5 g6 g7 g8 g9)
  refine ⟨.int (a.tdiv b) :: rest, s3, n2 + (n3 + 1), ⟨a, b, rest, rfl, rfl⟩, ?_, ?_,
    ?_, h3fr⟩
  · have hskip : Eval main Cmd.skip s3 s3 1 := Eval.skip s3
    have h' := Eval.seq he2 (Eval.seq he3 hskip)
    simpa [divProgTdiv, seqs, seqs_cons, seqs_nil] using h'
  · have h2b : n2 ≤ 24 + 40 * (isz a + isz b + 1) +
        (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := hn2
    have h3b : n3 ≤ 40 * ((a.natAbs.size + 1) + (b.natAbs.size + 1) + 2) + 60 := hn3
    change n2 + (n3 + 1) ≤ 1000 * isz a * isz b
    rw [isz_eq, isz_eq] at h2b ⊢
    nlinarith [Nat.zero_le n2, Nat.zero_le n3]
  · rw [h30, encs_cons_int, List.append_assoc]

theorem div_tmod_word (main : Cmd) :
    WordR main divProgTmod (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ b ≠ 0)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a.tmod b) :: rest)
      (binCost (fun a b => 1000 * isz a * isz b)) := by
  intro vs hv s R h0
  obtain ⟨a, b, rest, rfl, hb⟩ := hv
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    rw [h0, encs_cons_int, encs_cons_int]
    simp only [List.append_assoc]
  obtain ⟨s2, n2, rv, qv, he2, h20, h2P, h2B, h2R, h2Q, h2eq, h2rlt, h2S, h2C, h2D, h2X, h2Y,
    h2fr, hn2⟩ := div_core_run main s a b (encs rest ++ R) h0' hb
  obtain ⟨hdv, hmv⟩ := divmod_unique (Int.natAbs_pos.mpr hb) h2eq h2rlt
  obtain ⟨s3, n3, he3, hn3, h30, h3fr⟩ :=
    div_fixTmod main s a b (encs rest ++ R) s2 hb (b.natAbs.size + 1) (a.natAbs.size + 1)
      rfl rv qv hmv hdv h20 h2P h2B h2R h2Q h2S h2C h2D h2X h2Y
      (fun k hk => by
        obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := not_marker_of_ge_ten hk
        exact h2fr k g0 g1 g2 g3 g4 g5 g6 g7 g8 g9)
  refine ⟨.int (a.tmod b) :: rest, s3, n2 + (n3 + 1), ⟨a, b, rest, rfl, rfl⟩, ?_, ?_, ?_, h3fr⟩
  · have hskip : Eval main Cmd.skip s3 s3 1 := Eval.skip s3
    have h' := Eval.seq he2 (Eval.seq he3 hskip)
    simpa [divProgTmod, seqs, seqs_cons, seqs_nil] using h'
  · have h2b : n2 ≤ 24 + 40 * (isz a + isz b + 1) +
        (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := hn2
    have h3b : n3 ≤ 40 * ((a.natAbs.size + 1) + (b.natAbs.size + 1) + 2) + 60 := hn3
    change n2 + (n3 + 1) ≤ 1000 * isz a * isz b
    rw [isz_eq, isz_eq] at h2b ⊢
    nlinarith [Nat.zero_le n2, Nat.zero_le n3]
  · rw [h30, encs_cons_int, List.append_assoc]

theorem div_fdiv_word (main : Cmd) :
    WordR main divProgFdiv (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ 0 < b)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a.fdiv b) :: rest)
      (binCost (fun a b => 1000 * isz a * isz b)) := by
  intro vs hv s R h0
  obtain ⟨a, b, rest, rfl, hb⟩ := hv
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    rw [h0, encs_cons_int, encs_cons_int]
    simp only [List.append_assoc]
  obtain ⟨s2, n2, rv, qv, he2, h20, h2P, h2B, h2R, h2Q, h2eq, h2rlt, h2S, h2C, h2D, h2X, h2Y,
    h2fr, hn2⟩ := div_core_run main s a b (encs rest ++ R) h0' (ne_of_gt hb)
  obtain ⟨hdv, hmv⟩ := divmod_unique (Int.natAbs_pos.mpr (ne_of_gt hb)) h2eq h2rlt
  have hvj : qv + 1 < 2 ^ (a.natAbs.size + 1) := by
    have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
    have hle : qv ≤ b.natAbs * qv := by simpa using Nat.mul_le_mul_right qv hb1
    have h1 : qv ≤ a.natAbs := by omega
    have h2 : a.natAbs + 1 ≤ 2 ^ a.natAbs.size := by
      have hlt : a.natAbs < 2 ^ a.natAbs.size :=
        (Nat.size_le (m := a.natAbs) (n := a.natAbs.size)).mp le_rfl
      omega
    have hpow : (2 : ℕ) ^ (a.natAbs.size + 1) = 2 ^ a.natAbs.size * 2 := by rw [pow_succ]
    have hpos : 1 ≤ 2 ^ a.natAbs.size := Nat.one_le_two_pow
    omega
  obtain ⟨s3, n3, he3, hn3, h30, h3fr⟩ :=
    div_fixFdiv main s a b (encs rest ++ R) s2 hb (b.natAbs.size + 1) (a.natAbs.size + 1)
      rfl rv qv hmv hdv hvj h20 h2P h2B h2R h2Q h2S h2C h2D h2X h2Y
      (fun k hk => by
        obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := not_marker_of_ge_ten hk
        exact h2fr k g0 g1 g2 g3 g4 g5 g6 g7 g8 g9)
  refine ⟨.int (a.fdiv b) :: rest, s3, n2 + (n3 + 1), ⟨a, b, rest, rfl, rfl⟩, ?_, ?_, ?_, h3fr⟩
  · have hskip : Eval main Cmd.skip s3 s3 1 := Eval.skip s3
    have h' := Eval.seq he2 (Eval.seq he3 hskip)
    simpa [divProgFdiv, seqs, seqs_cons, seqs_nil] using h'
  · have h2b : n2 ≤ 24 + 40 * (isz a + isz b + 1) +
        (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := hn2
    have h3b : n3 ≤ 60 * ((a.natAbs.size + 1) + (b.natAbs.size + 1) + 2) + 60 := hn3
    change n2 + (n3 + 1) ≤ 1000 * isz a * isz b
    rw [isz_eq, isz_eq] at h2b ⊢
    nlinarith [Nat.zero_le n2, Nat.zero_le n3]
  · rw [h30, encs_cons_int, List.append_assoc]

theorem div_fmod_word (main : Cmd) :
    WordR main divProgFmod (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ 0 < b)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a.fmod b) :: rest)
      (binCost (fun a b => 1000 * isz a * isz b)) := by
  intro vs hv s R h0
  obtain ⟨a, b, rest, rfl, hb⟩ := hv
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    rw [h0, encs_cons_int, encs_cons_int]
    simp only [List.append_assoc]
  obtain ⟨s2, n2, rv, qv, he2, h20, h2P, h2B, h2R, h2Q, h2eq, h2rlt, h2S, h2C, h2D, h2X, h2Y,
    h2fr, hn2⟩ := div_core_run main s a b (encs rest ++ R) h0' (ne_of_gt hb)
  obtain ⟨hdv, hmv⟩ := divmod_unique (Int.natAbs_pos.mpr (ne_of_gt hb)) h2eq h2rlt
  obtain ⟨s3, n3, he3, hn3, h30, h3fr⟩ :=
    div_fixFmod main s a b (encs rest ++ R) s2 hb (b.natAbs.size + 1) (a.natAbs.size + 1)
      rfl rv qv hmv hdv h20 h2P h2B h2R h2Q h2S h2C h2D h2X h2Y
      (fun k hk => by
        obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := not_marker_of_ge_ten hk
        exact h2fr k g0 g1 g2 g3 g4 g5 g6 g7 g8 g9)
  refine ⟨.int (a.fmod b) :: rest, s3, n2 + (n3 + 1), ⟨a, b, rest, rfl, rfl⟩, ?_, ?_, ?_, h3fr⟩
  · have hskip : Eval main Cmd.skip s3 s3 1 := Eval.skip s3
    have h' := Eval.seq he2 (Eval.seq he3 hskip)
    simpa [divProgFmod, seqs, seqs_cons, seqs_nil] using h'
  · have h2b : n2 ≤ 24 + 40 * (isz a + isz b + 1) +
        (a.natAbs.size + 2) * (150 * (b.natAbs.size + 2) + 150) := hn2
    have h3b : n3 ≤ 60 * ((a.natAbs.size + 1) + (b.natAbs.size + 1) + 2) + 60 := hn3
    change n2 + (n3 + 1) ≤ 1000 * isz a * isz b
    rw [isz_eq, isz_eq] at h2b ⊢
    nlinarith [Nat.zero_le n2, Nat.zero_le n3]
  · rw [h30, encs_cons_int, List.append_assoc]

end Work.IntLib.Div
