import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.intDivAPI
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.eval_mvRev
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.div_prep_eval
import Submission.Work.IntLib.div_emit_eval
import Submission.Work.IntLib.cleanupSpecStk0
import Submission.Work.IntLib.div_fixFdiv

namespace Work.IntLib

open HvdH
open Work.IntLib.Div

theorem div_fixTdiv (main : HvdH.Cmd) (b0 : HvdH.State) (a b : ℤ) (Z : List HvdH.Glyph)
    (S : HvdH.State) (hb : b ≠ 0) (L j : ℕ) (hL : L = b.natAbs.size + 1) (rv qv : ℕ)
    (hrv : rv = a.natAbs % b.natAbs) (hqv : qv = a.natAbs / b.natAbs) (hqvj : qv < 2 ^ j)
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
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.fixTdiv S s' n ∧
      n ≤ 40 * (j + L + 2) + 60 ∧
      s'.stk 0 = (HvdH.Val.int (a.tdiv b)).enc ++ Z ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  have hL1 : 1 ≤ L := by rw [hL]; omega
  -- ## readSigns
  set sb : Glyph := if b < 0 then Glyph.neg else Glyph.pos with hsb
  set sa : Glyph := if a < 0 then Glyph.neg else Glyph.pos with hsa
  have hSY : S.stk stY = sb :: sa :: ([gY] ++ b0.stk stY) := by rw [hS9]; simp [hsb, hsa]
  set R1 : State := ⟨Function.update S.reg rgT sb,
    Function.update S.stk stY (sa :: ([gY] ++ b0.stk stY))⟩ with hR1
  have hpop1 : Eval main (.pop stY rgT) S R1 1 := by
    rw [hR1]
    have h := Eval.pop (main := main) stY rgT S
    rw [hSY] at h
    simpa using h
  have hR1Y : R1.stk stY = sa :: ([gY] ++ b0.stk stY) := by simp [hR1]
  set R2 : State := ⟨Function.update R1.reg rgU sa,
    Function.update R1.stk stY ([gY] ++ b0.stk stY)⟩ with hR2
  have hpop2 : Eval main (.pop stY rgU) R1 R2 1 := by
    rw [hR2]
    have h := Eval.pop (main := main) stY rgU R1
    rw [hR1Y] at h
    simpa using h
  have hread : Eval main readSigns S R2 3 := by
    have h := Eval.seq hpop1 (Eval.seq hpop2 (Eval.skip R2))
    simpa [readSigns, seqs, seqs_cons, seqs_nil] using h
  have hR2Y : R2.stk stY = [gY] ++ b0.stk stY := by simp [hR2]
  have hR2regU : R2.reg rgU = sa := by simp [hR2]
  have hR2regT : R2.reg rgT = sb := by
    show (Function.update (Function.update S.reg rgT sb) rgU sa) rgT = sb
    rw [Function.update_of_ne (by decide : (rgT : Reg) ≠ rgU)]
    exact Function.update_self rgT sb S.reg
  have hR2oth : ∀ q : Stk, q ≠ stY → R2.stk q = S.stk q := by
    intro q hq
    simp [hR2, hR1, Function.update_apply, if_neg hq]
  have hR2hot : ∀ k : Stk, 10 ≤ k.val → R2.stk k = b0.stk k := by
    intro k hk
    have hkY : k ≠ stY := by intro h; rw [h] at hk; simp at hk
    rw [hR2oth k hkY]; exact hoth k hk
  -- ## sign ite (nested: dividend sign and divisor sign)
  set w1 : Glyph := (if sa = Glyph.neg then (if sb = Glyph.neg then Glyph.pos else Glyph.neg)
    else (if sb = Glyph.neg then Glyph.neg else Glyph.pos)) with hw1
  set W1 : State := ⟨Function.update R2.reg rgW w1, R2.stk⟩ with hW1
  have hite1 : Eval main (.ite rgU Glyph.neg
      (.ite rgT Glyph.neg (.set rgW Glyph.pos) (.set rgW Glyph.neg))
      (.ite rgT Glyph.neg (.set rgW Glyph.neg) (.set rgW Glyph.pos))) R2 W1 3 := by
    by_cases h : sa = Glyph.neg
    · have hregU : R2.reg rgU = Glyph.neg := by rw [hR2regU, h]
      by_cases h2 : sb = Glyph.neg
      · have hregT : R2.reg rgT = Glyph.neg := by rw [hR2regT, h2]
        have hs : Eval main (.set rgW Glyph.pos) R2 W1 1 := by
          rw [hW1, hw1, if_pos h, if_pos h2]
          exact Eval.set rgW Glyph.pos R2
        exact Eval.iteT hregU (Eval.iteT hregT hs)
      · have hregT : R2.reg rgT ≠ Glyph.neg := by rw [hR2regT]; exact h2
        have hs : Eval main (.set rgW Glyph.neg) R2 W1 1 := by
          rw [hW1, hw1, if_pos h, if_neg h2]
          exact Eval.set rgW Glyph.neg R2
        exact Eval.iteT hregU (Eval.iteF hregT hs)
    · have hregU : R2.reg rgU ≠ Glyph.neg := by rw [hR2regU]; exact h
      by_cases h2 : sb = Glyph.neg
      · have hregT : R2.reg rgT = Glyph.neg := by rw [hR2regT, h2]
        have hs : Eval main (.set rgW Glyph.neg) R2 W1 1 := by
          rw [hW1, hw1, if_neg h, if_pos h2]
          exact Eval.set rgW Glyph.neg R2
        exact Eval.iteF hregU (Eval.iteT hregT hs)
      · have hregT : R2.reg rgT ≠ Glyph.neg := by rw [hR2regT]; exact h2
        have hs : Eval main (.set rgW Glyph.pos) R2 W1 1 := by
          rw [hW1, hw1, if_neg h, if_neg h2]
          exact Eval.set rgW Glyph.pos R2
        exact Eval.iteF hregU (Eval.iteF hregT hs)
  have hW1stk : ∀ q : Stk, W1.stk q = R2.stk q := fun q => rfl
  have hW1W : W1.reg rgW = w1 := by simp [hW1]
  have hW1regU : W1.reg rgU = sa := by rw [hW1]; exact hR2regU
  -- ## prep stQ gQ
  have hwrites : writesOnly (fun r => r = rgT) (prep stQ gQ) := by
    simp [prep, seqs, seqs_cons, seqs_nil, writesOnly, mkG, stripZeros,
      writesOnly_mvRevOnto, writesOnly_mkG]
  have hQ' : W1.stk stQ = bitsG (padBits qv j) ++ gQ :: b0.stk stQ := by
    rw [hW1stk stQ, hR2oth stQ (by decide), hQ]; simp
  have hX' : W1.stk stX = [gX] ++ b0.stk stX := by
    rw [hW1stk stX, hR2oth stX (by decide), hS8]
  obtain ⟨P1, n4, hev4, hc4, h4Q, h4X, h4fr⟩ :=
    div_prep_eval main stQ gQ (padBits qv j) (b0.stk stQ) (b0.stk stX) W1
      (fun b' => by intro h; cases h) hQ' hX' (by decide)
  have hc4' : n4 ≤ 7 * j + 19 := by rw [padBits_length] at hc4; exact hc4
  have h4regU : P1.reg rgU = sa := by
    rw [Eval_reg_frame hev4 (R := fun r => r = rgT) hwrites rgU (by decide), hW1regU]
  have h4regW : P1.reg rgW = w1 := by
    rw [Eval_reg_frame hev4 (R := fun r => r = rgT) hwrites rgW (by decide), hW1W]
  -- ## peek
  set K1 : State := ⟨Function.update P1.reg rgV ((P1.stk stX).headD Glyph.eos), P1.stk⟩ with hK1
  have hpeek : Eval main (.peek stX rgV) P1 K1 1 := by rw [hK1]; exact Eval.peek stX rgV P1
  have hK1stk : ∀ q : Stk, K1.stk q = P1.stk q := fun q => rfl
  have hK1V : K1.reg rgV = (P1.stk stX).headD Glyph.eos := by simp [hK1]
  have hK1W : K1.reg rgW = w1 := by rw [hK1]; exact h4regW
  -- ## the stripped quotient region
  set l2 : List Glyph := ((bitsG (padBits qv j)).reverse).dropWhile (fun g => g = Glyph.bit false)
    with hl2
  have hP1X : P1.stk stX = l2 ++ [gX] ++ b0.stk stX := by rw [h4X, hl2]
  have hl2G : l2 = bitsG (((padBits qv j).reverse).dropWhile (fun b => b = false)) := by
    have h1 : (bitsG (padBits qv j)).reverse = bitsG ((padBits qv j).reverse) := bitsG_reverse _
    rw [hl2, h1, dropWhile_false_bitsG]
  have hl2rev : l2.reverse = bitsG (Computability.encodeNat qv) := by
    rw [hl2, emit_bits_reverse (padBits qv j), ofBits_padBits, Nat.mod_eq_of_lt hqvj]
  have hl2nil : l2 = [] ↔ qv = 0 := by
    constructor
    · intro h
      have h1 : bitsG (Computability.encodeNat qv) = [] := by rw [← hl2rev, h]; rfl
      have h2 : Computability.encodeNat qv = [] := by simpa using h1
      exact (encodeNat_eq_nil_iff qv).mp h2
    · intro h
      have h1 : Computability.encodeNat qv = [] := (encodeNat_eq_nil_iff qv).mpr h
      have h2 : bitsG (Computability.encodeNat qv) = [] := by simp [bitsG, h1]
      have h3 : l2.reverse = [] := by rw [hl2rev, h2]
      have h4 : l2.reverse.reverse = ([] : List Glyph).reverse := by rw [h3]
      simpa using h4
  have hhead_ne : l2 ≠ [] → (l2 ++ [gX] ++ b0.stk stX).headD Glyph.eos ≠ gX := by
    intro hne
    obtain ⟨y, ys, hy⟩ : ∃ y ys, l2 = y :: ys := by
      cases h : l2 with
      | nil => exact absurd h hne
      | cons y ys => exact ⟨y, ys, rfl⟩
    have hybit : y ≠ gX := by
      have hyin : y ∈ bitsG (((padBits qv j).reverse).dropWhile (fun b => b = false)) := by
        rw [← hl2G, hy]; exact List.mem_cons_self ..
      obtain ⟨c, -, hc⟩ := List.mem_map.mp hyin
      rw [← hc]; exact bit_ne_gX c
    rw [hy]; intro hcon; exact hybit hcon
  have hsafe : ∀ g ∈ l2, g ≠ gX := by
    intro g hg hcon
    have hgin : g ∈ bitsG (((padBits qv j).reverse).dropWhile (fun b => b = false)) := by
      rw [← hl2G]; exact hg
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hgin
    rw [← hc] at hcon; exact bit_ne_gX c hcon
  -- ## ite over rgV (kill the sign if the quotient vanishes)
  set V1 : State := (if K1.reg rgV = gX then
    (⟨Function.update K1.reg rgW Glyph.pos, K1.stk⟩ : State) else K1) with hV1
  have hite2 : Eval main (.ite rgV gX (.set rgW Glyph.pos) .skip) K1 V1 2 := by
    rw [hV1]
    by_cases hc : K1.reg rgV = gX
    · rw [if_pos hc]; exact Eval.iteT hc (Eval.set rgW Glyph.pos K1)
    · rw [if_neg hc]; exact Eval.iteF hc (Eval.skip K1)
  have hV1stk : ∀ q : Stk, V1.stk q = K1.stk q := by
    intro q; rw [hV1]; by_cases hc : K1.reg rgV = gX <;> simp [hc]
  have htdiv : a.tdiv b = (if a < 0 then (-1 : ℤ) else 1) * (if b < 0 then (-1 : ℤ) else 1) *
      ((qv : ℕ) : ℤ) := by
    have h := intDivAPI.1 a b hb
    rw [← hqv] at h
    exact h
  have hw1val : w1 = (if a < 0 then (if b < 0 then Glyph.pos else Glyph.neg)
      else (if b < 0 then Glyph.neg else Glyph.pos)) := by
    rw [hw1, hsa, hsb]
    by_cases ha : a < 0
    · by_cases hbb : b < 0
      · simp [ha, hbb]
      · simp [ha, hbb]
    · by_cases hbb : b < 0
      · simp [ha, hbb]
      · simp [ha, hbb]
  have hV1W : V1.reg rgW = (if a.tdiv b < 0 then Glyph.neg else Glyph.pos) := by
    rw [hV1]
    by_cases hc : K1.reg rgV = gX
    · rw [if_pos hc]
      have hl2e : l2 = [] := by
        by_contra hne
        exact hhead_ne hne (by rw [← hP1X, ← hK1V]; exact hc)
      have hqv0 : qv = 0 := hl2nil.mp hl2e
      have hz : a.tdiv b = 0 := by rw [htdiv, hqv0]; simp
      rw [hz]; norm_num
    · rw [if_neg hc]
      have hqv0 : qv ≠ 0 := by
        intro h0
        exact hc (by rw [hK1V, hP1X, hl2nil.mpr h0]; rfl)
      have hqz : (0 : ℤ) < ((qv : ℕ) : ℤ) := by
        exact_mod_cast Nat.pos_of_ne_zero hqv0
      rw [hK1W, hw1val]
      by_cases ha : a < 0
      · by_cases hbb : b < 0
        · have hval' : a.tdiv b = ((qv : ℕ) : ℤ) := by
            rw [htdiv, if_pos ha, if_pos hbb]; ring
          rw [if_pos ha, if_pos hbb,
            if_neg (by rw [hval']; exact not_lt.mpr (Int.natCast_nonneg qv))]
        · have hval' : a.tdiv b = -(((qv : ℕ) : ℤ)) := by
            rw [htdiv, if_pos ha, if_neg hbb]; ring
          rw [if_pos ha, if_neg hbb, if_pos (by rw [hval']; linarith)]
      · by_cases hbb : b < 0
        · have hval' : a.tdiv b = -(((qv : ℕ) : ℤ)) := by
            rw [htdiv, if_neg ha, if_pos hbb]; ring
          rw [if_neg ha, if_pos hbb, if_pos (by rw [hval']; linarith)]
        · have hval' : a.tdiv b = ((qv : ℕ) : ℤ) := by
            rw [htdiv, if_neg ha, if_neg hbb]; ring
          rw [if_neg ha, if_neg hbb,
            if_neg (by rw [hval']; exact not_lt.mpr (Int.natCast_nonneg qv))]
  -- ## emit
  have hV1X : V1.stk stX = l2 ++ gX :: b0.stk stX := by
    rw [hV1stk stX, hK1stk stX, hP1X]
    simp [List.append_assoc]
  have hV10 : V1.stk 0 = Z := by
    rw [hV1stk 0, hK1stk 0, h4fr 0 (by decide) (by decide), hW1stk 0, hR2oth 0 (by decide)]
    exact h0
  obtain ⟨E1, n7, hev7, hc7, h70, h7X, h7fr⟩ :=
    div_emit_eval main rgW l2 (b0.stk stX) Z V1 hV1X hV10 hsafe (by decide) (by decide)
  -- ## cleanup
  have h7stack : ∀ q : Stk, q ≠ 0 → q ≠ stX → q ≠ stQ → q ≠ stY → E1.stk q = S.stk q := by
    intro q hq0 hqX hqQ hqY
    rw [h7fr q hq0 hqX, hV1stk q, hK1stk q, h4fr q hqQ hqX, hW1stk q, hR2oth q hqY]
  have h7P : E1.stk stP = ([] : List Glyph) ++ [gP] ++ b0.stk stP := by
    rw [h7stack stP (by decide) (by decide) (by decide) (by decide), hP]; simp
  have h7B : E1.stk stB = bitsG (padBits b.natAbs L) ++ [gB] ++ b0.stk stB := by
    rw [h7stack stB (by decide) (by decide) (by decide) (by decide)]; exact hB
  have h7R : E1.stk stR = bitsG (padBits rv L) ++ [gR] ++ b0.stk stR := by
    rw [h7stack stR (by decide) (by decide) (by decide) (by decide)]; exact hR
  have h7Q : E1.stk stQ = ([] : List Glyph) ++ [gQ] ++ b0.stk stQ := by
    rw [h7fr stQ (by decide) (by decide), hV1stk stQ, hK1stk stQ, h4Q]; simp
  have h7S : E1.stk stS = ([] : List Glyph) ++ [gS] ++ b0.stk stS := by
    rw [h7stack stS (by decide) (by decide) (by decide) (by decide), hS5]; simp
  have h7C : E1.stk stC = ([] : List Glyph) ++ [gC] ++ b0.stk stC := by
    rw [h7stack stC (by decide) (by decide) (by decide) (by decide), hS6]; simp
  have h7D : E1.stk stD = ([] : List Glyph) ++ [gD] ++ b0.stk stD := by
    rw [h7stack stD (by decide) (by decide) (by decide) (by decide), hS7]; simp
  have h7Xc : E1.stk stX = ([] : List Glyph) ++ [gX] ++ b0.stk stX := by
    rw [h7X]; simp
  have h7Y : E1.stk stY = ([] : List Glyph) ++ [gY] ++ b0.stk stY := by
    rw [h7fr stY (by decide) (by decide), hV1stk stY, hK1stk stY,
      h4fr stY (by decide) (by decide), hW1stk stY, hR2Y]; simp
  have h7hot : ∀ k : Stk, 10 ≤ k.val → E1.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk
    have hkX : k ≠ stX := by intro h; rw [h] at hk; simp at hk
    have hkQ : k ≠ stQ := by intro h; rw [h] at hk; simp at hk
    have hkY : k ≠ stY := by intro h; rw [h] at hk; simp at hk
    rw [h7stack k hk0 hkX hkQ hkY]; exact hoth k hk
  obtain ⟨C1, n8, hev8, hc8, h80, h8fr⟩ :=
    cleanupSpecStk0 main b0 E1 ([] : List Glyph) (bitsG (padBits b.natAbs L))
      (bitsG (padBits rv L)) ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
      ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
      h7P h7B h7R h7Q h7S h7C h7D h7Xc h7Y
      (by intro g hg; cases hg)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; cases hg)
      (by intro g hg; cases hg) (by intro g hg; cases hg) (by intro g hg; cases hg)
      (by intro g hg; cases hg) (by intro g hg; cases hg) h7hot
  -- ## assembly
  have hAll : Eval main Div.fixTdiv S C1
      (3 + (3 + (n4 + (1 + (2 + (n7 + (n8 + 1))))))) := by
    have h := Eval.seq hread (Eval.seq hite1 (Eval.seq hev4 (Eval.seq hpeek (Eval.seq hite2
      (Eval.seq hev7 (Eval.seq hev8 (Eval.skip C1)))))))
    simpa [Div.fixTdiv, seqs, seqs_cons, seqs_nil] using h
  -- ## value
  have hnat : (a.tdiv b).natAbs = qv := by
    rw [htdiv]
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    rcases lt_or_ge a 0 with ha | ha
    · rcases lt_or_ge b 0 with hb' | hb'
      · rw [if_pos ha, if_pos hb']; simp
      · rw [if_pos ha, if_neg (not_lt.mpr hb')]; simp
    · rcases lt_or_ge b 0 with hb' | hb'
      · rw [if_neg (not_lt.mpr ha), if_pos hb']; simp
      · rw [if_neg (not_lt.mpr ha), if_neg (not_lt.mpr hb')]; simp
  have hval : C1.stk 0 = (HvdH.Val.int (a.tdiv b)).enc ++ Z := by
    rw [h80, h70, hV1W, hl2rev, enc_int, hnat]
    simp only [bitsG, List.cons_append, List.append_assoc]
  refine ⟨C1, 3 + (3 + (n4 + (1 + (2 + (n7 + (n8 + 1)))))), hAll, ?_, hval, h8fr⟩
  -- ## cost
  have hl2len : l2.length ≤ j := by
    rw [hl2]
    calc (((bitsG (padBits qv j)).reverse).dropWhile (fun g => g = Glyph.bit false)).length
        ≤ ((bitsG (padBits qv j)).reverse).length :=
          List.Sublist.length_le (List.dropWhile_sublist _)
      _ = (bitsG (padBits qv j)).length := List.length_reverse ..
      _ = j := by simp [bitsG, padBits_length]
  have hc8' : n8 ≤ 5 * (2 * L + j) + 117 := by
    have h1 : (bitsG (padBits b.natAbs L)).length = L := by simp [bitsG, padBits_length]
    have h2 : (bitsG (padBits rv L)).length = L := by simp [bitsG, padBits_length]
    rw [h1, h2] at hc8
    simp only [List.length_nil, Nat.add_zero] at hc8
    omega
  omega

end Work.IntLib
