import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.intDivAPI
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.eval_mvRev
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.div_prep_eval
import Submission.Work.IntLib.div_emit_eval
import Submission.Work.IntLib.cleanupSpecStk0
import Submission.Work.IntLib.div_fixFdiv

namespace Work.IntLib

open HvdH
open Work.IntLib.Div

theorem div_fixTmod (main : HvdH.Cmd) (b0 : HvdH.State) (a b : ℤ) (Z : List HvdH.Glyph)
    (S : HvdH.State) (hb : b ≠ 0) (L j : ℕ) (hL : L = b.natAbs.size + 1) (rv qv : ℕ)
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
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.fixTmod S s' n ∧
      n ≤ 40 * (j + L + 2) + 60 ∧
      s'.stk 0 = (HvdH.Val.int (a.tmod b)).enc ++ Z ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  -- ## size facts
  have hbabs : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hrvlt : rv < b.natAbs := by rw [hrv]; exact Nat.mod_lt _ hbabs
  have hL1 : 1 ≤ L := by rw [hL]; omega
  have hrvL : rv < 2 ^ L := by
    have h1 : b.natAbs < 2 ^ b.natAbs.size := Nat.lt_size_self _
    have h2 : 2 ^ b.natAbs.size < 2 ^ L := by
      rw [hL]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  -- ## readSigns
  set sb : Glyph := if b < 0 then Glyph.neg else Glyph.pos with hsb
  set sa : Glyph := if a < 0 then Glyph.neg else Glyph.pos with hsa
  have hSY : S.stk stY = sb :: sa :: ([gY] ++ b0.stk stY) := by
    rw [hS9]; simp [hsb, hsa]
  set S1 : State := ⟨Function.update S.reg rgT sb,
    Function.update S.stk stY (sa :: ([gY] ++ b0.stk stY))⟩ with hS1
  have hpop1 : Eval main (.pop stY rgT) S S1 1 := by
    rw [hS1]
    have h := Eval.pop (main := main) stY rgT S
    rw [hSY] at h
    simpa using h
  have hS1Y : S1.stk stY = sa :: ([gY] ++ b0.stk stY) := by simp [hS1]
  set S2 : State := ⟨Function.update S1.reg rgU sa,
    Function.update S1.stk stY ([gY] ++ b0.stk stY)⟩ with hS2
  have hpop2 : Eval main (.pop stY rgU) S1 S2 1 := by
    rw [hS2]
    have h := Eval.pop (main := main) stY rgU S1
    rw [hS1Y] at h
    simpa using h
  have hread : Eval main readSigns S S2 3 := by
    have h := Eval.seq hpop1 (Eval.seq hpop2 (Eval.skip S2))
    simpa [readSigns, seqs, seqs_cons, seqs_nil] using h
  have hS2Y : S2.stk stY = [gY] ++ b0.stk stY := by simp [hS2]
  have hS2regU : S2.reg rgU = sa := by simp [hS2]
  have hS2oth : ∀ q : Stk, q ≠ stY → S2.stk q = S.stk q := by
    intro q hq
    simp [hS2, hS1, Function.update_apply, if_neg hq]
  have hS2hot : ∀ k : Stk, 10 ≤ k.val → S2.stk k = b0.stk k := by
    intro k hk
    have hkY : k ≠ stY := by intro h; rw [h] at hk; simp at hk
    rw [hS2oth k hkY]; exact hoth k hk
  -- ## prep stR gR
  have hR' : S2.stk stR = bitsG (padBits rv L) ++ gR :: b0.stk stR := by
    rw [hS2oth stR (by decide), hR]; simp
  have hS8' : S2.stk stX = [gX] ++ b0.stk stX := by
    rw [hS2oth stX (by decide), hS8]
  obtain ⟨S3, n3, hev3, hc3, h3R, h3X, h3fr⟩ :=
    div_prep_eval main stR gR (padBits rv L) (b0.stk stR) (b0.stk stX) S2
      (fun b' => by intro h; cases h) hR' hS8' (by decide)
  have hc3' : n3 ≤ 7 * L + 19 := by rw [padBits_length] at hc3; exact hc3
  have h3regU : S3.reg rgU = sa := by
    have hw : writesOnly (fun r => r = rgT) (prep stR gR) := by
      simp [prep, seqs, seqs_cons, seqs_nil, writesOnly, mkG, stripZeros,
        writesOnly_mvRevOnto, writesOnly_mkG]
    rw [Eval_reg_frame hev3 (R := fun r => r = rgT) hw rgU (by decide), hS2regU]
  -- ## sign ite
  set w1 : Glyph := if sa = Glyph.neg then Glyph.neg else Glyph.pos with hw1
  set S4 : State := ⟨Function.update S3.reg rgW w1, S3.stk⟩ with hS4def
  have hw1val : w1 = (if a < 0 then Glyph.neg else Glyph.pos) := by
    rw [hw1, hsa]; by_cases h : a < 0 <;> simp [h]
  have hite1 : Eval main (.ite rgU Glyph.neg (.set rgW Glyph.neg) (.set rgW Glyph.pos)) S3 S4 2 := by
    by_cases h : sa = Glyph.neg
    · have hreg : S3.reg rgU = Glyph.neg := by rw [h3regU, h]
      have hs : Eval main (.set rgW Glyph.neg) S3 S4 1 := by
        rw [hS4def, hw1, if_pos h]; exact Eval.set rgW Glyph.neg S3
      exact Eval.iteT hreg hs
    · have hreg : S3.reg rgU ≠ Glyph.neg := by rw [h3regU]; exact h
      have hs : Eval main (.set rgW Glyph.pos) S3 S4 1 := by
        rw [hS4def, hw1, if_neg h]; exact Eval.set rgW Glyph.pos S3
      exact Eval.iteF hreg hs
  have hS4stk : ∀ q : Stk, S4.stk q = S3.stk q := fun q => rfl
  have h4W : S4.reg rgW = w1 := by simp [hS4def]
  -- ## peek
  set S5 : State := ⟨Function.update S4.reg rgV ((S4.stk stX).headD Glyph.eos), S4.stk⟩ with hS5def
  have hpeek : Eval main (.peek stX rgV) S4 S5 1 := by rw [hS5def]; exact Eval.peek stX rgV S4
  have hS5stk : ∀ q : Stk, S5.stk q = S4.stk q := fun q => rfl
  have h5V : S5.reg rgV = (S3.stk stX).headD Glyph.eos := by simp [hS5def, hS4def]
  have hS5W : S5.reg rgW = w1 := by rw [hS5def]; exact h4W
  -- ## the stripped region
  set l2 : List Glyph := ((bitsG (padBits rv L)).reverse).dropWhile (fun g => g = Glyph.bit false) with hl2
  have hS3X : S3.stk stX = l2 ++ [gX] ++ b0.stk stX := by rw [h3X, hl2]
  have hl2G : l2 = bitsG (((padBits rv L).reverse).dropWhile (fun b => b = false)) := by
    have h1 : (bitsG (padBits rv L)).reverse = bitsG ((padBits rv L).reverse) := bitsG_reverse _
    rw [hl2, h1, dropWhile_false_bitsG]
  have hl2rev : l2.reverse = bitsG (Computability.encodeNat rv) := by
    rw [hl2, emit_bits_reverse (padBits rv L), ofBits_padBits, Nat.mod_eq_of_lt hrvL]
  have hl2nil : l2 = [] ↔ rv = 0 := by
    constructor
    · intro h
      have h1 : bitsG (Computability.encodeNat rv) = [] := by rw [← hl2rev, h]; rfl
      have h2 : Computability.encodeNat rv = [] := by simpa using h1
      exact (encodeNat_eq_nil_iff rv).mp h2
    · intro h
      have h1 : Computability.encodeNat rv = [] := (encodeNat_eq_nil_iff rv).mpr h
      have h2 : bitsG (Computability.encodeNat rv) = [] := by simp [bitsG, h1]
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
      have hyin : y ∈ bitsG (((padBits rv L).reverse).dropWhile (fun b => b = false)) := by
        rw [← hl2G, hy]; exact List.mem_cons_self ..
      obtain ⟨c, -, hc⟩ := List.mem_map.mp hyin
      rw [← hc]; exact bit_ne_gX c
    rw [hy]; intro hcon; exact hybit hcon
  -- ## ite over rgV
  set S6 : State := (if S5.reg rgV = gX then (⟨Function.update S5.reg rgW Glyph.pos, S5.stk⟩ : State) else S5) with hS6def
  have hite2 : Eval main (.ite rgV gX (.set rgW Glyph.pos) .skip) S5 S6 2 := by
    rw [hS6def]
    by_cases hc : S5.reg rgV = gX
    · rw [if_pos hc]; exact Eval.iteT hc (Eval.set rgW Glyph.pos S5)
    · rw [if_neg hc]; exact Eval.iteF hc (Eval.skip S5)
  have h6stk : ∀ q : Stk, S6.stk q = S5.stk q := by
    intro q
    rw [hS6def]
    by_cases hc : S5.reg rgV = gX <;> simp [hc]
  have htmod : a.tmod b = (if a < 0 then (-1 : ℤ) else 1) * ((rv : ℕ) : ℤ) := by
    have h := intDivAPI.2.1 a b hb
    rw [← hrv] at h
    exact h
  have h6W : S6.reg rgW = (if a.tmod b < 0 then Glyph.neg else Glyph.pos) := by
    rw [hS6def]
    by_cases hc : S5.reg rgV = gX
    · rw [if_pos hc]
      have hl2e : l2 = [] := by
        by_contra hne
        exact hhead_ne hne (by rw [← hS3X, ← h5V]; exact hc)
      have hrv0 : rv = 0 := hl2nil.mp hl2e
      have hz : a.tmod b = 0 := by rw [htmod, hrv0]; simp
      rw [hz]; norm_num
    · rw [if_neg hc]
      have hrv0 : rv ≠ 0 := by
        intro h0
        exact hc (by rw [h5V, hS3X, hl2nil.mpr h0]; rfl)
      rw [hS5W, hw1val]
      rcases lt_or_ge a 0 with ha | ha
      · rw [if_pos ha]
        have hneg : a.tmod b < 0 := by
          rw [htmod, if_pos ha]
          have : (0 : ℤ) < (rv : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hrv0
          linarith
        rw [if_pos hneg]
      · rw [if_neg (not_lt.mpr ha)]
        have hnn : ¬ a.tmod b < 0 := by
          rw [htmod, if_neg (not_lt.mpr ha), one_mul]
          exact not_lt.mpr (Int.natCast_nonneg rv)
        rw [if_neg hnn]
  -- ## emit
  have h6X : S6.stk stX = l2 ++ gX :: b0.stk stX := by
    rw [h6stk stX, hS5stk stX, hS4stk stX, hS3X]
    simp [List.append_assoc]
  have h60 : S6.stk 0 = Z := by
    rw [h6stk 0, hS5stk 0, hS4stk 0]
    rw [h3fr 0 (by decide) (by decide), hS2oth 0 (by decide)]
    exact h0
  have hsafe : ∀ g ∈ l2, g ≠ gX := by
    intro g hg hcon
    have hgin : g ∈ bitsG (((padBits rv L).reverse).dropWhile (fun b => b = false)) := by
      rw [← hl2G]; exact hg
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hgin
    rw [← hc] at hcon; exact bit_ne_gX c hcon
  obtain ⟨S7, n7, hev7, hc7, h70, h7X, h7fr⟩ :=
    div_emit_eval main rgW l2 (b0.stk stX) Z S6 h6X h60 hsafe (by decide) (by decide)
  -- ## cleanup
  have h7stack : ∀ q : Stk, q ≠ 0 → q ≠ stX → q ≠ stR → q ≠ stY → S7.stk q = S.stk q := by
    intro q hq0 hqX hqR hqY
    rw [h7fr q hq0 hqX, h6stk q, hS5stk q, hS4stk q, h3fr q hqR hqX, hS2oth q hqY]
  have h7P : S7.stk stP = ([] : List Glyph) ++ [gP] ++ b0.stk stP := by
    rw [h7stack stP (by decide) (by decide) (by decide) (by decide), hP]; simp
  have h7B : S7.stk stB = bitsG (padBits b.natAbs L) ++ [gB] ++ b0.stk stB := by
    rw [h7stack stB (by decide) (by decide) (by decide) (by decide)]; exact hB
  have h7R : S7.stk stR = ([] : List Glyph) ++ [gR] ++ b0.stk stR := by
    rw [h7fr stR (by decide) (by decide), h6stk stR, hS5stk stR, hS4stk stR, h3R]; simp
  have h7Q : S7.stk stQ = bitsG (padBits qv j) ++ [gQ] ++ b0.stk stQ := by
    rw [h7stack stQ (by decide) (by decide) (by decide) (by decide)]; exact hQ
  have h7S : S7.stk stS = ([] : List Glyph) ++ [gS] ++ b0.stk stS := by
    rw [h7stack stS (by decide) (by decide) (by decide) (by decide), hS5]; simp
  have h7C : S7.stk stC = ([] : List Glyph) ++ [gC] ++ b0.stk stC := by
    rw [h7stack stC (by decide) (by decide) (by decide) (by decide), hS6]; simp
  have h7D : S7.stk stD = ([] : List Glyph) ++ [gD] ++ b0.stk stD := by
    rw [h7stack stD (by decide) (by decide) (by decide) (by decide), hS7]; simp
  have h7Xc : S7.stk stX = ([] : List Glyph) ++ [gX] ++ b0.stk stX := by
    rw [h7X]; simp
  have h7Y : S7.stk stY = ([] : List Glyph) ++ [gY] ++ b0.stk stY := by
    rw [h7fr stY (by decide) (by decide), h6stk stY, hS5stk stY, hS4stk stY,
      h3fr stY (by decide) (by decide), hS2Y]; simp
  have h7hot : ∀ k : Stk, 10 ≤ k.val → S7.stk k = b0.stk k := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk
    have hkX : k ≠ stX := by intro h; rw [h] at hk; simp at hk
    have hkR : k ≠ stR := by intro h; rw [h] at hk; simp at hk
    have hkY : k ≠ stY := by intro h; rw [h] at hk; simp at hk
    rw [h7stack k hk0 hkX hkR hkY]; exact hoth k hk
  obtain ⟨S8, n8, hev8, hc8, h80, h8fr⟩ :=
    cleanupSpecStk0 main b0 S7 ([] : List Glyph) (bitsG (padBits b.natAbs L)) ([] : List Glyph)
      (bitsG (padBits qv j)) ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
      ([] : List Glyph) ([] : List Glyph)
      h7P h7B h7R h7Q h7S h7C h7D h7Xc h7Y
      (by intro g hg; cases hg)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; cases hg)
      (by intro g hg; obtain ⟨b', -, hb'⟩ := List.mem_map.mp hg; rw [← hb']; intro hc; cases hc)
      (by intro g hg; cases hg) (by intro g hg; cases hg) (by intro g hg; cases hg)
      (by intro g hg; cases hg) (by intro g hg; cases hg) h7hot
  -- ## assembly
  have hAll : Eval main Div.fixTmod S S8
      (3 + (n3 + (2 + (1 + (2 + (n7 + (n8 + 1))))))) := by
    have h := Eval.seq hread (Eval.seq hev3 (Eval.seq hite1 (Eval.seq hpeek (Eval.seq hite2
      (Eval.seq hev7 (Eval.seq hev8 (Eval.skip S8)))))))
    simpa [Div.fixTmod, seqs, seqs_cons, seqs_nil] using h
  -- ## cost
  have hl2len : l2.length ≤ L := by
    rw [hl2]
    calc (((bitsG (padBits rv L)).reverse).dropWhile (fun g => g = Glyph.bit false)).length
        ≤ ((bitsG (padBits rv L)).reverse).length :=
          List.Sublist.length_le (List.dropWhile_sublist _)
      _ = (bitsG (padBits rv L)).length := List.length_reverse ..
      _ = L := by simp [bitsG, padBits_length]
  have hc8' : n8 ≤ 5 * (L + j) + 117 := by
    have h1 : (bitsG (padBits b.natAbs L)).length = L := by simp [bitsG, padBits_length]
    have h2 : (bitsG (padBits qv j)).length = j := by simp [bitsG, padBits_length]
    rw [h1, h2] at hc8
    simp only [List.length_nil, Nat.add_zero] at hc8
    omega
  -- ## value
  have hnat : (a.tmod b).natAbs = rv := by
    rw [htmod]
    rcases lt_or_ge a 0 with ha | ha
    · rw [if_pos ha]; simp
    · rw [if_neg (not_lt.mpr ha), one_mul, Int.natAbs_natCast]
  have hval : S8.stk 0 = (HvdH.Val.int (a.tmod b)).enc ++ Z := by
    rw [h80, h70, h6W, hl2rev, enc_int, hnat]
    simp only [bitsG, List.cons_append, List.append_assoc]
  refine ⟨S8, 3 + (n3 + (2 + (1 + (2 + (n7 + (n8 + 1)))))), hAll, ?_, hval, h8fr⟩
  omega

end Work.IntLib
