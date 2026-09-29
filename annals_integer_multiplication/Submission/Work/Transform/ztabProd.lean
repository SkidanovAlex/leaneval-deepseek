import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.ConvR.basic
import Submission.Work.Transform.Defs
import Submission.Work.Transform.ztpDefs
import Submission.Work.Transform.ztpSizeMul
import Submission.Work.Transform.ztpPowSize
import Submission.Work.Transform.ztpProdGt
import Submission.Work.Transform.ztpSisz
import Submission.Work.Transform.ztpBsz
import Submission.Work.Transform.ztpPowB

set_option autoImplicit false

namespace Work.Transform

open HvdH Work.Layout

/-! ## Auxiliary lemmas for the walk of `Work.Transform.ztabProd` -/

/-- `isz` of a natural number. -/
theorem ztp_isz_natCast (t : ℕ) : isz (t : ℤ) = t.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

/-- `(encodeNat t).map Glyph.bit = [Glyph.bit true]` iff `t = 1`. -/
theorem ztp_bits_one (t : ℕ) :
    (Computability.encodeNat t).map Glyph.bit = [Glyph.bit true] ↔ t = 1 := by
  constructor
  · intro h
    have h1 : (Computability.encodeNat t).length = 1 := by
      have h2 := congrArg List.length h; simpa using h2
    rw [Work.IntLib.encodeNat_length] at h1
    have h2 : t ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
    have h3 : t < 2 := by
      have h4 := (Nat.size_le (m := t) (n := 1)).mp (by omega : t.size ≤ 1)
      simpa using h4
    omega
  · intro h; subst h; rw [Work.IntLib.encodeNat_eq_bits]; simp

/-- `Work.Layout.mvVal` with the *full* frame: the buffer `c` and the counter `d` are restored too
(the published statement only records the frame outside `{a,b,c,d}`). -/
theorem ztp_mvVal_ev {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B C D : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) (hc : X c = C)
    (hd : X d = D) :
    ∃ s' n, Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧ s'.stk c = C ∧ s'.stk d = D ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.mvA_ev (main := main) hac had hcd v A C D g X ha hc hd
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    Work.Layout.mvB_ev (main := main) hbc (G := v.enc.reverse) (C := C) (B := B)
      (Work.Layout.gMark_not_mem_enc_rev v) hc₁ hb₁
  have hd₂ : s₂.stk d = D := by rw [hf₂ d hcd.symm hbd.symm]; exact hd₁
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hn₂' : n₂ ≤ 4 * (vsz v + 1) + 3 := by rw [← hlen]; exact hn₂
  have hmain : Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold Work.Layout.mvVal
    exact Ev.seq h1 h2
  refine ⟨s₂, n₁ + n₂, hmain, ?_, ?_, ?_, hc₂, hd₂, ?_⟩
  · have h₁ := hn₁; have h₂ := hn₂'; have hv := Work.Layout.one_le_vsz v; omega
  · rw [hf₂ a hac hab]; exact ha₁
  · rw [hb₂, List.reverse_reverse]
  · intro k hka hkb hkc hkd
    rw [hf₂ k hkc hkb]; exact hf₁ k hka hkc hkd

/-- The "test" part of one walk iteration: the three ite tests and the multiplication. -/
theorem ztpStepTail (main : Cmd) (mulProg : Cmd) (Km Bz : ℕ)
    (hmul : WordR main mulProg (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest)
        (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a * b) :: rest)
        (binCost (fun a b => Km * isz a * isz b)))
    {t : ℕ} (ht : 0 < t) {P : ℕ} {V : List Val} {R B : List Glyph}
    (hB : B = (Computability.encodeNat t).map Glyph.bit)
    {g : Reg → Glyph} {X : Stk → List Glyph} {W : List Glyph}
    (hW : W = encs (.int (P:ℤ) :: V) ++ R)
    (hZA : g rZA = Glyph.pos) (hZB : g rZB = B.headD Glyph.eos)
    (hZC : g rZC = (B.tail ++ (Glyph.iend :: W)).headD Glyph.eos)
    (hX0 : X 0 = B.tail ++ (Glyph.iend :: W)) (hsz : P.size ≤ Bz) :
    ∃ (s' : State) (C : ℕ),
      Ev main (Cmd.seq (zITE mulProg) (.set rZL zCont)) ⟨g, X⟩ s' C ∧
      C ≤ 6 + (if 2 ≤ t then Km * (t.size + 2) * (Bz + 2) else 0) ∧
      s'.reg rZL = zCont ∧
      s'.stk 0 = encs (.int ((P * t : ℕ) : ℤ) :: V) ++ R ∧
      (∀ k, k ≠ 0 → s'.stk k = X k) := by
  have hent : (Val.int (t:ℤ)).enc = Glyph.pos :: (B ++ [Glyph.iend]) := by
    rw [Work.IntLib.enc_int, Int.natAbs_natCast]
    simp only [hB]
    rw [if_neg (by simp : ¬ ((t : ℤ) < 0))]
  have hW' : (Val.int (P:ℤ)).enc ++ (encs V ++ R) = W := by
    rw [hW, Work.Kernel.encs_cons, List.append_assoc]
  have hBne : B ≠ [] := by
    intro h
    have h1 : (Computability.encodeNat t).map Glyph.bit = [] := by rw [← hB]; exact h
    rw [List.map_eq_nil_iff] at h1
    exact absurd ((Work.IntLib.encodeNat_eq_nil_iff t).mp h1) (by omega)
  have hB1 : B = [Glyph.bit true] ↔ t = 1 := by rw [hB]; exact ztp_bits_one t
  have hBmem : ∀ c ∈ B, ∃ b, c = Glyph.bit b := by
    intro c hc; rw [hB] at hc
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hc
    exact ⟨b, hb.symm⟩
  have hBcons : B.headD Glyph.eos :: B.tail = B := by
    cases B with
    | nil => exact absurd rfl hBne
    | cons b bs => rfl
  have hSET : ∀ (gg : Reg → Glyph) (XX : Stk → List Glyph),
      Ev main (.set rZL zCont) ⟨gg, XX⟩ ⟨Function.update gg rZL zCont, XX⟩ 1 := fun gg XX =>
    Work.Layout.ev_set' main rZL zCont gg XX
  have hMUL : ∃ (s' : State) (C : ℕ),
      Ev main (Work.Layout.seqs [.push 0 rZB, .push 0 rZA, mulProg]) ⟨g, X⟩ s' C ∧
      C ≤ 2 + Km * (t.size + 2) * (Bz + 2) ∧
      s'.stk 0 = encs (.int ((t * P : ℕ) : ℤ) :: V) ++ R ∧
      (∀ k, k ≠ 0 → s'.stk k = X k) := by
    have hp1 : Ev main (.push 0 rZB) ⟨g, X⟩ ⟨g, Function.update X 0 (g rZB :: X 0)⟩ 1 :=
      Work.Layout.ev_push' main 0 rZB g X
    have hp2 : Ev main (.push 0 rZA) ⟨g, Function.update X 0 (g rZB :: X 0)⟩
        ⟨g, Function.update (Function.update X 0 (g rZB :: X 0)) 0 (g rZA :: g rZB :: X 0)⟩ 1 :=
      Work.Layout.ev_push' main 0 rZA g (Function.update X 0 (g rZB :: X 0))
    set X₂ : Stk → List Glyph :=
      Function.update (Function.update X 0 (g rZB :: X 0)) 0 (g rZA :: g rZB :: X 0) with hX₂
    have hX₂0 : X₂ 0 = encs (.int (t:ℤ) :: .int (P:ℤ) :: V) ++ R := by
      have h1 : X₂ 0 = g rZA :: (g rZB :: (B.tail ++ (Glyph.iend :: W))) := by
        simp only [hX₂, Function.update_self, hX0]
      have hL : g rZA :: g rZB :: (B.tail ++ (Glyph.iend :: W)) =
          Glyph.pos :: (B ++ (Glyph.iend :: W)) := by
        rw [hZA, hZB]
        conv_rhs => rw [← hBcons]
        simp only [List.headD_cons, List.tail_cons, List.cons_append, List.append_assoc]
      have hR : encs (.int (t:ℤ) :: .int (P:ℤ) :: V) ++ R =
          Glyph.pos :: (B ++ (Glyph.iend :: W)) := by
        rw [Work.Kernel.encs_cons, Work.Kernel.encs_cons]
        simp only [List.append_assoc]
        rw [hW', hent]
        simp only [List.singleton_append, List.cons_append, List.append_assoc,
          List.nil_append]
      rw [h1, hL, ← hR]
    obtain ⟨out, s₃, n₃, hpost, hev₃, hn₃, hstk₃, hoth₃⟩ :=
      hmul (.int (t:ℤ) :: .int (P:ℤ) :: V) ⟨(t:ℤ), (P:ℤ), V, rfl⟩ ⟨g, X₂⟩ R hX₂0
    have hev₃' : Ev main mulProg ⟨g, X₂⟩ s₃ n₃ := ⟨n₃, hev₃, le_rfl⟩
    obtain ⟨a, b, rest, hvs, hout⟩ := hpost
    have ha : (t:ℤ) = a := by simpa using (List.cons.inj hvs).1
    have hb : (P:ℤ) = b := by simpa using (List.cons.inj (List.cons.inj hvs).2).1
    have hr : V = rest := by simpa using (List.cons.inj (List.cons.inj hvs).2).2
    have hout' : out = .int ((t * P : ℕ) : ℤ) :: V := by
      have h1 : out = .int ((t:ℤ) * (P:ℤ)) :: rest := by rw [hout, ← ha, ← hb]
      rw [h1, ← hr]
      simp only [Int.natCast_mul]
    have hn₃' : n₃ ≤ Km * (t.size + 2) * (P.size + 2) := by
      simpa [binCost, ztp_isz_natCast] using hn₃
    have h3 : P.size + 2 ≤ Bz + 2 := by omega
    have h4 : Km * (t.size + 2) * (P.size + 2) ≤ Km * (t.size + 2) * (Bz + 2) :=
      Nat.mul_le_mul_left (Km * (t.size + 2)) h3
    refine ⟨s₃, 1 + (1 + n₃), Ev.seq hp1 (Ev.seq hp2 hev₃'), ?_, ?_, ?_⟩
    · have h6 := Nat.add_le_add_left (le_trans hn₃' h4) 2
      have h7 : 1 + (1 + n₃) = 2 + n₃ := by omega
      rw [h7]
      exact h6
    · rw [hstk₃, hout']
    · intro k hk
      rw [hoth₃ k hk]
      simp only [hX₂, Function.update_of_ne hk]
  by_cases ht1 : t = 1
  · -- the "skip" branch
    have hB1' : B = [Glyph.bit true] := hB1.mpr ht1
    have hZB' : g rZB = Glyph.bit true := by rw [hZB, hB1']; rfl
    have hZC' : g rZC = Glyph.iend := by rw [hZC, hB1']; rfl
    have hX0' : X 0 = Glyph.iend :: W := by rw [hX0, hB1']; rfl
    have hSKIP : Ev main (.pop 0 rZX) ⟨g, X⟩
        ⟨Function.update g rZX Glyph.iend, Function.update X 0 W⟩ 1 := by
      have h := Work.Layout.ev_pop' main 0 rZX g X
      rw [hX0'] at h
      simpa using h
    have hITE : Ev main (zITE mulProg) ⟨g, X⟩
        ⟨Function.update g rZX Glyph.iend, Function.update X 0 W⟩ (1 + 1 + 1 + 1) :=
      Ev.iteT hZA (Ev.iteT hZB' (Ev.iteT hZC' hSKIP))
    refine ⟨⟨Function.update (Function.update g rZX Glyph.iend) rZL zCont, Function.update X 0 W⟩,
      1 + 1 + 1 + 1 + 1, ?_, ?_, ?_, ?_, ?_⟩
    · exact Ev.seq hITE (hSET (Function.update g rZX Glyph.iend) (Function.update X 0 W))
    · rw [if_neg (by omega : ¬ (2 ≤ t))]
      omega
    · simp only [Function.update_apply]
      simp
    · simp only [Work.Layout.stk_mk, Function.update_self]
      rw [ht1, Nat.mul_one, hW]
    · intro k hk
      simp only [Work.Layout.stk_mk, Function.update_of_ne hk]
  · -- the "multiply" branch
    have hBne1 : B ≠ [Glyph.bit true] := fun h => ht1 (hB1.mp h)
    obtain ⟨sM, CM, hevM, hCM, hstkM, hfrM⟩ := hMUL
    have hZCne_of : g rZB = Glyph.bit true → g rZC ≠ Glyph.iend := by
      intro hZB1 hZC1
      have hBheadbt : B.headD Glyph.eos = Glyph.bit true := by rw [← hZB]; exact hZB1
      have hBtailie : (B.tail ++ (Glyph.iend :: W)).headD Glyph.eos = Glyph.iend := by
        rw [← hZC]; exact hZC1
      have hBeq : B = [Glyph.bit true] := by
        cases B with
        | nil => exact absurd rfl hBne
        | cons c cs =>
          simp only [List.headD_cons] at hBheadbt
          subst hBheadbt
          cases cs with
          | nil => rfl
          | cons d ds =>
            exfalso
            simp only [List.tail_cons, List.headD_cons] at hBtailie
            obtain ⟨b', hb'⟩ := hBmem d (by simp)
            rw [hb'] at hBtailie
            exact absurd hBtailie (fun h => by cases h)
      exact hBne1 hBeq
    by_cases hZB1 : g rZB = Glyph.bit true
    · have hITE : Ev main (zITE mulProg) ⟨g, X⟩ ⟨sM.reg, sM.stk⟩ (CM + 1 + 1 + 1) :=
        Ev.iteT hZA (Ev.iteT hZB1 (Ev.iteF (hZCne_of hZB1) hevM))
      refine ⟨⟨Function.update sM.reg rZL zCont, sM.stk⟩, CM + 1 + 1 + 1 + 1, ?_, ?_, ?_, ?_, ?_⟩
      · exact Ev.seq hITE (hSET sM.reg sM.stk)
      · rw [if_pos (by omega : 2 ≤ t)]
        omega
      · simp only [Function.update_apply]
        simp
      · simp only [Work.Layout.stk_mk]
        rw [hstkM]
        congr 1
        rw [Nat.mul_comm]
      · intro k hk; exact hfrM k hk
    · have hITE : Ev main (zITE mulProg) ⟨g, X⟩ ⟨sM.reg, sM.stk⟩ (CM + 1 + 1) :=
        Ev.iteT hZA (Ev.iteF hZB1 hevM)
      refine ⟨⟨Function.update sM.reg rZL zCont, sM.stk⟩, CM + 1 + 1 + 1, ?_, ?_, ?_, ?_, ?_⟩
      · exact Ev.seq hITE (hSET sM.reg sM.stk)
      · rw [if_pos (by omega : 2 ≤ t)]
        omega
      · simp only [Function.update_apply]
        simp
      · simp only [Work.Layout.stk_mk]
        rw [hstkM]
        congr 1
        rw [Nat.mul_comm]
      · intro k hk; exact hfrM k hk

/-! ## List helpers -/

theorem ztp_headD_append (B W : List Glyph) (h : B ≠ []) :
    (B ++ (Glyph.iend :: W)).headD Glyph.eos = B.headD Glyph.eos := by
  cases B with
  | nil => exact absurd rfl h
  | cons b bs => rfl

theorem ztp_tail_append (B W : List Glyph) (h : B ≠ []) :
    (B ++ (Glyph.iend :: W)).tail = B.tail ++ (Glyph.iend :: W) := by
  cases B with
  | nil => exact absurd rfl h
  | cons b bs => rfl

theorem ztp_cons_headD (B : List Glyph) (h : B ≠ []) : B.headD Glyph.eos :: B.tail = B := by
  cases B with
  | nil => exact absurd rfl h
  | cons b bs => rfl

/-- One `cons` iteration of the walk: pop the `cons`, move the element onto the accumulator
(`mvVal`), inspect its first three glyphs and stop just before the `ite` tree. -/
theorem ztpPre (main : Cmd) {t : ℕ} (ht : 0 < t) {rem : List ℕ} {P : ℕ} {V : List Val}
    {R S1 : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} {W : List Glyph}
    (hW : W = encs (.int (P:ℤ) :: V) ++ R)
    (hX0 : X 0 = W) (hX1 : X 1 = encLN (t :: rem) ++ zM :: S1) :
    ∃ (s' : State) (C : ℕ) (B : List Glyph),
      B = (Computability.encodeNat t).map Glyph.bit ∧
      Ev main (Work.Layout.seqs [.pop 1 rZX, Work.Layout.mvVal 1 0 2 3, .pop 0 rZA, .pop 0 rZB,
        .peek 0 rZC]) ⟨g, X⟩ s' C ∧
      C ≤ 5 + 16 * (t.size + 3) ∧
      s'.reg rZA = Glyph.pos ∧
      s'.reg rZB = B.headD Glyph.eos ∧
      s'.reg rZC = (B.tail ++ (Glyph.iend :: W)).headD Glyph.eos ∧
      s'.stk 0 = B.tail ++ (Glyph.iend :: W) ∧
      s'.stk 1 = encLN rem ++ zM :: S1 ∧
      (∀ k, k ≠ 0 → k ≠ 1 → s'.stk k = X k) := by
  have hheadX : (X 1).headD Glyph.eos = Glyph.cons := by
    rw [hX1, encLN_cons]; simp only [List.cons_append, List.append_assoc, List.headD_cons]
  have htailX : (X 1).tail = (Val.int (t:ℤ)).enc ++ (encLN rem ++ zM :: S1) := by
    rw [hX1, encLN_cons]; simp only [List.cons_append, List.append_assoc, List.tail_cons]
  have h2 : Ev main (.pop 1 rZX) ⟨g, X⟩
      ⟨Function.update g rZX Glyph.cons, Function.update X 1 ((X 1).tail)⟩ 1 := by
    have h := Work.Layout.ev_pop' main 1 rZX g X
    rw [hheadX] at h
    exact h
  set g₂ : Reg → Glyph := Function.update g rZX Glyph.cons with hg₂
  set X₂ : Stk → List Glyph := Function.update X 1 ((X 1).tail) with hX₂
  have hX₂1 : X₂ 1 = (Val.int (t:ℤ)).enc ++ (encLN rem ++ zM :: S1) := by
    simp only [hX₂, Function.update_self]; exact htailX
  have hX₂0 : X₂ 0 = W := by
    simp only [hX₂, Function.update_of_ne (by decide : (0:Stk) ≠ 1)]; exact hX0
  have hvsz : vsz (Val.int (t:ℤ)) = t.size + 2 := by
    rw [Work.ConvR.vsz_int, ztp_isz_natCast]
  obtain ⟨s₃, n₃, h3, hn₃, h3a, h3b, h3c, h3d, h3f⟩ :=
    ztp_mvVal_ev (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g₂) (X := X₂) (v := .int (t:ℤ)) (A := encLN rem ++ zM :: S1) (B := W)
      (C := X₂ 2) (D := X₂ 3) hX₂1 hX₂0 rfl rfl
  have hn₃' : n₃ ≤ 16 * (t.size + 3) := by rw [hvsz] at hn₃; omega
  have h3c' : s₃.stk 2 = X 2 := by
    rw [h3c]; simp only [hX₂, Function.update_of_ne (by decide : (2:Stk) ≠ 1)]
  have h3d' : s₃.stk 3 = X 3 := by
    rw [h3d]; simp only [hX₂, Function.update_of_ne (by decide : (3:Stk) ≠ 1)]
  set B : List Glyph := (Computability.encodeNat t).map Glyph.bit with hB
  have hent : (Val.int (t:ℤ)).enc = Glyph.pos :: (B ++ [Glyph.iend]) := by
    rw [Work.IntLib.enc_int, Int.natAbs_natCast]
    simp only [hB]
    rw [if_neg (by simp : ¬ ((t : ℤ) < 0))]
  have hBne : B ≠ [] := by
    intro h
    have h1 : (Computability.encodeNat t).map Glyph.bit = [] := by rw [← hB]; exact h
    rw [List.map_eq_nil_iff] at h1
    exact absurd ((Work.IntLib.encodeNat_eq_nil_iff t).mp h1) (by omega)
  have hbhead := ztp_headD_append B W hBne
  have hbtail := ztp_tail_append B W hBne
  have h3b' : s₃.stk 0 = Glyph.pos :: (B ++ (Glyph.iend :: W)) := by
    rw [h3b, hent]; simp only [List.cons_append, List.append_assoc, List.nil_append]
  have h4 : Ev main (.pop 0 rZA) s₃
      ⟨Function.update s₃.reg rZA Glyph.pos, Function.update s₃.stk 0 (B ++ (Glyph.iend :: W))⟩ 1 := by
    have h := Work.Layout.ev_pop' main 0 rZA s₃.reg s₃.stk
    rw [h3b'] at h
    simpa only [List.headD_cons, List.tail_cons] using h
  set g₄ : Reg → Glyph := Function.update s₃.reg rZA Glyph.pos with hg₄
  set X₄ : Stk → List Glyph := Function.update s₃.stk 0 (B ++ (Glyph.iend :: W)) with hX₄
  have hX₄0 : X₄ 0 = B ++ (Glyph.iend :: W) := by simp [hX₄]
  have h5 : Ev main (.pop 0 rZB) ⟨g₄, X₄⟩
      ⟨Function.update g₄ rZB (B.headD Glyph.eos),
        Function.update X₄ 0 (B.tail ++ (Glyph.iend :: W))⟩ 1 := by
    have h := Work.Layout.ev_pop' main 0 rZB g₄ X₄
    rw [hX₄0, hbhead, hbtail] at h
    exact h
  set g₅ : Reg → Glyph := Function.update g₄ rZB (B.headD Glyph.eos) with hg₅
  set X₅ : Stk → List Glyph := Function.update X₄ 0 (B.tail ++ (Glyph.iend :: W)) with hX₅
  have hX₅0 : X₅ 0 = B.tail ++ (Glyph.iend :: W) := by simp [hX₅]
  have h6 : Ev main (.peek 0 rZC) ⟨g₅, X₅⟩
      ⟨Function.update g₅ rZC ((B.tail ++ (Glyph.iend :: W)).headD Glyph.eos), X₅⟩ 1 := by
    have h := Work.Layout.ev_peek' main 0 rZC g₅ X₅
    rw [hX₅0] at h
    exact h
  set g₆ : Reg → Glyph := Function.update g₅ rZC ((B.tail ++ (Glyph.iend :: W)).headD Glyph.eos)
    with hg₆
  have hrgA : g₆ rZA = Glyph.pos := by
    rw [hg₆, hg₅, hg₄, Function.update_of_ne (by decide : rZA ≠ rZC),
      Function.update_of_ne (by decide : rZA ≠ rZB), Function.update_self]
  have hrgB : g₆ rZB = B.headD Glyph.eos := by
    rw [hg₆, hg₅, Function.update_of_ne (by decide : rZB ≠ rZC), Function.update_self]
  have hrgC : g₆ rZC = (B.tail ++ (Glyph.iend :: W)).headD Glyph.eos := by
    rw [hg₆, Function.update_self]
  have hEv : Ev main (Work.Layout.seqs [.pop 1 rZX, Work.Layout.mvVal 1 0 2 3, .pop 0 rZA,
      .pop 0 rZB, .peek 0 rZC]) ⟨g, X⟩ ⟨g₆, X₅⟩ (1 + (n₃ + (1 + (1 + 1)))) :=
    Ev.seq h2 (Ev.seq h3 (Ev.seq h4 (Ev.seq h5 h6)))
  have hstk1 : (⟨g₆, X₅⟩ : State).stk 1 = encLN rem ++ zM :: S1 := by
    have h1 : X₅ 1 = X₄ 1 := by simp only [hX₅, Function.update_of_ne (by decide : (1:Stk) ≠ 0)]
    have h2' : X₄ 1 = s₃.stk 1 := by
      simp only [hX₄, Function.update_of_ne (by decide : (1:Stk) ≠ 0)]
    simp only [Work.Layout.stk_mk, h1, h2']; exact h3a
  have hfr : ∀ k, k ≠ 0 → k ≠ 1 → (⟨g₆, X₅⟩ : State).stk k = X k := by
    intro k hk0 hk1
    have hst : (⟨g₆, X₅⟩ : State).stk k = s₃.stk k := by
      have h1 : X₅ k = X₄ k := by simp only [hX₅, Function.update_of_ne hk0]
      have h2' : X₄ k = s₃.stk k := by simp only [hX₄, Function.update_of_ne hk0]
      simp only [Work.Layout.stk_mk, h1, h2']
    rw [hst]
    by_cases hk2 : k = 2
    · rw [hk2, h3c']
    · by_cases hk3 : k = 3
      · rw [hk3, h3d']
      · rw [h3f k hk1 hk0 hk2 hk3]
        simp only [hX₂, Function.update_of_ne hk1]
  exact ⟨⟨g₆, X₅⟩, 1 + (n₃ + (1 + (1 + 1))), B, hB, hEv, by omega, hrgA, hrgB, hrgC, hX₅0,
    hstk1, hfr⟩

/-- One full iteration of the walk (the `cons` case): body of `zBody`. -/
theorem ztpStepCons (main : Cmd) (mulProg : Cmd) (Km Bz : ℕ)
    (hmul : WordR main mulProg (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest)
        (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a * b) :: rest)
        (binCost (fun a b => Km * isz a * isz b)))
    {t : ℕ} (ht : 0 < t) {rem : List ℕ} {P : ℕ} {V : List Val} {R S1 : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hg : g rZL = zCont)
    (hX0 : X 0 = encs (.int (P:ℤ) :: V) ++ R)
    (hX1 : X 1 = encLN (t :: rem) ++ zM :: S1)
    (hsz : P.size + zBsz (t :: rem) ≤ Bz) :
    ∃ s' C, Ev main (zBody mulProg) ⟨g, X⟩ s' C ∧
      C ≤ 30 + 16 * (t.size + 2) + (if 2 ≤ t then Km * (t.size + 2) * (Bz + 2) else 0) ∧
      s'.reg rZL = zCont ∧
      s'.stk 0 = encs (.int ((P * t : ℕ) : ℤ) :: V) ++ R ∧
      s'.stk 1 = encLN rem ++ zM :: S1 ∧
      (∀ k, k ≠ 0 → k ≠ 1 → s'.stk k = X k) := by
  have hheadX : (X 1).headD Glyph.eos = Glyph.cons := by
    rw [hX1, encLN_cons]; simp only [List.cons_append, List.append_assoc, List.headD_cons]
  have hpeek : Ev main (.peek 1 rZH) ⟨g, X⟩ ⟨Function.update g rZH Glyph.cons, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main 1 rZH g X
    rw [hheadX] at h
    exact h
  set g₁ : Reg → Glyph := Function.update g rZH Glyph.cons with hg₁
  obtain ⟨s₆, C₆, B, hB, hpre, hC₆, hZA, hZB, hZC, hX₀, hX₁, hfr₆⟩ :=
    ztpPre (main := main) (t := t) ht (rem := rem) (P := P) (V := V) (R := R) (S1 := S1)
      (g := g₁) (X := X) (W := encs (.int (P:ℤ) :: V) ++ R) rfl hX0 hX1
  have hsz' : P.size ≤ Bz := by
    have h0 : 0 ≤ zBsz (t :: rem) := Nat.zero_le _
    omega
  obtain ⟨s₇, C₇, htail, hC₇, hr₇, hstk₇, hfr₇⟩ :=
    ztpStepTail (main := main) (mulProg := mulProg) (Km := Km) (Bz := Bz) hmul ht
      (hB := hB) (hW := rfl) (hZA := hZA) (hZB := hZB) (hZC := hZC) (hX0 := hX₀) hsz'
  have hnil : (Function.update g rZH Glyph.cons) rZH ≠ Glyph.nil := by
    simp only [Function.update_self]; decide
  have hcons : Ev main (zCons mulProg) ⟨g₁, X⟩ s₇ (C₆ + C₇) := Ev.seq hpre htail
  have hite : Ev main (.ite rZH Glyph.nil (Work.Layout.seqs [.pop 1 rZX, .set rZL zStop])
      (zCons mulProg)) ⟨g₁, X⟩ s₇ (C₆ + C₇ + 1) := Ev.iteF hnil hcons
  have hbody : Ev main (zBody mulProg) ⟨g, X⟩ s₇ (1 + (C₆ + C₇ + 1)) :=
    Ev.seq hpeek hite
  have hstk₁' : s₇.stk 1 = encLN rem ++ zM :: S1 := by
    rw [hfr₇ 1 (by decide), hX₁]
  refine ⟨s₇, 1 + (C₆ + C₇ + 1), hbody, ?_, hr₇, hstk₇, hstk₁', ?_⟩
  · omega
  · intro k hk0 hk1
    rw [hfr₇ k hk0, hfr₆ k hk0 hk1]

/-- decomposition of `zWalkRunCost` along a `cons`. -/
theorem zWalkRunCost_cons (Km Bz : ℕ) (t : ℕ) (rem : List ℕ) :
    zWalkRunCost Km Bz (t :: rem) =
      31 + 16 * (t.size + 2) + (if 2 ≤ t then Km * (t.size + 2) * (Bz + 2) else 0)
        + zWalkRunCost Km Bz rem := by
  simp only [zWalkRunCost, List.map_cons, List.sum_cons]
  omega

/-- bound on the total walk cost. -/
theorem ztpWalkCostBound (Km Bz : ℕ) (ts : List ℕ) :
    zWalkRunCost Km Bz ts ≤ 5 + ts.length * 31 + 16 * zSAll ts + Km * zSisz ts * (Bz + 2) := by
  induction ts with
  | nil => simp [zWalkRunCost, zSAll, zSisz]
  | cons t ts ih =>
    have hdec := zWalkRunCost_cons Km Bz t ts
    have hA : (if 2 ≤ t then Km * (t.size + 2) * (Bz + 2) else 0)
        = Km * (if 2 ≤ t then t.size + 2 else 0) * (Bz + 2) := by
      by_cases h : 2 ≤ t <;> simp [h]
    have hsplit : Km * ((if 2 ≤ t then t.size + 2 else 0) + zSisz ts) * (Bz + 2)
        = Km * (if 2 ≤ t then t.size + 2 else 0) * (Bz + 2) + Km * zSisz ts * (Bz + 2) := by
      ring
    have h31 : (ts.length + 1) * 31 = ts.length * 31 + 31 := by ring
    have h16 : 16 * ((t.size + 2) + zSAll ts) = 16 * (t.size + 2) + 16 * zSAll ts :=
      Nat.mul_add _ _ _
    rw [hdec, List.length_cons, zSAll_cons, zSisz_cons, h31, h16, hsplit, ← hA]
    omega

/-- the walk loop, from an invariant state. -/
theorem zWalkRun (main : Cmd) (mulProg : Cmd) (Km Bz : ℕ)
    (hmul : WordR main mulProg (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest)
        (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a * b) :: rest)
        (binCost (fun a b => Km * isz a * isz b))) :
    ∀ (rem : List ℕ) (P : ℕ) (V : List Val) (R S1 : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      (∀ t ∈ rem, 0 < t) → g rZL = zCont → P.size + zBsz rem ≤ Bz →
      X 0 = encs (.int (P:ℤ) :: V) ++ R → X 1 = encLN rem ++ zM :: S1 →
      ∃ s' C, loopRuns main rZL zCont (zBody mulProg) (rem.length + 1) ⟨g, X⟩ s' C ∧
        C ≤ zWalkRunCost Km Bz rem ∧
        s'.reg rZL = zStop ∧
        s'.stk 0 = encs (.int ((P * rem.prod : ℕ) : ℤ) :: V) ++ R ∧
        s'.stk 1 = zM :: S1 ∧
        (∀ k, k ≠ 0 → k ≠ 1 → s'.stk k = X k) := by
  intro rem
  induction rem with
  | nil =>
    intro P V R S1 g X hpos hg hsz hX0 hX1
    have hX1' : X 1 = Glyph.nil :: zM :: S1 := by rw [hX1]; rfl
    have hhead : (X 1).headD Glyph.eos = Glyph.nil := by rw [hX1']; rfl
    have htail : (X 1).tail = zM :: S1 := by rw [hX1']; rfl
    have hpeek : Ev main (.peek 1 rZH) ⟨g, X⟩ ⟨Function.update g rZH Glyph.nil, X⟩ 1 := by
      have h := Work.Layout.ev_peek' main 1 rZH g X
      rw [hhead] at h
      exact h
    have hpop : Ev main (.pop 1 rZX) ⟨Function.update g rZH Glyph.nil, X⟩
        ⟨Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil,
          Function.update X 1 (zM :: S1)⟩ 1 := by
      have h := Work.Layout.ev_pop' main 1 rZX (Function.update g rZH Glyph.nil) X
      rw [hhead, htail] at h
      exact h
    have hset : Ev main (.set rZL zStop)
        ⟨Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil,
          Function.update X 1 (zM :: S1)⟩
        ⟨Function.update (Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil) rZL zStop,
          Function.update X 1 (zM :: S1)⟩ 1 :=
      Work.Layout.ev_set' main rZL zStop _ _
    have hnil : (Function.update g rZH Glyph.nil) rZH = Glyph.nil := by
      simp only [Function.update_self]
    have hbody : Ev main (zBody mulProg) ⟨g, X⟩
        ⟨Function.update (Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil) rZL zStop,
          Function.update X 1 (zM :: S1)⟩ (1 + (1 + (1 + 1))) :=
      Ev.seq hpeek (Ev.iteT hnil (Ev.seq hpop hset))
    have hrl : (Function.update (Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil)
        rZL zStop) rZL = zStop := by
      simp only [Function.update_apply]
      simp
    refine ⟨⟨Function.update (Function.update (Function.update g rZH Glyph.nil) rZX Glyph.nil)
        rZL zStop, Function.update X 1 (zM :: S1)⟩, 1 + (1 + (1 + 1)) + 1, ?_, ?_, hrl, ?_, ?_, ?_⟩
    · exact loopRuns.one hg hbody
    · simp [zWalkRunCost]
    · simp only [Work.Layout.stk_mk, Function.update_of_ne (by decide : (0:Stk) ≠ 1),
        List.prod_nil, Nat.mul_one, hX0]
    · simp only [Work.Layout.stk_mk, Function.update_self]
    · intro k hk0 hk1
      simp only [Work.Layout.stk_mk, Function.update_of_ne hk1]
  | cons t rem ih =>
    intro P V R S1 g X hpos hg hsz hX0 hX1
    have ht : 0 < t := hpos t (by simp)
    have hpos' : ∀ s ∈ rem, 0 < s := fun s hs => hpos s (by simp [hs])
    obtain ⟨s₁, C₁, hev₁, hC₁, hr₁, hstk₁, hstk₁', hfr₁⟩ :=
      ztpStepCons (main := main) (mulProg := mulProg) (Km := Km) (Bz := Bz) hmul ht hg hX0 hX1 hsz
    have hsz' : (P * t).size + zBsz rem ≤ Bz := by
      rw [zBsz_cons] at hsz
      by_cases h2 : 2 ≤ t
      · rw [if_pos h2] at hsz
        have h := ztpSizeMul P t
        omega
      · rw [if_neg h2, Nat.zero_add] at hsz
        have ht1 : t = 1 := by omega
        rw [ht1, Nat.mul_one]
        exact hsz
    obtain ⟨s₂, C₂, hrun₂, hC₂, hr₂, hstk₂, hstk₂', hfr₂⟩ :=
      ih (P * t) V R S1 s₁.reg s₁.stk hpos' hr₁ hsz' hstk₁ hstk₁'
    have hstk₂'' : s₂.stk 0 = encs (.int ((P * (t :: rem).prod : ℕ) : ℤ) :: V) ++ R := by
      rw [List.prod_cons, ← Nat.mul_assoc]
      exact hstk₂
    refine ⟨s₂, (C₁ + 1) + C₂, ?_, ?_, hr₂, hstk₂'', hstk₂', ?_⟩
    · have h1 := loopRuns.one hg hev₁
      have h2 := loopRuns.concat (rem.length + 1) h1 hrun₂
      have h3 : (t :: rem).length + 1 = 1 + (rem.length + 1) := by
        simp [List.length_cons, Nat.add_comm]
      rw [h3]
      exact h2
    · rw [zWalkRunCost_cons]
      omega
    · intro k hk0 hk1
      rw [hfr₂ k hk0 hk1, hfr₁ k hk0 hk1]

/-- The arithmetic endgame of `ztabProd`. -/
theorem ztpEndArith (p : ℕ) (ts : List ℕ) (Km Kpv Kdup : ℕ)
    (h100 : 100 ≤ p) (hpos : ∀ t ∈ ts, 0 < t) :
    Kdup * (vsz (intList ts) + 1) + 16 * (vsz (intList ts) + 1) + 4 * Kpv + 10 +
        ts.length * 31 + 16 * zSAll ts + Km * zSisz ts * (zBsz ts + 3) ≤
      (Kdup + 4 * Kpv + Km + 100) * (vsz (intList ts) + ts.prod * p ^ 2 + 1) := by
  set V := vsz (intList ts) with hV
  set Ws := ts.prod * p ^ 2 with hWs
  have hVeq : V = zSAll ts + ts.length + 1 := by rw [hV, vsz_intList]
  have hSle : zSAll ts ≤ V := by omega
  have hnle : ts.length ≤ V := by omega
  have hge1 : 1 ≤ V + Ws + 1 := by omega
  have hnl : zSisz ts * (zBsz ts + 3) ≤ V + Ws + 1 := by
    have h1 : zSisz ts ≤ 4 * zB ts := ztpSisz ts
    have h2 : zBsz ts + 3 ≤ 2 * zB ts + 3 := by
      have h := ztpBsz ts
      have h' : zBsz ts ≤ 2 * zB ts := h
      omega
    have h3 : (4 * zB ts) * (2 * zB ts + 3) = 8 * (zB ts) ^ 2 + 12 * (zB ts) := by ring
    have h4 : 8 * (zB ts) ^ 2 + 12 * (zB ts) ≤ 2 ^ (zB ts) * 100 ^ 2 := ztpPowB (zB ts)
    have h5 : 2 ^ (zB ts) * 100 ^ 2 ≤ ts.prod * p ^ 2 :=
      Nat.mul_le_mul (ztpProdGt ts hpos) (Nat.pow_le_pow_left h100 2)
    calc zSisz ts * (zBsz ts + 3)
        ≤ (4 * zB ts) * (2 * zB ts + 3) := Nat.mul_le_mul h1 h2
      _ = 8 * (zB ts) ^ 2 + 12 * (zB ts) := h3
      _ ≤ 2 ^ (zB ts) * 100 ^ 2 := h4
      _ ≤ ts.prod * p ^ 2 := h5
      _ ≤ V + Ws + 1 := by rw [hWs]; omega
  have h1 : Kdup * (V + 1) ≤ Kdup * (V + Ws + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : 16 * (V + 1) ≤ 100 * (V + Ws + 1) := by
    have h1 : 16 * (V + 1) ≤ 16 * (V + Ws + 1) :=
      Nat.mul_le_mul_left 16 (show V + 1 ≤ V + Ws + 1 by omega)
    have h2' : 16 * (V + Ws + 1) ≤ 100 * (V + Ws + 1) :=
      Nat.mul_le_mul_right _ (by omega : 16 ≤ 100)
    exact le_trans h1 h2'
  have h3 : 4 * Kpv ≤ 4 * Kpv * (V + Ws + 1) := by
    simpa using Nat.mul_le_mul_left (4 * Kpv) hge1
  have h4 : 10 ≤ 100 * (V + Ws + 1) := by
    have h1 : 10 ≤ 10 * (V + Ws + 1) := by simpa using Nat.mul_le_mul_left 10 hge1
    have h2' : 10 * (V + Ws + 1) ≤ 100 * (V + Ws + 1) :=
      Nat.mul_le_mul_right _ (by omega : 10 ≤ 100)
    exact le_trans h1 h2'
  have h5 : ts.length * 31 ≤ 100 * (V + Ws + 1) := by
    have h1 : ts.length * 31 ≤ (V + Ws + 1) * 31 :=
      Nat.mul_le_mul_right _ (show ts.length ≤ V + Ws + 1 by omega)
    have h2' : (V + Ws + 1) * 31 ≤ (V + Ws + 1) * 100 :=
      Nat.mul_le_mul_left _ (by omega : 31 ≤ 100)
    have h3 : (V + Ws + 1) * 100 = 100 * (V + Ws + 1) := Nat.mul_comm _ _
    rw [h3] at h2'
    exact le_trans h1 h2'
  have h6 : 16 * zSAll ts ≤ 100 * (V + Ws + 1) := by
    have h1 : 16 * zSAll ts ≤ 16 * (V + Ws + 1) :=
      Nat.mul_le_mul_left 16 (show zSAll ts ≤ V + Ws + 1 by omega)
    have h2' : 16 * (V + Ws + 1) ≤ 100 * (V + Ws + 1) :=
      Nat.mul_le_mul_right _ (by omega : 16 ≤ 100)
    exact le_trans h1 h2'
  have h7 : Km * zSisz ts * (zBsz ts + 3) ≤ Km * (V + Ws + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left Km hnl
  have hexp : (Kdup + 4 * Kpv + Km + 100) * (V + Ws + 1)
      = Kdup * (V + Ws + 1) + 4 * Kpv * (V + Ws + 1) + Km * (V + Ws + 1)
        + 100 * (V + Ws + 1) := by ring
  rw [hexp]
  omega

/-- **The list-product word with the "skip the 1's" optimisation.**

From the encoded list `intList ts` of naturals on top of the value stack, compute `T = ts.prod` and
push it (`int T :: intList ts :: rest`, the list is *preserved*).

The cost bound `K * (vsz (intList ts) + ts.prod * p ^ 2 + 1)` is the point of the lemma: it is
*linear* in the encoding size `vsz (intList ts)` plus `T * p^2`, and in particular it must hold for
`ts = [2^(p-2)] ++ [1]*N` with `N` arbitrary — where `T` stays small while the list is huge.  Hence
the implementation MUST walk the encoded list glyph by glyph and must NOT spend `Ω(p)` per element:
* a `KernelLib.foldList` / `mapList`-based product is over budget (their cost formula charges the
  *uniform* bound `K*(L+1)` on every element, `L = max vsz ≈ p`);
* `Work.ConvR.listProdB` (a proven word, cost `K*(vsz+1)^2`) is over budget (quadratic in `vsz`);
* the only affordable walk checks each element for the value `1` (cheap: `vsz (.int 1) = 3`, so the
  first three glyphs, or `IntLib.eq`, cost `O(vsz (.int t)) = O(isz t)`) and then skips the
  multiplication for `t = 1`.

Sketch of an implementation: (i) drain the encoded list from stack 0 onto a scratch stack so that
the elements are exposed one at a time on top (each glyph popped/pushed once, cost `O(vsz)` per
element); (ii) keep the running product `P` on stack 0; per element: test `t = 1` (cheap), if yes
drop the element, else call `IntLib.mulS` on `(t, P)`; (iii) push `int 1` as the initial
accumulator.  (The list must be restored at the end, e.g. by draining a `dup` of it.)

Cost proof: let `len2 = #{i | t_i ≥ 2}` and `B = Σ_{t_i ≥ 2} (t_i.size - 1) ≥ len2`.  Every partial
product divides `T`, and `T = Π_{t_i ≥ 2} t_i ≥ 2^B` while `T.size ≤ B + len2 ≤ 2B`, so
`isz P ≤ isz T ≤ 2B + 2`, `Σ_{t_i ≥ 2} isz t_i ≤ Σ (B_i + 3) ≤ 4B`, hence the multiplication cost is
at most `4B*(2B+2) ≤ 16 B^2`, and `16 B^2 ≤ 2^B * p^2 ≤ ts.prod * p^2` (as `p ≥ 100`). -/
theorem ztabProd : HvdH.KernelLib → HvdH.IntLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (ts : List ℕ) (rest : List HvdH.Val),
      100 ≤ p → (∀ t ∈ ts, 0 < t) → (∀ t ∈ ts, t < 2 ^ p) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.intList ts :: rest)
        (fun _ out => out = HvdH.Val.int ((ts.prod : ℤ)) :: HvdH.intList ts :: rest)
        (fun _ => K * (HvdH.vsz (HvdH.intList ts) + ts.prod * p ^ 2 + 1)) := by
  intro hk hi
  obtain ⟨dupProg, Kdup, hdup⟩ := hk.dup
  obtain ⟨pvProg, Kpv, hpv⟩ := hk.pushVal
  obtain ⟨mulProg, Km, hmulRaw⟩ := hi.mulS
  have hmul : ∀ main : Cmd, WordR main mulProg
      (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (a * b) :: rest)
      (binCost (fun a b => Km * isz a * isz b)) := by
    intro main
    have h := hmulRaw main
    unfold HvdH.BinOp at h
    simpa using h
  refine ⟨zProg dupProg (pvProg (.int 1)) mulProg, Kdup + 4 * Kpv + Km + 100, ?_⟩
  intro main p ts rest h100 hpos hlt vs hvs s R hR
  subst hvs
  have hsz1 : vsz (.int (1:ℤ)) = 3 := by decide
  -- Phase 1: duplicate the list
  obtain ⟨out₁, s₁, n₁, hpost₁, hev₁, hn₁, hstk₁, hoth₁⟩ :=
    hdup main (intList ts :: rest) (by simp) s R hR
  obtain ⟨v, rest₁, hvs₁, hout₁⟩ := hpost₁
  obtain ⟨hv, hr₁⟩ := List.cons.inj hvs₁
  subst hv
  subst hr₁
  have hn₁' : n₁ ≤ Kdup * (vsz (intList ts) + 1) := by
    simpa [List.headD_cons] using hn₁
  have hstk₁' : s₁.stk 0 = encs (intList ts :: intList ts :: rest) ++ R := by
    rw [hstk₁, hout₁]
  -- Phase 2: marker on stack 1
  have h2 : Ev main (.set rZX zM) ⟨s₁.reg, s₁.stk⟩
      ⟨Function.update s₁.reg rZX zM, s₁.stk⟩ 1 :=
    Work.Layout.ev_set' main rZX zM s₁.reg s₁.stk
  set g₂ : Reg → Glyph := Function.update s₁.reg rZX zM with hg₂
  have h3 : Ev main (.push 1 rZX) ⟨g₂, s₁.stk⟩
      ⟨g₂, Function.update s₁.stk 1 (zM :: s₁.stk 1)⟩ 1 :=
    Work.Layout.ev_push' main 1 rZX g₂ s₁.stk
  set X₂ : Stk → List Glyph := Function.update s₁.stk 1 (zM :: s₁.stk 1) with hX₂
  have hX₂0 : X₂ 0 = (intList ts).enc ++ ((intList ts).enc ++ (encs rest ++ R)) := by
    have h0 : X₂ 0 = s₁.stk 0 := by
      simp only [hX₂, Function.update_of_ne (by decide : (0:Stk) ≠ 1)]
    rw [h0, hstk₁', Work.Kernel.encs_cons, Work.Kernel.encs_cons, List.append_assoc,
      List.append_assoc]
  have hX₂1 : X₂ 1 = zM :: s₁.stk 1 := by simp only [hX₂, Function.update_self]
  obtain ⟨s₃, n₃, h3v, hn₃, hstk₃, hstk₃₁, hstk₃₂, hstk₃₃, hfr₃⟩ :=
    ztp_mvVal_ev (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g₂) (X := X₂) (v := intList ts) (A := (intList ts).enc ++ (encs rest ++ R))
      (B := zM :: s₁.stk 1) (C := X₂ 2) (D := X₂ 3) hX₂0 hX₂1 rfl rfl
  have hstk₃' : s₃.stk 0 = encs (intList ts :: rest) ++ R := by
    rw [hstk₃, Work.Kernel.encs_cons, List.append_assoc]
  have hstk₃₁' : s₃.stk 1 = encLN ts ++ zM :: s₁.stk 1 := by
    rw [hstk₃₁, ← encLN_eq]
  have hn₃' : n₃ ≤ 16 * (vsz (intList ts) + 1) := hn₃
  -- Phase 4: push the initial accumulator `int 1`
  obtain ⟨out₄, s₄, n₄, hpost₄, hev₄, hn₄, hstk₄, hoth₄⟩ :=
    hpv main (.int 1) (intList ts :: rest) (by trivial) s₃ R hstk₃'
  have hn₄' : n₄ ≤ Kpv * 4 := by rw [hsz1] at hn₄; omega
  have hstk₄1 : s₄.stk 1 = encLN ts ++ zM :: s₁.stk 1 := by
    rw [hoth₄ 1 (by decide), hstk₃₁']
  have hstk₄0 : s₄.stk 0 = encs (.int (1:ℤ) :: intList ts :: rest) ++ R := by
    rw [hstk₄, hpost₄]
  -- Phase 5: set the loop register
  have h5 : Ev main (.set rZL zCont) ⟨s₄.reg, s₄.stk⟩
      ⟨Function.update s₄.reg rZL zCont, s₄.stk⟩ 1 :=
    Work.Layout.ev_set' main rZL zCont s₄.reg s₄.stk
  set g₅ : Reg → Glyph := Function.update s₄.reg rZL zCont with hg₅
  have hg₅r : g₅ rZL = zCont := by simp only [hg₅, Function.update_self]
  -- Phase 6: the walk
  obtain ⟨s₆, C₆, hrun₆, hC₆, hr₆, hstk₆, hstk₆₁, hfr₆⟩ :=
    zWalkRun (main := main) (mulProg := mulProg) (Km := Km) (Bz := zBsz ts + 1) (hmul main)
      ts 1 (intList ts :: rest) R (s₁.stk 1) g₅ s₄.stk hpos hg₅r
      (by rw [Nat.size_one]; omega) hstk₄0 hstk₄1
  obtain ⟨n₆, hev₆Eval, hn₆⟩ := loopRuns.eval' hrun₆ (by rw [hr₆]; decide)
  have hev₆ : Ev main (.loop rZL zCont (zBody mulProg)) ⟨g₅, s₄.stk⟩ s₆ (C₆ + 1) :=
    ⟨n₆, hev₆Eval, hn₆⟩
  -- Phase 7: remove the marker
  have h7 : Ev main (.pop 1 rZX) s₆
      ⟨Function.update s₆.reg rZX zM, Function.update s₆.stk 1 (s₆.stk 1).tail⟩ 1 := by
    have h := Work.Layout.ev_pop' main 1 rZX s₆.reg s₆.stk
    rw [show (s₆.stk 1).headD Glyph.eos = zM from by rw [hstk₆₁]; rfl] at h
    exact h
  set sf : State := ⟨Function.update s₆.reg rZX zM, Function.update s₆.stk 1 (s₆.stk 1).tail⟩
    with hsf
  have hsf1 : sf.stk 1 = s₁.stk 1 := by
    simp only [hsf, Work.Layout.stk_mk, Function.update_self, hstk₆₁, List.tail_cons]
  -- assemble
  have hprog : Ev main (zProg dupProg (pvProg (.int 1)) mulProg) ⟨s.reg, s.stk⟩ sf
      (n₁ + (1 + (1 + (n₃ + (n₄ + (1 + ((C₆ + 1) + 1))))))) := by
    refine Ev.seq ⟨n₁, hev₁, le_rfl⟩ ?_
    refine Ev.seq h2 ?_
    refine Ev.seq h3 ?_
    refine Ev.seq h3v ?_
    refine Ev.seq ⟨n₄, hev₄, le_rfl⟩ ?_
    refine Ev.seq h5 ?_
    exact Ev.seq hev₆ h7
  obtain ⟨nout, hevout, hnout⟩ := hprog
  refine ⟨.int ((ts.prod : ℤ)) :: intList ts :: rest, sf, nout, rfl, hevout, ?_, ?_, ?_⟩
  · -- the cost bound
    have hwalk := ztpWalkCostBound Km (zBsz ts + 1) ts
    rw [show (zBsz ts + 1) + 2 = zBsz ts + 3 from by omega] at hwalk
    have hcost : nout ≤ Kdup * (vsz (intList ts) + 1) + 16 * (vsz (intList ts) + 1) + 4 * Kpv + 10 +
        ts.length * 31 + 16 * zSAll ts + Km * zSisz ts * (zBsz ts + 3) := by
      omega
    exact le_trans hcost (ztpEndArith p ts Km Kpv Kdup h100 hpos)
  · -- stack 0
    have hs6 : s₆.stk 0 = encs (.int (1 * ts.prod : ℕ) :: intList ts :: rest) ++ R := hstk₆
    rw [hsf, Work.Layout.stk_mk, Function.update_of_ne (by decide : (0:Stk) ≠ 1)]
    simpa [Nat.one_mul] using hs6
  · -- the frame
    intro k hk
    by_cases hk1 : k = 1
    · rw [hk1, hsf1]
      exact hoth₁ 1 (by decide)
    · have hk0 : k ≠ 0 := hk
      have hstep : sf.stk k = s₄.stk k := by
        rw [hsf, Work.Layout.stk_mk, Function.update_of_ne hk1]
        exact hfr₆ k hk0 hk1
      rw [hstep]
      by_cases hk2 : k = 2
      · rw [hk2, hoth₄ 2 (by decide), hstk₃₂]
        simp only [hX₂, Function.update_of_ne (by decide : (2:Stk) ≠ 1)]
        exact hoth₁ 2 (by decide)
      · by_cases hk3 : k = 3
        · rw [hk3, hoth₄ 3 (by decide), hstk₃₃]
          simp only [hX₂, Function.update_of_ne (by decide : (3:Stk) ≠ 1)]
          exact hoth₁ 3 (by decide)
        · rw [hoth₄ k hk0, hfr₃ k hk0 hk1 hk2 hk3,
            hX₂, Function.update_of_ne hk1]
          exact hoth₁ k hk0


end Work.Transform
