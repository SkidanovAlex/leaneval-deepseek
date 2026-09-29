import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbWords
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Resample.pbKit2

/-!
# Strengthened mover words for the `Ã` program

The mover words of `Work.Resample.pbWords` state their `WordM` postcondition only for the stack they
touch (`b src = []` etc.), which is not enough to keep track of the stacks 2–7 of the `Ã` program.
This file re-states the same programs with the *full* description `b = Function.update …` of the
resulting value lists; the proofs are the proofs of `pbWords` with the post strengthened (the
witnesses for `b` are already literally those terms there).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `pbW1` with the resulting stack description fully specified. -/
theorem paW1 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b = Function.update a src [])
        (fun _ _ => Kc * (vsz v + 1)) := by
  intro src hsrc
  obtain ⟨c, d, hcd, hc0, hcs, hd0, hds⟩ := pbScratch2 src
  refine ⟨Work.Layout.mvVal src 0 c d, 16, ?_⟩
  intro main v rest vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  rw [hvs] at h0
  rw [hvs]
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs rest ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have haX : X src = v.enc ++ Bg src := by
    rw [hkX src hsrc, ha, Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  obtain ⟨s', N, hev, hN, hsA, hsB, hfr⟩ :=
    pbMvValEv (main := main) (a := src) (b := 0) (c := c) (d := d)
      (hab := hsrc) (hac := Ne.symm hcs) (had := Ne.symm hds)
      (hbc := Ne.symm hc0) (hbd := Ne.symm hd0) (hcd := hcd)
      (g := g) (X := X) (v := v) (A := Bg src) (B := encs rest ++ R) haX h0X
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨v :: rest, Function.update a src [], s', n, ⟨rfl, rfl⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [hsB, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      simp only [hsA, Function.update_self, Work.Kernel.encs_nil, List.nil_append]
    · rw [Function.update_of_ne hks, hfr k hks hk0, hkX k hk0]

/-- `pbW2` with the resulting stack description fully specified. -/
theorem paW2 : ∀ (tgt : Stk), tgt ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val) (L : List Val),
      WordM main prog
        (fun vs a => vs = v :: rest ∧ a tgt = L)
        (fun vs a out b => out = rest ∧ b = Function.update a tgt (v :: L))
        (fun _ _ => Kc * (vsz v + 1)) := by
  intro tgt htgt
  obtain ⟨c, d, hcd, hc0, hct, hd0, hdt⟩ := pbScratch2 tgt
  refine ⟨Work.Layout.mvVal 0 tgt c d, 16, ?_⟩
  intro main v rest L vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h00 : X 0 = v.enc ++ (encs rest ++ R) := by
    rw [h0X, hvs, Work.Kernel.encs_cons, List.append_assoc]
  have htgtX : X tgt = encs L ++ Bg tgt := by rw [hkX tgt htgt, ha]
  obtain ⟨s', N, hev, hN, h0', htgt', hfr⟩ :=
    pbMvValEv (main := main) (a := 0) (b := tgt) (c := c) (d := d)
      (hab := Ne.symm htgt) (hac := Ne.symm hc0) (had := Ne.symm hd0)
      (hbc := Ne.symm hct) (hbd := Ne.symm hdt) (hcd := hcd)
      (g := g) (X := X) (v := v) (A := encs rest ++ R) (B := encs L ++ Bg tgt) h00 htgtX
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨rest, Function.update a tgt (v :: L), s', n, ⟨rfl, rfl⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [h0']
  · intro k hk0
    by_cases hkt : k = tgt
    · rw [hkt]
      simp only [htgt', Function.update_self, Work.Kernel.encs_cons, List.append_assoc]
    · rw [Function.update_of_ne hkt, hfr k hk0 hkt, hkX k hk0]

/-- `pbW3` (duplicate the top value) with the resulting stack description fully specified. -/
theorem paW3 : ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (rest : List Val),
      WordM main prog
        (fun vs _ => vs = v :: rest)
        (fun vs a out b => out = v :: v :: rest ∧ b = a)
        (fun _ _ => Kc * (vsz v + 1)) := by
  refine ⟨pbDupProg, 56, ?_⟩
  intro main v rest vs a hpre s R Bg h0 hk
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h00 : X 0 = v.enc ++ (encs rest ++ R) := by
    rw [h0X, hpre, Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₁, N₁, hev₁, hN₁, h0₁, h7₁, hfr₁⟩ :=
    pbMvValEv (main := main) (a := 0) (b := pbElt) (c := pbV1) (d := pbV2)
      (hab := by decide) (hac := by decide) (had := by decide) (hbc := by decide)
      (hbd := by decide) (hcd := by decide)
      (g := g) (X := X) (v := v) (A := encs rest ++ R) (B := X pbElt) h00 rfl
  obtain ⟨s₂, N₂, hev₂, hN₂, h7₂, h0₂, hfr₂⟩ :=
    pbCopyEv (main := main) (a := pbElt) (b := 0) (c := pbC1) (d := pbC2)
      (hab := by decide) (hac := by decide) (had := by decide) (hbc := by decide)
      (hbd := by decide) (hcd := by decide)
      (g := s₁.reg) (X := s₁.stk) (v := v) (A := X pbElt) (B := encs rest ++ R) h7₁ h0₁
  obtain ⟨s₃, N₃, hev₃, hN₃, h7₃, h0₃, hfr₃⟩ :=
    pbMvValEv (main := main) (a := pbElt) (b := 0) (c := pbV1) (d := pbV2)
      (hab := by decide) (hac := by decide) (had := by decide) (hbc := by decide)
      (hbd := by decide) (hcd := by decide)
      (g := s₂.reg) (X := s₂.stk) (v := v) (A := X pbElt) (B := v.enc ++ (encs rest ++ R)) h7₂ h0₂
  obtain ⟨n₁, he₁, hn₁⟩ := hev₁
  obtain ⟨n₂, he₂, hn₂⟩ := hev₂
  obtain ⟨n₃, he₃, hn₃⟩ := hev₃
  have hfin : Eval main pbDupProg ⟨g, X⟩ s₃ (n₁ + (n₂ + n₃)) := by
    unfold pbDupProg
    exact Eval.seq he₁ (Eval.seq he₂ he₃)
  refine ⟨v :: v :: rest, a, s₃, n₁ + (n₂ + n₃), ⟨rfl, rfl⟩, hfin, ?_, ?_, ?_⟩
  · have hlt1 : n₁ ≤ 16 * (vsz v + 1) := le_trans hn₁ hN₁
    have hlt2 : n₂ ≤ 24 * (vsz v + 1) := le_trans hn₂ hN₂
    have hlt3 : n₃ ≤ 16 * (vsz v + 1) := le_trans hn₃ hN₃
    have hv := Work.ConvR.vsz_one_le v
    show n₁ + (n₂ + n₃) ≤ 56 * (vsz v + 1)
    omega
  · rw [h0₃, Work.Kernel.encs_cons, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hk7 : k = pbElt
    · rw [hk7]
      simp only [h7₃, hkX pbElt (by decide)]
    · rw [hfr₃ k hk7 hk0, hfr₂ k hk7 hk0, hfr₁ k hk0 hk7, hkX k hk0]

/-- `pbW4` (copy the top value of a non-zero stack, keeping it) with `b` fully specified. -/
theorem paW4 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b = a)
        (fun _ _ => Kc * (vsz v + 1)) := by
  intro src hsrc
  obtain ⟨c, d, hcd, hc0, hcs, hd0, hds⟩ := pbScratch2 src
  refine ⟨pbCopy src 0 c d, 24, ?_⟩
  intro main v rest vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  rw [hvs] at h0
  rw [hvs]
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs rest ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have haX : X src = v.enc ++ Bg src := by
    rw [hkX src hsrc, ha, Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  obtain ⟨s', N, hev, hN, hsA, h0', hfr⟩ :=
    pbCopyEv (main := main) (a := src) (b := 0) (c := c) (d := d)
      (hab := hsrc) (hac := Ne.symm hcs) (had := Ne.symm hds)
      (hbc := Ne.symm hc0) (hbd := Ne.symm hd0) (hcd := hcd)
      (g := g) (X := X) (v := v) (A := Bg src) (B := encs rest ++ R) haX h0X
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨v :: rest, a, s', n, ⟨rfl, rfl⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [h0', Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      simp only [hsA, ha, Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
    · rw [hfr k hks hk0, hkX k hk0]

/-- `pbW5` (split the head of a list value on a non-zero stack) with `b` fully specified. -/
theorem paW5 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v tl : Val)
    (L : List Val) (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = Val.cons v tl :: L)
        (fun vs a out b => out = v :: vs ∧ b = Function.update a src (tl :: L))
        (fun _ _ => Kc * (vsz (Val.cons v tl) + vsz v + 1)) := by
  intro src hsrc
  obtain ⟨c, d, hcd, hc0, hcs, hd0, hds⟩ := pbScratch2 src
  refine ⟨pbUnconsProg src c d, 12, ?_⟩
  intro main v tl L rest vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  rw [hvs] at h0
  rw [hvs]
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs rest ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have hsrcX : X src = (Val.cons v tl).enc ++ (encs L ++ Bg src) := by
    rw [hkX src hsrc, ha, Work.Kernel.encs_cons, List.append_assoc]
  have htail : (X src).tail = v.enc ++ (encs (tl :: L) ++ Bg src) := by
    have h1 : X src = Glyph.cons :: ((v.enc ++ tl.enc) ++ (encs L ++ Bg src)) := by
      rw [hsrcX]; rfl
    rw [h1, List.tail_cons, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  have hpopEv : Work.Layout.Ev main (.pop src pbRpop) ⟨g, X⟩
      ⟨Function.update g pbRpop ((X src).headD .eos), Function.update X src (X src).tail⟩ 1 :=
    Work.Layout.ev_pop' main src pbRpop g X
  obtain ⟨s₁, N₁, hev₁, hN₁, hs₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.mvA_ev (main := main) (a := src) (c := c) (d := d) (Ne.symm hcs) (Ne.symm hds) hcd
      v (encs (tl :: L) ++ Bg src)
      (Function.update X src (X src).tail c) (Function.update X src (X src).tail d)
      (Function.update g pbRpop ((X src).headD .eos)) (Function.update X src (X src).tail)
      (by simpa using htail) rfl rfl
  obtain ⟨s₂, N₂, hev₂, hN₂, hc₂, h0₂, hf₂⟩ :=
    Work.Layout.mvB_ev (main := main) (c := c) (b := 0) (Ne.symm hc0)
      (G := v.enc.reverse) (C := Function.update X src (X src).tail c) (B := s₁.stk 0)
      (g := s₁.reg) (X := s₁.stk)
      (Work.Layout.gMark_not_mem_enc_rev v) hc₁ rfl
  obtain ⟨npop, hepop, hnpop⟩ := hpopEv
  obtain ⟨n₁, he₁, hn₁⟩ := hev₁
  obtain ⟨n₂, he₂, hn₂⟩ := hev₂
  have hfin : Eval main (pbUnconsProg src c d) ⟨g, X⟩ s₂ (npop + (n₁ + n₂)) := by
    unfold pbUnconsProg
    exact Eval.seq hepop (Eval.seq he₁ he₂)
  refine ⟨v :: rest, Function.update a src (tl :: L), s₂, npop + (n₁ + n₂), ⟨rfl, rfl⟩, hfin,
    ?_, ?_, ?_⟩
  · have hv := Work.ConvR.vsz_one_le v
    have htl := Work.ConvR.vsz_one_le tl
    have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
    rw [hlen] at hN₂
    have h₂ : n₂ ≤ 4 * vsz v + 7 := by omega
    rw [Work.ConvR.vsz_cons]
    show npop + (n₁ + n₂) ≤ 12 * (vsz v + vsz tl + 1 + vsz v + 1)
    omega
  · rw [h0₂, List.reverse_reverse, hf₁ 0 (Ne.symm hsrc) (Ne.symm hc0) (Ne.symm hd0),
      Function.update_of_ne (Ne.symm hsrc), h0X, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      simp only [hf₂ src (Ne.symm hcs) hsrc, hs₁, Function.update_self]
    · by_cases hkc : k = c
      · rw [hkc]
        simp only [hc₂, Function.update_of_ne hcs, Function.update_of_ne hks,
          hkX c hc0]
      · by_cases hkd : k = d
        · rw [hkd]
          simp only [hf₂ d (Ne.symm hcd) hd0, hd₁,
            Function.update_of_ne hds, Function.update_of_ne hks, hkX d hd0]
        · rw [Function.update_of_ne hks, hf₂ k hkc hk0, hf₁ k hks hkc hkd,
            Function.update_of_ne hks, hkX k hk0]

end Work.Resample
