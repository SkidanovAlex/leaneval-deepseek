import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbKit
import Submission.Work.Resample.pbKit2
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.dupFromEv
import Submission.Work.ConvR.sizes
import Submission.Work.Resample.pbFoldEv
import Submission.Work.Resample.mulNatWord

/-!
# The value-stack words of the resampling area (`Work.Resample.pbWords`)

Six unconditional words on value stacks, built from the marker-based movers of the Layout area
(`Work.Layout.mvVal_ev_full`, `mvA_ev`, `mvB_ev`, `drain2_ev`, through the helpers
`Work.Resample.pbMvValEv` and `Work.Resample.pbCopyEv` of `Submission/Work/Resample/pbKit2.lean`):

1. move the top value of a non-zero stack onto stack 0;
2. move the top value of stack 0 onto a non-zero stack;
3. duplicate the top value of stack 0;
4. copy the top value of a non-zero stack onto stack 0, keeping it there;
5. split a `Val.cons` on a non-zero stack: head onto stack 0, tail stays;
6. multiply the elements of the list `intList l` held on stack 2 into the accumulator on stack 0.

Statement 6 uses the copy word `Work.Resample.pbCopy` and the fold loop `Work.Resample.pbFoldProg`
(both in `Submission/Work/Resample/pbKit.lean`), proved in `Submission/Work/Resample/pbFoldEv.lean`
against a multiplier word (`Submission/Work/Resample/mulNatWord.lean`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- register used by the `pop` of the un-cons word -/
def pbRpop : Reg := 10

/-! ## 1. Move the top value of a non-zero stack onto stack 0 -/


theorem pbW1 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b src = [])
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
  refine ⟨v :: rest, Function.update a src [], s', n, ⟨rfl, by simp⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [hsB, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      simp only [hsA, Function.update_self, Work.Kernel.encs_nil, List.nil_append]
    · rw [Function.update_of_ne hks, hfr k hks hk0, hkX k hk0]

/-! ## 2. Move the top value of stack 0 onto a non-zero stack -/

theorem pbW2 : ∀ (tgt : Stk), tgt ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val) (L : List Val),
      WordM main prog
        (fun vs a => vs = v :: rest ∧ a tgt = L)
        (fun vs a out b => out = rest ∧ b tgt = v :: L)
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
  refine ⟨rest, Function.update a tgt (v :: L), s', n, ⟨rfl, by simp⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [h0']
  · intro k hk0
    by_cases hkt : k = tgt
    · rw [hkt]
      simp only [htgt', Function.update_self, Work.Kernel.encs_cons, List.append_assoc]
    · rw [Function.update_of_ne hkt, hfr k hk0 hkt, hkX k hk0]

/-! ## 3. Duplicate the top value of stack 0 -/

/-- The duplicate word: move the top value of stack 0 to the pile on stack 7, copy it back onto
stack 0 (`pbCopy 7 0`), and move the second copy from stack 7 onto stack 0. -/
def pbDupProg : Cmd :=
  Cmd.seq (Work.Layout.mvVal 0 pbElt pbV1 pbV2)
    (Cmd.seq (pbCopy pbElt 0 pbC1 pbC2) (Work.Layout.mvVal pbElt 0 pbV1 pbV2))

theorem pbW3 : ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (rest : List Val),
      WordM main prog
        (fun vs _ => vs = v :: rest)
        (fun _ _ out _ => out = v :: v :: rest)
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
  refine ⟨v :: v :: rest, a, s₃, n₁ + (n₂ + n₃), rfl, hfin, ?_, ?_, ?_⟩
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

/-! ## 4. Copy the top value of a non-zero stack onto stack 0, keeping it there -/

theorem pbW4 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val)
    (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b src = v :: [])
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
  refine ⟨v :: rest, a, s', n, ⟨rfl, ha⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [h0', Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      simp only [hsA, ha, Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
    · rw [hfr k hks hk0, hkX k hk0]

/-! ## 5. Split a `Val.cons` on a non-zero stack -/

/-- The un-cons word: pop the `cons` glyph, move the exposed head value to stack 0, leave the tail
on the source stack. -/
def pbUnconsProg (src c d : Stk) : Cmd :=
  Cmd.seq (Cmd.pop src pbRpop) (Cmd.seq (Work.Layout.mvA src c d) (Work.Layout.mvB c 0))

theorem pbW5 : ∀ (src : Stk), src ≠ 0 → ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v tl : Val)
    (L : List Val) (rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = Val.cons v tl :: L)
        (fun vs a out b => out = v :: vs ∧ b src = tl :: L)
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
  refine ⟨v :: rest, Function.update a src (tl :: L), s₂, npop + (n₁ + n₂), ⟨rfl, by simp⟩, hfin,
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
        simp only [hc₂, Function.update_of_ne hcs, hkX c hc0]
      · by_cases hkd : k = d
        · rw [hkd]
          simp only [hf₂ d (Ne.symm hcd) hd0, hd₁,
            Function.update_of_ne hds, hkX d hd0]
        · rw [Function.update_of_ne hks, hf₂ k hkc hk0, hf₁ k hks hkc hkd,
            Function.update_of_ne hks, hkX k hk0]

/-! ## 6. Multiply the elements of the list on stack 2 into the accumulator -/

/-- The two spellings of `Σ isz` over a list of naturals differ (`l.map (fun t : ℕ => …)` coerces
each element, `l.map fun t => …` coerces the list); they are equal. -/
theorem pbSumB (l : List ℕ) :
    (l.map (fun t : ℕ => isz (t : ℤ))).sum = (l.map fun t => isz (t : ℤ)).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    rw [show (t :: ts).map (fun t : ℕ => isz (t : ℤ)) =
        isz (t : ℤ) :: (ts.map (fun t : ℕ => isz (t : ℤ))) from rfl,
      Work.ConvR.map_isz_cons, List.sum_cons, List.sum_cons, ih]

/-- Cost arithmetic for the list-product word: the copy step costs `O(vsz (intList l))`, the fold
step `Kf * (1 + Σ isz + l.length) * (l.prod.size + 2)`, and both fit the statement's bound. -/
theorem pbW6cost (Kf : ℕ) (l : List ℕ) (n₁ n₂ N₁ N₂ : ℕ)
    (hN₁ : N₁ ≤ 24 * (vsz (intList l) + 1))
    (hN₂ : N₂ ≤ Kf * (1 + ((l.map (fun t : ℕ => isz (t : ℤ))).sum + l.length)) *
      ((1 * l.prod).size + 2))
    (hn₁ : n₁ ≤ N₁) (hn₂ : n₂ ≤ N₂) :
    n₁ + n₂ ≤ 200 * (Kf + 1) * (l.length + 1) *
      (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) * (l.prod.size + 2) := by
  have hA : n₁ ≤ 24 * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length + 2) := by
    have h := le_trans hn₁ hN₁
    rw [Work.ConvR.vsz_intList, ← pbSumB l] at h
    omega
  have hB : n₂ ≤ Kf * (1 + (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length)) *
      (l.prod.size + 2) := by
    have h := le_trans hn₂ hN₂
    simpa only [Nat.one_mul] using h
  have hSle : ((l.map (fun t : ℕ => isz (t : ℤ))).sum) ≤
      (l.length + 1) * ((l.map (fun t : ℕ => isz (t : ℤ))).sum) := by
    have h1 : 1 * ((l.map (fun t : ℕ => isz (t : ℤ))).sum) ≤
        (l.length + 1) * ((l.map (fun t : ℕ => isz (t : ℤ))).sum) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
    simpa using h1
  have hkey1 : ((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length + 2 ≤
      (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) *
        (l.prod.size + 2) := by
    have hm : (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + 2) ≤
        (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : ((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length + 2 ≤
        (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) := by
      nlinarith [hm, hSle]
    exact le_trans h2 (Nat.le_mul_of_pos_right _ (by omega : 0 < l.prod.size + 2))
  have hkey2 : (1 + (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length)) * (l.prod.size + 2) ≤
      (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) *
        (l.prod.size + 2) := by
    have hm : (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + 1) ≤
        (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : 1 + (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length) ≤
        (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) := by
      nlinarith [hm, hSle]
    calc (1 + (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.length)) * (l.prod.size + 2)
        ≤ ((l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2)) *
            (l.prod.size + 2) := Nat.mul_le_mul_right _ h2
      _ = (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) *
            (l.prod.size + 2) := by ring
  nlinarith [hA, hB, hkey1, hkey2]

theorem pbW6 : ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (l : List ℕ) (L : List Val)
    (acc : List Val),
      (∀ t ∈ l, 2 ≤ t) →
      WordM main prog
        (fun vs a => vs = Val.int 1 :: acc ∧ a 2 = intList l :: L)
        (fun vs a out b => out = Val.int l.prod :: acc ∧ b 2 = intList l :: L)
        (fun _ _ => Kc * (l.length + 1) * (((l.map (fun t : ℕ => isz (t : ℤ))).sum) + l.prod.size + 2) *
          (l.prod.size + 2)) := by
  obtain ⟨mulP, Km, hmul⟩ := mulNatWord
  obtain ⟨Kf, hfold⟩ := pbFoldEv mulP Km hmul
  refine ⟨pbProdProg mulP, 200 * (Kf + 1), ?_⟩
  intro main l L acc hl
  intro vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h0acc : X 0 = (Val.int 1).enc ++ (encs acc ++ R) := by
    rw [h0X, hvs, Work.Kernel.encs_cons, List.append_assoc]
  have h2X : X 2 = (intList l).enc ++ (encs L ++ Bg 2) := by
    rw [hkX 2 (by decide), ha, Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₁, N₁, hev₁, hN₁, h2₁, h7₁, hfr₁⟩ :=
    pbCopyEv (main := main) (a := 2) (b := pbElt) (c := pbC1) (d := pbC2)
      (hab := by decide) (hac := by decide) (had := by decide) (hbc := by decide)
      (hbd := by decide) (hcd := by decide)
      (g := g) (X := X) (v := intList l) (A := encs L ++ Bg 2) (B := X pbElt) h2X rfl
  have h0₁ : s₁.stk 0 = (Val.int (1 : ℤ)).enc ++ (encs acc ++ R) := by
    rw [hfr₁ 0 (by decide) (by decide)]
    exact h0acc
  obtain ⟨s₂, N₂, hev₂, hN₂, h0₂, h7₂, hfr₂⟩ :=
    hfold main 1 (le_refl 1) l (fun t ht => by have := hl t ht; omega) acc R (X pbElt) s₁.reg
      s₁.stk h0₁ h7₁
  obtain ⟨n₁, he₁, hn₁⟩ := hev₁
  obtain ⟨n₂, he₂, hn₂⟩ := hev₂
  have hfin : Eval main (pbProdProg mulP) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold pbProdProg
    exact Eval.seq he₁ he₂
  refine ⟨Val.int l.prod :: acc, Function.update a 2 (intList l :: L), s₂, n₁ + n₂,
    ⟨rfl, by simp⟩, hfin, ?_, ?_, ?_⟩
  · exact pbW6cost Kf l n₁ n₂ N₁ N₂ hN₁ hN₂ hn₁ hn₂
  · rw [h0₂, Work.Kernel.encs_cons]
    simp only [Nat.one_mul, List.append_assoc]
  · intro k hk0
    by_cases hk2 : k = 2
    · rw [hk2]
      simp only [Function.update_self, hfr₂ 2 (by decide) (by decide), h2₁,
        Work.Kernel.encs_cons, List.append_assoc]
    · by_cases hk7 : k = pbElt
      · rw [hk7]
        have h7₂' : s₂.stk pbElt = X pbElt := h7₂
        rw [h7₂', Function.update_of_ne (by decide : pbElt ≠ 2), hkX pbElt (by decide)]
      · rw [Function.update_of_ne hk2, hfr₂ k hk0 hk7, hfr₁ k hk2 hk7, hkX k hk0]

/-! ## The six words -/

theorem pbWords :
    (∀ (src : HvdH.Stk), src ≠ 0 → ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val)
      (rest : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b src = [])
        (fun _ _ => Kc * (HvdH.vsz v + 1))) ∧
    (∀ (tgt : HvdH.Stk), tgt ≠ 0 → ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val)
      (rest : List HvdH.Val) (L : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = v :: rest ∧ a tgt = L)
        (fun vs a out b => out = rest ∧ b tgt = v :: L)
        (fun _ _ => Kc * (HvdH.vsz v + 1))) ∧
    (∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val) (rest : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs _ => vs = v :: rest)
        (fun _ _ out _ => out = v :: v :: rest)
        (fun _ _ => Kc * (HvdH.vsz v + 1))) ∧
    (∀ (src : HvdH.Stk), src ≠ 0 → ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val)
      (rest : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: [])
        (fun vs a out b => out = v :: vs ∧ b src = v :: [])
        (fun _ _ => Kc * (HvdH.vsz v + 1))) ∧
    (∀ (src : HvdH.Stk), src ≠ 0 → ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (v tl : HvdH.Val)
      (L : List HvdH.Val) (rest : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = rest ∧ a src = HvdH.Val.cons v tl :: L)
        (fun vs a out b => out = v :: vs ∧ b src = tl :: L)
        (fun _ _ => Kc * (HvdH.vsz (HvdH.Val.cons v tl) + HvdH.vsz v + 1))) ∧
    (∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (l : List ℕ) (L : List HvdH.Val) (acc : List HvdH.Val),
      (∀ t ∈ l, 2 ≤ t) →
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.Val.int 1 :: acc ∧ a 2 = HvdH.intList l :: L)
        (fun vs a out b => out = HvdH.Val.int l.prod :: acc ∧ b 2 = HvdH.intList l :: L)
        (fun _ _ => Kc * (l.length + 1) * (((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum) + l.prod.size + 2) *
          (l.prod.size + 2)))
    := ⟨pbW1, pbW2, pbW3, pbW4, pbW5, pbW6⟩

end Work.Resample
