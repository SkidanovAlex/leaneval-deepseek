import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.labArith
import Submission.Work.Kernel.Raw
import Submission.Work.Main.defs
import Submission.Work.Layout.mvVal_ev_full

/-!
# `labStep`: shared framework

`Work.MainP.labStep` computes `q = P / t` from `int t :: int P :: ofList ACC :: acc` and leaves
`int q :: ofList (triple 0 q P :: ACC) :: acc`.  The value `int q` has to be *prepended* to the
list after the triple has been consed onto `ofList ACC`, which is impossible with stack-0 operations
alone (the merged value sits on top); the program therefore parks a copy of `int q` on stack 1 while
the triple is built.

This file provides the bookkeeping that such a program needs:

* `WordR1` — `WordR` with an explicit *stack-1 payload* (a list of glyphs that is present before
  and after a fragment), all other stacks `≠ 0, 1` restored;
* `WordR1_of_WordR`, `WordR1_seq`, `WordR1_seq_pp`, `WordR1_conseq`, `WordR_of_WordR1`,
  `wrd_at` — the composition laws;
* `labStep_cost_le` — the pure-arithmetic estimate closing the cost bound.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## `WordR` with an explicit stack-1 payload -/

/-- `WordR` extended by an explicit stack-1 frame: stack 1 holds the payload `S1` on entry and
`S1'` on exit, and every stack other than `0` and `1` is restored. -/
def WordR1 (main p : Cmd) (S1 S1' : List Glyph) (Pre : List Val → Prop)
    (Post : List Val → List Val → Prop) (C : List Val → ℕ) : Prop :=
  ∀ vs, Pre vs → ∀ s R, s.stk 0 = encs vs ++ R → s.stk 1 = S1 →
    ∃ out s' n, Post vs out ∧ Eval main p s s' n ∧ n ≤ C vs ∧ s'.stk 0 = encs out ++ R ∧
      s'.stk 1 = S1' ∧ ∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k

/-- A `WordR` is a `WordR1` with the payload unchanged. -/
theorem WordR1_of_WordR {main p : Cmd} {S1 S1' : List Glyph} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ} (hS : S1' = S1)
    (h : WordR main p Pre Post C) : WordR1 main p S1 S1' Pre Post C := by
  subst hS
  intro vs hvs s R hs h1s
  obtain ⟨out, s', n, hP, he, hn, h0, hfr⟩ := h vs hvs s R hs
  refine ⟨out, s', n, hP, he, hn, h0, ?_, fun k hk0 hk1 => hfr k hk0⟩
  rw [hfr 1 (by decide), h1s]

/-- Sequencing of two `WordR1` fragments (the payload may change from `S1` to `S1''`). -/
theorem WordR1_seq {main p q : Cmd} {S1 S1' S1'' : List Glyph} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C : List Val → ℕ} {P' : List Val → Prop}
    {Q' : List Val → List Val → Prop} {C' B : List Val → ℕ}
    (hp : WordR1 main p S1 S1' P Q C) (hq : WordR1 main q S1' S1'' P' Q' C')
    (hmid : ∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) :
    WordR1 main (.seq p q) S1 S1'' P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out)
      (fun vs => C vs + B vs) := by
  intro vs hP s R hs h1s
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, h0₁, hS₁, hfr₁⟩ := hp vs hP s R hs h1s
  obtain ⟨hP', hC'⟩ := hmid vs mid hP hQ
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, h0₂, hS₂, hfr₂⟩ := hq mid hP' s₂ R h0₁ hS₁
  exact ⟨out, s₃, n₁ + n₂, ⟨mid, hQ, hQ'⟩, Eval.seq he₁ he₂,
    Nat.add_le_add hn₁ (le_trans hn₂ hC'), h0₂, hS₂,
    fun k hk0 hk1 => by rw [hfr₂ k hk0 hk1, hfr₁ k hk0 hk1]⟩

/-- Sequencing of two fragments with exact pre/post value lists and constant costs. -/
theorem WordR1_seq_pp {main p q : Cmd} {S1 S1' S1'' : List Glyph} {A B₁ B₂ : List Val}
    {c₁ c₂ : ℕ}
    (hp : WordR1 main p S1 S1' (fun vs => vs = A) (fun _ out => out = B₁) (fun _ => c₁))
    (hq : WordR1 main q S1' S1'' (fun vs => vs = B₁) (fun _ out => out = B₂) (fun _ => c₂)) :
    WordR1 main (.seq p q) S1 S1'' (fun vs => vs = A) (fun _ out => out = B₂)
      (fun _ => c₁ + c₂) := by
  intro vs hvs s R hs h1s
  rw [hvs] at hs ⊢
  obtain ⟨mid, s₁, n₁, hmid, he₁, hn₁, h0₁, hS₁, hfr₁⟩ := hp A rfl s R hs h1s
  obtain ⟨out, s₂, n₂, hout, he₂, hn₂, h0₂, hS₂, hfr₂⟩ := hq mid hmid s₁ R h0₁ hS₁
  exact ⟨out, s₂, n₁ + n₂, hout, Eval.seq he₁ he₂,
    show n₁ + n₂ ≤ (fun _ => c₁ + c₂) A from Nat.add_le_add hn₁ hn₂, h0₂, hS₂,
    fun k hk0 hk1 => by rw [hfr₂ k hk0 hk1, hfr₁ k hk0 hk1]⟩

/-- Consequence for `WordR1`. -/
theorem WordR1_conseq {main p : Cmd} {S1 S1' : List Glyph} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (h : WordR1 main p S1 S1' P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR1 main p S1 S1' P' Q' C' := by
  intro vs hP' s R hs h1s
  obtain ⟨out, s', n, hQh, he, hn, h0, hS, hfr⟩ := h vs (hP vs hP') s R hs h1s
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), h0, hS, hfr⟩

/-- A program that is a `WordR1` for every stack-1 payload is a `WordR`. -/
theorem WordR_of_WordR1 {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : ∀ S1, WordR1 main p S1 S1 P Q C) : WordR main p P Q C := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hQ, he, hn, h0, h1s, hfr⟩ := h (s.stk 1) vs hvs s R hs rfl
  exact ⟨out, s', n, hQ, he, hn, h0, fun k hk => by
    by_cases hk1 : k = 1
    · subst hk1; exact h1s
    · exact hfr k hk hk1⟩

/-- Specialise a `WordR` to a concrete input list, output list and constant cost. -/
theorem wrd_at {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {c : ℕ}
    (h : WordR main p P Q C) (hA : P A) (hB : ∀ out, Q A out → out = B) (hc : C A ≤ c) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  intro vs hvs s R hs
  rw [hvs] at hs ⊢
  obtain ⟨out, s', n, hQ, he, hn, h0, hfr⟩ := h A hA s R hs
  exact ⟨out, s', n, hB out hQ, he, le_trans hn hc, h0, hfr⟩

/-! ## Cost arithmetic -/

/-- The accumulated cost of the nine stages of the `labStep` program is bounded by the target
bound, with `a = t.size`, `b = P.size` and `qs ≤ b` the bit size of `P / t`. -/
theorem labStep_cost_le (Kp Kd Kud Kcv Kpv a b qs : ℕ) (hqs : qs ≤ b) :
    Kp * (2 * (a + b + 5)) + Kd * ((b + 2) * (a + 2)) + (Kud + 32) * (qs + 3) + 3 * Kcv + 3 * Kpv
      ≤ 128 * (Kp + Kd + Kud + Kcv + Kpv + 1) * ((a + 1) * (b + 1) + (b + 2)) := by
  have hX : 2 * (a + b + 5) + (b + 2) * (a + 2) + 32 * (b + 3) + 6
      ≤ 128 * ((a + 1) * (b + 1) + (b + 2)) := by
    nlinarith [Nat.zero_le a, Nat.zero_le b]
  have e1 : Kp * (2 * (a + b + 5)) ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * (2 * (a + b + 5)) := by
    have h : Kp ≤ Kp + Kd + Kud + Kcv + Kpv + 1 := by omega
    exact Nat.mul_le_mul_right _ h
  have e2 : Kd * ((b + 2) * (a + 2)) ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * ((b + 2) * (a + 2)) := by
    have h : Kd ≤ Kp + Kd + Kud + Kcv + Kpv + 1 := by omega
    exact Nat.mul_le_mul_right _ h
  have e3 : (Kud + 32) * (qs + 3) ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * (32 * (b + 3)) := by
    have h1 : Kud + 32 ≤ 32 * (Kp + Kd + Kud + Kcv + Kpv + 1) := by omega
    have h2 : qs + 3 ≤ b + 3 := by omega
    calc (Kud + 32) * (qs + 3) ≤ (32 * (Kp + Kd + Kud + Kcv + Kpv + 1)) * (b + 3) :=
          Nat.mul_le_mul h1 h2
      _ = (Kp + Kd + Kud + Kcv + Kpv + 1) * (32 * (b + 3)) := by ring
  have e4 : 3 * Kcv ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * 3 := by
    have h : Kcv * 3 ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * 3 :=
      Nat.mul_le_mul_right 3 (by omega : Kcv ≤ Kp + Kd + Kud + Kcv + Kpv + 1)
    linarith [h]
  have e5 : 3 * Kpv ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * 3 := by
    have h : Kpv * 3 ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * 3 :=
      Nat.mul_le_mul_right 3 (by omega : Kpv ≤ Kp + Kd + Kud + Kcv + Kpv + 1)
    linarith [h]
  have htot : Kp * (2 * (a + b + 5)) + Kd * ((b + 2) * (a + 2)) + (Kud + 32) * (qs + 3)
      + 3 * Kcv + 3 * Kpv
      ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) *
        (2 * (a + b + 5) + (b + 2) * (a + 2) + 32 * (b + 3) + 6) := by
    nlinarith [e1, e2, e3, e4, e5]
  calc Kp * (2 * (a + b + 5)) + Kd * ((b + 2) * (a + 2)) + (Kud + 32) * (qs + 3)
        + 3 * Kcv + 3 * Kpv
      ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) *
        (2 * (a + b + 5) + (b + 2) * (a + 2) + 32 * (b + 3) + 6) := htot
    _ ≤ (Kp + Kd + Kud + Kcv + Kpv + 1) * (128 * ((a + 1) * (b + 1) + (b + 2))) :=
        Nat.mul_le_mul_left _ hX
    _ = 128 * (Kp + Kd + Kud + Kcv + Kpv + 1) * ((a + 1) * (b + 1) + (b + 2)) := by ring

/-- `isz` of a cast natural. -/
theorem isz_natCast' (n : ℕ) : isz ((n : ℤ)) = n.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

/-- The bit size of `P / t` is at most the bit size of `P`. -/
theorem size_div_le (P t : ℕ) : (P / t).size ≤ P.size :=
  Nat.size_le_size (Nat.div_le_self P t)

/-- `vsz` of a value is at least `1`. -/
theorem one_le_vsz' (v : Val) : 1 ≤ vsz v := Work.Layout.one_le_vsz v

end Work.MainP
