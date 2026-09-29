import Mathlib
import Submission.Work.IntLib.SqrtGcd.sqrtLoopKit
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.SqrtGcd.sqrtStepSpec
import Submission.Work.IntLib.SqrtGcd.subLoopEvalXU
import Submission.Work.IntLib.SqrtGcd.dup2EvalGen
import Submission.Work.IntLib.SqrtGcd.moveSameSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.IntLib.SqrtGcd

open HvdH Work.Layout Work.IntLib
open Work.IntLib.SG

/-! ## `Ev` composes along list concatenation -/

theorem swSeqsAppend {main : Cmd} : ∀ (l₁ l₂ : List Cmd) (s t u : State) (C₁ C₂ : ℕ),
    Ev main (seqs l₁) s t C₁ → Ev main (seqs l₂) t u C₂ →
    Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ s t u C₁ C₂ h₁ h₂
    obtain ⟨n, he, -⟩ := h₁
    cases he
    exact h₂.mono (by omega)
  | cons c cs ih =>
    intro l₂ s t u C₁ C₂ h₁ h₂
    cases cs with
    | nil =>
      cases l₂ with
      | nil =>
        obtain ⟨n, he, -⟩ := h₂
        cases he
        exact h₁.mono (by omega)
      | cons d ds => exact Ev.seq h₁ h₂
    | cons d ds =>
      obtain ⟨n, e, hn⟩ := h₁
      rw [show seqs (c :: d :: ds) = .seq c (seqs (d :: ds)) from rfl] at e
      cases e with
      | seq e₁ e₂ =>
        have hrec : Ev main (seqs ((d :: ds) ++ l₂)) _ u (_ + C₂) :=
          ih l₂ _ _ u _ C₂ ⟨_, e₂, le_rfl⟩ h₂
        exact (Ev.seq ⟨_, e₁, le_rfl⟩ hrec).mono (by omega)

/-! ## The two branches of one restoring step -/

/-- Branch A of `sqrtWork` (`rgC = bit true`, i.e. the subtraction underflowed): the digit region
on `sP` is dropped, the region of `sQ` is moved onto `sB` and `bit false` is pushed on `sC`. -/
theorem swBranchAEv (main : Cmd) (s : State) (bB bC bP bQ : List Glyph)
    (x y : Bool) (rb rc dl : List Bool)
    (hB : s.stk sB = Glyph.mk sB :: bB)
    (hC : s.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC)
    (hP : s.stk sP = dl.reverse.map Glyph.bit ++ Glyph.mk sP :: bP)
    (hQ : s.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ) :
    ∃ s', Ev main (seqs [SG.rLoop sP (Glyph.mk sP) none rgT,
        SG.rLoop sQ (Glyph.mk sQ) (some sP) rgT, SG.rLoop sP (Glyph.mk sP) (some sB) rgT,
        .set rgU (.bit false), .push sC rgU]) s s'
        (7 + dl.length * 5
          + (7 + ((y :: x :: rb).map Glyph.bit).length * 5)
          + (7 + ((y :: x :: rb).map Glyph.bit).length * 5) + 2) ∧
      s'.stk sB = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sB :: bB ∧
      s'.stk sC = Glyph.bit false :: (rc.map Glyph.bit ++ Glyph.mk sC :: bC) ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      (∀ j : Stk, j ≠ sB → j ≠ sC → j ≠ sP → j ≠ sQ → s'.stk j = s.stk j) := by
  obtain ⟨s1, e1, h1P, -, -, h1o⟩ :=
    rLoopDrop main sP (Glyph.mk sP) rgT (dl.reverse.map Glyph.bit) bP s (mkNeEos sP)
      (memMapBitNeMk dl.reverse sP) hP
  have h1B : s1.stk sB = Glyph.mk sB :: bB := (h1o sB (by decide)).trans hB
  have h1Q : s1.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ :=
    (h1o sQ (by decide)).trans hQ
  obtain ⟨s2, e2, h2P, h2Q, -, -, h2o⟩ :=
    rLoopMove main sQ sP (Glyph.mk sQ) rgT ((y :: x :: rb).map Glyph.bit) bQ s1 (mkNeEos sQ)
      (by decide) (memMapBitNeMk (y :: x :: rb) sQ) h1Q
  have h2B : s2.stk sB = Glyph.mk sB :: bB := (h2o sB (by decide) (by decide)).trans h1B
  have h2C : s2.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h2o sC (by decide) (by decide)).trans ((h1o sC (by decide)).trans hC)
  have h2P' : s2.stk sP = ((y :: x :: rb).map Glyph.bit).reverse ++ Glyph.mk sP :: bP := by
    rw [h2P, h1P]
  obtain ⟨s3, e3, h3B, h3P, -, -, h3o⟩ :=
    rLoopMove main sP sB (Glyph.mk sP) rgT (((y :: x :: rb).map Glyph.bit).reverse) bP s2
      (mkNeEos sP) (by decide) (memMapBitNeMk_rev (y :: x :: rb) sP) h2P'
  have h3C : s3.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h3o sC (by decide) (by decide)).trans h2C
  have h3B' : s3.stk sB = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sB :: bB := by
    rw [h3B, h2B, List.reverse_reverse]
  obtain ⟨s4, e4, h4C, h4o⟩ := evSetPush main sC rgU (Glyph.bit false) s3
  have h4B : s4.stk sB = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sB :: bB :=
    (h4o sB (by decide)).trans h3B'
  have h4C' : s4.stk sC = Glyph.bit false :: (rc.map Glyph.bit ++ Glyph.mk sC :: bC) := by
    rw [h4C, h3C]
  refine ⟨s4, ?_, h4B, h4C', ?_, ?_, ?_⟩
  · refine (swSeqsAppend [SG.rLoop sP (Glyph.mk sP) none rgT]
        [SG.rLoop sQ (Glyph.mk sQ) (some sP) rgT, SG.rLoop sP (Glyph.mk sP) (some sB) rgT,
         .set rgU (.bit false), .push sC rgU] s s1 s4 _ _ e1
      (swSeqsAppend [SG.rLoop sQ (Glyph.mk sQ) (some sP) rgT]
        [SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit false), .push sC rgU]
        s1 s2 s4 _ _ e2
        (swSeqsAppend [SG.rLoop sP (Glyph.mk sP) (some sB) rgT]
          [.set rgU (.bit false), .push sC rgU] s2 s3 s4 _ _ e3 e4))).mono ?_
    simp only [List.length_map, List.length_reverse]
    linarith
  · rw [h4o sP (by decide), h3P]
  · rw [h4o sQ (by decide), h3o sQ (by decide) (by decide), h2Q]
  · intro j hjB hjC hjP hjQ
    exact (h4o j hjC).trans ((h3o j hjP hjB).trans ((h2o j hjQ hjP).trans (h1o j hjP)))

/-- Branch B of `sqrtWork` (`rgC ≠ bit true`, i.e. the subtraction did not underflow): the regions
of `sB` and `sQ` are dropped, the digit region of `sP` is moved onto `sB` and `bit true` is pushed
on `sC`. -/
theorem swBranchBEv (main : Cmd) (s : State) (bB bC bP bQ : List Glyph)
    (x y : Bool) (rb rc dl : List Bool)
    (hB : s.stk sB = Glyph.mk sB :: bB)
    (hC : s.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC)
    (hP : s.stk sP = dl.reverse.map Glyph.bit ++ Glyph.mk sP :: bP)
    (hQ : s.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ) :
    ∃ s', Ev main (seqs [SG.rLoop sB (Glyph.mk sB) none rgT, SG.rLoop sQ (Glyph.mk sQ) none rgT,
        SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit true), .push sC rgU]) s s'
        ((7 + ([] : List Glyph).length * 5) + (7 + ((y :: x :: rb).map Glyph.bit).length * 5)
          + (7 + dl.length * 5) + 2) ∧
      s'.stk sB = dl.map Glyph.bit ++ Glyph.mk sB :: bB ∧
      s'.stk sC = Glyph.bit true :: (rc.map Glyph.bit ++ Glyph.mk sC :: bC) ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      (∀ j : Stk, j ≠ sB → j ≠ sC → j ≠ sP → j ≠ sQ → s'.stk j = s.stk j) := by
  obtain ⟨s1, e1, h1B, -, -, h1o⟩ :=
    rLoopDrop main sB (Glyph.mk sB) rgT ([] : List Glyph) bB s (mkNeEos sB)
      (by intro g hg; exact absurd hg (by simp)) hB
  have h1C : s1.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC := (h1o sC (by decide)).trans hC
  have h1P : s1.stk sP = dl.reverse.map Glyph.bit ++ Glyph.mk sP :: bP :=
    (h1o sP (by decide)).trans hP
  have h1Q : s1.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ :=
    (h1o sQ (by decide)).trans hQ
  obtain ⟨s2, e2, h2Q, -, -, h2o⟩ :=
    rLoopDrop main sQ (Glyph.mk sQ) rgT ((y :: x :: rb).map Glyph.bit) bQ s1 (mkNeEos sQ)
      (memMapBitNeMk (y :: x :: rb) sQ) h1Q
  have h2B : s2.stk sB = Glyph.mk sB :: bB := (h2o sB (by decide)).trans h1B
  have h2C : s2.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC := (h2o sC (by decide)).trans h1C
  have h2P : s2.stk sP = dl.reverse.map Glyph.bit ++ Glyph.mk sP :: bP :=
    (h2o sP (by decide)).trans h1P
  obtain ⟨s3, e3, h3B, h3P, -, -, h3o⟩ :=
    rLoopMove main sP sB (Glyph.mk sP) rgT (dl.reverse.map Glyph.bit) bP s2 (mkNeEos sP)
      (by decide) (memMapBitNeMk dl.reverse sP) h2P
  have h3C : s3.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h3o sC (by decide) (by decide)).trans h2C
  have h3B' : s3.stk sB = dl.map Glyph.bit ++ Glyph.mk sB :: bB := by
    rw [h3B, h2B, List.map_reverse, List.reverse_reverse]
  obtain ⟨s4, e4, h4C, h4o⟩ := evSetPush main sC rgU (Glyph.bit true) s3
  have h4B : s4.stk sB = dl.map Glyph.bit ++ Glyph.mk sB :: bB :=
    (h4o sB (by decide)).trans h3B'
  have h4C' : s4.stk sC = Glyph.bit true :: (rc.map Glyph.bit ++ Glyph.mk sC :: bC) := by
    rw [h4C, h3C]
  refine ⟨s4, ?_, h4B, h4C', ?_, ?_, ?_⟩
  · refine (swSeqsAppend [SG.rLoop sB (Glyph.mk sB) none rgT]
        [SG.rLoop sQ (Glyph.mk sQ) none rgT, SG.rLoop sP (Glyph.mk sP) (some sB) rgT,
         .set rgU (.bit true), .push sC rgU] s s1 s4 _ _ e1
      (swSeqsAppend [SG.rLoop sQ (Glyph.mk sQ) none rgT]
        [SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit true), .push sC rgU]
        s1 s2 s4 _ _ e2
        (swSeqsAppend [SG.rLoop sP (Glyph.mk sP) (some sB) rgT]
          [.set rgU (.bit true), .push sC rgU] s2 s3 s4 _ _ e3 e4))).mono ?_
    simp only [List.length_map, List.length_reverse]
    linarith
  · rw [h4o sP (by decide), h3P]
  · rw [h4o sQ (by decide), h3o sQ (by decide) (by decide), h2Q]
  · intro j hjB hjC hjP hjQ
    exact (h4o j hjC).trans ((h3o j hjP hjB).trans ((h2o j hjQ).trans (h1o j hjB)))

/-! ## The one-step lemma -/

/-- TEMPORARY copy of the one-step lemma, to be replaced by
`import Submission.Work.IntLib.SqrtGcd.sqrtWorkStep`. -/
theorem sqrtWorkStep (main : HvdH.Cmd) (s₀ s : HvdH.State)
    (bA bB bC bP bQ bR bS : List HvdH.Glyph) (x y : Bool) (rest rb rc : List Bool) (rem r : ℕ)
    (hA : s.stk Work.IntLib.SG.sA
      = (x :: y :: rest).map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: bA)
    (hB : s.stk Work.IntLib.SG.sB
      = rb.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB)
    (hC : s.stk Work.IntLib.SG.sC
      = rc.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS)
    (hfr : Work.IntLib.SqrtGcd.Frame7 s₀ s)
    (hBv : Work.IntLib.ofBits rb = rem) (hCv : Work.IntLib.ofBits rc = r) :
    ∃ (s' : HvdH.State) (m : ℕ) (rbl rcl : List Bool),
      HvdH.Eval main Work.IntLib.SG.sqrtWork s s' m ∧
      m ≤ 500 + 200 * rb.length + 200 * rc.length ∧
      s'.stk Work.IntLib.SG.sA
        = rest.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: bA ∧
      s'.stk Work.IntLib.SG.sB
        = rbl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB ∧
      s'.stk Work.IntLib.SG.sC
        = rcl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC ∧
      Work.IntLib.ofBits rcl
        = 2 * r + (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 1 else 0) ∧
      Work.IntLib.ofBits rbl
        = 4 * rem + (2 * x.toNat + y.toNat)
          - (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 4 * r + 1 else 0) ∧
      rcl.length = rc.length + 1 ∧
      rbl.length ≤ max rb.length rc.length + 2 ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP ∧
      s'.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ ∧
      s'.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR ∧
      s'.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS ∧
      Work.IntLib.SqrtGcd.Frame7 s₀ s' := by
  -- ## 1. `sS` receives a copy of the root region
  obtain ⟨s1, m1, he1, hm1, h1C, h1S, h1P, h1Q, h1o⟩ :=
    dup2EvalGen main sC sS sP sQ rgT rc bC bS bP bQ s hC hS hP hQ
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have E1 : Ev main (dup2 sC sS sP sQ rgT) s s1 (100 + rc.length * 40) := ⟨m1, he1, hm1⟩
  have h1A : s1.stk sA = (x :: y :: rest).map Glyph.bit ++ Glyph.mk sA :: bA :=
    (h1o sA (by decide) (by decide) (by decide) (by decide)).trans hA
  have h1B : s1.stk sB = rb.map Glyph.bit ++ Glyph.mk sB :: bB :=
    (h1o sB (by decide) (by decide) (by decide) (by decide)).trans hB
  have h1R : s1.stk sR = Glyph.mk sR :: bR :=
    (h1o sR (by decide) (by decide) (by decide) (by decide)).trans hR
  -- ## 2. push `false` and `true` on `sS`
  obtain ⟨s2, E2, h2S, h2o⟩ := evSetPush main sS rgU (Glyph.bit false) s1
  obtain ⟨s3, E3, h3S, h3o⟩ := evSetPush main sS rgU (Glyph.bit true) s2
  have h3S' : s3.stk sS = (true :: false :: rc).map Glyph.bit ++ Glyph.mk sS :: bS := by
    rw [h3S, h2S, h1S]; rfl
  have h3A : s3.stk sA = (x :: y :: rest).map Glyph.bit ++ Glyph.mk sA :: bA :=
    (h3o sA (by decide)).trans ((h2o sA (by decide)).trans h1A)
  have h3B : s3.stk sB = rb.map Glyph.bit ++ Glyph.mk sB :: bB :=
    (h3o sB (by decide)).trans ((h2o sB (by decide)).trans h1B)
  have h3C : s3.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h3o sC (by decide)).trans ((h2o sC (by decide)).trans h1C)
  have h3P : s3.stk sP = Glyph.mk sP :: bP :=
    (h3o sP (by decide)).trans ((h2o sP (by decide)).trans h1P)
  have h3Q : s3.stk sQ = Glyph.mk sQ :: bQ :=
    (h3o sQ (by decide)).trans ((h2o sQ (by decide)).trans h1Q)
  have h3R : s3.stk sR = Glyph.mk sR :: bR :=
    (h3o sR (by decide)).trans ((h2o sR (by decide)).trans h1R)
  -- ## 3. pop the next bit pair
  obtain ⟨s4, E4, h4A, h4X, h4Y, h4o⟩ := evPop2 main sA rgX rgY (by decide) s3
  have h4A' : s4.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA := by
    rw [h4A, h3A]; simp
  have h4X' : s4.reg rgX = Glyph.bit x := by rw [h4X, h3A]; simp
  have h4Y' : s4.reg rgY = Glyph.bit y := by rw [h4Y, h3A]; simp
  have h4B : s4.stk sB = rb.map Glyph.bit ++ Glyph.mk sB :: bB := (h4o sB (by decide)).trans h3B
  have h4C : s4.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC := (h4o sC (by decide)).trans h3C
  have h4P : s4.stk sP = Glyph.mk sP :: bP := (h4o sP (by decide)).trans h3P
  have h4Q : s4.stk sQ = Glyph.mk sQ :: bQ := (h4o sQ (by decide)).trans h3Q
  have h4R : s4.stk sR = Glyph.mk sR :: bR := (h4o sR (by decide)).trans h3R
  have h4S : s4.stk sS = (true :: false :: rc).map Glyph.bit ++ Glyph.mk sS :: bS :=
    (h4o sS (by decide)).trans h3S'
  -- ## 4. move the remainder region onto `sQ`, through `sP`
  obtain ⟨s5, m5, he5, hm5, h5B, h5P, h5Q, h5o⟩ :=
    moveSameSpec main sB sQ sP rgT rb bB bP s4 h4B h4P (by decide) (by decide) (by decide)
  have E5 : Ev main (moveSame sB sQ sP rgT) s4 s5 (14 + 10 * rb.length) := ⟨m5, he5, by rw [hm5]⟩
  have h5Q' : s5.stk sQ = rb.map Glyph.bit ++ Glyph.mk sQ :: bQ := by rw [h5Q, h4Q]
  have h5X : s5.reg rgX = Glyph.bit x := (Ev.reg_frame E5 (r := rgX) (by decide)).trans h4X'
  have h5Y : s5.reg rgY = Glyph.bit y := (Ev.reg_frame E5 (r := rgY) (by decide)).trans h4Y'
  have h5A : s5.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA :=
    (h5o sA (by decide) (by decide) (by decide)).trans h4A'
  have h5C : s5.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h5o sC (by decide) (by decide) (by decide)).trans h4C
  have h5R : s5.stk sR = Glyph.mk sR :: bR :=
    (h5o sR (by decide) (by decide) (by decide)).trans h4R
  have h5S : s5.stk sS = (true :: false :: rc).map Glyph.bit ++ Glyph.mk sS :: bS :=
    (h5o sS (by decide) (by decide) (by decide)).trans h4S
  -- ## 5. append the bit pair to `sQ`
  obtain ⟨s6, E6, h6Q, h6o⟩ := evPush2 main sQ rgX rgY s5
  have h6Q' : s6.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ := by
    rw [h6Q, h5Y, h5X, h5Q']; rfl
  have h6A : s6.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA := (h6o sA (by decide)).trans h5A
  have h6B : s6.stk sB = Glyph.mk sB :: bB := (h6o sB (by decide)).trans h5B
  have h6C : s6.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC := (h6o sC (by decide)).trans h5C
  have h6P : s6.stk sP = Glyph.mk sP :: bP := (h6o sP (by decide)).trans h5P
  have h6R : s6.stk sR = Glyph.mk sR :: bR := (h6o sR (by decide)).trans h5R
  have h6S : s6.stk sS = (true :: false :: rc).map Glyph.bit ++ Glyph.mk sS :: bS :=
    (h6o sS (by decide)).trans h5S
  -- ## 6. duplicate `sQ` onto `sR`
  obtain ⟨s7, m7, he7, hm7, h7Q, h7R, h7P, h7B, h7o⟩ :=
    dup2EvalGen main sQ sR sP sB rgT (y :: x :: rb) bQ bR bP bB s6 h6Q' h6R h6P h6B
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have E7 : Ev main (dup2 sQ sR sP sB rgT) s6 s7 (100 + (rb.length + 2) * 40) := by
    refine ⟨m7, he7, ?_⟩
    have h := hm7
    simp only [List.length_cons] at h
    omega
  have h7A : s7.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA :=
    (h7o sA (by decide) (by decide) (by decide) (by decide)).trans h6A
  have h7C : s7.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h7o sC (by decide) (by decide) (by decide) (by decide)).trans h6C
  have h7S : s7.stk sS = (true :: false :: rc).map Glyph.bit ++ Glyph.mk sS :: bS :=
    (h7o sS (by decide) (by decide) (by decide) (by decide)).trans h6S
  -- ## 7. the ripple subtraction `sR - sS`
  obtain ⟨s8, m8, he8, hm8, h8R, h8S, h8P, h8C, h8o⟩ :=
    Work.IntLib.SGX.subLoopEvalXU main sR sS (Glyph.mk sR) (Glyph.mk sS) sP rgX rgY rgC rgZ rgT
      rgU rgW (y :: x :: rb) (true :: false :: rc) bR bS s7
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (mkNeEos sR) (mkNeEos sS)
      (fun b h => by cases h) (fun b h => by cases h) h7R h7S
  set n : ℕ := max (y :: x :: rb).length (true :: false :: rc).length with hndef
  set β : Bool := (SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).1 with hβdef
  set dg : List Bool := (SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).2 with hdgdef
  have E8 : Ev main (subLoop sR sS (Glyph.mk sR) (Glyph.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW)
      s7 s8 (40 * (rb.length + rc.length + 3) + 4) := by
    refine ⟨m8, he8, ?_⟩
    have hlen1 : (y :: x :: rb).length = rb.length + 2 := by
      rw [List.length_cons, List.length_cons]
    have hlen2 : (true :: false :: rc).length = rc.length + 2 := by
      rw [List.length_cons, List.length_cons]
    have hn : n = max rb.length rc.length + 2 := by
      rw [hndef, hlen1, hlen2, max_add_two]
    have h := hm8
    rw [hn] at h
    have hmx : max rb.length rc.length ≤ rb.length + rc.length :=
      max_le (by omega : rb.length ≤ rb.length + rc.length)
        (by omega : rc.length ≤ rb.length + rc.length)
    linarith
  have h8P' : s8.stk sP = dg.reverse.map Glyph.bit ++ Glyph.mk sP :: bP := by
    rw [h8P, h7P]
  have h8A : s8.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA :=
    (h8o sA (by decide) (by decide) (by decide)).trans h7A
  have h8B : s8.stk sB = Glyph.mk sB :: bB :=
    (h8o sB (by decide) (by decide) (by decide)).trans h7B
  have h8C'' : s8.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC :=
    (h8o sC (by decide) (by decide) (by decide)).trans h7C
  have h8Q : s8.stk sQ = (y :: x :: rb).map Glyph.bit ++ Glyph.mk sQ :: bQ :=
    (h8o sQ (by decide) (by decide) (by decide)).trans h7Q
  have hfr8 : Frame7 s₀ s8 :=
    hfr.trans
    ((frame7_of_keeps4CL (a := sC) (b := sS) (c := sP) (d := sQ)
      (by decide) (by decide) (by decide) (by decide) h1o).trans
    ((frame7_of_keeps1 (a := sS) (by decide) h2o).trans
    ((frame7_of_keeps1 (a := sS) (by decide) h3o).trans
    ((frame7_of_keeps1 (a := sA) (by decide) h4o).trans
    ((frame7_of_keeps3CL (a := sB) (b := sP) (c := sQ)
      (by decide) (by decide) (by decide) h5o).trans
    ((frame7_of_keeps1 (a := sQ) (by decide) h6o).trans
    ((frame7_of_keeps4CL (a := sQ) (b := sR) (c := sP) (d := sB)
      (by decide) (by decide) (by decide) (by decide) h7o).trans
    (frame7_of_keeps3CL (a := sR) (b := sS) (c := sP)
      (by decide) (by decide) (by decide) h8o))))))))
  have hdg_n : dg.length = max rb.length rc.length + 2 := by
    have h1 : (SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).2.length = n :=
      subDigitsArith.2.2.2 n (y :: x :: rb) (true :: false :: rc) false
    rw [hdgdef, h1, hndef]
    simp only [List.length_cons]
    rw [show rb.length + 1 + 1 = rb.length + 2 from by omega,
        show rc.length + 1 + 1 = rc.length + 2 from by omega, max_add_two]
  have hdg_le : dg.length ≤ rb.length + rc.length + 2 := by
    rw [hdg_n]
    exact Nat.add_le_add_right (max_le (by omega : rb.length ≤ rb.length + rc.length)
      (by omega : rc.length ≤ rb.length + rc.length)) 2
  have hxy : ((y :: x :: rb).map Glyph.bit).length = rb.length + 2 := by
    simp only [List.length_map, List.length_cons]
  -- ## 8. branch on the borrow
  by_cases hβ : β = true
  · -- **branch A**: the subtraction underflowed; root bit `false`
    have hregC : s8.reg rgC = Glyph.bit true := by rw [h8C, hβ]
    have hcondA : ¬ (4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat)) := by
      have hb : (SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).1 = true := by
        rw [← hβdef]; exact hβ
      have h1 := (subDigitsArith.1 n (y :: x :: rb) (true :: false :: rc)).mp hb
      rw [subDigitsArith.2.2.1 n (y :: x :: rb) (le_max_left _ _),
          subDigitsArith.2.2.1 n (true :: false :: rc) (le_max_right _ _)] at h1
      rw [ofBits_pair_append, hBv, ofBits_true_false_cons rc r hCv] at h1
      omega
    obtain ⟨s9, E9, h9B, h9C, h9P, h9Q, h9o⟩ :=
      swBranchAEv main s8 bB bC bP bQ x y rb rc dg h8B h8C'' h8P' h8Q
    have h9A : s9.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA :=
      (h9o sA (by decide) (by decide) (by decide) (by decide)).trans h8A
    have h9R : s9.stk sR = Glyph.mk sR :: bR :=
      (h9o sR (by decide) (by decide) (by decide) (by decide)).trans h8R
    have h9S : s9.stk sS = Glyph.mk sS :: bS :=
      (h9o sS (by decide) (by decide) (by decide) (by decide)).trans h8S
    have hvvC : ofBits (false :: rc)
        = 2 * r + (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 1 else 0) := by
      rw [if_neg hcondA, ofBits_false_cons rc r hCv, Nat.add_zero]
    have hvvB : ofBits (y :: x :: rb)
        = 4 * rem + (2 * x.toNat + y.toNat)
          - (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 4 * r + 1 else 0) := by
      rw [if_neg hcondA, ofBits_pair_append, hBv, Nat.sub_zero]
    have hfr9 : Frame7 s₀ s9 := hfr8.trans (frame7_of_keeps4CL (a := sB) (b := sC) (c := sP)
      (d := sQ) (by decide) (by decide) (by decide) (by decide) h9o)
    have hEvA : Ev main sqrtWork s s9 (500 + 200 * rb.length + 200 * rc.length) := by
      refine (swSeqsAppend [dup2 sC sS sP sQ rgT, .set rgU (.bit false), .push sS rgU,
          .set rgU (.bit true), .push sS rgU, .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT,
          .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
          subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW]
        [.ite rgC (.bit true)
          (seqs [SG.rLoop sP (Glyph.mk sP) none rgT, SG.rLoop sQ (Glyph.mk sQ) (some sP) rgT,
            SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit false), .push sC rgU])
          (seqs [SG.rLoop sB (Glyph.mk sB) none rgT, SG.rLoop sQ (Glyph.mk sQ) none rgT,
            SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit true), .push sC rgU])]
        s s8 s9 _ _
        (swSeqsAppend [dup2 sC sS sP sQ rgT]
          [.set rgU (.bit false), .push sS rgU, .set rgU (.bit true), .push sS rgU,
           .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY,
           dup2 sQ sR sP sB rgT,
           subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s s1 s8 _ _ E1
          (swSeqsAppend [.set rgU (.bit false), .push sS rgU]
            [.set rgU (.bit true), .push sS rgU, .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT,
             .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
             subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s1 s2 s8 _ _ E2
            (swSeqsAppend [.set rgU (.bit true), .push sS rgU]
              [.pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY,
               dup2 sQ sR sP sB rgT,
               subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s2 s3 s8 _ _ E3
              (swSeqsAppend [.pop sA rgX, .pop sA rgY]
                [moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
                 subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s3 s4 s8 _ _ E4
                (swSeqsAppend [moveSame sB sQ sP rgT]
                  [.push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
                   subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s4 s5 s8 _ _ E5
                  (swSeqsAppend [.push sQ rgX, .push sQ rgY]
                    [dup2 sQ sR sP sB rgT,
                     subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s5 s6 s8 _ _ E6
                    (swSeqsAppend [dup2 sQ sR sP sB rgT]
                      [subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW]
                      s6 s7 s8 _ _ E7 E8)))))))
        (Ev.iteT hregC E9)).mono ?_
      simp only [hxy]
      linarith [hdg_le, hdg_n, hxy]
    obtain ⟨m9, he9, hm9⟩ := hEvA
    refine ⟨s9, m9, y :: x :: rb, false :: rc, he9, hm9, h9A, h9B, h9C, hvvC, hvvB, rfl, ?_,
      h9P, h9Q, h9R, h9S, hfr9⟩
    · have hlen : rb.length + 1 + 1 ≤ max rb.length rc.length + 2 := by
        have h := Nat.add_le_add_right (le_max_left rb.length rc.length) 2
        omega
      simpa only [List.length_cons] using hlen
  · -- **branch B**: the subtraction did not underflow; root bit `true`
    have hβf : β = false := by cases hb : β <;> simp_all
    have hregC : ¬ (s8.reg rgC = Glyph.bit true) := by rw [h8C, hβf]; intro h; cases h
    have hcondB : 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) := by
      have hb : ¬ ((SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).1 = true) := by
        rw [← hβdef]; exact hβ
      have h1 : ¬ (ofBits (SG.padTo n (y :: x :: rb))
          < ofBits (SG.padTo n (true :: false :: rc))) :=
        fun hlt => hb ((subDigitsArith.1 n (y :: x :: rb) (true :: false :: rc)).mpr hlt)
      rw [subDigitsArith.2.2.1 n (y :: x :: rb) (le_max_left _ _),
          subDigitsArith.2.2.1 n (true :: false :: rc) (le_max_right _ _)] at h1
      rw [ofBits_pair_append, hBv, ofBits_true_false_cons rc r hCv] at h1
      omega
    have hbvF : (SG.subDigits n (y :: x :: rb) (true :: false :: rc) false).1 = false := by
      rw [← hβdef]; exact hβf
    have hdig : ofBits dg = 4 * rem + (2 * x.toNat + y.toNat) - (4 * r + 1) := by
      have h := (subDigitsArith.2.1 n (y :: x :: rb) (true :: false :: rc)) hbvF
      rw [subDigitsArith.2.2.1 n (y :: x :: rb) (le_max_left _ _),
          subDigitsArith.2.2.1 n (true :: false :: rc) (le_max_right _ _)] at h
      rw [ofBits_pair_append, hBv, ofBits_true_false_cons rc r hCv] at h
      rw [hdgdef]; exact h
    obtain ⟨s9, E9, h9B, h9C, h9P, h9Q, h9o⟩ :=
      swBranchBEv main s8 bB bC bP bQ x y rb rc dg h8B h8C'' h8P' h8Q
    have h9A : s9.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA :=
      (h9o sA (by decide) (by decide) (by decide) (by decide)).trans h8A
    have h9R : s9.stk sR = Glyph.mk sR :: bR :=
      (h9o sR (by decide) (by decide) (by decide) (by decide)).trans h8R
    have h9S : s9.stk sS = Glyph.mk sS :: bS :=
      (h9o sS (by decide) (by decide) (by decide) (by decide)).trans h8S
    have hvvC : ofBits (true :: rc)
        = 2 * r + (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 1 else 0) := by
      rw [if_pos hcondB, ofBits_true_cons rc r hCv]
    have hvvB : ofBits dg
        = 4 * rem + (2 * x.toNat + y.toNat)
          - (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 4 * r + 1 else 0) := by
      rw [if_pos hcondB]; exact hdig
    have hfr9 : Frame7 s₀ s9 := hfr8.trans (frame7_of_keeps4CL (a := sB) (b := sC) (c := sP)
      (d := sQ) (by decide) (by decide) (by decide) (by decide) h9o)
    have hEvB : Ev main sqrtWork s s9 (500 + 200 * rb.length + 200 * rc.length) := by
      refine (swSeqsAppend [dup2 sC sS sP sQ rgT, .set rgU (.bit false), .push sS rgU,
          .set rgU (.bit true), .push sS rgU, .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT,
          .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
          subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW]
        [.ite rgC (.bit true)
          (seqs [SG.rLoop sP (Glyph.mk sP) none rgT, SG.rLoop sQ (Glyph.mk sQ) (some sP) rgT,
            SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit false), .push sC rgU])
          (seqs [SG.rLoop sB (Glyph.mk sB) none rgT, SG.rLoop sQ (Glyph.mk sQ) none rgT,
            SG.rLoop sP (Glyph.mk sP) (some sB) rgT, .set rgU (.bit true), .push sC rgU])]
        s s8 s9 _ _
        (swSeqsAppend [dup2 sC sS sP sQ rgT]
          [.set rgU (.bit false), .push sS rgU, .set rgU (.bit true), .push sS rgU,
           .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY,
           dup2 sQ sR sP sB rgT,
           subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s s1 s8 _ _ E1
          (swSeqsAppend [.set rgU (.bit false), .push sS rgU]
            [.set rgU (.bit true), .push sS rgU, .pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT,
             .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
             subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s1 s2 s8 _ _ E2
            (swSeqsAppend [.set rgU (.bit true), .push sS rgU]
              [.pop sA rgX, .pop sA rgY, moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY,
               dup2 sQ sR sP sB rgT,
               subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s2 s3 s8 _ _ E3
              (swSeqsAppend [.pop sA rgX, .pop sA rgY]
                [moveSame sB sQ sP rgT, .push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
                 subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s3 s4 s8 _ _ E4
                (swSeqsAppend [moveSame sB sQ sP rgT]
                  [.push sQ rgX, .push sQ rgY, dup2 sQ sR sP sB rgT,
                   subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s4 s5 s8 _ _ E5
                  (swSeqsAppend [.push sQ rgX, .push sQ rgY]
                    [dup2 sQ sR sP sB rgT,
                     subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW] s5 s6 s8 _ _ E6
                    (swSeqsAppend [dup2 sQ sR sP sB rgT]
                      [subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW]
                      s6 s7 s8 _ _ E7 E8)))))))
        (Ev.iteF hregC E9)).mono ?_
      simp only [hxy, List.length_nil]
      linarith [hdg_le]
    obtain ⟨m9, he9, hm9⟩ := hEvB
    refine ⟨s9, m9, dg, true :: rc, he9, hm9, h9A, h9B, h9C, hvvC, hvvB, rfl, ?_, h9P, h9Q, h9R, h9S, hfr9⟩
    · exact le_of_eq hdg_n

end Work.IntLib.SqrtGcd
