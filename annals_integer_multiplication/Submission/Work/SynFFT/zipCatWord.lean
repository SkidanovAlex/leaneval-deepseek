import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.zipKit
import Submission.Work.SynFFT.zipStepCC
import Submission.Work.SynFFT.zipStepCN
import Submission.Work.SynFFT.zipStepNC
import Submission.Work.Layout.appendWord
import Submission.Work.Layout.reverseWord

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace Work.SynFFT

open HvdH
open Work.Layout

/-! ## The iteration count of the loop -/

/-- number of iterations of the loop for the remaining groups `A₁`, `A₂` (one per consumed row,
plus the final test that stops the loop) -/
def zIters (A₁ A₂ : List (List Val)) : ℕ := max A₁.length A₂.length + 1

theorem zIters_nil_nil : zIters ([] : List (List Val)) [] = 1 := rfl

theorem zIters_cc (r1 r2 : List Val) (t1 t2 : List (List Val)) :
    zIters (r1 :: t1) (r2 :: t2) = 1 + zIters t1 t2 := by
  simp only [zIters, List.length_cons]
  omega

theorem zIters_cn (r1 : List Val) (t1 : List (List Val)) :
    zIters (r1 :: t1) [] = 1 + zIters t1 [] := by
  simp only [zIters, List.length_cons, List.length_nil]
  omega

theorem zIters_nc (r2 : List Val) (t2 : List (List Val)) :
    zIters [] (r2 :: t2) = 1 + zIters [] t2 := by
  simp only [zIters, List.length_cons, List.length_nil]
  omega

/-- the cost budget of the loop (one `zStepCost` per iteration, plus one extra unit per iteration
for the loop test of `loopRuns`, absorbed by the `+1` in the factor `KA + 101`) -/
def zLoopCost (KA : ℕ) (A₁ A₂ : List (List Val)) : ℕ :=
  (KA + 101) * (vsz (grpVal A₁) + vsz (grpVal A₂) + 1)

/-- one iteration of the loop fits in the budget: the body cost `zStepCost`, the loop test, and the
budget of the remaining iterations -/
theorem zLoopCost_step (KA : ℕ) (A₁ A₂ : List (List Val)) (h : A₁ ≠ [] ∨ A₂ ≠ []) :
    zStepCost KA A₁ A₂ + 1 + zLoopCost KA (A₁.tailD []) (A₂.tailD []) ≤ zLoopCost KA A₁ A₂ := by
  have hb : 1 ≤ zBump A₁ + zBump A₂ := by
    rcases h with h | h
    · cases A₁ with
      | nil => exact absurd rfl h
      | cons r t =>
          rw [zBump_cons]
          have := one_le_vsz (ofList r)
          omega
    · cases A₂ with
      | nil => exact absurd rfl h
      | cons r t =>
          rw [zBump_cons]
          have := one_le_vsz (ofList r)
          omega
  rw [zLoopCost, zStepCost, zLoopCost, vsz_grpVal_eq_zBump A₁, vsz_grpVal_eq_zBump A₂]
  first
  | nlinarith [hb]
  | omega

/-! ## The step in which both groups are exhausted -/

/-- the body with both stacks exhausted: it only sets the flag to `eos` -/
private theorem zStepNN (main zApp : Cmd) (rest : List Val) (R : List Glyph)
    (Racc : List (List Val)) (Z1 Z2 Z3 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (h1 : X 1 = (ofList ([] : List Val)).enc ++ Z1)
    (h2 : X 2 = (ofList ([] : List Val)).enc ++ Z2)
    (hF : g zF = Glyph.cons) :
    ∃ s', Ev main (zBody zApp) ⟨g, X⟩ s' 5 ∧ s'.stk = X ∧ s'.reg zF = Glyph.eos := by
  -- the second half of the body, on an arbitrary state whose stack 2 is exhausted
  have hElse : ∀ (S : State), S.stk 2 = (ofList ([] : List Val)).enc ++ Z2 →
      ∃ s', Ev main (seqs [.peek 2 zP,
          .ite zP Glyph.cons
            (seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
            (.set zF Glyph.eos)])
        S s' 3 ∧ s'.stk = S.stk ∧ s'.reg zF = Glyph.eos := by
    intro S hS2
    have hhead : (S.stk 2).headD Glyph.eos = Glyph.nil := by rw [hS2]; rfl
    have hp : Ev main (.peek 2 zP) S ⟨Function.update S.reg zP Glyph.nil, S.stk⟩ 1 := by
      have := ev_peek' (main := main) 2 zP S.reg S.stk
      rw [hhead] at this
      exact this
    have hi : Ev main (.ite zP Glyph.cons
        (seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
        (.set zF Glyph.eos))
        ⟨Function.update S.reg zP Glyph.nil, S.stk⟩
        ⟨Function.update (Function.update S.reg zP Glyph.nil) zF Glyph.eos, S.stk⟩ 2 :=
      Ev.iteF (by simp) (ev_set' (main := main) zF Glyph.eos _ _)
    have hseq : Ev main (seqs [.peek 2 zP, .ite zP Glyph.cons
          (seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
          (.set zF Glyph.eos)]) S
        ⟨Function.update (Function.update S.reg zP Glyph.nil) zF Glyph.eos, S.stk⟩ 3 := by
      simp only [seqs]
      exact Ev.seq' hp hi (by omega)
    exact ⟨_, hseq, rfl, by simp⟩
  -- the first peek
  have hhead1 : (X 1).headD Glyph.eos = Glyph.nil := by rw [h1]; rfl
  have hp1 : Ev main (.peek 1 zP) ⟨g, X⟩ ⟨Function.update g zP Glyph.nil, X⟩ 1 := by
    have := ev_peek' (main := main) 1 zP g X
    rw [hhead1] at this
    exact this
  obtain ⟨s', hElseEv, hstk, hreg⟩ := hElse ⟨Function.update g zP Glyph.nil, X⟩ (by simp [h2])
  have hite : Ev main (.ite zP Glyph.cons
      (seqs [.pop 1 rA,
        .peek 2 zP,
        .ite zP Glyph.cons
          (seqs [.pop 2 rA, mvVal 2 0 4 5, mvVal 1 0 4 5, zMer zApp zF])
          (seqs [pushConst 0 Glyph.nil, mvVal 1 0 4 5, zMer zApp zF])])
      (seqs [.peek 2 zP,
        .ite zP Glyph.cons
          (seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
          (.set zF Glyph.eos)]))
      ⟨Function.update g zP Glyph.nil, X⟩ s' 4 :=
    Ev.iteF (by simp) hElseEv
  have hseq0 : Ev main (.seq (.peek 1 zP)
      (.ite zP Glyph.cons
        (seqs [.pop 1 rA,
          .peek 2 zP,
          .ite zP Glyph.cons
            (seqs [.pop 2 rA, mvVal 2 0 4 5, mvVal 1 0 4 5, zMer zApp zF])
            (seqs [pushConst 0 Glyph.nil, mvVal 1 0 4 5, zMer zApp zF])])
        (seqs [.peek 2 zP,
          .ite zP Glyph.cons
            (seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
            (.set zF Glyph.eos)]))) ⟨g, X⟩ s' 5 :=
    Ev.seq' hp1 hite (by omega)
  have hbody : Ev main (zBody zApp) ⟨g, X⟩ s' 5 := by
    simpa only [zBody, seqs] using hseq0
  exact ⟨s', hbody, hstk, hreg⟩

/-! ## The loop -/

/-- the loop of the `zipCat` word, run on the remaining groups `A₁`, `A₂`: it consumes one row of
each group (using the empty row when a group is exhausted), merges them and prepends the result to
the accumulator until both groups are exhausted; the accumulator holds the reverse of the merged
result. -/
private theorem zLoop_aux {main : Cmd} {zApp : Cmd} {KA : ℕ}
    (hApp : ∀ (xs ys rest' : List Val), WordR main zApp
      (fun vs => vs = ofList xs :: ofList ys :: rest')
      (fun _ out => out = ofList (xs ++ ys) :: rest')
      (fun _ => KA * (vsz (ofList xs) + 1)))
    (C : List (List Val)) (rest : List Val) (R : List Glyph) :
    ∀ (n : ℕ) (A₁ A₂ : List (List Val)) (Racc : List (List Val))
      (Z1 Z2 Z3 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      A₁.length + A₂.length ≤ n →
      X 0 = encs rest ++ R →
      X 1 = (ofList (A₁.map ofList)).enc ++ Z1 →
      X 2 = (ofList (A₂.map ofList)).enc ++ Z2 →
      X 3 = (ofList (Racc.map ofList)).enc ++ Z3 →
      Racc.reverse ++ zipCat A₁ A₂ = C →
      g zF = Glyph.cons →
      ∃ s', loopRuns main zF Glyph.cons (zBody zApp) (zIters A₁ A₂) ⟨g, X⟩ s'
          (zLoopCost KA A₁ A₂) ∧
        s'.stk 0 = X 0 ∧
        s'.stk 1 = (ofList ([] : List Val)).enc ++ Z1 ∧
        s'.stk 2 = (ofList ([] : List Val)).enc ++ Z2 ∧
        s'.stk 3 = (ofList (C.reverse.map ofList)).enc ++ Z3 ∧
        s'.reg zF = Glyph.eos ∧
        s'.stk 4 = X 4 ∧ s'.stk 5 = X 5 ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → s'.stk k = X k) := by
  intro n
  induction n with
  | zero =>
      intro A₁ A₂ Racc Z1 Z2 Z3 g X hlen h0 h1 h2 h3 hinv hF
      have hA₁ : A₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hA₂ : A₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hA₁
      subst hA₂
      have hinv' : Racc.reverse = C := by simpa using hinv
      obtain ⟨s', hEv, hstk, hreg⟩ := zStepNN main zApp rest R Racc Z1 Z2 Z3 g X h1 h2 hF
      have hRC : Racc = C.reverse := by rw [← hinv', List.reverse_reverse]
      have hrun1 : loopRuns main zF Glyph.cons (zBody zApp) 1 ⟨g, X⟩ s' 6 :=
        loopRuns.one hF hEv
      have hrun : loopRuns main zF Glyph.cons (zBody zApp) (zIters [] []) ⟨g, X⟩ s'
          (zLoopCost KA [] []) :=
        loopRuns.mono (by simp only [zIters]; omega) hrun1
          (by simp only [zLoopCost, vsz_grpVal_nil]; omega)
      refine ⟨s', hrun, ?_, ?_, ?_, ?_, hreg, ?_, ?_, ?_⟩
      · rw [hstk]
      · rw [hstk]; simpa using h1
      · rw [hstk]; simpa using h2
      · rw [hstk]; simpa [hRC] using h3
      · rw [hstk]
      · rw [hstk]
      · intro k hk0 hk1 hk2 hk3 hk4 hk5
        rw [hstk]
  | succ n ih =>
      intro A₁ A₂ Racc Z1 Z2 Z3 g X hlen h0 h1 h2 h3 hinv hF
      rcases A₁ with _ | ⟨r1, t1⟩
      · -- first group exhausted
        rcases A₂ with _ | ⟨r2, t2⟩
        · -- both exhausted: run the no-op iteration
          have hinv' : Racc.reverse = C := by simpa using hinv
          obtain ⟨s', hEv, hstk, hreg⟩ := zStepNN main zApp rest R Racc Z1 Z2 Z3 g X h1 h2 hF
          have hRC : Racc = C.reverse := by rw [← hinv', List.reverse_reverse]
          have hrun1 : loopRuns main zF Glyph.cons (zBody zApp) 1 ⟨g, X⟩ s' 6 :=
            loopRuns.one hF hEv
          have hrun : loopRuns main zF Glyph.cons (zBody zApp) (zIters [] []) ⟨g, X⟩ s'
              (zLoopCost KA [] []) :=
            loopRuns.mono (by simp only [zIters]; omega) hrun1
              (by simp only [zLoopCost, vsz_grpVal_nil]; omega)
          refine ⟨s', ?_, ?_, ?_, ?_, ?_, hreg, ?_, ?_, ?_⟩
          · simpa [zIters] using hrun
          · rw [hstk]
          · rw [hstk]; simpa using h1
          · rw [hstk]; simpa using h2
          · rw [hstk]; simpa [hRC] using h3
          · rw [hstk]
          · rw [hstk]
          · intro k hk0 hk1 hk2 hk3 hk4 hk5
            rw [hstk]
        · -- `[]` vs `r2 :: t2`
          have h2' : X 2 = Glyph.cons :: ((ofList r2).enc ++
              ((ofList (t2.map ofList)).enc ++ Z2)) := by
            rw [h2, ofList_map_ofList_cons, List.cons_append, List.append_assoc]
          obtain ⟨s₁, n₁, hEv₁, hn₁, hs₁0, hs₁1, hs₁2, hs₁3, hs₁reg, hs₁4, hs₁5, hfr₁⟩ :=
            zipStepNC (main := main) (zApp := zApp) (KA := KA) hApp h0 h1 h2' h3
          have hinv' : ((([] : List Val) ++ r2) :: Racc).reverse ++ zipCat [] t2 = C := by
            rw [← hinv]
            simp
          have hlen' : ([] : List (List Val)).length + t2.length ≤ n := by
            simp only [List.length_nil, List.length_cons] at hlen ⊢
            omega
          obtain ⟨s₂, hrun₂, hA0, hA1, hA2, hA3, hreg, hA4, hA5, hfram⟩ :=
            ih ([] : List (List Val)) t2 ((([] : List Val) ++ r2) :: Racc) Z1 Z2 Z3 s₁.reg s₁.stk
              hlen' (by rw [hs₁0, h0]) (by rw [hs₁1]; exact h1) hs₁2 hs₁3 hinv' hs₁reg
          have hB0 : s₂.stk 0 = X 0 := by rw [hA0, hs₁0]
          have hB4 : s₂.stk 4 = X 4 := by rw [hA4, hs₁4]
          have hB5 : s₂.stk 5 = X 5 := by rw [hA5, hs₁5]
          have hBfram : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 →
              s₂.stk k = X k := by
            intro k hk0 hk1 hk2 hk3 hk4 hk5
            rw [hfram k hk0 hk1 hk2 hk3 hk4 hk5, hfr₁ k hk0 hk1 hk2 hk3 hk4 hk5]
          refine ⟨s₂, ?_, hB0, hA1, hA2, hA3, hreg, hB4, hB5, hBfram⟩
          · refine loopRuns.mono (by simp only [zIters]; omega)
              (loopRuns.cast (zIters_nc r2 t2).symm (loopRuns.concat (zIters [] t2)
                (loopRuns.one hF hEv₁) hrun₂)) ?_
            have hstep : zStepCost KA ([] : List (List Val)) (r2 :: t2) + 1 + zLoopCost KA [] t2
                ≤ zLoopCost KA [] (r2 :: t2) := by
              simpa using zLoopCost_step KA ([] : List (List Val)) (r2 :: t2) (Or.inr (by simp))
            omega
      · rcases A₂ with _ | ⟨r2, t2⟩
        · -- `r1 :: t1` vs `[]`
          have h1' : X 1 = Glyph.cons :: ((ofList r1).enc ++
              ((ofList (t1.map ofList)).enc ++ Z1)) := by
            rw [h1, ofList_map_ofList_cons, List.cons_append, List.append_assoc]
          obtain ⟨s₁, n₁, hEv₁, hn₁, hs₁0, hs₁1, hs₁2, hs₁3, hs₁reg, hs₁4, hs₁5, hfr₁⟩ :=
            zipStepCN (main := main) (zApp := zApp) (KA := KA) hApp h0 h1' h2 h3
          have hinv' : ((r1 ++ ([] : List Val)) :: Racc).reverse ++ zipCat t1 [] = C := by
            rw [← hinv]
            simp
          have hlen' : t1.length + ([] : List (List Val)).length ≤ n := by
            simp only [List.length_nil, List.length_cons] at hlen ⊢
            omega
          obtain ⟨s₂, hrun₂, hA0, hA1, hA2, hA3, hreg, hA4, hA5, hfram⟩ :=
            ih t1 ([] : List (List Val)) ((r1 ++ ([] : List Val)) :: Racc) Z1 Z2 Z3 s₁.reg s₁.stk
              hlen' (by rw [hs₁0, h0]) hs₁1 (by rw [hs₁2]; exact h2) hs₁3 hinv' hs₁reg
          have hB0 : s₂.stk 0 = X 0 := by rw [hA0, hs₁0]
          have hB4 : s₂.stk 4 = X 4 := by rw [hA4, hs₁4]
          have hB5 : s₂.stk 5 = X 5 := by rw [hA5, hs₁5]
          have hBfram : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 →
              s₂.stk k = X k := by
            intro k hk0 hk1 hk2 hk3 hk4 hk5
            rw [hfram k hk0 hk1 hk2 hk3 hk4 hk5, hfr₁ k hk0 hk1 hk2 hk3 hk4 hk5]
          refine ⟨s₂, ?_, hB0, hA1, hA2, hA3, hreg, hB4, hB5, hBfram⟩
          · refine loopRuns.mono (by simp only [zIters]; omega)
              (loopRuns.cast (zIters_cn r1 t1).symm (loopRuns.concat (zIters t1 [])
                (loopRuns.one hF hEv₁) hrun₂)) ?_
            have hstep : zStepCost KA (r1 :: t1) ([] : List (List Val)) + 1 + zLoopCost KA t1 []
                ≤ zLoopCost KA (r1 :: t1) [] := by
              simpa using zLoopCost_step KA (r1 :: t1) ([] : List (List Val)) (Or.inl (by simp))
            omega
        · -- `r1 :: t1` vs `r2 :: t2`
          have h1' : X 1 = Glyph.cons :: ((ofList r1).enc ++
              ((ofList (t1.map ofList)).enc ++ Z1)) := by
            rw [h1, ofList_map_ofList_cons, List.cons_append, List.append_assoc]
          have h2' : X 2 = Glyph.cons :: ((ofList r2).enc ++
              ((ofList (t2.map ofList)).enc ++ Z2)) := by
            rw [h2, ofList_map_ofList_cons, List.cons_append, List.append_assoc]
          obtain ⟨s₁, n₁, hEv₁, hn₁, hs₁0, hs₁1, hs₁2, hs₁3, hs₁reg, hs₁4, hs₁5, hfr₁⟩ :=
            zipStepCC (main := main) (zApp := zApp) (KA := KA) hApp h0 h1' h2' h3
          have hinv' : ((r1 ++ r2) :: Racc).reverse ++ zipCat t1 t2 = C := by
            have hz : zipCat (r1 :: t1) (r2 :: t2) = (r1 ++ r2) :: zipCat t1 t2 := rfl
            have hrev : ((r1 ++ r2) :: Racc).reverse = Racc.reverse ++ [r1 ++ r2] :=
              List.reverse_cons ..
            rw [hrev, ← hinv, hz]
            simp
          have hlen' : t1.length + t2.length ≤ n := by
            simp only [List.length_cons] at hlen ⊢
            omega
          obtain ⟨s₂, hrun₂, hA0, hA1, hA2, hA3, hreg, hA4, hA5, hfram⟩ :=
            ih t1 t2 ((r1 ++ r2) :: Racc) Z1 Z2 Z3 s₁.reg s₁.stk
              hlen' (by rw [hs₁0, h0]) hs₁1 hs₁2 hs₁3 hinv' hs₁reg
          have hB0 : s₂.stk 0 = X 0 := by rw [hA0, hs₁0]
          have hB4 : s₂.stk 4 = X 4 := by rw [hA4, hs₁4]
          have hB5 : s₂.stk 5 = X 5 := by rw [hA5, hs₁5]
          have hBfram : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 →
              s₂.stk k = X k := by
            intro k hk0 hk1 hk2 hk3 hk4 hk5
            rw [hfram k hk0 hk1 hk2 hk3 hk4 hk5, hfr₁ k hk0 hk1 hk2 hk3 hk4 hk5]
          refine ⟨s₂, ?_, hB0, hA1, hA2, hA3, hreg, hB4, hB5, hBfram⟩
          · refine loopRuns.mono (by simp only [zIters]; omega)
              (loopRuns.cast (zIters_cc r1 r2 t1 t2).symm (loopRuns.concat (zIters t1 t2)
                (loopRuns.one hF hEv₁) hrun₂)) ?_
            have hstep : zStepCost KA (r1 :: t1) (r2 :: t2) + 1 + zLoopCost KA t1 t2
                ≤ zLoopCost KA (r1 :: t1) (r2 :: t2) := by
              simpa using zLoopCost_step KA (r1 :: t1) (r2 :: t2) (Or.inl (by simp))
            omega

/-! ## The assembly -/

/-- the setup of the `zipCat` word: move the two group values aside, push the empty accumulator and
set the loop flag -/
private def zSetup : Cmd :=
  seqs [mvVal 0 1 4 5, mvVal 0 2 4 5, pushConst 3 Glyph.nil, .set zF Glyph.cons]

/-- the tail of the `zipCat` word: drop the two leftover `nil`s, move the accumulator to the value
stack and reverse it -/
private def zFinish (revP : Cmd) : Cmd := seqs [.pop 1 rA, .pop 2 rA, mvVal 3 0 4 5, revP]

/-- the whole `zipCat` word -/
private def zipProg (zApp revP : Cmd) : Cmd := seqs [zSetup, zProg zApp, zFinish revP]

/-- the final cost arithmetic -/
private theorem zFinalBound (KA Krev A B n₁ n₂ n₃ n₈ n₉ : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h1 : n₁ ≤ 16 * (A + 1)) (h2 : n₂ ≤ 16 * (B + 1)) (h3 : n₃ ≤ 2)
    (h8 : n₈ ≤ 16 * (A + B + 1)) (h9 : n₉ ≤ Krev * (A + B + 1)) :
    n₁ + (n₂ + (n₃ + 1)) + (((KA + 101) * (A + B + 1) + 1) + (1 + (1 + (n₈ + n₉))))
      ≤ 1000 * (KA + Krev + 1000) * (A + B + 1) + 1000 * (KA + Krev + 1000) := by
  first
  | nlinarith [h1, h2, h3, h8, h9, hA, hB]
  | omega

theorem zipCatWord : ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (G₁ G₂ : List (List HvdH.Val)) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = Work.SynFFT.grpVal G₁ :: Work.SynFFT.grpVal G₂ :: rest)
        (fun _ out => out = Work.SynFFT.grpVal (Work.SynFFT.zipCat G₁ G₂) :: rest)
        (fun _ => K * (HvdH.vsz (Work.SynFFT.grpVal G₁) + HvdH.vsz (Work.SynFFT.grpVal G₂) + 1) + K) := by
  obtain ⟨zApp, KA, hAppA⟩ := Work.Layout.appendWord
  obtain ⟨revP, Krev, hRevA⟩ := Work.Layout.reverseWord
  refine ⟨zipProg zApp revP, 1000 * (KA + Krev + 1000), ?_⟩
  intro main G₁ G₂ rest vs hpre s R hR
  obtain rfl := hpre
  -- the append word, with the tail of the two values as an explicit parameter
  have hApp : ∀ (xs ys rest' : List Val), WordR main zApp
      (fun vs => vs = ofList xs :: ofList ys :: rest')
      (fun _ out => out = ofList (xs ++ ys) :: rest')
      (fun _ => KA * (vsz (ofList xs) + 1)) := by
    intro xs ys rest'
    refine Work.Kernel.WordR_conseq (hAppA main xs ys) (fun vs hv => ⟨rest', hv⟩) ?_
      (fun vs _ => le_rfl)
    intro vs out hv hQ
    obtain ⟨r, hr, hout⟩ := hQ
    have key : ofList xs :: ofList ys :: rest' = ofList xs :: ofList ys :: r := by rw [← hv, hr]
    have h2 : rest' = r := by
      have key' : ofList ys :: rest' = ofList ys :: r :=
        ((List.cons.injEq (ofList xs) (ofList ys :: rest') (ofList xs) (ofList ys :: r)).mp key).2
      exact ((List.cons.injEq (ofList ys) rest' (ofList ys) r).mp key').2
    rw [hout, h2]
  -- ## 1. setup: move the two group values aside, push `nil` on stack 3, set the flag
  have hX0 : s.stk 0 = (grpVal G₁).enc ++ ((grpVal G₂).enc ++ (encs rest ++ R)) := by
    rw [hR]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₁, n₁, hm1, hn1, hsU0, hsU1, hsU4, hsU5, hfU⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := grpVal G₁) (A := (grpVal G₂).enc ++ (encs rest ++ R))
      (B := s.stk 1) hX0 rfl
  obtain ⟨s₂, n₂, hm2, hn2, hsV0, hsV2, hsV4, hsV5, hfV⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 2) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := grpVal G₂) (A := encs rest ++ R) (B := s₁.stk 2)
      hsU0 rfl
  obtain ⟨s₃, n₃, hpc, hn3, hpc3, hpcO, -, -⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := 3) (cst := Glyph.nil) (g := s₂.reg) (X := s₂.stk)
  have hset : Ev main (.set zF Glyph.cons) s₃
      ⟨Function.update s₃.reg zF Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' main zF Glyph.cons s₃.reg s₃.stk
  have hSetup : Ev main zSetup s ⟨Function.update s₃.reg zF Glyph.cons, s₃.stk⟩
      (n₁ + (n₂ + (n₃ + 1))) := by
    unfold zSetup
    simp only [seqs]
    exact Ev.seq hm1 (Ev.seq hm2 (Ev.seq hpc hset))
  -- ## 2. the loop
  have hs12 : s₁.stk 2 = s.stk 2 := hfU 2 (by decide) (by decide) (by decide) (by decide)
  have hs13 : s₁.stk 3 = s.stk 3 := hfU 3 (by decide) (by decide) (by decide) (by decide)
  have hs23 : s₂.stk 3 = s₁.stk 3 := hfV 3 (by decide) (by decide) (by decide) (by decide)
  have hs34 : s₃.stk 4 = s.stk 4 := by
    rw [hpcO 4 (by decide), hsV4]
    exact hsU4
  have hs35 : s₃.stk 5 = s.stk 5 := by
    rw [hpcO 5 (by decide), hsV5]
    exact hsU5
  have hloop0 : s₃.stk 0 = encs rest ++ R := by
    rw [hpcO 0 (by decide)]
    exact hsV0
  have hloop1 : s₃.stk 1 = (ofList (G₁.map ofList)).enc ++ s.stk 1 := by
    rw [hpcO 1 (by decide), hfV 1 (by decide) (by decide) (by decide) (by decide), hsU1]
    rfl
  have hloop2 : s₃.stk 2 = (ofList (G₂.map ofList)).enc ++ s.stk 2 := by
    rw [hpcO 2 (by decide), hsV2, hs12]
    rfl
  have hloop3 : s₃.stk 3 = (ofList (([] : List (List Val)).map ofList)).enc ++ s.stk 3 := by
    rw [hpc3, hs23, hs13]
    rfl
  obtain ⟨s₅, hrun, hs₅0, hs₅1, hs₅2, hs₅3, hs₅reg, hs₅4, hs₅5, hfr₅⟩ :=
    zLoop_aux (main := main) (zApp := zApp) (KA := KA) hApp (zipCat G₁ G₂) rest R
      (G₁.length + G₂.length) G₁ G₂ [] (s.stk 1) (s.stk 2) (s.stk 3)
      (Function.update s₃.reg zF Glyph.cons) s₃.stk le_rfl hloop0 hloop1 hloop2 hloop3
      (by simp) (by simp)
  have hloopEv : Ev main (zProg zApp) ⟨Function.update s₃.reg zF Glyph.cons, s₃.stk⟩ s₅
      (zLoopCost KA G₁ G₂ + 1) :=
    loopRuns.eval hrun (by rw [hs₅reg]; decide)
  -- ## 3. drop the two leftover `nil`s
  set s₆ : State := ⟨Function.update s₅.reg rA ((s₅.stk 1).headD Glyph.eos),
      Function.update s₅.stk 1 (s₅.stk 1).tail⟩ with hs₆
  have hpop1 : Ev main (.pop 1 rA) s₅ s₆ 1 := by
    rw [hs₆]
    exact ev_pop' main 1 rA s₅.reg s₅.stk
  have hs₆k : ∀ k : Stk, k ≠ 1 → s₆.stk k = s₅.stk k := by
    intro k hk
    rw [hs₆]
    simp only [stk_mk]
    exact stkFn_ne s₅.stk hk (s₅.stk 1).tail
  have hs₆1 : s₆.stk 1 = s.stk 1 := by
    rw [hs₆]
    simp only [stk_mk, stkFn_same, hs₅1]
    rfl
  set s₇ : State := ⟨Function.update s₆.reg rA ((s₆.stk 2).headD Glyph.eos),
      Function.update s₆.stk 2 (s₆.stk 2).tail⟩ with hs₇
  have hpop2 : Ev main (.pop 2 rA) s₆ s₇ 1 := by
    rw [hs₇]
    exact ev_pop' main 2 rA s₆.reg s₆.stk
  have hs₇k : ∀ k : Stk, k ≠ 2 → s₇.stk k = s₆.stk k := by
    intro k hk
    rw [hs₇]
    simp only [stk_mk]
    exact stkFn_ne s₆.stk hk (s₆.stk 2).tail
  have hs₇2 : s₇.stk 2 = s.stk 2 := by
    rw [hs₇]
    simp only [stk_mk, stkFn_same, hs₆k 2 (by decide), hs₅2]
    rfl
  have hs₇0 : s₇.stk 0 = encs rest ++ R := by
    rw [hs₇k 0 (by decide), hs₆k 0 (by decide), hs₅0]
    exact hloop0
  have hs₇3 : s₇.stk 3 = (ofList ((zipCat G₁ G₂).reverse.map ofList)).enc ++ s.stk 3 := by
    rw [hs₇k 3 (by decide), hs₆k 3 (by decide)]
    exact hs₅3
  -- ## 4. move the accumulator to the value stack
  obtain ⟨s₈, n₈, hm8, hn8, hs₈3, hs₈0, hs₈4, hs₈5, hf₈⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 3) (b := 0) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₇.reg) (X := s₇.stk) (v := ofList ((zipCat G₁ G₂).reverse.map ofList))
      (A := s.stk 3) (B := encs rest ++ R) hs₇3 hs₇0
  -- ## 5. reverse the accumulator
  have hs₈0' : s₈.stk 0 = encs (ofList ((zipCat G₁ G₂).reverse.map ofList) :: rest) ++ R := by
    rw [hs₈0]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨out₉, s₉, n₉, hpost₉, hev₉, hn₉, hs₉0, hoth₉⟩ :=
    hRevA main ((zipCat G₁ G₂).reverse.map ofList)
      (ofList ((zipCat G₁ G₂).reverse.map ofList) :: rest) ⟨rest, rfl⟩ s₈ R hs₈0'
  obtain ⟨rest₉, hpre₉, hout₉⟩ := hpost₉
  have hrest₉ : rest = rest₉ :=
    ((List.cons.injEq (ofList ((zipCat G₁ G₂).reverse.map ofList)) rest _ _).mp hpre₉).2
  have hout : out₉ = grpVal (zipCat G₁ G₂) :: rest := by
    rw [hout₉, ← hrest₉]
    simp only [List.map_reverse, List.reverse_reverse, grpVal]
  have hFinish : Ev main (zFinish revP) s₅ s₉ (1 + (1 + (n₈ + n₉))) := by
    unfold zFinish
    simp only [seqs]
    exact Ev.seq hpop1 (Ev.seq hpop2 (Ev.seq hm8 ⟨n₉, hev₉, le_rfl⟩))
  have hAll : Ev main (zipProg zApp revP) s s₉
      ((n₁ + (n₂ + (n₃ + 1))) + ((zLoopCost KA G₁ G₂ + 1) + (1 + (1 + (n₈ + n₉))))) := by
    unfold zipProg
    simp only [seqs]
    exact Ev.seq hSetup (Ev.seq hloopEv hFinish)
  obtain ⟨n, hEval, hnle⟩ := hAll
  -- ## 6. the final frame
  have hframe : ∀ k : Stk, k ≠ 0 → s₉.stk k = s.stk k := by
    intro k hk
    rw [hoth₉ k hk]
    by_cases hk1 : k = 1
    · subst hk1
      rw [hf₈ 1 (by decide) (by decide) (by decide) (by decide), hs₇k 1 (by decide)]
      exact hs₆1
    by_cases hk2 : k = 2
    · subst hk2
      rw [hf₈ 2 (by decide) (by decide) (by decide) (by decide)]
      exact hs₇2
    by_cases hk3 : k = 3
    · subst hk3
      exact hs₈3
    by_cases hk4 : k = 4
    · subst hk4
      rw [hs₈4, hs₇k 4 (by decide), hs₆k 4 (by decide), hs₅4]
      exact hs34
    by_cases hk5 : k = 5
    · subst hk5
      rw [hs₈5, hs₇k 5 (by decide), hs₆k 5 (by decide), hs₅5]
      exact hs35
    · rw [hf₈ k hk3 hk hk4 hk5, hs₇k k hk2, hs₆k k hk1,
        hfr₅ k hk hk1 hk2 hk3 hk4 hk5, hpcO k hk3, hfV k hk hk2 hk4 hk5,
        hfU k hk hk1 hk4 hk5]
  -- ## 7. the cost bound
  have hZle : vsz (ofList ((zipCat G₁ G₂).reverse.map ofList))
      ≤ vsz (grpVal G₁) + vsz (grpVal G₂) := by
    have hZ1 : vsz (ofList ((zipCat G₁ G₂).reverse.map ofList))
        = vsz (grpVal ((zipCat G₁ G₂).reverse)) := rfl
    rw [hZ1, vsz_grpVal_reverse]
    exact vsz_grpVal_le_zipCat G₁ G₂
  have hbound : n ≤ 1000 * (KA + Krev + 1000) *
      (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + 1000 * (KA + Krev + 1000) := by
    have h8 : n₈ ≤ 16 * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) := by
      have := hn8
      omega
    have h9 : n₉ ≤ Krev * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) :=
      le_trans hn₉ (Nat.mul_le_mul_left Krev (by omega))
    have h1 : n₁ ≤ 16 * (vsz (grpVal G₁) + 1) := hn1
    have h2 : n₂ ≤ 16 * (vsz (grpVal G₂) + 1) := hn2
    have h3 : n₃ ≤ 2 := hn3
    have hA : 1 ≤ vsz (grpVal G₁) := one_le_vsz _
    have hB : 1 ≤ vsz (grpVal G₂) := one_le_vsz _
    have hloop : zLoopCost KA G₁ G₂
        = (KA + 101) * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) := rfl
    rw [hloop] at hnle
    exact le_trans hnle
      (zFinalBound KA Krev (vsz (grpVal G₁)) (vsz (grpVal G₂)) n₁ n₂ n₃ n₈ n₉
        hA hB h1 h2 h3 h8 h9)
  refine ⟨grpVal (zipCat G₁ G₂) :: rest, s₉, n, rfl, hEval, hbound, ?_, hframe⟩
  rw [hs₉0, hout]

end Work.SynFFT
