import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbStacks
import Submission.Work.Resample.pbWords
import Submission.Work.Resample.auCS_dropTopStk
import Submission.Work.Resample.pbCostDefs
import Submission.Work.ConvR.sizes

/-!
# The frame cleanup of `progTensorB` (`Work.Resample.pbClr`)

After the epilogue of `progTensorB` only stack 0 carries data: the result array, the marker `M` and
the honest suffix `rest`.  The auxiliary stacks `1, …, 13` still hold the leftovers of the round
loop, as described by `Work.Resample.PBStacks` at round `D`:

* stack `2` holds `intList (ts.drop D)`, stack `3` holds `intList (ss.drop D)`,
* stack `4` holds `α`, stack `5` holds `p`,
* stack `6` holds `∏ (ss.take D)`, stack `7` holds `∏ (ts.drop D)`, stack `12` holds `M`,
* every other non-zero stack is empty.

The cleanup word `clr = killChain pbClrPairs` empties exactly those seven stacks, one value at a
time: the single-value word `pbKillP src` moves the top value of stack `src` onto stack 0
(`auCS_dropTopStk`) and `Work.Kernel.dropValue` removes it again, at cost `O(vsz v + 1)` per value.
`killChain_spec` is the list induction that composes these words and adds up their costs; `pbClr`
instantiates it and discharges the cost estimate against the bracket `BrClr` of
`Submission/Work/Resample/pbCostDefs.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Resample

open HvdH

/-! ## Killing a single value of a non-zero stack -/

/-- Emptying a non-zero stack `src` that holds exactly one value `v`, leaving the value stack and
every other non-zero stack untouched.  Derived from `auCS_dropTopStk` (which keeps an arbitrary
tail `L` on `src`): instantiate the tail with `[]` and the value stack with itself. -/
theorem pbKillOne (src : Stk) (hsrc : src ≠ 0) :
    ∃ (prog : Cmd) (Kf : ℕ), ∀ (main : Cmd) (v : Val),
      WordM main prog
        (fun vs a => a src = v :: [])
        (fun vs a out b => out = vs ∧ b src = [] ∧
          (∀ k : Stk, k ≠ 0 → k ≠ src → b k = a k))
        (fun _ _ => Kf * (vsz v + 1)) := by
  obtain ⟨prog, K, h⟩ := auCS_dropTopStk src hsrc
  refine ⟨prog, K, fun main v => ?_⟩
  intro vs a hpre s R Bg h0 hk
  exact h main v [] vs vs a ⟨rfl, hpre⟩ s R Bg h0 hk

/-- The cleanup word for a single source stack. -/
noncomputable def pbKillP (src : Stk) (h : src ≠ 0) : Cmd := (pbKillOne src h).choose

/-- Its cost constant. -/
noncomputable def pbKf (src : Stk) : ℕ :=
  if h : src ≠ 0 then (pbKillOne src h).choose_spec.choose else 0

/-- The specification of `pbKillP src`. -/
theorem pbKillSpec (src : Stk) (h : src ≠ 0) (main : Cmd) (v : Val) :
    WordM main (pbKillP src h)
      (fun vs a => a src = v :: [])
      (fun vs a out b => out = vs ∧ b src = [] ∧
        (∀ k : Stk, k ≠ 0 → k ≠ src → b k = a k))
      (fun _ _ => pbKf src * (vsz v + 1)) := by
  have hspec := (pbKillOne src h).choose_spec.choose_spec main v
  have hval : pbKf src = (pbKillOne src h).choose_spec.choose := by
    simp only [pbKf]
    exact dite_eq_left h
  rw [hval]
  exact hspec

/-! ## Composing words along a list of sources -/

/-- The right-nested composition of the words of a list, in the order of the list. -/
def killChain : List (Stk × Cmd) → Cmd
  | [] => Cmd.skip
  | q :: rest => Cmd.seq q.2 (killChain rest)

@[simp] theorem killChain_nil : killChain [] = Cmd.skip := rfl

@[simp] theorem killChain_cons (q : Stk × Cmd) (rest : List (Stk × Cmd)) :
    killChain (q :: rest) = Cmd.seq q.2 (killChain rest) := rfl

/-- `WordM.seq` with the precondition of the first word available when proving the hypotheses of
the composition: the cleanup passes the *values* it has just read from the precondition on to the
recursive call, which `WordM.seq` alone does not allow. -/
theorem seqPre {main : Cmd} {p q : Cmd}
    {Pre₁ : List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ : List Val → (Stk → List Val) → ℕ} {C₂ : List Val → (Stk → List Val) → ℕ}
    {B : List Val → (Stk → List Val) → ℕ}
    (h₁ : WordM main p Pre₁ Post₁ C₁) (h₂ : WordM main q Pre₂ Post₂ C₂)
    (hpre : ∀ vs a mid a', Pre₁ vs a → Post₁ vs a mid a' → Pre₂ mid a')
    (hcost : ∀ vs a mid a', Pre₁ vs a → Post₁ vs a mid a' → C₂ mid a' ≤ B vs a) :
    WordM main (.seq p q) Pre₁
      (fun vs a out b => ∃ mid a', Post₁ vs a mid a' ∧ Post₂ mid a' out b)
      (fun vs a => C₁ vs a + B vs a) := by
  intro vs a hPre s R Bg h0 hk
  obtain ⟨mid, a', s', n₁, hP₁, hev₁, hc₁, h0', hk'⟩ := h₁ vs a hPre s R Bg h0 hk
  obtain ⟨out, b, s'', n₂, hP₂, hev₂, hc₂, h0'', hk''⟩ :=
    h₂ mid a' (hpre vs a mid a' hPre hP₁) s' R Bg h0' hk'
  refine ⟨out, b, s'', n₁ + n₂, ⟨mid, a', hP₁, hP₂⟩, Eval.seq hev₁ hev₂, ?_, h0'', hk''⟩
  exact Nat.add_le_add hc₁ (le_trans hc₂ (hcost vs a mid a' hPre hP₁))

/-- A source stack together with the word that empties it and the value it holds. -/
structure KillSpec where
  /-- the source stack -/
  src : Stk
  /-- the word emptying it -/
  prog : Cmd
  /-- the value it holds -/
  val : Val

/-- The precondition of the chain: the source stacks of `l` hold exactly the values recorded in
`l`, and every other non-zero stack is empty. -/
def KillPre (l : List KillSpec) : List Val → (Stk → List Val) → Prop :=
  fun _ a => (∀ q ∈ l, a q.src = q.val :: []) ∧
    (∀ k : Stk, k ≠ 0 → k ∉ l.map KillSpec.src → a k = [])

/-- The list induction behind `pbClr`: given the single-value words of the members of `l`, the
composition `killChain (l.map (·.src, ·.prog))` empties all the source stacks of `l` at cost
`O((Σ K) · (Σ vsz + 1))`. -/
theorem killChain_spec (Kf : Stk → ℕ) :
    ∀ (l : List KillSpec), (l.map KillSpec.src).Nodup → (∀ q ∈ l, q.src ≠ 0) →
    (∀ q ∈ l, ∀ (main : Cmd) (v : Val),
      WordM main q.prog
        (fun vs a => a q.src = v :: [])
        (fun vs a out b => out = vs ∧ b q.src = [] ∧
          (∀ k : Stk, k ≠ 0 → k ≠ q.src → b k = a k))
        (fun _ _ => Kf q.src * (vsz v + 1))) →
    ∀ (main : Cmd),
      WordM main (killChain (l.map (fun q => (q.src, q.prog)))) (KillPre l)
        (fun vs a out b => out = vs ∧ (∀ k : Stk, k ≠ 0 → b k = []))
        (fun _ _ => ((l.map (fun q => Kf q.src)).sum + 1) *
          ((l.map (fun q => vsz q.val + 1)).sum + 1)) := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ main vs a hpre s R Bg h0 hk
    refine ⟨vs, a, s, 1, ⟨rfl, ?_⟩, Eval.skip s, ?_, h0, hk⟩
    · intro k hk0
      simp only [KillPre] at hpre
      exact hpre.2 k hk0 (by simp)
    · simp
  | cons q₀ rest ih =>
    intro hnd hnz hkill main
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
    have hnz' : ∀ q ∈ rest, q.src ≠ 0 := fun q hq => hnz q (List.mem_cons_of_mem q₀ hq)
    have hkill' : ∀ q ∈ rest, ∀ (main : Cmd) (v : Val),
        WordM main q.prog (fun vs a => a q.src = v :: [])
          (fun vs a out b => out = vs ∧ b q.src = [] ∧
            (∀ k : Stk, k ≠ 0 → k ≠ q.src → b k = a k))
          (fun _ _ => Kf q.src * (vsz v + 1)) :=
      fun q hq => hkill q (List.mem_cons_of_mem q₀ hq)
    have h₁ : WordM main q₀.prog (fun vs a => a q₀.src = q₀.val :: [])
        (fun vs a out b => out = vs ∧ b q₀.src = [] ∧
          (∀ k : Stk, k ≠ 0 → k ≠ q₀.src → b k = a k))
        (fun _ _ => Kf q₀.src * (vsz q₀.val + 1)) := hkill q₀ (by simp) main q₀.val
    -- strengthen the precondition of the first word to the precondition of the whole chain
    have h₁T : WordM main q₀.prog (KillPre (q₀ :: rest))
        (fun vs a out b => out = vs ∧ b q₀.src = [] ∧
          (∀ k : Stk, k ≠ 0 → k ≠ q₀.src → b k = a k))
        (fun _ _ => Kf q₀.src * (vsz q₀.val + 1)) :=
      WordM.conseq h₁ (fun vs a hp => by
        simp only [KillPre] at hp
        exact hp.1 q₀ (by simp)) (fun vs a out b _ h => h) (fun vs a _ => le_rfl)
    have h₂ : WordM main (killChain (rest.map (fun q => (q.src, q.prog)))) (KillPre rest)
        (fun vs a out b => out = vs ∧ (∀ k : Stk, k ≠ 0 → b k = []))
        (fun _ _ => ((rest.map (fun q => Kf q.src)).sum + 1) *
          ((rest.map (fun q => vsz q.val + 1)).sum + 1)) := ih hnd' hnz' hkill' main
    have hprog : killChain ((q₀ :: rest).map (fun q => (q.src, q.prog))) =
        Cmd.seq q₀.prog (killChain (rest.map (fun q => (q.src, q.prog)))) := rfl
    rw [hprog]
    refine WordM.conseq (h := seqPre (h₁ := h₁T) (h₂ := h₂)
      (B := fun _ _ => ((rest.map (fun q => Kf q.src)).sum + 1) *
        ((rest.map (fun q => vsz q.val + 1)).sum + 1)) ?_ ?_) ?_ ?_ ?_
    · intro vs a mid a' hp hp1
      simp only [KillPre] at hp ⊢
      obtain ⟨-, hkilld, hagree⟩ := hp1
      refine ⟨?_, ?_⟩
      · intro q hq
        have hq0 : q.src ≠ 0 := hnz q (List.mem_cons_of_mem q₀ hq)
        have hqne : q.src ≠ q₀.src := by
          intro hcon
          exact hnotin (hcon ▸ List.mem_map_of_mem hq)
        rw [hagree q.src hq0 hqne]
        exact hp.1 q (List.mem_cons_of_mem q₀ hq)
      · intro k hk0 hknot
        by_cases hkq : k = q₀.src
        · rw [hkq]
          exact hkilld
        · rw [hagree k hk0 hkq]
          exact hp.2 k hk0 (by
            rw [List.map_cons]
            intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · exact hkq h
            · exact hknot h)
    · intro vs a mid a' hp hp1
      exact le_rfl
    · intro vs a hp
      exact hp
    · intro vs a out b hp hpost
      obtain ⟨mid, a', hp1, hp2⟩ := hpost
      obtain ⟨hmid, -, -⟩ := hp1
      obtain ⟨hout, hb⟩ := hp2
      exact ⟨by rw [hout, hmid], hb⟩
    · intro vs a hp
      simp only [List.map_cons, List.sum_cons]
      set A := Kf q₀.src
      set V := vsz q₀.val + 1
      set S := (rest.map (fun q => Kf q.src)).sum
      set W := (rest.map (fun q => vsz q.val + 1)).sum
      have h1' : A * V ≤ A * (V + W + 1) := Nat.mul_le_mul_left A (by omega)
      have h2' : (S + 1) * (W + 1) ≤ (S + 1) * (V + W + 1) :=
        Nat.mul_le_mul_left (S + 1) (by omega)
      calc A * V + (S + 1) * (W + 1) ≤ A * (V + W + 1) + (S + 1) * (V + W + 1) :=
            add_le_add h1' h2'
        _ = (A + S + 1) * (V + W + 1) := by ring

/-! ## The concrete cleanup word -/

theorem hne2 : (2 : Stk) ≠ 0 := by decide
theorem hne3 : (3 : Stk) ≠ 0 := by decide
theorem hne4 : (4 : Stk) ≠ 0 := by decide
theorem hne5 : (5 : Stk) ≠ 0 := by decide
theorem hne6 : (6 : Stk) ≠ 0 := by decide
theorem hne7 : (7 : Stk) ≠ 0 := by decide
theorem hne12 : (12 : Stk) ≠ 0 := by decide

/-- The source stacks emptied by the cleanup, with their words. -/
noncomputable def pbClrPairs : List (Stk × Cmd) :=
  [(2, pbKillP 2 hne2), (3, pbKillP 3 hne3), (4, pbKillP 4 hne4), (5, pbKillP 5 hne5),
   (6, pbKillP 6 hne6), (7, pbKillP 7 hne7), (12, pbKillP 12 hne12)]

/-- The source stacks emptied by the cleanup, with their words and the values they hold in the
`PBStacks` invariant at round `D`. -/
noncomputable def pbClrSpecs (ss ts : List ℕ) (p α : ℕ) (M : Val) : List KillSpec :=
  [⟨2, pbKillP 2 hne2, intList (ts.drop D)⟩,
   ⟨3, pbKillP 3 hne3, intList (ss.drop D)⟩,
   ⟨4, pbKillP 4 hne4, Val.int (α : ℤ)⟩,
   ⟨5, pbKillP 5 hne5, Val.int (p : ℤ)⟩,
   ⟨6, pbKillP 6 hne6, Val.int (((ss.take D).prod : ℕ) : ℤ)⟩,
   ⟨7, pbKillP 7 hne7, Val.int (((ts.drop D).prod : ℕ) : ℤ)⟩,
   ⟨12, pbKillP 12 hne12, M⟩]

/-- The word of the cleanup. -/
noncomputable def pbClrProg : Cmd := killChain pbClrPairs

/-- `PBStacks` at round `D` gives exactly the precondition of `killChain_spec` on `pbClrSpecs`. -/
theorem pbStacks_pre (ss ts : List ℕ) (p α : ℕ) (M : Val) (a : Stk → List Val)
    (h : PBStacks ss ts p α M D a) :
    (∀ q ∈ pbClrSpecs ss ts p α M, a q.src = q.val :: []) ∧
    (∀ k : Stk, k ≠ 0 → k ∉ (pbClrSpecs ss ts p α M).map KillSpec.src → a k = []) := by
  rw [PBStacks] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hrest⟩ := h
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [pbClrSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h12
  · intro k hk0 hknot
    have hsrcs : (pbClrSpecs ss ts p α M).map KillSpec.src =
        [(2 : Stk), 3, 4, 5, 6, 7, 12] := rfl
    rw [hsrcs] at hknot
    fin_cases k
    · exact absurd rfl hk0
    · exact h1
    · exact absurd (by decide) hknot
    · exact absurd (by decide) hknot
    · exact absurd (by decide) hknot
    · exact absurd (by decide) hknot
    · exact absurd (by decide) hknot
    · exact absurd (by decide) hknot
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact absurd (by decide) hknot
    · exact h13
    · exact hrest 14 hk0 (by decide)
    · exact hrest 15 hk0 (by decide)

/-- The encoded size of the tail of a list is at most the encoded size of the list. -/
theorem vsz_intList_drop_le (l : List ℕ) (n : ℕ) :
    vsz (intList (l.drop n)) ≤ vsz (intList l) := by
  induction l generalizing n with
  | nil => simp
  | cons t ts ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.drop_succ_cons]
      rw [Work.ConvR.vsz_intList_cons]
      have h := ih m
      generalize hX : vsz (intList (ts.drop m)) = X at h
      omega

theorem pbClr (KL : HvdH.KernelLib) (Kb : ℕ) :
    ∃ (clr : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ)
      (ss ts : List ℕ) (M : HvdH.Val) (rest : List HvdH.Val),
      HvdH.ResParams p α ss ts →
      Work.Resample.WordM main clr
        (fun vs a => ∃ (ws : List (ℤ × ℤ)), vs = HvdH.cvecVal ws :: rest ∧
          Work.Resample.PBStacks ss ts p α M HvdH.D a)
        (fun vs a out b => out = vs ∧ (∀ k : HvdH.Stk, k ≠ 0 → b k = []))
        (fun _ _ => Kc * (HvdH.vsz M + HvdH.vsz (HvdH.intList ts) + HvdH.vsz (HvdH.intList ss) +
          HvdH.vsz (HvdH.Val.int ((ss.take HvdH.D).prod)) + HvdH.vsz (HvdH.Val.int ((ts.drop HvdH.D).prod)) +
          HvdH.vsz (HvdH.Val.int p) + HvdH.vsz (HvdH.Val.int α) + 100)) := by
  refine ⟨pbClrProg, 9 * ((pbClrPairs.map (fun q => pbKf q.1)).sum + 1), ?_⟩
  intro main N Cm p α ss ts M rest _hRP
  have hnd : ((pbClrSpecs ss ts p α M).map KillSpec.src).Nodup := by
    rw [show (pbClrSpecs ss ts p α M).map KillSpec.src = [(2 : Stk), 3, 4, 5, 6, 7, 12] from rfl]
    decide
  have hnz : ∀ q ∈ pbClrSpecs ss ts p α M, q.src ≠ 0 := by
    intro q hq
    simp only [pbClrSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hne2
    · exact hne3
    · exact hne4
    · exact hne5
    · exact hne6
    · exact hne7
    · exact hne12
  have hkil : ∀ q ∈ pbClrSpecs ss ts p α M, ∀ (main : Cmd) (v : Val),
      WordM main q.prog (fun vs a => a q.src = v :: [])
        (fun vs a out b => out = vs ∧ b q.src = [] ∧
          (∀ k : Stk, k ≠ 0 → k ≠ q.src → b k = a k))
        (fun _ _ => pbKf q.src * (vsz v + 1)) := by
    intro q hq
    simp only [pbClrSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact fun main v => pbKillSpec 2 hne2 main v
        | exact fun main v => pbKillSpec 3 hne3 main v
        | exact fun main v => pbKillSpec 4 hne4 main v
        | exact fun main v => pbKillSpec 5 hne5 main v
        | exact fun main v => pbKillSpec 6 hne6 main v
        | exact fun main v => pbKillSpec 7 hne7 main v
        | exact fun main v => pbKillSpec 12 hne12 main v
  have hchain := killChain_spec pbKf (pbClrSpecs ss ts p α M) hnd hnz hkil main
  have hmap : (pbClrSpecs ss ts p α M).map (fun q => (q.src, q.prog)) = pbClrPairs := rfl
  rw [hmap] at hchain
  refine WordM.conseq (h := hchain) ?_ ?_ ?_
  · rintro vs a ⟨ws, rfl, hPS⟩
    exact pbStacks_pre ss ts p α M a hPS
  · intro vs a out b hp hpost
    exact hpost
  · intro vs a hp
    have hKsum : ((pbClrSpecs ss ts p α M).map (fun q => pbKf q.src)).sum =
        (pbClrPairs.map (fun q => pbKf q.1)).sum := rfl
    have hvsum : ((pbClrSpecs ss ts p α M).map (fun q => vsz q.val + 1)).sum + 1 ≤
        BrClr p α ss ts M + 8 := by
      simp only [pbClrSpecs, BrClr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      have hd1 := vsz_intList_drop_le ts D
      have hd2 := vsz_intList_drop_le ss D
      omega
    have hBr1 : 1 ≤ BrClr p α ss ts M := by
      simp only [BrClr]
      omega
    rw [hKsum]
    refine le_trans (Nat.mul_le_mul_left _ hvsum) ?_
    have h8 : BrClr p α ss ts M + 8 ≤ 9 * BrClr p α ss ts M := by omega
    calc ((pbClrPairs.map (fun q => pbKf q.1)).sum + 1) * (BrClr p α ss ts M + 8)
        ≤ ((pbClrPairs.map (fun q => pbKf q.1)).sum + 1) * (9 * BrClr p α ss ts M) :=
          Nat.mul_le_mul_left _ h8
      _ = 9 * ((pbClrPairs.map (fun q => pbKf q.1)).sum + 1) * BrClr p α ss ts M := by ring

end Work.Resample
