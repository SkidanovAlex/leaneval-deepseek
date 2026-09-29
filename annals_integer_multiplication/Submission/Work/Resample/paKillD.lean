import Mathlib
import Submission.Work.Resample.pbClr
import Submission.Work.Resample.paDefs

/-!
# The frame cleanup of `progTensorA` (`Work.Resample.paKillD`)

The `Ã` half of the tensoring program leaves, after its epilogue, the leftover dimension data on
the auxiliary stacks `2, …, 6`:

* stack `2` holds `intList (ss.drop D)`, stack `3` holds `intList (ts.drop D)`,
* stack `4` holds `α`, stack `5` holds `p`, stack `6` holds `∏ (ts.take D)`,

and every other non-zero stack is empty.  The cleanup word empties exactly those five stacks one
value at a time, reusing the single-value word `pbKillP` of `Submission/Work/Resample/pbClr.lean`
and the list induction `killChain_spec` proved there.  The cost is linear in the total encoded size
of the five values.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-! ## The cleanup of the `Ã` leftovers -/

/-- The five source stacks of the `Ã` cleanup, each with the word that empties it and the value it
holds after the epilogue of `progTensorA`. -/
noncomputable def paKillSpecs (ss ts : List ℕ) (p α : ℕ) : List KillSpec :=
  [⟨2, pbKillP 2 hne2, intList (ss.drop D)⟩,
   ⟨3, pbKillP 3 hne3, intList (ts.drop D)⟩,
   ⟨4, pbKillP 4 hne4, Val.int (α : ℤ)⟩,
   ⟨5, pbKillP 5 hne5, Val.int (p : ℤ)⟩,
   ⟨6, pbKillP 6 hne6, Val.int (((ts.take D).prod : ℕ) : ℤ)⟩]

/-- The same list, projected to the `(stack, word)` pairs the chain runs. -/
noncomputable def paKillPairs : List (Stk × Cmd) :=
  [(2, pbKillP 2 hne2), (3, pbKillP 3 hne3), (4, pbKillP 4 hne4), (5, pbKillP 5 hne5),
   (6, pbKillP 6 hne6)]

/-- The cleanup word of the `Ã` half. -/
noncomputable def paKillProg : Cmd := killChain paKillPairs

/-- The projection identity: the chain of `paKillSpecs` is `paKillProg`, independently of the
parameters. -/
theorem paKillSpecs_map (ss ts : List ℕ) (p α : ℕ) :
    (paKillSpecs ss ts p α).map (fun q => (q.src, q.prog)) = paKillPairs := rfl

/-- `List`-membership in the source list implies `Finset`-membership of the coercion. -/
theorem paKill_mem_finset (k : Stk) :
    k ∉ ([(2 : Stk), 3, 4, 5, 6] : List Stk) → (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) := by
  fin_cases k <;> decide

/-- The precondition of the `Ã` cleanup, in the `KillPre` form consumed by `killChain_spec`. -/
theorem paKillPre_of {ss ts : List ℕ} {p α : ℕ} {a : Stk → List Val} (vs : List Val)
    (h2 : a 2 = [intList (ss.drop D)]) (h3 : a 3 = [intList (ts.drop D)])
    (h4 : a 4 = [Val.int (α : ℤ)]) (h5 : a 5 = [Val.int (p : ℤ)])
    (h6 : a 6 = [Val.int (((ts.take D).prod : ℕ) : ℤ)])
    (hrest : ∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) → a k = []) :
    KillPre (paKillSpecs ss ts p α) vs a := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [paKillSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  · intro k hk0 hknot
    have hsrcs : (paKillSpecs ss ts p α).map KillSpec.src = [(2 : Stk), 3, 4, 5, 6] := rfl
    rw [hsrcs] at hknot
    exact hrest k hk0 (paKill_mem_finset k hknot)

/-- The five source stacks of the cleanup are pairwise distinct and non-zero. -/
theorem paKill_nodup (ss ts : List ℕ) (p α : ℕ) :
    ((paKillSpecs ss ts p α).map KillSpec.src).Nodup := by
  rw [show (paKillSpecs ss ts p α).map KillSpec.src = [(2 : Stk), 3, 4, 5, 6] from rfl]
  decide

theorem paKill_ne_zero (ss ts : List ℕ) (p α : ℕ) :
    ∀ q ∈ paKillSpecs ss ts p α, q.src ≠ 0 := by
  intro q hq
  simp only [paKillSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hne2
  · exact hne3
  · exact hne4
  · exact hne5
  · exact hne6

/-- Each member of `paKillSpecs` is emptied by its word at cost `O(vsz v + 1)`. -/
theorem paKill_kill (ss ts : List ℕ) (p α : ℕ) : ∀ q ∈ paKillSpecs ss ts p α, ∀ (main : Cmd) (v : Val),
    WordM main q.prog (fun vs a => a q.src = v :: [])
      (fun vs a out b => out = vs ∧ b q.src = [] ∧
        (∀ k : Stk, k ≠ 0 → k ≠ q.src → b k = a k))
      (fun _ _ => pbKf q.src * (vsz v + 1)) := by
  intro q hq
  simp only [paKillSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact fun main v => pbKillSpec 2 hne2 main v
      | exact fun main v => pbKillSpec 3 hne3 main v
      | exact fun main v => pbKillSpec 4 hne4 main v
      | exact fun main v => pbKillSpec 5 hne5 main v
      | exact fun main v => pbKillSpec 6 hne6 main v

/-- The cost of the chain is exactly `Kf` times the requested bound. -/
theorem paKill_cost (ss ts : List ℕ) (p α : ℕ) :
    ((paKillSpecs ss ts p α).map (fun q => vsz q.val + 1)).sum + 1 ≤
      vsz (intList (ss.drop D)) + vsz (intList (ts.drop D)) + vsz (Val.int (α : ℤ)) +
        vsz (Val.int (p : ℤ)) + vsz (Val.int (((ts.take D).prod : ℕ) : ℤ)) + 6 := by
  simp only [paKillSpecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem paKillD :
    ∃ (kill : HvdH.Cmd) (Kf : ℕ),
      ∀ (main : HvdH.Cmd) (p α : ℕ) (ss ts : List ℕ),
      Work.Resample.WordM main kill
        (fun _ a => a 2 = [HvdH.intList (ss.drop HvdH.D)] ∧
          a 3 = [HvdH.intList (ts.drop HvdH.D)] ∧
          a 4 = [HvdH.Val.int (α : ℤ)] ∧ a 5 = [HvdH.Val.int (p : ℤ)] ∧
          a 6 = [HvdH.Val.int (((ts.take HvdH.D).prod : ℕ) : ℤ)] ∧
          (∀ k : HvdH.Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) → a k = []))
        (fun vs a out b => out = vs ∧ (∀ k : HvdH.Stk, k ≠ 0 → b k = []))
        (fun _ _ => Kf * (HvdH.vsz (HvdH.intList (ss.drop HvdH.D)) +
          HvdH.vsz (HvdH.intList (ts.drop HvdH.D)) + HvdH.vsz (HvdH.Val.int (α : ℤ)) +
          HvdH.vsz (HvdH.Val.int (p : ℤ)) +
          HvdH.vsz (HvdH.Val.int (((ts.take HvdH.D).prod : ℕ) : ℤ)) + 6)) := by
  refine ⟨paKillProg, (paKillPairs.map (fun q => pbKf q.1)).sum + 1, ?_⟩
  intro main p α ss ts
  have hchain := killChain_spec pbKf (paKillSpecs ss ts p α) (paKill_nodup ss ts p α)
    (paKill_ne_zero (ss := ss) (ts := ts) (p := p) (α := α))
    (paKill_kill ss ts p α) main
  rw [paKillSpecs_map] at hchain
  refine WordM.conseq (h := hchain) ?_ ?_ ?_
  · intro vs a hp
    obtain ⟨h2, h3, h4, h5, h6, hrest⟩ := hp
    exact paKillPre_of vs h2 h3 h4 h5 h6 hrest
  · intro vs a out b hp hpost
    exact hpost
  · intro vs a hp
    have hmap : (paKillSpecs ss ts p α).map (fun q => pbKf q.src) =
        paKillPairs.map (fun q => pbKf q.1) := rfl
    rw [hmap]
    exact Nat.mul_le_mul_left _ (paKill_cost ss ts p α)

end Work.Resample
