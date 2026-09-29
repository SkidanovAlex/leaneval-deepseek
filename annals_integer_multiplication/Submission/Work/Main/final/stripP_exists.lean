import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.glue

namespace Work.Main.final

open HvdH

/-! `stripP_exists`: the program that removes the *third* value of the value stack.

`KernelLib.roll 2` moves the third value to the top (cost `O(vsz a + vsz b + vsz v)` for a stack
`a :: b :: v :: rest`) and `KernelLib.drop` removes it, giving `a :: b :: rest`. -/

/-- `getD 2` on a list with at least three elements. -/
theorem stripP_getD_two (a b v : Val) (rest : List Val) :
    (a :: b :: v :: rest).getD 2 .nil = v := by
  simp

/-- `eraseIdx 2` on a list with at least three elements. -/
theorem stripP_eraseIdx_two (a b v : Val) (rest : List Val) :
    (a :: b :: v :: rest).eraseIdx 2 = a :: b :: rest := by
  simp

/-- Cost arithmetic: `roll 2` followed by `drop` fits the claimed constant. -/
theorem stripP_cost_le (Kr Kd A B V : ℕ) :
    3 * Kr * (A + B + V + 1) + Kd * (V + 1) ≤ (3 * Kr + Kd) * (A + B + V + 1) := by
  have hV : Kd * (V + 1) ≤ Kd * (A + B + V + 1) := Nat.mul_le_mul_left Kd (by omega)
  rw [Nat.add_mul]
  exact Nat.add_le_add_left hV (3 * Kr * (A + B + V + 1))

theorem stripP_exists (hKer : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (C : ℕ), ∀ (main : HvdH.Cmd) (a b v : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog (fun vs => vs = a :: b :: v :: rest) (fun _ out => out = a :: b :: rest)
        (fun _ => C * (HvdH.vsz a + HvdH.vsz b + HvdH.vsz v + 1)) := by
  obtain ⟨rollProg, Kr, hroll⟩ := hKer.roll
  obtain ⟨dropProg, Kd, hdrop⟩ := hKer.drop
  refine ⟨Cmd.seq (rollProg 2) dropProg, 3 * Kr + Kd, ?_⟩
  intro main a b v rest
  -- 1. `roll 2` : `a :: b :: v :: rest ↦ v :: a :: b :: rest`
  have h1 : WordR main (rollProg 2) (fun vs => vs = a :: b :: v :: rest)
      (fun _ out => out = v :: a :: b :: rest)
      (fun _ => 3 * Kr * (vsz a + vsz b + vsz v + 1)) := by
    refine conseq' hKer (hroll main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout, stripP_getD_two, stripP_eraseIdx_two]
    · intro vs hvs
      rw [hvs]
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      nlinarith
  -- 2. `drop` : `v :: a :: b :: rest ↦ a :: b :: rest`
  have h2 : WordR main dropProg (fun vs => vs = v :: a :: b :: rest)
      (fun _ out => out = a :: b :: rest) (fun _ => Kd * (vsz v + 1)) := by
    refine conseq' hKer (hdrop main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hout
      obtain ⟨v', rest', hv', hout'⟩ := hout
      rw [hvs] at hv'
      obtain ⟨-, hrr⟩ := List.cons.inj hv'
      rw [hout', hrr]
    · intro vs hvs
      rw [hvs]
      simp
  -- 3. chain the two words
  have h3 : WordR main (Cmd.seq (rollProg 2) dropProg)
      (fun vs => vs = a :: b :: v :: rest)
      (fun _ out => out = a :: b :: rest)
      (fun _ => 3 * Kr * (vsz a + vsz b + vsz v + 1) + Kd * (vsz v + 1)) := by
    refine conseq' hKer (chain2c hKer h1 h2 (fun vs mid _ hmid => by rw [hmid])) ?_ ?_ ?_
    · intro vs hvs
      exact hvs
    · intro vs out _ hout
      obtain ⟨mid, hmid, hout'⟩ := hout
      exact hout'
    · intro vs _
      exact le_rfl
  -- 4. cost arithmetic
  refine conseq' hKer h3 ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out _ hout
    exact hout
  · intro vs _
    exact stripP_cost_le Kr Kd (vsz a) (vsz b) (vsz v)

end Work.Main.final
