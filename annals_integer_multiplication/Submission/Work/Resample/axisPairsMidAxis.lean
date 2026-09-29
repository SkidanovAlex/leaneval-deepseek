import Mathlib
import Submission.Work.Resample.axisDefs

namespace Work.Resample

/-- `midAxis` computes, index by index, the same thing as the list-level `axisPairs`: this is the
"no-op" bridge between the `List.ofFn` description used by the program-level lemmas and the
`Fin`-indexed description used by the mathematical ones. -/
theorem axisPairsMidAxis (A m n B : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (u : Fin (A * m * B) → ℤ × ℤ) :
    Work.Resample.axisPairs A m n B Φ (List.ofFn u)
      = List.ofFn (Work.Resample.midAxis A m n B Φ u) := by
  -- read the input array through `getD` (agreeing with `u` wherever it is in range)
  have key : List.ofFn u =
      List.ofFn (fun i : Fin (A*m*B) => (List.ofFn u).getD (i:ℕ) (0,0)) := by
    apply List.ofFn_inj.mpr; funext i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [key]
  rw [axisPairs_ofFn (A:=A) (m:=m) (n:=n) (B:=B) hn hB Φ
    (fun i => (List.ofFn u).getD i (0,0))]
  apply List.ofFn_inj.mpr
  funext idx
  rw [axisOp, dite_eq_left hn]
  simp only [midAxis]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact Nat.mod_lt _ hn),
    List.getElem_ofFn]

end Work.Resample
