import Mathlib

namespace Work.RPCore.Chain

/-- Folding the successive maps of a chain
`ys 0 --fs 0--> ys 1 --fs 1--> ... --fs m--> ys (m+1)`
starting at `ys 0` returns the endpoint `ys (m+1)`. -/
theorem foldl_ofFn_chain {α : Type*} (m : ℕ) (fs : Fin (m + 1) → α → α)
    (ys : Fin (m + 2) → α)
    (h : ∀ i : Fin (m + 1), fs i (ys i.castSucc) = ys i.succ) :
    (List.ofFn fs).foldl (fun acc f => f acc) (ys 0) = ys (Fin.last (m + 1)) := by
  induction m with
  | zero =>
    rw [List.ofFn_succ]
    simp only [List.ofFn_zero, List.foldl_cons, List.foldl_nil]
    exact h 0
  | succ n ih =>
    have h' : ∀ i : Fin (n + 1),
        (fun i : Fin (n+1) => fs i.castSucc) i ((fun i : Fin (n+1+1) => ys i.castSucc) i.castSucc)
          = (fun i : Fin (n+1+1) => ys i.castSucc) i.succ := by
      intro i
      show fs i.castSucc (ys (i.castSucc).castSucc) = ys i.succ.castSucc
      rw [← Fin.succ_castSucc i, h i.castSucc]
    have ih' := ih (fun i : Fin (n+1) => fs i.castSucc) (fun i : Fin (n+1+1) => ys i.castSucc) h'
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
    rw [show List.foldl (fun acc f => f acc) (ys 0) (List.ofFn (fun i : Fin (n+1) => fs i.castSucc))
          = (fun i : Fin (n+1+1) => ys i.castSucc) (Fin.last (n+1)) from ih']
    rw [h (Fin.last (n+1)), Fin.succ_last]

end Work.RPCore.Chain
