import Mathlib
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.tlLowCycDefs

namespace Work.OROneRel

/-- The weight of the cycle word under the constant weight `1` on the generators is `p + q`: every
one of the `p + q` letters of `cycList` is read forward and contributes `1`. -/
theorem lsig_one_cycList (p q : ℕ) :
    lsig (fun _ : Fin 2 => (1 : ℤ)) (cycList p q) = ((p + q : ℕ) : ℤ) := by
  rw [lsig, cycList, List.map_map]
  rw [show (fun x : Fin 2 × Bool => if x.2 then (1 : ℤ) else -1) ∘
        (fun k : ℕ => (cycLetter p q (k : ℤ), true)) = fun _ => (1 : ℤ) from by
      funext k; simp]
  rw [List.map_const', List.length_range, List.sum_replicate]
  simp

theorem cohom_one_cycWord (p q : ℕ) :
    Work.OROneRel.cohom (fun _ : Fin 2 => (1 : ℤ)) (Work.OROneRel.cycWord p q) =
      Multiplicative.ofAdd ((p + q : ℕ) : ℤ) := by
  rw [cycWord, cohom_mk, lsig_one_cycList]

end Work.OROneRel
