import Mathlib
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

namespace Work.WilG0

/-- `snocIt n m` is surjective: any `z : Fin (n+m) → ℝ` is glued from its first `n` and
its last `m` coordinates. -/
theorem snocIt_surjective (n m : ℕ) :
    Function.Surjective (fun p : (Fin n → ℝ) × (Fin m → ℝ) => snocIt n m p.1 p.2) := by
  intro z
  refine ⟨(fun i => z (Fin.castAdd m i), fun j => z (Fin.natAdd n j)), ?_⟩
  funext k
  refine Fin.addCases (motive := fun k => snocIt n m (fun i => z (Fin.castAdd m i))
      (fun j => z (Fin.natAdd n j)) k = z k) ?_ ?_ k
  · intro i; rw [snocIt_castAdd]
  · intro j; rw [snocIt_natAdd]

end Work.WilG0
