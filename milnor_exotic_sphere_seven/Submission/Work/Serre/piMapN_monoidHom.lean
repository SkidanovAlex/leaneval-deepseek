import Submission.Work.Serre.Models

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `π_n`-functoriality is a group homomorphism

`Work.StemsB.πmap` gives the induced map on homotopy groups one index up
(`HomotopyGroup (Fin (k+1))`); the chapter's `Work.Serre.piMapN` gives it in the exact degree `n`.
This file proves that it is a morphism of groups, by identifying it with `πmap` in the successor
case (Mathlib has no induced map on homotopy groups at all).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- **`Work.Serre.piMapN f n x` is a group homomorphism** (for `0 < n`, so that `π_n` carries
Mathlib's group structure). -/
theorem piMapN_monoidHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) [Nonempty (Fin n)] (x : X) :
    ∃ F : HomotopyGroup (Fin n) X x →* HomotopyGroup (Fin n) Y (f x),
      ∀ a, F a = piMapN f n x a := by
  rcases n with _ | k
  · obtain ⟨i⟩ := (inferInstance : Nonempty (Fin 0))
    exact Fin.elim0 i
  · refine ⟨Work.StemsB.πmap f k x, fun a => ?_⟩
    induction a using Quotient.inductionOn with
    | h p => rfl

end

end Work.Serre
