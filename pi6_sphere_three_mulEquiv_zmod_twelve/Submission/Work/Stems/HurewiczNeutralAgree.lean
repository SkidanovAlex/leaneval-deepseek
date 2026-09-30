import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Stems.HurewiczMapNatural

/-!
# Agreement of the fork-neutral Hurewicz map with `Work.Stems.hurewiczMap`

`Work.Stems.hurewiczMapN` (`Stems/HurewiczNeutral.lean`) and `Work.Stems.hurewiczMap`
(`Stems/HurewiczMap.lean`) are the same function: both are the descent of `hurewiczChain` to the
homotopy group.  This file records that (it imports the *non*-fork-neutral `HurewiczMapNatural`, so
it can only be used on the `Work.Stems` side of the workspace).

Consequences: the additive packaging `Work.Stems.hurewiczHom` computes `hurewiczMapN`, and the
naturality/additivity available for `hurewiczMap` transfer to `hurewiczMapN` in this fork.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- The fork-neutral Hurewicz map is the Hurewicz map. -/
theorem hurewiczMapN_eq_hurewiczMap (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (x₀ : X) : hurewiczMapN n hn x₀ = hurewiczMap n hn x₀ := rfl

/-- The additive packaging of the Hurewicz map computes the fork-neutral Hurewicz map. -/
theorem hurewiczHom_eq_hurewiczMapN (n : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X)
    (a : Additive (HomotopyGroup (Fin (n + 1)) X x₀)) :
    hurewiczHom n x₀ a = hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀
      (Additive.toMul a) := rfl

end

end Work.Stems
