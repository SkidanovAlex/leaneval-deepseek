import Mathlib
import Submission.Work.Rat.RankOneEMDefs
import Submission.Work.Serre.Engine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rank-one level clauses of the `K(A,n)` computation

`Work.Rat.RankOneOddFree c` is the *odd* clause of the rank-one Eilenberg--MacLane computation in
free-top form: for odd `n ≥ 3`, a space whose homotopy groups vanish up to degree `N` except in
degree `n`, where `H_n(-;ℚ) ≅ ℚ`, has vanishing rational homology in degrees `n < j ≤ N - c·n`.

This file splits the interface into its *level clauses*, exactly as
`Submission/Work/Stems/c2FreeClauses.lean` does for the `K(ℤ,·)` layer, so that the mutual
induction can be run as an ordinary strong induction on the level:

* `OddClauseR n N` — the odd clause at level `n` and top `N` (for `n = 1` it carries the
  abelianness of `π₁`, which is exactly `Work.Rat.RankOneC1Ab`'s clause);
* `EvenClauseR j N` — the even clause at level `j` (degree `2j`) and top `N`.

The even step (`OddClauseR (2j-1) → EvenClauseR j`) is the Euler-class/Gysin periodicity
(`Work.Serre.SerreE3b`); the odd step (`EvenClauseR j → OddClauseR (2j+1)`) is the cover/Wang
argument of the `C2` odd step with the loop space's rational cohomology supplied by the even clause.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- The abelianness of `π₁` (the extra hypothesis of the level-`1` odd clause).  Kept as a
separate `abbrev` so that the *statement* of `OddClauseR` has no typeclass-implicit content, which
would otherwise make the clauses awkward to manipulate by unification. -/
abbrev Pi1Ab (X : Type) [TopologicalSpace X] (x₀ : X) : Prop :=
  ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a

/-- **The odd clause at level `n` and top `N`.**  A space all of whose homotopy groups vanish in
degrees `≤ N` except in degree `n`, where `H_n(-;ℚ) ≅ ℚ`, has vanishing rational homology in
degrees `n < j ≤ N - n`.

For `n = 1` the abelianness of `π₁` is carried as an extra hypothesis (it is exactly the hypothesis
of `Work.Rat.RankOneC1Ab`). -/
abbrev OddClauseR (n N : ℕ) : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (x₀ : X),
    (n = 1 → Pi1Ab X x₀) →
    (∀ j : ℕ, j ≤ N → j ≠ n → Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) →
    ∀ j : ℕ, n < j → j ≤ N - n → IsZero (Work.Serre.ratH (TopCat.of X) j)

/-- **The even clause at level `j` (degree `2j`) and top `N`.**  A space all of whose homotopy
groups vanish in degrees `≤ N` except in degree `2j`, where `H_{2j}(-;ℚ) ≅ ℚ`, has the rational
homology of `ℂP^∞` rescaled by `2j` through degree `N - 2j + 1`. -/
abbrev EvenClauseR (j N : ℕ) : Prop :=
  2 * j ≤ N →
  ∀ {X : Type} [TopologicalSpace X] (x₀ : X),
    (∀ i : ℕ, i ≤ N → i ≠ 2 * j → Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j) ≅ ModuleCat.of ℚ ℚ) →
    (∀ k : ℕ, 2 * j * k ≤ N - 2 * j + 1 →
      Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
    (∀ d : ℕ, d ≤ N - 2 * j + 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
      IsZero (Work.Serre.ratH (TopCat.of X) d))

/-- The odd interface follows from the odd level clauses at odd levels `≥ 3`. -/
theorem rankOneOddFree_of_clauses
    (h : ∀ (n N : ℕ), 3 ≤ n → Odd n → OddClauseR n N) :
    Work.Rat.RankOneOddFree 1 := by
  intro n N hn hnodd X _ x₀ hvan hgen j hj hjN
  exact h n N hn hnodd x₀ (fun h1 => absurd h1 (by omega)) hvan hgen j hj
    (by simpa only [one_mul] using hjN)

/-- The clause of `Work.Rat.RankOneC1Ab` is the level-`1` odd clause. -/
theorem oddClauseR_one_of_c1 (h : Work.Rat.RankOneC1Ab) : ∀ N : ℕ, OddClauseR 1 N := by
  intro N X _ x₀ hab hvan hgen j hj1 hjN
  exact h N x₀ (hvan 0 (by omega) (by omega)) (hab rfl) hgen
    (fun i hi hiN => hvan i (by omega) (by omega)) j hj1 hjN

end

end Work.Stems
