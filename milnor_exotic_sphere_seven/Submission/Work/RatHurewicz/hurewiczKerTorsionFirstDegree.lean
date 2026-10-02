import Mathlib
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Stems.HurewiczMap
import Submission.Work.RatHurewicz.Basic
import Submission.Work.RatHurewicz.degenCycleKilled

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

/-!
# The Hurewicz map modulo torsion in the first non-vanishing degree

For `m ≥ 1` and a space `X` whose homotopy groups `π_i(X,x₀)`, `i < m+1`, all vanish (so `X` is
`m`-connected, `π_0` and `π_1` included), the kernel of the Hurewicz map
`Work.Stems.hurewiczMapN (m+1) : π_{m+1}(X,x₀) → H_{m+1}(X;ℤ)` consists of torsion elements: a class
whose Hurewicz image is zero has finite order.

Classically (Hatcher 4.32, the absolute Hurewicz result) the map is an *isomorphism* in this
degree, so the kernel is trivial; the mod-torsion form stated here is exactly what the rational
Hurewicz statement in the stable range needs in the first non-vanishing degree.  It is also the
first-degree case of Serre's Hurewicz result modulo the Serre class of torsion groups, and the base
case of the inductive proof of `Work.Drive.RationalHurewiczStable`.

Routes to a proof:
(a) the CW route -- replace `X` by a CW model with no cells below dimension `m+1`, use the long
exact sequences of pairs and triples in homotopy and homology, the relative Hurewicz result for the
pair `(X, X^{(m)})` with its cell-by-cell case (the pair `(X ∪ ⋁ D^{m+1}, X)`, whose relative
homology is free on the cells) and a diagram chase;
(b) the Serre spectral sequence of the path-loop fibration `ΩX → PX → X` plus the mod-𝒞 Hurewicz
argument (Serre);
(c) the simplicial route: `Sing X` is a Kan complex with `π_*(Sing X) ≅ π_*(X)` and singular
homology `H_*(ℤ[Sing X]) ≅ H_*(X;ℤ)`, and the Hurewicz map is the unit `K → ℤ[K]` of the free
simplicial abelian group, so the statement becomes combinatorial (Dold-Kan: `π_n(ℤK) ≅ H_n(NℤK)`).

The conclusion is the hypothesis-free form needed by the file
`Submission/Work/RatHurewicz/hurewiczModTorsionFirstDegree.lean`: it implies
`Work.RatHurewicz.HurewiczModTorsionFirstDegree` (via `Work.Stems.hurewiczMap_mul`, which gives
`h(a^N) = N • h(a)`, so a class with torsion Hurewicz image can be replaced by its power, whose
Hurewicz image is zero).
-/

theorem hurewiczKerTorsionFirstDegree :
    ∀ (m : ℕ), 1 ≤ m → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
      (∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
        ∀ a : HomotopyGroup (Fin (m + 1)) X x₀,
          Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a = 0 →
            ∃ N : ℕ, 0 < N ∧ a ^ N = 1 :=
  hurewiczKerTorsionFirstDegree_of_degenCycle degenCycleKilled

end Work.RatHurewicz
