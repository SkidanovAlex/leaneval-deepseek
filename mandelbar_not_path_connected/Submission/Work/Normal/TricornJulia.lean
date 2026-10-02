import Mathlib
import Submission.Work.Normal.Tricorn
import Submission.Work.Normal.TricornDynamics
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.Frontier
import Submission.Work.Normal.isCompact_juliaSet
import Submission.Work.Normal.juliaSet_subset_filledJuliaSet
import Submission.Work.Normal.juliaSet_infinite
import Submission.Work.Normal.Perfect
import Submission.Work.Normal.Preimages

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Julia set of the tricorn quartic `TantibarSq c`

Concrete corollaries of the general Fatou/Julia theory for the polynomial map
`TantibarSq c z = (z^2 + conj c)^2 + c`, which is the holomorphic second iterate of the
antiholomorphic quadratic map `T̄_c` and is the map whose dynamics governs the mandelbar.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- `TantibarSq c` has degree `4 ≥ 2`, so the general theory applies with `d = 4`. -/
theorem two_le_four : 2 ≤ 4 := by norm_num

theorem juliaSet_eq_frontier_tantibarSq (c : ℂ) :
    JuliaSet (TantibarSq c) = frontier (FilledJuliaSet (TantibarSq c)) :=
  juliaSet_eq_frontier two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem juliaSet_subset_filledJuliaSet_tantibarSq (c : ℂ) :
    JuliaSet (TantibarSq c) ⊆ FilledJuliaSet (TantibarSq c) :=
  juliaSet_subset_filledJuliaSet two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem isCompact_juliaSet_tantibarSq (c : ℂ) : IsCompact (JuliaSet (TantibarSq c)) :=
  isCompact_juliaSet two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem juliaSet_nonempty_tantibarSq (c : ℂ) : (JuliaSet (TantibarSq c)).Nonempty :=
  juliaSet_nonempty two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem mapsTo_juliaSet_tantibarSq (c : ℂ) :
    MapsTo (TantibarSq c) (JuliaSet (TantibarSq c)) (JuliaSet (TantibarSq c)) :=
  mapsTo_juliaSet two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem preimage_juliaSet_subset_tantibarSq (c : ℂ) :
    (TantibarSq c) ⁻¹' (JuliaSet (TantibarSq c)) ⊆ JuliaSet (TantibarSq c) :=
  preimage_juliaSet_subset two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem juliaSet_infinite_tantibarSq (c : ℂ) : (JuliaSet (TantibarSq c)).Infinite :=
  juliaSet_infinite two_le_four (isPolynomialMapOfDegree_tantibarSq c)

theorem juliaSet_perfect_tantibarSq (c : ℂ) : Perfect (JuliaSet (TantibarSq c)) :=
  juliaSet_perfect two_le_four (isPolynomialMapOfDegree_tantibarSq c)

/-- Density of iterated preimages in the Julia set of the tricorn quartic. -/
theorem subset_closure_iUnion_preimage_tantibarSq (c : ℂ) {y : ℂ}
    (hy : y ∈ JuliaSet (TantibarSq c)) :
    JuliaSet (TantibarSq c) ⊆ closure (⋃ n : ℕ, (TantibarSq c)^[n] ⁻¹' {y}) :=
  subset_closure_iUnion_preimage two_le_four (isPolynomialMapOfDegree_tantibarSq c) hy

end Work.Normal
