import Mathlib
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.Port.Glue
import Submission.Work.ThomBordism.Port.PdGoodUnivChart
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.ThomBordism.RelDuality.interiorHomology
import Submission.Work.ThomBordism.RelDuality.relClass_lift
import Submission.Work.ThomBordism.RelDuality.goodOfOpen
import Submission.Work.ThomBordism.RelDuality.doubleFundClass
import Submission.Work.ThomBordism.RelDuality.lefschetzDualityBdry_of_pieces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Middle-dimensional Poincaré–Lefschetz duality for the pair `(W, ∂W)`

`Work.ThomBordism.LefschetzDualityBdry W` (`Submission/Work/ThomBordism/bdryInterfaces.lean`) is the
statement that the relative cap product with the relative fundamental class `W.w`
(`NullBordismFamily.w`, whose localisations at interior points are generators, by `w_fund`)

`y ↦ y ⌢ W.w : H^k(W, ∂W; ℤ) ⟶ H_{9−k}(W; ℤ)`

is **bijective in every bidegree** `k + m = 9`.  This is Hatcher's Theorem 3.43 for the pair
`(M, ∂M)` with `A = ∂M`, `B = ∅` (*Lefschetz duality*); it is the workspace's named input
`Work.Surgery.LefschetzDuality` (`Submission/Work/Surgery/RelativeDisc.lean`), which is proved there
only for the model pairs (the disc pair `(Dⁿ, Sⁿ⁻¹)` and the disc-bundle pair of a `4`-handle).

## The route used here (Hatcher 3.43: compactly supported duality + two comparisons)

Hatcher's proof of Theorem 3.43 for `B = ∅` has three ingredients:

1. **compactly supported Poincaré duality for the open interior** `int M` (Hatcher's Theorem 3.35):
   the cap product with the local fundamental class is bijective on compactly supported classes;
2. the comparison `H^k(M, ∂M; ℤ) ≅ H^k_c(int M; ℤ)` ("every relative class is supported away from
   the boundary");
3. the comparison `H_{n−k}(M; ℤ) ≅ H_{n−k}(int M; ℤ)` (the interior inclusion is a homology
   equivalence — Hatcher's "obvious isomorphisms", which classically use a collar of `∂M` in `M`).

In this workspace (2) and (3) are realised *without* the collar neighbourhood theorem, by
finite-cover Mayer–Vietoris inductions (plus compactness for the increasing-union limits), and (1)
is realised through the workspace's `Work.Cohomology.Good` machinery (the elementwise form of
compactly supported duality) applied to the **double** `D = W ∪_{∂W} W̄` of `W`.

Concretely, with

* `M := W.W` the compact `C¹` `9`-manifold with boundary of the `NullBordismFamily`,
* `D := Work.ThomBordism.Double 8 M` its double (charted over `ℝ⁹`, compact, `T2`; all three are
  proved in `Submission/Work/ThomBordism/doubleCharted{,T2}.lean`),
* `A`, `B ⊆ D` the two closed halves (`B` the second copy), `A ∩ B` the seam,

the three ingredients become

* **`Work.ThomBordism.doubleFundClass`** (delegated): a class `c ∈ H₉(D; ℤ)` whose image in
  `H₉(D, B; ℤ)` is `w` (under the excision identification) and whose localisation at *every* point
  of `D` generates the local homology `H₉(D, D∖{x}; ℤ)`;
* **`Work.Cohomology.Good 9 c Set.univ`** for `D` (from the previous item and
  `Work.ThomBordism.goodUniv_of_localGen`), and its **descent to the open half** `int A ≅ int M`
  (`Good` for arbitrary open subsets, delegated as `Work.ThomBordism.good_of_open`);
* **`Work.ThomBordism.interiorHomology`** (delegated): the inclusion `int A ↪ A` induces a
  bijection on homology of every degree;
* **`Work.ThomBordism.relClass_lift`** (delegated): every class in `H^k(M, ∂M; ℤ)` is the image of a
  class in `H^k(M, M∖K; ℤ)` for some compact `K ⊆ int M` (the cohomological half of the
  comparison (2));

and the eventual assembly below turns the `hit`/`kill` clauses of `Good 9 c (int A)` into
surjectivity and injectivity of the relative cap product with `W.w`.

## Status

The four lemmas above are the delegated inputs; the file is organised so that the final proof of
`Work.ThomBordism.lefschetzDualityBdry` is the assembly.  Everything is stated in the vocabulary of
`bdryInterfaces.lean` (`LefschetzDualityBdry`, `lefschetzMapBdry`) plus `Work.Cohomology.Good`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-- **Middle-dimensional Poincaré–Lefschetz duality for the pair `(W, ∂W)`.**

Assembled from the four ingredients of Hatcher's proof of Theorem 3.43: the interior comparison
(`RelDuality/interiorHomology`), the lifting of relative classes off the boundary
(`RelDuality/relClass_lift`), compactly supported duality for open subsets of the double
(`RelDuality/goodOfOpen`) and the fundamental class of the double with its identification with the
relative fundamental class of `(W, ∂W)` (`RelDuality/doubleFundClass`); the assembly itself is
`RelDuality/lefschetzDualityBdry_of_pieces`. -/
theorem lefschetzDualityBdry {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) : LefschetzDualityBdry W :=
  Work.ThomBordism.RelDuality.lefschetzDualityBdry_of_pieces
    Work.ThomBordism.RelDuality.interiorHomology
    Work.ThomBordism.RelDuality.relClass_lift
    Work.ThomBordism.RelDuality.goodOfOpen
    Work.ThomBordism.RelDuality.doubleFundClass
    W

end

end Work.ThomBordism
