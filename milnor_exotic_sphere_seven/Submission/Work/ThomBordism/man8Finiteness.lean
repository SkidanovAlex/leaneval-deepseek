import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.sigmaCohomology
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.finiteRatCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Finiteness of `H⁴(·;ℚ)` for a `Man8` and for a finite disjoint union of `Man8`s

* `Work.ThomBordism.instFiniteDimensionalRatCoh` — `H⁴(V;ℚ)` is finite dimensional for every
  `Man8` `V`: the local generation of the fundamental class (`Man8.c_fund`) gives `Good` for the
  whole closed manifold (`Work.ThomBordism.goodUniv_of_localGen`), middle-degree Poincaré duality
  (`Work.Cohomology.pd_middleDegree_of_good`) then identifies `H⁴` with `H₄`, and the homology of
  the compact `C^∞` manifold `V` is finitely generated
  (`Work.ThomBordism.compactHomologyFinite`).
* `Work.ThomBordism.instFiniteDimensionalRatCohSigma` — the same for a finite disjoint union
  `Σ i, Y i`, from the coproduct splitting `Work.ThomBordism.pullbackRat_sigma_bijective`.

These are exactly the `FiniteDimensional ℚ (H^k(·;ℚ))` hypotheses that the additivity statements of
`σ` need (`Work.Bordism.sigma_disj`, `Work.ThomBordism.sigmaSigmaTypeSum`), and they are *not*
available in general (`Interface.lean` explains why the *final* assembly of `BoundarySigma` avoids
them but the proof of `BoundarySigma` needs them).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology

namespace Work.ThomBordism

noncomputable section

/-- **The rational middle cohomology of a `Man8` is finite dimensional.** -/
instance instFiniteDimensionalRatCoh (V : Man8) :
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj V.X)) := by
  have hfg : Module.Finite ℤ
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (Man8.X V))).homology 4) :=
    compactHomologyFinite (n := 8) (k := 4) ↑(Man8.X V)
  have hgood : Work.Cohomology.Good 8 (V.c : (Work.Cohomology.singularChains ℤ
      (Man8.X V)).homology 8) Set.univ isOpen_univ :=
    goodUniv_of_localGen (N := 8) V.c (fun x => V.c_fund x) (by norm_num)
  haveI hC4 : ChartedSpace (EuclideanSpace ℝ (Fin (4 + 4))) ↑(Man8.X V) := Man8.chartedSpace V
  exact finiteDimensional_ratCohomology_of_good (n := 4) (M := Man8.X V) hgood hfg

/-- **The rational middle cohomology of a finite disjoint union of `Man8`s is finite
dimensional**, from the coproduct splitting `pullbackRat_sigma_bijective`. -/
instance instFiniteDimensionalRatCohSigma {ι : Type} [Fintype ι] (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)]
    [∀ i, FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (Y i))))] :
    FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (Σ i, Y i)))) :=
  Module.Finite.equiv
    (LinearEquiv.ofBijective _
      (pullbackRat_sigma_bijective (fun i => TopCat.of (Y i)) 4)).symm

end

end Work.ThomBordism
