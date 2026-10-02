import Submission.Work.StemsB.CubePairHomology
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.RelCup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomological targets of the E4 (Wang sequence) development

The Wang sequence over a sphere (`WangSequence.lean`, `WangSphere.lean`) is exact as soon as two
identifications are supplied:

* `γ : H^n(E|_V) ≅ H^n(F)` — provided by `nonempty_singularCohomology_iso_fibreTriv`
  (`FibreTrivCohomology.lean`), no extra input;
* `τ : H^n(E, E|_V) ≅ H^{n-m}(F)` — **the remaining input**.

`τ` is excision + the relative Künneth of the disc pair.  In homology these are theorems of this
directory (`isIso_relChainsMap_excision`, `isIso_relMap`, `serreSphere_collar_iso`); the
cohomological counterparts are the targets recorded here, in the order in which they are used.

* `CubePairCohomology` — the relative cohomology of the cube pair `(Iᵐ × Y, ∂Iᵐ × Y)` is a shift
  of the cohomology of `Y`.  This is the cohomological mirror of `cubePair_main`; it supplies the
  relative Künneth for the disc pair and, with the cohomological normalisation of the collar, the
  identification `τ`.

The counterparts of the two remaining steps (excision and the fibrewise triviality) are obtained from
the homological quasi-isomorphisms by `Work.Cohomology.dualComplexMap_quasiIso` (the `ℤ`-dual of a
quasi-isomorphism between degreewise projective chain complexes is a quasi-isomorphism) together with
`Work.Cohomology.relComplexIsoDual` (`C^*(X,A) ≅ Hom(C_*(X,A), ℤ)`), so no further geometric input is
needed.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The relative cohomology of the cube pair.**
`H^{j+m}(Iᵐ × Y, ∂Iᵐ × Y; ℤ) ≅ H^j(Y; ℤ)` for every parameter space `Y`.

This is the cohomological counterpart of `Work.StemsB.cubePair_main`. -/
def CubePairCohomology : Prop :=
  ∀ (m : ℕ) (Y : Type) [TopologicalSpace Y] (j : ℕ),
    Nonempty (((Work.Cohomology.relComplex ℤ (CubeSpace Y m)
        (cubeBdryK Y m)).homology (j + m)) ≅
      (Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y)).homology j)

/-- **The relative cohomology of the collar pair.**  `H^{j+b}(G × Y, collar × Y; ℤ) ≅ H^j(Y; ℤ)` for
`G = sphLoopBig b` and `collar = sphLoopCollar b`.  This is the cohomological counterpart of
`Work.StemsB.serreSphere_collar_iso`, and the single remaining ingredient of the cohomological Wang
sequence over a sphere: from it, together with the cohomological excision
(`Work.StemsB.nonempty_relCohomology_iso_excision`) and the cohomological fibrewise triviality
(`Work.StemsB.nonempty_relCohomology_iso_of_relChains_quasiIso` applied to `Work.StemsB.relMap`),
the identification `τ` follows.

The proof route that the library makes available:
* `bigToEucRelChainMap` and `eucNormRelMap` are chain maps with the quasi-isomorphism property
  (`isIso_bigToEucRelChains`, `isIso_eucNormRelChains`), so by
  `nonempty_relCohomology_iso_of_relChains_quasiIso` the statement reduces to
  `H^{j+b}(eucCube b × Y, eucBdryProd b Y) ≅ H^j(Y)`;
* the radial homeomorphism `v ↦ v · ‖v‖_∞ / ‖v‖₂` of `ℝ^b` maps the `L^∞`-sphere `eucBdry b` onto
  the `L²`-sphere `mSph b` and the cube `eucCube b` onto the ball `mBall b`, and the radial
  retraction `(mBall, mSph) ≃ (ℝ^b, mSph)` is a homotopy equivalence of pairs, so the statement
  reduces to `H^{j+b}(Y × ℝ^b, Y × mSph b) ≅ H^j(Y)`;
* that last statement is exactly the content of `Work.Thom.modelThom_all`
  (`Work.Thom.ModelThom Y b`: cupping with the model Thom class is bijective). -/
def CollarCohomology : Prop :=
  ∀ (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (j : ℕ),
    Nonempty (((Work.Cohomology.relComplex ℤ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology (j + b)) ≅
      (Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y)).homology j)

/-- **The relative cohomology of the collar pair vanishes below the dimension** — the
cohomological counterpart of `Work.StemsB.serreSphere_collar_isZero`, and the second half of the
cohomological relative Künneth of the collar.  Like `CollarCohomology` it reduces to
`Work.Thom.subsingleton_relComplex_cube` (the cohomological vanishing `H^m(W × euCube n, W × ∂) = 0`
for `m < n`, which is already proved) through the chain-map quasi-isomorphisms
`bigToEucRelChainMap` and `eucNormRelMap` and the radial comparison of the cube pair with the ball
pair. -/
def CollarCohomologyZero : Prop :=
  ∀ (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ), m < b →
    IsZero ((Work.Cohomology.relComplex ℤ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)).homology m)

end

end Work.StemsB
