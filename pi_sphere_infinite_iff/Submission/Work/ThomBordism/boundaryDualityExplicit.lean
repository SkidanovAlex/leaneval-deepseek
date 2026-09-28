import Submission.Work.ThomBordism.boundarySigmaReduction
import Submission.Work.ThomBordism.sigmaBoundarySum
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.isZero_dualComplex_empty

/-!
# `BoundarySigma` from the *explicit* boundary bordism

`Submission/Work/ThomBordism/boundarySigmaReduction.lean` reduces `Work.ThomBordism.BoundarySigma`
(bordism invariance of the signature in dimension `8`) to the structure `BoundaryDuality`, whose
`halfDimension` field is middle-degree Lefschetz duality for the bordism `(∂W, ∂w) ⟶ (∅, 0)`.

**One correction is needed before that input can be proved.**  There, the bordism is
`boundaryBordism W := Classical.choice (existsBoundaryBordism W)`.  `Work.Bordism.Bordism` imposes
no condition on its `W` field (only on the two parametrisations and the class relation), so the type
`Bordism (bdryClosed W) emptyClosed` contains degenerate elements (e.g. `W = pt` with the constant
parametrisation, the class relation holding because `H₈(pt;ℤ) = 0`), for which `HalfDimension` is
*false* as soon as `H⁴(∂W;ℚ) ≠ 0`; and `Classical.choice` carries no specification, so a proof of
`HalfDimension 4 (Classical.choice _)` would have to hold for every element of that type.  This file
therefore *defines* the bordism explicitly — the same data as the proof of `existsBoundaryBordism`,
the manifold `W` itself with the inclusion of its boundary — so that the geometric input is stated
about the honest bordism, where it is the classical theorem.

The remaining inputs are named, exactly as before, and are the only ones:

* `BoundaryFinite` — `H⁴(∂W;ℚ)` is finite dimensional (from the pieces, along `W.bdry`);
* `BoundaryNondegenerate` — the middle intersection form of the closed `8`-manifold `∂W` is
  non-degenerate (Poincaré duality for `∂W`, i.e. `Good` from the local generation of `∂w` —
  inherited from the pieces' `Man8.c_fund` through `W.bdry`);
* `BoundaryHalfDimension` — **the crux**: middle-degree Lefschetz duality for the pair `(W, ∂W)`,
  i.e. the image of `H⁴(W;ℚ) → H⁴(∂W;ℚ)` is a Lagrangian of that middle form (isotropy is the
  theorem `Work.Bordism.boundaryForm_middleMap_eq_zero`; only the dimension count is missing).  Its
  plan, the pieces of the classical proof that are available, and the two classical routes are in
  `Submission/Work/ThomBordism/HALFDIM_PLAN.md`.

The two *empty* end conditions of `BoundaryDuality` are not inputs: they are proved here
(`finite_empty`, `nondegenerate_empty`), because `H⁴(∅;ℚ) = 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-! ## The explicit boundary bordism -/

/-- **The bordism `(∂W, ∂w) ⟶ (∅, 0)`, explicitly**: the bordism manifold is `W` itself, the
parametrisation of the first end is the inclusion of the boundary `∂W ⊆ W`, the second end is empty,
and the class relation is `i_* ∘ ∂ = 0` (`Work.Cohomology.hPairδ_comp`) applied to the relative
fundamental class `W.w`.

This is the same datum that `Work.ThomBordism.existsBoundaryBordism` produces; it is a *definition*
rather than a `Classical.choice` because `HalfDimension` for a bordism depends on its `W` field, and
`Work.Bordism.Bordism` does not restrict it. -/
noncomputable def boundaryBordismExplicit {ι : Type} [Fintype ι] {F : ι → Man8}
    (Wb : NullBordismFamily ι F) : Work.Bordism.Bordism (bdryClosed Wb) emptyClosed where
  W := TopCat.of Wb.W
  iM := Work.Cohomology.subtypeIncl (TopCat.of Wb.W) (bdrySet Wb.W)
  iN := TopCat.ofHom ⟨fun e => PEmpty.elim e,
    continuous_iff_continuousAt.mpr (fun x => PEmpty.elim x)⟩
  hbd := by
    rw [map_zero]
    have hz : (Work.Cohomology.hPairδ (TopCat.of Wb.W) (bdrySet Wb.W) 8 ≫
          HomologicalComplex.homologyMap
            (Work.Cohomology.inclChains (TopCat.of Wb.W) (bdrySet Wb.W)) 8) Wb.w = 0 := by
      rw [Work.Cohomology.hPairδ_comp]
      simp
    have h3 : (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains (TopCat.of Wb.W) (bdrySet Wb.W)) 8)
          ((Work.Cohomology.hPairδ (TopCat.of Wb.W) (bdrySet Wb.W) 8) Wb.w) = 0 := by
      simpa using hz
    show (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (bdrySet Wb.W)) (TopCat.of Wb.W)
          (Work.Cohomology.subtypeIncl (TopCat.of Wb.W) (bdrySet Wb.W))) 8).hom
        ((Work.Cohomology.hPairδ (TopCat.of Wb.W) (bdrySet Wb.W) 8).hom Wb.w) = 0
    simpa only [Work.Cohomology.inclChains] using h3

/-! ## The empty end: not an input -/

/-- `H⁴(∅;ℚ) = 0`: the singular cochain complex of the empty space is a zero complex, so its
homology vanishes and so does its rationalisation. -/
theorem subsingleton_ratCohomology_pempty (n : ℕ) :
    Subsingleton (Work.SignatureBordism.ratCohomology n
      (TopCat.toSSet.obj (TopCat.of PEmpty))) := by
  haveI : Subsingleton
      ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of PEmpty))).homology n) :=
    ModuleCat.subsingleton_of_isZero
      (Work.Cohomology.isZero_homology_of_isZero_X_cochain n
        (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty _ n))
  infer_instance

/-- The middle cohomology of the empty `8`-manifold is finite dimensional. -/
theorem finite_empty :
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of PEmpty))) := by
  haveI := subsingleton_ratCohomology_pempty 4
  exact Module.Finite.of_finite

/-- The middle form of the empty `8`-manifold is non-degenerate (its space is trivial). -/
theorem nondegenerate_empty :
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) emptyClosed) := by
  intro x _
  haveI := subsingleton_ratCohomology_pempty 4
  exact Subsingleton.elim x 0

/-! ## The named inputs, and the assembly -/

/-- **The finiteness input**: the middle cohomology of the closed oriented `8`-manifold `∂W` is
finite dimensional.  (From the pieces: `∂W ≅ Σ i, (F i).pt` along `W.bdry`, each piece has finite
dimensional middle cohomology by `Work.ThomBordism.finiteDimensional_ratCohomology_of_good`, and a
finite coproduct of finite dimensional spaces is finite dimensional.) -/
def BoundaryFinite : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))))

/-- **The non-degeneracy input**: the middle intersection form of the closed oriented `8`-manifold
`∂W` is non-degenerate (middle-degree Poincaré duality of `∂W`, from the local generation of its
fundamental class `∂w` — inherited from the pieces through `W.bdry`). -/
def BoundaryNondegenerate : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (bdryClosed W))

/-- **The crux**: middle-degree Lefschetz duality for the pair `(W, ∂W)` — the image of the
restriction `H⁴(W;ℚ) → H⁴(∂W;ℚ)` has half the dimension of `H⁴(∂W;ℚ)`, i.e. it is a Lagrangian of
the middle intersection form of `∂W` (the isotropy being the theorem
`Work.Bordism.boundaryForm_middleMap_eq_zero`).  See `HALFDIM_PLAN.md`. -/
def BoundaryHalfDimension : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    Work.Bordism.HalfDimension 4 (boundaryBordismExplicit W)

/-- The named inputs of `BoundarySigma`, for the explicit boundary bordism. -/
structure BoundaryDualityExplicit : Prop where
  /-- `H⁴(∂W;ℚ)` is finite dimensional -/
  finite : BoundaryFinite
  /-- the middle form of `∂W` is non-degenerate -/
  nondegenerate : BoundaryNondegenerate
  /-- **the crux**: middle-degree Lefschetz duality for the pair `(W, ∂W)` -/
  halfDimension : BoundaryHalfDimension

/-- **`BoundarySigma` from the three named inputs.**  `σ(∂W) = 0` by bordism invariance of the
signature applied to the explicit bordism `(∂W,∂w) ⟶ (∅,0)` (whose second end has `σ = 0`), and
`σ(∂W) = ∑ i, (F i).sigma` by `Work.ThomBordism.sigmaBoundarySum`. -/
theorem boundarySigma_of_explicit (h : BoundaryDualityExplicit) : BoundarySigma := by
  intro ι _ F W
  rw [← sigmaBoundarySum W]
  haveI := h.finite ι F W
  haveI := finite_empty
  have heq := Work.Bordism.sigma_eq_of_bordant_eight (boundaryBordismExplicit W)
    (h.nondegenerate ι F W) nondegenerate_empty (h.halfDimension ι F W)
  rw [heq]
  simp

end

end Work.ThomBordism
