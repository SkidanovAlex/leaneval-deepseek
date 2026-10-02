import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Gen.Basic
import Submission.Work.Gen.Euler
import Submission.Work.Gen.CP4Smooth8
import Submission.Work.Gen.CP2CP2Smooth8
import Submission.Work.Gen.CP4NumbersOf
import Submission.Work.Gen.CP2CP2NumbersOf
import Submission.Work.Gen.Generators8Of
import Submission.Work.Gen.Cp2Cp2TangentClasses
import Submission.Work.Gen.cp2cp2TangentClasses
import Submission.Work.Gen.cp2cp2TangentSplits
import Submission.Work.Gen.Cp2Cp2KunnethInput
import Submission.Work.Gen.WhFormulaCP4Par
import Submission.Work.Gen.cp2cp2TangentClassesPar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

AREA GEN. Prove `Work.Drive.Generators8`: two closed connected oriented C^∞ 8-manifolds (`Work.Drive.Smooth8`)
that satisfy 45σ = 7p₂ − p₁² with the tangent-bundle classes AS DEFINED (`Work.Thom.p1Tangent'`,
`p2Tangent'` = ±c₂, c₄ of TM ⊗ ℂ), and whose (p₁², p₂)-number vectors are linearly independent.
Classical values: ℂP⁴ = (σ,p₁²,p₂) = (1,25,10); ℂP²×ℂP² = (1,18,9); ℍP² = (1,4,7). Any independent pair works.

Existing material: Submission/Work/Projective/ (README.md): ℂPⁿ as a concrete space and a manifold,
CP4Concrete, CP4Manifold8, cpn_cohomology/cpn_homology, cp4_cupSquare_generates, CP2CP2*, and
Submission/Work/Thom/nonempty_closedOrientedSmooth8.lean (ℂP⁴ as a C¹ ClosedOrientedSmooth8). Also
Submission/Work/OrientedBordism8/ (algebraic L-genus bookkeeping; its ℂPⁿ is only an algebraic model).
What is genuinely missing: the Pontryagin numbers of the DEFINED classes. The classical route is the Euler
sequence TℂPⁿ ⊕ ℂ ≅ (n+1)·L̄ (as complex bundles in the gluing model), c₁(L̄) = ± the generator x ∈ H²,
H*(ℂPⁿ) = ℤ[x]/(xⁿ⁺¹) with ⟨x⁴,[ℂP⁴]⟩ = ±1, and the Whitney sum formula c(E⊕F) = c(E)c(F). A sibling
area (WHITNEY, directory Submission/Work/Whitney/) is building the Whitney formula: do NOT build it yourself;
develop everything else first and import Submission.Work.Whitney.* once it lands (check its README).
For the second generator choose whichever of ℂP²×ℂP² (needs Künneth / cross products for σ and the
numbers) and ℍP² (needs its own smooth structure and tangent bundle) is cheaper given what exists.
Keep all new files under Submission/Work/Gen/.
-/

/-! ## State of the argument (see `Submission/Work/Gen/README.md` §S6–S11 for the full account)

**Everything in AREA GEN that does not need the Whitney sum formula or Künneth is done.**  The
assembly is `Work.Gen.Generators8Of`: from the two characteristic-class inputs below it produces
`Work.Drive.Generators8` (`Generators8Of.lean`, `sorry`-free), because

* `G₁ = ℂP⁴` is `Work.Gen.cp4Smooth8Of cp4C cp4C_span` (`CP4NumbersOf.lean`), its three numbers are
  `(σ, p₁², p₂) = ε·(1, 25, 10)` for `ε = ⟨u⁴, cp4C⟩ = ±1` (`Work.Gen.kronH_uFourth_pm_one`), so
  `45σ = 7p₂ - p₁²` (`Work.Gen.cp4NumbersOf`);
* `G₂ = ℂP² × ℂP²` is `Work.Gen.cp2cp2Smooth8Of` (smooth `8`-manifold structure from
  `Work.Gen.Cp2Cp2Smooth`), its three numbers are `(1, 18, 9)` from a `CP2CP2Model H₈`-generator
  (`Work.Gen.cp2cp2NumbersOf`);
* the number vectors are independent because `25·9 ≠ 10·18`.

The remaining gaps of the area are exactly the hypotheses of `Generators8Of`, isolated below:

1. `cp4_p1_eq`, `cp4_p2_eq` — the Chern/Pontryagin classes of *ℂP⁴*'s **defined** tangent bundle.
   `Work.Gen.EulerChern` (`EulerChern.lean`, in progress) derives them from the Euler sequence
   `TℂP⁴ ⊕ ε² ≅ (O(1) ⊕ O(-1))⁵` (`Work.Gen.eulerSequence_iso`) together with the **Whitney sum
   formula** (owned by `Submission/Work/Whitney/`) and the duality sign
   `c₁(O(-1)) = -c₁(O(1))` (`Work.Gen.chernClass_tautLine`); `Work.Gen.TangentPresentation` (proved)
   and `Work.Gen.cp4ChernPresentation` transport the `stdTangentC` presentation to
   `Work.Thom.p1Tangent'`/`p2Tangent'`.

2. `cp2cp2_model` — the Künneth ring of `ℂP² × ℂP²` for the concrete space together with a generator
   of `H₈(ℂP² × ℂP²;ℤ) ≅ ℤ` and the identification of the defined tangent classes with the model's
   `p₁ = 3(a² + b²)`, `p₂ = 9a²b²`.  The ring is the interface `Work.Projective.CP2CP2Model`
   (KUNNETH subproject, `Submission/Work/Kunneth/`); the generator is
   `Work.Gen.Cp2Cp2FundamentalClass` (delegated); the identification is the product tangent bundle
   `T(ℂP² × ℂP²) ≅ π₁^*TℂP² ⊕ π₂^*TℂP²` plus the Whitney sum formula.

## SESSION 7 note: the one project-level blocker, and where it is documented

Both gaps above consume the **cross-rank** Whitney sum formula, and, for the second, the
identification of *defined* Chern classes with the classical ones.  Both cross-rank statements are
*equivalent* to `σ(2) = σ(4) = 1`, where `σ(k)` is the orientation sign of the **opaque**
`Classical.choice` `Work.Thom.covE k` (see `README.md` SESSION 7, and
`Submission/Work/Whitney/_tcm/REDUCTION.md` §3 for the same analysis in the WHITNEY area).  The
repair is a **one-line definitional change in the Thom area** (replace `covE` by the canonical
sum-compatible realification `Work.Whitney.rif`, whose compatibility `rif_sum_compatible` is proved
`sorry`-free); it is *not* in this area's files, and no same-index theorem of the workspace is
affected by it.  The `ℂP² × ℂP²` side has been made *explicit* here
(`Work.Gen.cp2cp2ChartedSpaceExplicit`, previously an opaque `Classical.choose` — see `README.md`
SESSION 7, D2), and its tangent half is delegated
(`Work.Gen.Cp2Cp2TangentSplits`, `Work.Gen.Cp2Cp2TangentClasses`).
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

/-! ## The wires: each gap of this file is *derived* here from its single external input

Two inputs live outside AREA GEN (`README.md`, SESSION 8), and each of them is the target of another
area, both now unblocked by the `D1` cure (the realification `Work.Gen.rifStd` adopted by
`Work.Thom.covE`, `Submission/Work/Thom/CovDefs.lean`):

* `Work.Gen.WhFormulaCP4` — the Whitney sum formula for pairs of complex bundles **over `ℂP⁴`**
  (WHITNEY / LERAYHIRSCH: `Work.Whitney.chernClass_whitneySum` and
  `Work.LerayHirsch.WhitneySumFormulaFromLerayHirsch`).  It is strictly weaker than
  `Work.Gen.WhitneyFormula` (`Work.Gen.whFormulaCP4_of_whitney`);
* the Künneth model of `ℂP² × ℂP²` — a `M : CP2CP2Model cppSSet` with `span{M.c} = ⊤` whose classes
  `a, b` are the pullbacks `π₁^*u, π₂^*u` (KUNNETH), together with the two identity hypotheses
  `h1`, `h2` below, which are *definitional* for that model.

The lemmas below verify that nothing else is missing: each gap of the deliverable is *derived* from
its input, so that when the input lands the gap closes by one application (`cp4_p1_eq_of hW`,
`cp4_p2_eq_of hW`, `cp2cp2_model_of_whitney hW M hc h1 h2`).
-/

/-- **Gap 1 from its input**: `p₁(TℂP⁴) = 5u²` for the *defined* class `Work.Thom.p1Tangent'`,
from the Whitney formula over `ℂP⁴` (via `Work.Gen.EulerChern_of_CP4` and the presentation
independence `Work.Gen.cp4ChernPresentation`). -/
theorem cp4_p1_eq_of (hW : WhFormulaCP4) :
    Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4) = (5 : ℤ) • uSq 4 := by
  rw [Work.Thom.p1Tangent'_def, Work.Gen.cp4ChernPresentation 2, (EulerChern_of_CP4 hW).1]
  exact neg_neg _

/-- **Gap 2 from its input**: `p₂(TℂP⁴) = 10u⁴` for the *defined* class `Work.Thom.p2Tangent'`. -/
theorem cp4_p2_eq_of (hW : WhFormulaCP4) :
    Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4) = (10 : ℤ) • uFourth 4 := by
  rw [Work.Thom.p2Tangent'_def, Work.Gen.cp4ChernPresentation 4, (EulerChern_of_CP4 hW).2]

/-- **Gap 3 from its inputs**: given the Whitney sum formula and a Künneth model `M` of
`ℂP² × ℂP²` whose classes `p₁`, `p₂` are the pullback expressions (the content of the Künneth
model's fields, with `a = π₁^*u`, `b = π₂^*u`), the *defined* tangent classes of `ℂP² × ℂP²` are
the model's.  This is `Work.Gen.cp2cp2TangentClasses` (the product splitting of
`Work.Gen.cp2cp2TangentSplits`, conditional on the Whitney sum formula) plugged into the model. -/
theorem cp2cp2_model_of_whitney (hW : Work.Gen.WhitneyFormula) (M : CP2CP2Model cppSSet)
    (hc : Submodule.span ℤ {M.c} = ⊤)
    (h1 : M.p₁ = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
    (h2 : M.p₂ = (9 : ℤ) • Work.Cohomology.cupH'
        ℤ (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))) 4 4
        ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
        ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))) :
    ∃ M' : CP2CP2Model cppSSet, Submodule.span ℤ {M'.c} = ⊤ ∧
      Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M'.p₁ ∧
      Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M'.p₂ := by
  have hC := Work.Gen.cp2cp2TangentClasses hW Work.Gen.cp2cp2TangentSplits
  exact ⟨M, hc, hC.1.trans h1.symm, hC.2.trans h2.symm⟩

/-- **THE DELIVERABLE FROM ITS TWO INPUTS**: `Work.Drive.Generators8` follows from

* the Whitney sum formula `Work.Gen.WhitneyFormula` (WHITNEY: `TopClassMul`/`chernClass_whitneySum`
  via the relative Thom-product formula; LERAYHIRSCH: the intermediate degrees.  Both are unblocked
  by the `D1` cure), and
* a Künneth model `M` of `ℂP² × ℂP²` with a generating fundamental class whose classes are the
  pullback expressions `3(π₁^*u² + π₂^*u²)` and `9(π₁^*u² ⌣ π₂^*u²)` (KUNNETH).

Nothing else is needed: `Work.Gen.cp2cp2_model_of_whitney` (gap `3`, via the product splitting of
`Work.Gen.cp2cp2TangentSplits`) and `Work.Gen.cp4_p1_eq_of`/`cp4_p2_eq_of` (gaps `1`–`2`, via
`Work.Gen.EulerChern_of_CP4` and `Work.Gen.cp4ChernPresentation`) reduce the two inputs to the
hypotheses of the assembly `Work.Gen.Generators8Of`. -/
theorem generators8_of (hW : Work.Gen.WhitneyFormula) (M : CP2CP2Model cppSSet)
    (hc : Submodule.span ℤ {M.c} = ⊤)
    (h1 : M.p₁ = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
    (h2 : M.p₂ = (9 : ℤ) • Work.Cohomology.cupH'
        ℤ (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))) 4 4
        ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
        ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))) :
    Work.Drive.Generators8 := by
  obtain ⟨M', hc', h1', h2'⟩ := cp2cp2_model_of_whitney hW M hc h1 h2
  exact Generators8Of (cp4_p1_eq_of (whFormulaCP4_of_whitney hW))
    (cp4_p2_eq_of (whFormulaCP4_of_whitney hW)) M' hc' h1' h2'
/-- **The Chern classes of the defined tangent bundle of `ℂP⁴`**:
`p₁(TℂP⁴) = 5·u²` and `p₂(TℂP⁴) = 10·u⁴`, with `u = Work.Gen.uCoh 4 = c₁(O(1))`.

This is the content of `Work.Gen.EulerChern`; it is isolated here so that the assembly below is a
complete proof from this single input. -/
theorem cp4_p1_eq :
    Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4) = (5 : ℤ) • uSq 4 := by
  -- The single remaining input: the Whitney sum formula (WHITNEY's `TopClassMul` /
  -- `chernClass_whitneySum`, LERAYHIRSCH's intermediate degrees), see `README.md` SESSION 9.
  -- The input in the *paracompact* form that the LERAYHIRSCH route delivers
  -- (`Work.Gen.whFormulaCP4_of_par`); `ℂP⁴` is compact Hausdorff.
  -- The single remaining input: the Leray--Hirsch theorem (`Work.LerayHirsch.LerayHirschFull`)
  -- for every complex bundle; the `(1,N)` input of the roof is the proved
  -- `Work.Gen.whitneySumFormulaPar_one_N`.
  have hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      Work.LerayHirsch.LerayHirschFull Z := Work.Gen.lerayHirschFull_all
  have hpar : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
    whitneySumFormulaPar_of_lerayHirsch' hLH
  exact cp4_p1_eq_of (whFormulaCP4_of_par hpar)

/-- **The second Pontryagin class of `ℂP⁴`**: `p₂(TℂP⁴) = 10·u⁴`.  See `cp4_p1_eq`. -/
theorem cp4_p2_eq :
    Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4) = (10 : ℤ) • uFourth 4 := by
  -- The single remaining input: the Leray--Hirsch theorem (`Work.LerayHirsch.LerayHirschFull`)
  -- for every complex bundle; the `(1,N)` input of the roof is the proved
  -- `Work.Gen.whitneySumFormulaPar_one_N`.
  have hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      Work.LerayHirsch.LerayHirschFull Z := Work.Gen.lerayHirschFull_all
  have hpar : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
    whitneySumFormulaPar_of_lerayHirsch' hLH
  exact cp4_p2_eq_of (whFormulaCP4_of_par hpar)

/-- **The Künneth ring of `ℂP² × ℂP²` for the concrete space, with a generating fundamental class
and the defined tangent classes identified with the model's `p₁`, `p₂`.** -/
theorem cp2cp2_model : ∃ M : CP2CP2Model cppSSet, Submodule.span ℤ {M.c} = ⊤ ∧
    Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₁ ∧
    Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₂ := by
  -- The same *paracompact* input as gaps 1--2: `ℂP² × ℂP²` is compact Hausdorff, and every base
  -- at which the class computation consumes the Whitney formula is compact too.
  -- The single remaining input: the Leray--Hirsch theorem (`Work.LerayHirsch.LerayHirschFull`)
  -- for every complex bundle; the `(1,N)` input of the roof is the proved
  -- `Work.Gen.whitneySumFormulaPar_one_N`.
  have hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      Work.LerayHirsch.LerayHirschFull Z := Work.Gen.lerayHirschFull_all
  have hpar : ∀ m₁ m₂ : ℕ, Work.LerayHirsch.WhitneySumFormulaPar m₁ m₂ :=
    whitneySumFormulaPar_of_lerayHirsch' hLH
  have hC : Work.Gen.Cp2Cp2TangentClasses :=
    Work.Gen.cp2cp2TangentClassesPar hpar Work.Gen.cp2cp2TangentSplits
  obtain ⟨M, hc, h1, h2⟩ := Work.Gen.cp2cp2KunnethInput
  exact ⟨M, hc, hC.1.trans h1.symm, hC.2.trans h2.symm⟩

/-- **THE DELIVERABLE**: two closed connected oriented `C^∞` `8`-manifolds satisfying
`45σ = 7p₂ - p₁²` for the defined tangent-bundle classes, with independent `(p₁², p₂)`-vectors.
They are `G₁ = ℂP⁴` and `G₂ = ℂP² × ℂP²`, with numbers `(1, 25, 10)` and `(1, 18, 9)`. -/
theorem generators8 : Work.Drive.Generators8 := by
  obtain ⟨M, hc, h1, h2⟩ := cp2cp2_model
  exact Generators8Of cp4_p1_eq cp4_p2_eq M hc h1 h2

end Work.Gen
