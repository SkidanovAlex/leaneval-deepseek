import Mathlib
import Submission.Work.Gen.Cp2Cp2TangentClasses
import Submission.Work.Gen.Cp2Cp2TangentSplits
import Submission.Work.Gen.eulerSequence_iso_two
import Submission.Work.Gen.TangentPresentation
import Submission.Work.Gen.C1LineTrivial
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Agree.PlumbDefs
import Submission.Work.Agree.whitneySumRCongr
import Submission.Work.Gen.cp4ChernPresentation
import Submission.Work.Projective.cpn_cohomology
import Submission.Work.Gen.stdTangentTwoChern
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — the defined tangent classes of `ℂP² × ℂP²`

`Work.Gen.cp2cp2TangentClasses`: the *defined* Pontryagin classes
`Work.Thom.p1Tangent'`, `Work.Thom.p2Tangent'` of `ℂP² × ℂP²` — i.e. `-c₂` and `c₄` of
`T ⊗_ℝ ℂ` in the canonical finite-cover presentation `Work.Thom.complexifiedTangentBundleFinite` —
are the classical ones

  `p₁ = 3·(π₁^*u² + π₂^*u²)`,  `p₂ = 9·(π₁^*u² ⌣ π₂^*u²)`,

with `u² = Work.Gen.uSq 2` the hyperplane square of `ℂP²`.

The proof assembles the two GEN-owned inputs:

* the product splitting `Work.Gen.Cp2Cp2TangentSplits` (`T(ℂP²×ℂP²) ≅ π₁^*TℂP² ⊕ π₂^*TℂP²` in the
  presentation of the explicit `ℝ⁸`-atlas), transported to the finite presentations by the
  reindexing self-isomorphisms `Work.Agree.nonempty_bundleIso_reindexCore_self` and the direct-sum
  congruence `Work.Agree.nonempty_bundleIso_sumCore_congr`;
* the Chern classes `c₁ = 0`, `c₂ = -3u²`, `c₃ = 0`, `c₄ = 3u⁴` of `ℂ ⊗_ℝ TℂP²`
  (`Work.Gen.stdTangentTwoChern`, the Euler sequence of `ℂP²`) transported along the two projections
  by naturality (`Work.Thom.chernClass_comap`);
* the Whitney sum formula in degrees `2` and `4` (the hypothesis `Work.Gen.WhitneyFormula`);
* `H⁸(ℂP²;ℤ) = 0` (`Work.Gen.uFourthTwoZero`), which kills the top Chern classes of the factors.
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

noncomputable section

open Work.Projective

attribute [local instance] cp2cp2ChartedSpaceEuclid
attribute [local instance] cp2cp2IsManifoldEuclid
attribute [local instance] cp2ChartedSpace
attribute [local instance] cp2IsManifold

local instance instCompactCP2 : CompactSpace (CP 2) := Work.Projective.compactSpace_CP 2

local instance instCompactCP2CP2 : CompactSpace (CP 2 × CP 2) := inferInstance

/-! ## `H⁸(ℂP²;ℤ) = 0` -/

/-- `Fin 0 → α` is a subsingleton. -/
theorem subsingleton_fin_zero (α : Type) : Subsingleton (Fin 0 → α) :=
  ⟨fun a b => funext fun i => i.elim0⟩

/-- **`u⁴ = 0` in `H⁸(ℂP²;ℤ)`**: `ℂP²` has real dimension `4`, so its cohomology vanishes above
degree `4` (`Work.Projective.cpn_cohomology`). -/
theorem uFourthTwoZero : Work.Gen.uFourth 2 = 0 := by
  obtain ⟨e⟩ := Work.Projective.cpn_cohomology 2 8
  haveI : Subsingleton (Fin (if Even 8 ∧ 8 ≤ 2 * 2 then 1 else 0) → ℤ) := by
    rw [show (if Even 8 ∧ 8 ≤ 2 * 2 then 1 else 0) = 0 from by norm_num]
    exact subsingleton_fin_zero ℤ
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact hinj (Subsingleton.elim _ _)

/-! ## The presentations of the product tangent bundle -/

/-- The finite chart cover of `ℂP² × ℂP²`, as a family of charts of the pushed-forward `ℝ⁸`-atlas. -/
abbrev cppCover8 : Fin (Work.Thom.chartCoverSize (H := EuclideanSpace ℝ (Fin 8))
      (M := CP 2 × CP 2)) → atlas (EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) :=
  Work.Thom.chartCover

/-- The covering property of `cppCover8`. -/
theorem cppCover8Covers : ∀ x : CP 2 × CP 2,
    ∃ i, x ∈ (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)).baseSet
      (cppCover8 i) :=
  fun x => Work.Thom.chartCover_reindex_cover 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) x

/-- The product splitting `π₁^*(ℂ ⊗ TℂP²) ⊕ π₂^*(ℂ ⊗ TℂP²)`, as stated in
`Work.Gen.Cp2Cp2TangentSplits`. -/
abbrev cppW : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin (4 + 4)))
    (atlas (EuclideanSpace ℝ (Fin 4)) (CP 2) × atlas (EuclideanSpace ℝ (Fin 4)) (CP 2)) :=
  Work.Whitney.whitneySum (factorTangentC projFirst) (factorTangentC projSecond)

/-- `cp2cp2TangentC` reindexed along the finite chart cover `cppCover8`. -/
abbrev cppLeftFin : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin 8))
    (Fin (Work.Thom.chartCoverSize (H := EuclideanSpace ℝ (Fin 8)) (M := CP 2 × CP 2))) :=
  Work.Agree.reindexCore cp2cp2TangentC cppCover8 cppCover8Covers

/-- The first factor `π₁^*(ℂ ⊗_ℝ TℂP²)`, reindexed along the three standard charts of `ℂP²`. -/
abbrev cppZ1 : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin 4)) (Fin 3) :=
  Work.Agree.reindexCore (factorTangentC projFirst) (stdChart 2)
    (fun x => stdChart_covers 2 (projFirst x))

/-- The second factor `π₂^*(ℂ ⊗_ℝ TℂP²)`, reindexed along the three standard charts of `ℂP²`. -/
abbrev cppZ2 : VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin 4)) (Fin 3) :=
  Work.Agree.reindexCore (factorTangentC projSecond) (stdChart 2)
    (fun x => stdChart_covers 2 (projSecond x))

/-- `cppZ1` is the pullback of the standard presentation `stdTangentC 2` along `projFirst`. -/
theorem cppZ1_eq : cppZ1 = Work.Thom.bundleComap (stdTangentC 2) projFirst := rfl

/-- `cppZ2` is the pullback of the standard presentation `stdTangentC 2` along `projSecond`. -/
theorem cppZ2_eq : cppZ2 = Work.Thom.bundleComap (stdTangentC 2) projSecond := rfl

/-! ## The general-base Whitney formula in degrees `2` and `4` -/

/-- **The Whitney formula in degree `2`**, over an arbitrary base. -/
theorem whitney_two_gen (hW : Work.Gen.WhitneyFormula) {B : Type} [TopologicalSpace B]
    {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 2 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 4 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 2 2 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 0 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 2), Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero, Nat.sub_self, Nat.add_zero,
    Nat.mul_zero]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']

/-- **The Whitney formula in degree `4`**, over an arbitrary base. -/
theorem whitney_four_gen (hW : Work.Gen.WhitneyFormula) {B : Type} [TopologicalSpace B]
    {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) 4 (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 8 (Work.Thom.chernClass m₁ 0 Z₁)
          (Work.Thom.chernClass m₂ 4 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 2 6 (Work.Thom.chernClass m₁ 1 Z₁)
          (Work.Thom.chernClass m₂ 3 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 (Work.Thom.chernClass m₁ 2 Z₁)
          (Work.Thom.chernClass m₂ 2 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 6 2 (Work.Thom.chernClass m₁ 3 Z₁)
          (Work.Thom.chernClass m₂ 1 Z₂)
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 8 0 (Work.Thom.chernClass m₁ 4 Z₁)
          (Work.Thom.chernClass m₂ 0 Z₂) := by
  rw [hW Z₁ Z₂ (j := 4), Fin.sum_univ_five]
  rw [Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id',
    Work.Gen.cohTransport_eq_id', Work.Gen.cohTransport_eq_id']
  rfl

/-! ## Integer multiples as sums -/

/-- `3 • x = x + x + x`. -/
theorem three_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    (3 : ℤ) • x = x + x + x := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, natCast_zsmul,
    show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul,
    show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]

/-- `9 • x = x + ⋯ + x` (nine times). -/
theorem nine_zsmul_eq {M : Type} [AddCommGroup M] (x : M) :
    (9 : ℤ) • x = x + x + x + x + x + x + x + x + x := by
  rw [show (9 : ℤ) = ((9 : ℕ) : ℤ) from rfl, natCast_zsmul,
    show (9 : ℕ) = 8 + 1 from rfl, add_nsmul, one_nsmul,
    show (8 : ℕ) = 7 + 1 from rfl, add_nsmul, one_nsmul,
    show (7 : ℕ) = 6 + 1 from rfl, add_nsmul, one_nsmul,
    show (6 : ℕ) = 5 + 1 from rfl, add_nsmul, one_nsmul,
    show (5 : ℕ) = 4 + 1 from rfl, add_nsmul, one_nsmul,
    show (4 : ℕ) = 3 + 1 from rfl, add_nsmul, one_nsmul,
    show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul,
    show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]

/-! ## The cup product, in the form `cupH'` expects -/
variable {B : Type} [TopologicalSpace B]

/-- **Negation in the first argument of the middle cup product.** -/
theorem cupH_neg_left4 (x y : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 (-x) y
      = -(Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x y) := by
  rw [map_neg, LinearMap.neg_apply]

/-- **Negation in the second argument of the middle cup product.** -/
theorem cupH_neg_right4 (x y : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x (-y)
      = -(Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x y) := by
  rw [map_neg]

/-- **Additivity in the first argument of the middle cup product.** -/
theorem cupH_add_left4 (x x' y : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 (x + x') y
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x y
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x' y :=
  Work.Cohomology.cupH'_add_left ℤ (Work.Whitney.ssB B) 4 4 x x' y

/-- **Additivity in the second argument of the middle cup product.** -/
theorem cupH_add_right4 (x y y' : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x (y + y')
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x y
        + Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 x y' :=
  Work.Cohomology.cupH'_add_right ℤ (Work.Whitney.ssB B) 4 4 x y y'

/-- `1 ⌣ x = x` in degree `4`. -/
theorem cupH_one_left4 (x : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 4
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) x = x := by
  rw [Work.Cohomology.cupH'_one_left]

/-- `x ⌣ 1 = x` in degree `4`. -/
theorem cupH_one_right4 (x : Work.Thom.Coh ℤ 4 B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 0 x
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) = x :=
  Work.Cohomology.cupH'_one_right ℤ (Work.Whitney.ssB B) 4 x

end

end Work.Gen

namespace Work.Gen

noncomputable section

open Work.Projective

attribute [local instance] cp2cp2ChartedSpaceEuclid
attribute [local instance] cp2cp2IsManifoldEuclid
attribute [local instance] cp2ChartedSpace
attribute [local instance] cp2IsManifold

local instance instCompactCP2' : CompactSpace (CP 2) := Work.Projective.compactSpace_CP 2

local instance instCompactCP2CP2' : CompactSpace (CP 2 × CP 2) := inferInstance

/-! ## The main theorem -/

theorem cp2cp2TangentClasses (hW : Work.Gen.WhitneyFormula) (hSplits : Work.Gen.Cp2Cp2TangentSplits) :
    Work.Gen.Cp2Cp2TangentClasses := by
  -- The isomorphism `cppLeftFin ≅ cppZ1 ⊕ cppZ2` in the finite presentations.
  have hiso : Nonempty (Work.Thom.BundleIso cppLeftFin (Work.Whitney.whitneySum cppZ1 cppZ2)) := by
    obtain ⟨e1⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self cp2cp2TangentC cppCover8
      cppCover8Covers
    obtain ⟨e2⟩ := hSplits
    obtain ⟨ea⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (factorTangentC projFirst)
      (stdChart 2) (fun x => stdChart_covers 2 (projFirst x))
    obtain ⟨eb⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (factorTangentC projSecond)
      (stdChart 2) (fun x => stdChart_covers 2 (projSecond x))
    obtain ⟨e3⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
      (Work.Whitney.sumFibreC 4 4) (Work.Whitney.sumFibreC 4 4)
      (factorTangentC projFirst) cppZ1 (factorTangentC projSecond) cppZ2 ea.symm eb.symm
    exact ⟨e1.trans (e2.trans e3)⟩
  -- Presentation independence: the canonical finite-cover presentation has the Chern classes of
  -- `cppLeftFin`.
  have hpres (j : ℕ) : Work.Thom.chernClass
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) j
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2))
      = Work.Thom.chernClass 8 j cppLeftFin := by
    have h1 : (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2)).mapFibre (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))).reindex
            cppCover8 cppCover8Covers)
        = (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2)).reindex cppCover8 cppCover8Covers).mapFibre
            (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))) := rfl
    unfold Work.Thom.complexifiedTangentBundleFinite
    rw [h1]
    rw [Work.Gen.chernClass_complexificationCore_mapFibre (k := 8)
      (l := Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) finrank_euclideanSpace_fin
      ((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (CP 2 × CP 2)).reindex cppCover8 cppCover8Covers)
      (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8))) j]
    rfl
  -- The Chern classes of the two factors, transported along the two projections.
  have hZ1c1 : Work.Thom.chernClass 4 1 cppZ1
      = (Work.Thom.CohMap projFirst ℤ 2).hom (Work.Thom.chernClass 4 1 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 1) (stdTangentC 2) projFirst
  have hZ2c1 : Work.Thom.chernClass 4 1 cppZ2
      = (Work.Thom.CohMap projSecond ℤ 2).hom (Work.Thom.chernClass 4 1 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 1) (stdTangentC 2) projSecond
  have hZ1c2 : Work.Thom.chernClass 4 2 cppZ1
      = (Work.Thom.CohMap projFirst ℤ 4).hom (Work.Thom.chernClass 4 2 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 2) (stdTangentC 2) projFirst
  have hZ2c2 : Work.Thom.chernClass 4 2 cppZ2
      = (Work.Thom.CohMap projSecond ℤ 4).hom (Work.Thom.chernClass 4 2 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 2) (stdTangentC 2) projSecond
  have hZ1c3 : Work.Thom.chernClass 4 3 cppZ1
      = (Work.Thom.CohMap projFirst ℤ (2 * 3)).hom
          (Work.Thom.chernClass 4 3 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 3) (stdTangentC 2) projFirst
  have hZ2c3 : Work.Thom.chernClass 4 3 cppZ2
      = (Work.Thom.CohMap projSecond ℤ (2 * 3)).hom
          (Work.Thom.chernClass 4 3 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 3) (stdTangentC 2) projSecond
  have hZ1c4 : Work.Thom.chernClass 4 4 cppZ1
      = (Work.Thom.CohMap projFirst ℤ (2 * 4)).hom
          (Work.Thom.chernClass 4 4 (stdTangentC 2)) := by
    rw [cppZ1_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 4) (stdTangentC 2) projFirst
  have hZ2c4 : Work.Thom.chernClass 4 4 cppZ2
      = (Work.Thom.CohMap projSecond ℤ (2 * 4)).hom
          (Work.Thom.chernClass 4 4 (stdTangentC 2)) := by
    rw [cppZ2_eq]
    exact Work.Thom.chernClass_comap (m := 4) (j := 4) (stdTangentC 2) projSecond
  obtain ⟨hs1, hs2, hs3, hs4⟩ := stdTangentTwoChern hW
  -- The four Chern classes of the factors, in additive form (no integer multiples inside `⌣`).
  have hZ1_1 : Work.Thom.chernClass 4 1 cppZ1 = 0 := by rw [hZ1c1, hs1, map_zero]
  have hZ2_1 : Work.Thom.chernClass 4 1 cppZ2 = 0 := by rw [hZ2c1, hs1, map_zero]
  have hZ1_2 : Work.Thom.chernClass 4 2 cppZ1
      = -(((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
          + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)) := by
    rw [hZ1c2, hs2]
    rw [map_neg (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
    rw [show (3 : ℤ) • (uSq 2) = ((uSq 2 + uSq 2) + uSq 2) from three_zsmul_eq (uSq 2)]
    rw [map_add (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
    rw [map_add (f := (Work.Thom.CohMap projFirst ℤ 4).hom)]
  have hZ2_2 : Work.Thom.chernClass 4 2 cppZ2
      = -(((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) := by
    rw [hZ2c2, hs2]
    rw [map_neg (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
    rw [show (3 : ℤ) • (uSq 2) = ((uSq 2 + uSq 2) + uSq 2) from three_zsmul_eq (uSq 2)]
    rw [map_add (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
    rw [map_add (f := (Work.Thom.CohMap projSecond ℤ 4).hom)]
  have hZ1_3 : Work.Thom.chernClass 4 3 cppZ1 = 0 := by rw [hZ1c3, hs3, map_zero]
  have hZ2_3 : Work.Thom.chernClass 4 3 cppZ2 = 0 := by rw [hZ2c3, hs3, map_zero]
  have hfour : Work.Thom.chernClass 4 4 (stdTangentC 2) = 0 := by
    rw [hs4]
    rw [show (3 : ℤ) • (Work.Gen.uFourth 2)
        = (Work.Gen.uFourth 2 + Work.Gen.uFourth 2) + Work.Gen.uFourth 2 from
      three_zsmul_eq (Work.Gen.uFourth 2)]
    rw [uFourthTwoZero, add_zero, add_zero]
  have hZ1_4 : Work.Thom.chernClass 4 4 cppZ1 = 0 := by rw [hZ1c4, hfour, map_zero]
  have hZ2_4 : Work.Thom.chernClass 4 4 cppZ2 = 0 := by rw [hZ2c4, hfour, map_zero]
  -- the same, with the total space of the finite cover's cohomology made explicit (the form in
  -- which `Work.Cohomology.cupH'` consumes its arguments)
  have hZ1_1u : (Work.Thom.chernClass 4 1 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 1)) = 0 := hZ1_1
  have hZ2_1u : (Work.Thom.chernClass 4 1 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 1)) = 0 := hZ2_1
  have hZ1_3u : (Work.Thom.chernClass 4 3 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 3)) = 0 := hZ1_3
  have hZ2_3u : (Work.Thom.chernClass 4 3 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 3)) = 0 := hZ2_3
  have hZ1_4u : (Work.Thom.chernClass 4 4 cppZ1 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 4)) = 0 := hZ1_4
  have hZ2_4u : (Work.Thom.chernClass 4 4 cppZ2 : (Work.Cohomology.SSetCochainComplex (R := ℤ)
      (Work.Whitney.ssB (CP 2 × CP 2))).homology (2 * 4)) = 0 := hZ2_4
  have hZ1_0 : Work.Thom.chernClass 4 0 cppZ1
      = Work.Cohomology.oneH ℤ (Work.Whitney.ssB (CP 2 × CP 2)) :=
    Work.Thom.chernClass_zero_eq_oneH cppZ1
  have hZ2_0 : Work.Thom.chernClass 4 0 cppZ2
      = Work.Cohomology.oneH ℤ (Work.Whitney.ssB (CP 2 × CP 2)) :=
    Work.Thom.chernClass_zero_eq_oneH cppZ2
  have hchern : ∀ j, Work.Thom.chernClass 8 j cppLeftFin
      = Work.Thom.chernClass 8 j (Work.Whitney.whitneySum cppZ1 cppZ2) :=
    fun j => Work.Thom.chernClass_BundleIso (j := j) cppLeftFin
      (Work.Whitney.whitneySum cppZ1 cppZ2) hiso.some
  unfold Work.Gen.Cp2Cp2TangentClasses
  refine ⟨?_, ?_⟩
  · show - Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 2
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2))
      = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
    rw [hpres 2, hchern 2, whitney_two_gen hW cppZ1 cppZ2, hZ1_0, hZ2_0, hZ1_1, hZ2_1,
      hZ1_2, hZ2_2]
    rw [Work.Cohomology.cupH'_zero_left]
    rw [cupH_one_left4]
    rw [cupH_one_right4]
    rw [show (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        = (((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
          + ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
          + ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
            + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) from
      three_zsmul_eq ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    abel
  · show Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 4
        (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (CP 2 × CP 2))
      = (9 : ℤ) • Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 4
          ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
          ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
    rw [hpres 4, hchern 4, whitney_four_gen hW cppZ1 cppZ2, hZ1_0, hZ2_0, hZ1_1u, hZ2_1u,
      hZ1_2, hZ2_2, hZ1_3u, hZ2_3u, hZ1_4u, hZ2_4u]
    simp only [map_zero, LinearMap.zero_apply, zero_add, add_zero]
    rw [cupH_neg_left4]
    rw [cupH_neg_right4]
    rw [cupH_add_left4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      (((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_left4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      (((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_right4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    rw [cupH_add_right4 ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))]
    have hnine := nine_zsmul_eq (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (CP 2 × CP 2)) 4 4
      ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
      ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)))
    rw [hnine]
    abel

end

end Work.Gen
