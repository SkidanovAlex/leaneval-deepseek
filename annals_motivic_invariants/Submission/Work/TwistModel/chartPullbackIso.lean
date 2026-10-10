/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.BaseChange
import Submission.Work.Twist.away_chart_mvPolynomial_X
import Submission.Work.TwistModel.mvPolynomial_tensorBaseChange

set_option linter.unusedVariables false -- v435-speed

/-!
# Each chart of the base change `ℙⁿ_K` is `𝔸ⁿ_K`

`Work.TwistModel.chartPullback 𝕜 n K i` is the `i`-th standard chart `D₊(X_i)` of the base change
`ℙⁿ_𝕜 ×_{Spec 𝕜} Spec K` of the projective space along a field extension `K/𝕜`.  This file proves
that it is the affine `n`-space over `K`:

  `chartPullbackIso 𝕜 n K i : chartPullback 𝕜 n K i ≅ Spec K[y₁,…,yₙ]`.

The proof is a chain of isomorphisms, all of them instances of Mathlib's calculus of fibre squares
and of the affine charts of `Proj`:

* `pullbackRestrictIsoRestrict`: the preimage of an open subscheme is the fibre product with it,
  so `chartPullback 𝕜 n K i ≅ pullback q (D₊(X_i)).ι` where `q : ℙⁿ_K ⟶ ℙⁿ`;
* `Proj.basicOpenIsoSpec`: the chart `D₊(X_i)` of `ℙⁿ` is `Spec A` for the chart ring
  `A = A⁰_{X_i}` (the degree-zero part of `𝕜[X₀,…,X_n]` localised at `X_i`);
* `pullbackRightPullbackFstIso`: two nested fibre products `Spec A ×_{ℙⁿ} (ℙⁿ ×_{Spec 𝕜} Spec K)`
  and `Spec A ×_{Spec 𝕜} Spec K` agree, using `awayι_projectiveSpaceToSpec`, i.e. that the chart
  inclusion `Spec A ⟶ ℙⁿ` is the structure morphism of `Spec A` over `Spec 𝕜` (with the
  `𝕜`-algebra structure `chartRingAlgebra` on `A` given by the grading);
* `pullbackSpecIso`: a fibre product of affine schemes over `Spec 𝕜` is the spectrum of the
  tensor product, so we arrive at `Spec (A ⊗_𝕜 K)`;
* the chart ring of `ℙⁿ` is a polynomial ring (`Work.Twist.away_chart_mvPolynomial_X`), and the
  base change of a polynomial ring is a polynomial ring
  (`Work.TwistModel.mvPolynomial_tensorBaseChange`), so `A ⊗_𝕜 K ≅ K[y₁,…,yₙ]`.

Consequently `chartPullback 𝕜 n K i` is an integral affine scheme, which is what the cover
argument of `Work.TwistModel.isIntegral_projectiveSpaceBaseChange` needs to conclude that the
base change of `ℙⁿ` is integral.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

namespace Work.TwistModel

noncomputable section

/-! ## 1. The chart ring of `ℙⁿ` at `X i` and its `𝕜`-algebra structure -/

/-- The coordinate ring `A⁰_{X_i}` of the affine chart `D₊(X_i)` of `ℙⁿ_𝕜`: the degree-zero part
of the localisation of `𝕜[X₀,…,X_n]` at `X_i`. -/
abbrev chartRing (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) : Type :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
    (MvPolynomial.X i)

/-- **The `𝕜`-algebra structure of the chart ring.**  `𝕜` is the degree-zero part `𝒜 0` of the
standard grading of `𝕜[X₀,…,X_n]`, mapped into the chart ring by `fromZeroRingHom`.  Mathlib does
not register this instance (the chart ring is only canonically an algebra over `𝒜 0`), so it is
recorded here. -/
@[instance_reducible]
def chartRingAlgebra (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Algebra 𝕜 (chartRing 𝕜 n i) :=
  RingHom.toAlgebra <|
    (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X i))).comp
      ((Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).symm.toRingHom)

/-- The structure morphism `ℙⁿ_𝕜 ⟶ Spec 𝕜`. -/
abbrev projStruct (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Work.PointlessIndexFive.projectiveSpace 𝕜 n ⟶ Spec (CommRingCat.of 𝕜) :=
  Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n

/-- The base change morphism `Spec K ⟶ Spec 𝕜`. -/
abbrev baseMap (𝕜 : Type) [Field 𝕜] (K : Type) [Field K] [Algebra 𝕜 K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K))

/-- The standard chart `D₊(X_i)` of `ℙⁿ_𝕜`. -/
abbrev chartOpen (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    (Work.PointlessIndexFive.projectiveSpace 𝕜 n).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i)

/-- The open immersion of the chart: `Spec A⁰_{X_i} ⟶ ℙⁿ_𝕜`. -/
abbrev chartIncl (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Spec (CommRingCat.of (chartRing 𝕜 n i)) ⟶ Work.PointlessIndexFive.projectiveSpace 𝕜 n :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i)
    (Work.Twist.Xi_mem_stdGrading 𝕜 n i) (by norm_num)

/-- `chartIncl` is an open immersion (Mathlib's instance is about `Proj.awayι`, which instance
search does not see through the abbreviation `chartIncl`). -/
instance chartIncl_isOpenImmersion (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (chartIncl 𝕜 n i) := by
  show IsOpenImmersion (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
    (MvPolynomial.X i) (Work.Twist.Xi_mem_stdGrading 𝕜 n i) (by norm_num))
  infer_instance

/-- The image of the chart inclusion is the standard chart `D₊(X_i)`. -/
theorem chartIncl_opensRange (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Scheme.Hom.opensRange (chartIncl 𝕜 n i) = chartOpen 𝕜 n i :=
  Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
    (MvPolynomial.X i) (Work.Twist.Xi_mem_stdGrading 𝕜 n i) (by norm_num)

/-! ## 2. The chart ring is the polynomial ring, compatibly with the constants -/

/-- **The dehomogenisation `chartPsiX` commutes with the constants.**  `Work.Twist.chartPsiX` is
the isomorphism `A⁰_{X_i} ≅ 𝕜[y₁,…,yₙ]` of `Work.Twist.away_chart_mvPolynomial_X`; here we record
that it sends the constants `𝒜 0` of `𝕜[X₀,…,X_n]` to the corresponding constants of
`𝕜[y₁,…,yₙ]`.  This is the general-`i` form of `Work.Twist.exists_chart_away_X_zero_compat`. -/
theorem chartPsiX_fromZeroRingHom (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1))
    (c : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 0)) :
    Work.Twist.chartPsiX 𝕜 n i
        (HomogeneousLocalization.fromZeroRingHom
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (Submonoid.powers (MvPolynomial.X i)) c)
      = MvPolynomial.C (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n c) := by
  have hx : c.1 ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 (0 • 1) := by
    rw [zero_smul]; exact c.2
  have hmk : HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X i)) c
      = HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (Work.Twist.Xi_mem_stdGrading 𝕜 n i) 0 c.1 hx := by
    have h1 : HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X i)) c
        = HomogeneousLocalization.mk ⟨0, c, 1, one_mem _⟩ := rfl
    rw [h1]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
    simp
  rw [hmk]
  change Work.Twist.chartPsiX 𝕜 n i
    (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
      (Work.Twist.Xi_mem_stdGrading 𝕜 n i) 0 c.1 hx) = _
  rw [Work.Twist.chartPsiX_awayMk]
  rw [← (Work.PointlessIndexFive.exists_zeroComponentRingEquiv 𝕜 (Fin (n + 1))).choose_spec c]
  rw [Work.Twist.chartDhomX_apply, MvPolynomial.rename_C, Work.Twist.chartDhom,
    MvPolynomial.eval₂Hom_C, MvPolynomial.algebraMap_eq]
  rfl

/-! ## 3. The chart inclusion is the structure morphism of the chart ring -/

/-- **The structure morphism of the chart.**  The open immersion `Spec A⁰_{X_i} ⟶ ℙⁿ_𝕜` of the
standard chart is `Spec.map` of the `𝕜`-algebra structure map of the chart ring
(`chartRingAlgebra`), i.e. the chart inclusion is a morphism of `Spec 𝕜`-schemes.  This is
`Proj.awayι_toSpecZero` combined with the definition of `projectiveSpaceToSpec` and of the
`𝕜`-algebra structure on the chart ring. -/
theorem awayι_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i)
      (Work.Twist.Xi_mem_stdGrading 𝕜 n i) (by norm_num) ≫
      Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n
    = Spec.map (CommRingCat.ofHom (@algebraMap 𝕜 (chartRing 𝕜 n i) _ _
        (chartRingAlgebra 𝕜 n i))) := by
  have hkey : (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X i)))
      = CommRingCat.ofHom (@algebraMap 𝕜 (chartRing 𝕜 n i) _ _ (chartRingAlgebra 𝕜 n i)) := by
    rw [show (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv
        = CommRingCat.ofHom (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).symm.toRingHom
        from rfl, ← CommRingCat.ofHom_comp]
  show Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i)
      (Work.Twist.Xi_mem_stdGrading 𝕜 n i) (by norm_num) ≫
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) ≫
        Spec.map (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)
    = Spec.map (CommRingCat.ofHom (@algebraMap 𝕜 (chartRing 𝕜 n i) _ _
        (chartRingAlgebra 𝕜 n i)))
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, hkey]

/-! ## 4. The chart of the base change is the affine space -/

/-- **The chart `D₊(X_i)` of the base change `ℙⁿ_K` is `𝔸ⁿ_K`.**  The preimage of the standard
chart `D₊(X_i)` of `ℙⁿ_𝕜` under the projection `ℙⁿ_K ⟶ ℙⁿ_𝕜` is isomorphic to
`Spec K[y₁,…,yₙ]`, the affine `n`-space over `K`. -/
theorem chartPullbackIso (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K] [Algebra 𝕜 K]
    (i : Fin (n + 1)) :
    Nonempty (Work.TwistModel.chartPullback 𝕜 n K i ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) K))) := by
  classical
  -- the `𝕜`-algebra structure on the chart ring, and the chart isomorphism over `𝕜`
  letI : Algebra 𝕜 (chartRing 𝕜 n i) := chartRingAlgebra 𝕜 n i
  let eA : chartRing 𝕜 n i ≃+* MvPolynomial (Fin n) 𝕜 :=
    RingEquiv.ofBijective (Work.Twist.chartPsiX 𝕜 n i)
      ⟨Work.Twist.chartPsiX_injective 𝕜 n i, Work.Twist.chartPsiX_surjective 𝕜 n i⟩
  have hAlg : ∀ r : 𝕜, eA (algebraMap 𝕜 (chartRing 𝕜 n i) r)
      = algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜) r := by
    intro r
    have h1 : algebraMap 𝕜 (chartRing 𝕜 n i) r
        = HomogeneousLocalization.fromZeroRingHom
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
            (Submonoid.powers (MvPolynomial.X i))
            ((Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).symm r) := rfl
    rw [h1]
    show Work.Twist.chartPsiX 𝕜 n i _ = _
    rw [chartPsiX_fromZeroRingHom, RingEquiv.apply_symm_apply, MvPolynomial.algebraMap_eq]
  let eA' : chartRing 𝕜 n i ≃ₐ[𝕜] MvPolynomial (Fin n) 𝕜 := AlgEquiv.ofRingEquiv (f := eA) hAlg
  -- the chart ring of the base change is a polynomial ring
  obtain ⟨eK⟩ := mvPolynomial_tensorBaseChange 𝕜 n K
  have hring : TensorProduct 𝕜 (chartRing 𝕜 n i) K ≃+* MvPolynomial (Fin n) K :=
    (Algebra.TensorProduct.congr eA' (AlgEquiv.refl : K ≃ₐ[𝕜] K)).toRingEquiv.trans eK.toRingEquiv
  -- the compatiblity of the chart inclusion with the structure morphisms
  have hcompat : chartIncl 𝕜 n i ≫ projStruct 𝕜 n
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (chartRing 𝕜 n i))) :=
    awayι_projectiveSpaceToSpec 𝕜 n i
  -- the chain of isomorphisms
  have step1 : Work.TwistModel.chartPullback 𝕜 n K i ≅
      pullback (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartOpen 𝕜 n i).ι :=
    (pullbackRestrictIsoRestrict (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K))
      (chartOpen 𝕜 n i)).symm
  have step2 : pullback (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartOpen 𝕜 n i).ι ≅
      pullback (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartIncl 𝕜 n i) := by
    refine IsOpenImmersion.isoOfRangeEq
      (pullback.fst (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartOpen 𝕜 n i).ι)
      (pullback.fst (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartIncl 𝕜 n i)) ?_
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
      Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Opens.opensRange_ι, chartIncl_opensRange]
  have step3 : pullback (pullback.fst (projStruct 𝕜 n) (baseMap 𝕜 K)) (chartIncl 𝕜 n i) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (chartRing 𝕜 n i)))) (baseMap 𝕜 K) :=
    (pullbackSymmetry _ _).trans <|
      (pullbackRightPullbackFstIso (projStruct 𝕜 n) (baseMap 𝕜 K) (chartIncl 𝕜 n i)).trans <|
        pullback.congrHom hcompat rfl
  have step4 : pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (chartRing 𝕜 n i))))
      (baseMap 𝕜 K) ≅ Spec (CommRingCat.of (TensorProduct 𝕜 (chartRing 𝕜 n i) K)) :=
    pullbackSpecIso 𝕜 (chartRing 𝕜 n i) K
  refine ⟨step1.trans (step2.trans (step3.trans (step4.trans ?_)))⟩
  exact (Scheme.Spec.mapIso hring.toCommRingCatIso.op).symm

end

end Work.TwistModel
