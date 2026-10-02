import Mathlib
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.ThomBordism.doubleChartedT2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Shared vocabulary for the Lefschetz duality of the pair `(W, ∂W)` (area THOM)

The proof of `Work.ThomBordism.LefschetzDualityBdry` follows Hatcher's proof of Theorem 3.43
(*Lefschetz duality*) for the pair `(M, ∂M)` with `A = ∂M`, `B = ∅`:

1. **compactly supported duality for the open interior** (Hatcher's Theorem 3.35), realised here
   through the workspace's `Work.Cohomology.Good` machinery applied to the **double**
   `D = M ∪_{∂M} M̄` (a closed charted `9`-manifold, `Work.ThomBordism.Double 8 M`);
2. the comparison `H^k(M, ∂M; ℤ) ≅ H^k_c(int M; ℤ)` (every relative class is supported away from
   the boundary);
3. the comparison `H_{9−k}(M; ℤ) ≅ H_{9−k}(int M; ℤ)` (the interior inclusion is a homology
   equivalence).

This file contains the vocabulary shared by the three ingredients and by the assembly:

* `Work.ThomBordism.secondHalf` — the second half `B ⊆ D` of the double;
* `Work.ThomBordism.inclRelMap` — the map of relative chain complexes `C_*(M, ∂M) ⟶ C_*(D, B)`
  (the map under which the relative fundamental class of `(M,∂M)` corresponds to the fundamental
  class of the double);
* `Work.ThomBordism.projSecondHalf` — the projection `C_*(D) ⟶ C_*(D,B)`;
* `Work.ThomBordism.relRestrOffBdry` — the restriction `H^k(M, Kᶜ) ⟶ H^k(M, ∂M)` for `K` compact in
  the interior (the map of ingredient 2);
* `Work.ThomBordism.relCapPairBdry`, `Work.ThomBordism.LefschetzDualityBdryGen` — the relative cap
  product and the target statement in general form (Hatcher's Theorem 3.43).

Everything here is sorry-free: it is only vocabulary, so that the delegated lemmas
(`ThomBordism/RelDuality/*`) can be stated in terms of it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

/-- **The second half of the double** `D = M ∪_{∂M} M̄`: the image of the second copy of `M`. -/
def secondHalf {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M] : Set (Double 8 M) :=
  Set.range (doubleιN (n := 8) (M := M))

/-- **The inclusion of the first half into the double.** -/
def doubleIncl {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M] :
    TopCat.of M ⟶ TopCat.of (Double 8 M) :=
  TopCat.ofHom ⟨doubleιM (n := 8) (M := M), continuous_doubleιM (n := 8) (M := M)⟩

/-- **The inclusion of the boundary into the seam**: the boundary of `M`, viewed as a subset of the
second half `B` of the double (the two copies of the boundary are identified). -/
def inclBdry {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] :
    TopCat.of {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M} ⟶
      TopCat.of (secondHalf (M := M)) :=
  TopCat.ofHom ⟨fun x => ⟨doubleιM (n := 8) (M := M) x.1,
      ⟨x.1, ((doubleιM_eq_ιN_iff (n := 8) (M := M)).mpr ⟨x, rfl, rfl⟩).symm⟩⟩,
    Continuous.subtype_mk
      (((continuous_doubleιM (n := 8) (M := M)).comp continuous_subtype_val)) _⟩

theorem inclBdry_comp {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M] :
    Work.Cohomology.subtypeIncl (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) ≫ doubleIncl (M := M)
      = inclBdry (M := M) ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double 8 M))
        (secondHalf (M := M)) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro x
  rfl

/-- **The map of relative chain complexes `C_*(M, ∂M) ⟶ C_*(D, B)`** induced by the inclusion of
the first half into the double.  On homology it is the "excision" identification
`H_9(M, ∂M) ≅ H_9(D, B)`. -/
def inclRelMap {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] :
    Work.Cohomology.relChains (TopCat.of M) ((modelWithCornersEuclideanHalfSpace 9).boundary M) ⟶
      Work.Cohomology.relChains (TopCat.of (Double 8 M)) (secondHalf (M := M)) :=
  Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double 8 M))
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) (secondHalf (M := M))
    (doubleIncl (M := M)) (inclBdry (M := M)) (inclBdry_comp (M := M))

/-- The projection `C_*(D) ⟶ C_*(D, B)` of the double onto the pair `(D, B)`. -/
def projSecondHalf {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] :
    Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M)) ⟶
      Work.Cohomology.relChains (TopCat.of (Double 8 M)) (secondHalf (M := M)) :=
  CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double 8 M))
    (secondHalf (M := M)))

/-- **The restriction `H^k(M, Kᶜ) ⟶ H^k(M, ∂M)`** for a compact `K` in the interior of `M`: the map
of relative cohomology induced by the inclusion of pairs `(M, ∂M) ⟶ (M, Kᶜ)` (valid because
`∂M ⊆ Kᶜ`).  Its surjectivity is the "compactly supported cohomology of the interior computes the
relative cohomology" half of Hatcher's Theorem 3.43. -/
def relRestrOffBdry {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M] (K : Set M)
    (hK : K ⊆ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ) ⟶
      Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) (Kᶜ)
    (𝟙 (TopCat.of M)) (by intro y hy hyK; exact (hK hyK) hy)

/-- The relative cap product `H^k(M, ∂M; ℤ) →ₗ (H_{k+m}(M, ∂M; ℤ) →ₗ H_m(M; ℤ))`, with the types of
source and target written out (this ascription is what makes the `▸` bookkeeping below — and in
`Work.ThomBordism.LefschetzDualityBdry` — elaborate). -/
def relCapPairBdry {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    (k m : ℕ) :
    ↑(Work.Cohomology.relCohomology ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) k) →ₗ[ℤ]
      (↑((Work.Cohomology.relChains (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology (k + m)) →ₗ[ℤ]
        ↑((Work.Cohomology.singularChains ℤ (TopCat.of M)).homology m)) :=
  Work.Cohomology.relCapPair (TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) k m

end

end Work.ThomBordism
