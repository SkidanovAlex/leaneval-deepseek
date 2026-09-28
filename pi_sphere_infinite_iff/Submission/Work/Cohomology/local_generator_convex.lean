import Mathlib
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.local_generator_ball
import Submission.Work.Cohomology.isZero_relSubPunctured

set_option synthInstance.maxHeartbeats 400000

/-!
# The local generator property propagates to a compact convex coordinate set

Let `M` be a compact Hausdorff space charted in dimension `N`, `cc : M`, `e := chartAt _ cc`,
`r > 0` with `Metric.ball (e cc) r ⊆ e.target`, and `c ∈ H_N(M;ℤ)` a class whose image in
`H_N(M, M∖{x})` generates for every `x` (`hc`).  Then for every compact convex `K' ⊆ ℝ^N`
contained in `Metric.ball (e cc) r`, and every `z ∈ e ⁻¹' K' ∩ e.source`, the image of `c` in
`H_N(M, M∖K)` with `K := e ⁻¹' K' ∩ e.source` generates.

The proof is the same argument as `local_generator_ball_of_isZero` (the closed-ball case), but
run for an *arbitrary* compact set `K` containing `z`: the triple sequence of
`M ⊇ M∖K ⊇ M∖{z}` has connecting map `φ : H_N(M,M∖K) → H_N(M,M∖{z})` sending `μ_K ↦ μ_z`, and
its kernel is the image of `H_N(M∖{z}, M∖K)`, which vanishes for `K` a compact convex set in a
coordinate chart (`isZero_relChains_punctured_chart`), so `φ` is injective and `μ_z = φ(μ_K)`
forces `span{μ_K} = ⊤`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The local generator property for an arbitrary erased set `K ∋ z`**, assuming the vanishing
of `H_*(M∖{z}, M∖K)` in the `coker (inclChainsSub …)` model. -/
theorem local_generator_of_isZero (N : ℕ) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (z : M) (K : Set M) (hzK : z ∈ K)
    (hvan : ∀ i, CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub M Kᶜ ({z} : Set M)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))).homology i)) :
    Submodule.span ℤ {relLocClass M N c K} = ⊤ := by
  have hKz : ({z} : Set M) ⊆ K := fun y hy => Set.mem_singleton_iff.mp hy ▸ hzK
  have hsub : Kᶜ ⊆ ({z} : Set M)ᶜ := fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := tripleShort M Kᶜ ({z} : Set M)ᶜ hsub
  have hSg : S.g = relCokerMap M Kᶜ ({z} : Set M)ᶜ hsub :=
    tripleShort_g M Kᶜ ({z} : Set M)ᶜ hsub
  -- the exactness of the triple sequence at its middle term
  have hexact : (ShortComplex.mk (HomologicalComplex.homologyMap S.f N)
      (HomologicalComplex.homologyMap S.g N) _).Exact :=
    (relChains_triple_shortExact M Kᶜ ({z} : Set M)ᶜ hsub).homology_exact₂ N
  have hrange := ShortComplex.Exact.moduleCat_range_eq_ker hexact
  -- the first term vanishes
  have hvanS : CategoryTheory.Limits.IsZero (S.X₁.homology N) := hvan N
  have hf0 : HomologicalComplex.homologyMap S.f N = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_src hvanS _
  have hrange0 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f N)).range = ⊥ := by
    rw [hf0]
    exact LinearMap.range_zero
  have hker0 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g N)).ker = ⊥ := by
    rw [← hrange, hrange0]
  have hinj : Function.Injective ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g N)) :=
    LinearMap.ker_eq_bot.mp hker0
  -- the map `φ : H_N(M,M∖K) → H_N(M,M∖{z})` and its injectivity
  have hinjφ : Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap M Kᶜ ({z} : Set M)ᶜ hsub) N) := by
    rw [← hSg]
    exact hinj
  -- `φ μ_K = μ_z` and `μ_z` generates
  have hrestrict : (HomologicalComplex.homologyMap (relCokerMap M Kᶜ ({z} : Set M)ᶜ hsub) N)
      (relLocClass M N c K) = relLocClass M N c ({z} : Set M) :=
    relLocClass_restrict M N c hKz
  have hgen : Submodule.span ℤ {relLocClass M N c ({z} : Set M)} = ⊤ :=
    relLocClass_point_span M N c hc z
  have hcomp : (LinearMap.toSpanSingleton ℤ _
        (relLocClass M N c ({z} : Set M))) =
      (HomologicalComplex.homologyMap (relCokerMap M Kᶜ ({z} : Set M)ᶜ hsub) N).hom.comp
        (LinearMap.toSpanSingleton ℤ _ (relLocClass M N c K)) := by
    apply LinearMap.ext_ring
    rw [LinearMap.toSpanSingleton_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
      one_smul, one_smul]
    exact hrestrict.symm
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ _ (relLocClass M N c K)) := by
    intro v
    have hmem : (HomologicalComplex.homologyMap (relCokerMap M Kᶜ ({z} : Set M)ᶜ hsub) N) v ∈
        (LinearMap.toSpanSingleton ℤ _ (relLocClass M N c ({z} : Set M))).range := by
      rw [LinearMap.range_toSpanSingleton, hgen]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, hinjφ ?_⟩
    rw [← LinearMap.comp_apply, ← hcomp]
    exact ha
  have hrange' : (LinearMap.toSpanSingleton ℤ _ (relLocClass M N c K)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [LinearMap.range_toSpanSingleton] at hrange'
  exact hrange'

/-- **The local generator property propagates to a compact convex coordinate set.**

Let `c ∈ H_N(M;ℤ)` be a class whose image in `H_N(M, M∖{x})` generates for every `x`
(the hypothesis `hc` of `pd_middle_even`), `cc : M`, `e := chartAt _ cc`, `r > 0` with
`Metric.ball (e cc) r ⊆ e.target`.  Then for every compact convex `K' ⊆ ℝ^N` with
`K' ⊆ Metric.ball (e cc) r` and every `z ∈ e ⁻¹' K' ∩ e.source`, the image `μ_K` of `c` in
`H_N(M, M∖K)` with `K := e ⁻¹' K' ∩ e.source` generates. -/
theorem local_generator_convex (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    ((K' : Set (EuclideanSpace ℝ (Fin N))) → IsCompact K' → Convex ℝ K' →
      K' ⊆ Metric.ball (e cc) r → (z : M) → z ∈ e ⁻¹' K' ∩ e.source →
      Submodule.span ℤ
        {((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains M ((e ⁻¹' K') ∩ e.source)ᶜ)) N) c)} = ⊤) := by
  intro e hball K' hKc hconv hKsub z hz
  -- the vanishing of `H_*(M∖{z}, M∖K)` transported from the subspace model
  have hvan : ∀ i, CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub M (e ⁻¹' K' ∩ e.source)ᶜ ({z} : Set M)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hz)))).homology i) := by
    intro i
    obtain ⟨eiso⟩ := relSubPunctured_homology_iso M z (e ⁻¹' K' ∩ e.source) hz i
    exact IsZero.of_iso
      (isZero_relChains_punctured_chart N hN M cc r hr K' hKc hconv hball hKsub z hz i) eiso
  exact local_generator_of_isZero N M c hc z (e ⁻¹' K' ∩ e.source) hz hvan

end

end Work.Cohomology
