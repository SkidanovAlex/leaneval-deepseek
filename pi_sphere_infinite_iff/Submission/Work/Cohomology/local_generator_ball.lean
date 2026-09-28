import Mathlib
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.isZero_relSubPunctured

set_option synthInstance.maxHeartbeats 400000

/-!
# The local generator property propagates to a coordinate ball

Let `M` be a compact Hausdorff space charted in dimension `N`, and `c ∈ H_N(M;ℤ)` a class whose
image in `H_N(M, M∖{x})` generates for every point `x` (`hc`, the `pd_middle_even` hypothesis).
Then for a coordinate closed ball `K = e⁻¹'closedBall (e z) r ∩ e.source` around `z`
(`e = chartAt _ z`), the image `μ_K` of `c` in `H_N(M, M∖K)` generates.

The proof uses the long exact sequence of the triple `M ⊇ M∖{z} ⊇ M∖K`
(`relChains_triple_shortExact`): the connecting map `φ : H_N(M, M∖K) → H_N(M, M∖{z})` sends `μ_K`
to `μ_z`, and its kernel is the image of `H_N(M∖{z}, M∖K) = 0`, so `φ` is injective.  For
`v ∈ H_N(M,M∖K)`, `hc` writes `φ v = a·μ_z = φ(a·μ_K)`, whence `v = a·μ_K`; that is
`span{μ_K} = ⊤`.

The vanishing `H_*(M∖{z}, M∖K) = 0` is the hypothesis `hvan` of the main lemma; it is the
transfer to `M` of the Euclidean statement `isZero_relChains_punctured`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **`local_generator_ball`, conditional on the vanishing of `H_*(M∖{z}, M∖K)`.** -/
theorem local_generator_ball_of_isZero (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    (hzK : z ∈ K) →
    (∀ i, CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub M Kᶜ ({z} : Set M)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))).homology i)) →
    Submodule.span ℤ
      {((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M Kᶜ)) N) c)} = ⊤ := by
  intro e hball K hzK hvan
  have hKz : ({z} : Set M) ⊆ K := fun y hy => Set.mem_singleton_iff.mp hy ▸ hzK
  have hsub : Kᶜ ⊆ ({z} : Set M)ᶜ := fun x hx hxz => hx (hKz hxz)
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
  have hrange : (LinearMap.toSpanSingleton ℤ _ (relLocClass M N c K)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [LinearMap.range_toSpanSingleton] at hrange
  exact hrange

/-- **The local generator property propagates to a coordinate ball.**

Let `c ∈ H_N(M;ℤ)` be a class whose image in `H_N(M, M∖{x})` generates for every `x`
(the hypothesis `hc` of `pd_middle_even`).  Then for the coordinate closed ball
`K = e⁻¹'(closedBall (e z) (r/2)) ∩ e.source` (`e = chartAt _ z`, `Metric.ball (e z) r ⊆ e.target`)
the image `μ_K` of `c` in `H_N(M, M∖K)` generates. -/
theorem local_generator_ball (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    Submodule.span ℤ
      {((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M (e ⁻¹' (Metric.closedBall (e z) (r/2)) ∩ e.source)ᶜ)) N) c)} = ⊤ := by
  intro e hball
  have hzK : z ∈ e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source := by
    refine ⟨?_, mem_chart_source _ z⟩
    show e z ∈ Metric.closedBall (e z) (r/2)
    rw [Metric.mem_closedBall, dist_self]
    linarith
  exact local_generator_ball_of_isZero N hN M c hc z r hr hball hzK
    (isZero_relSubPunctured N hN M z r hr hball hzK)

end

end Work.Cohomology
