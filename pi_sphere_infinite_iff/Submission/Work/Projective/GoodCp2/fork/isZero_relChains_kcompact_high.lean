import Mathlib
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Projective.GoodCp2.fork.isZero_relSubPunctured
import Submission.Work.Cohomology.localCohomology

set_option synthInstance.maxHeartbeats 400000

/-!
# `H_i(M, M∖K) = 0` above the dimension (Hatcher, Lemma 3.27)

For a charted `N`-manifold `M` and a coordinate closed ball
`K = e⁻¹'(closedBall (e z) (r/2)) ∩ e.source` around `z`, the relative homology `H_i(M, M∖K)`
vanishes for every `i > N`.

The proof uses the triple `Kᶜ ⊆ {z}ᶜ ⊆ M` (`tripleShort`, `relChains_triple_shortExact`): the long
exact sequence of the triple reads

`H_i(M∖{z}, M∖K) → H_i(M, M∖K) → H_i(M, M∖{z}) → H_{i-1}(M∖{z}, M∖K)`

and for `i > N` both outer groups vanish — the first is `isZero_relSubPunctured`, the second is the
local homology of a point (`localHomology_charted`, `H_k(M, M∖{z}) = 0` for `k ≠ N`).  Exactness
therefore forces `H_i(M, M∖K) = 0`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **`H_i(M, M∖K) = 0` for `i > N`** (`K` a coordinate closed ball around `z`). -/
theorem isZero_relChains_kcompact_high (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    ∀ i, N < i → CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains M Kᶜ).homology i) := by
  intro e hball K i hi
  have hzK : z ∈ K := by
    refine ⟨?_, mem_chart_source _ z⟩
    show e z ∈ Metric.closedBall (e z) (r/2)
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hsub : Kᶜ ⊆ ({z} : Set M)ᶜ :=
    fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := tripleShort M Kᶜ ({z} : Set M)ᶜ hsub
  -- the outer terms of the triple vanish in degree `i > N`
  have h1 : CategoryTheory.Limits.IsZero (S.X₁.homology i) :=
    isZero_relSubPunctured N hN M z r hr hball hzK i
  have h3' : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of M) {y : M | y ≠ z}).homology i) :=
    (Work.Cohomology.localHomology_charted N hN ↥M z i).2 (by omega)
  have h3 : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains M ({z} : Set M)ᶜ).homology i) :=
    (Set.compl_singleton_eq z) ▸ h3'
  -- exactness of the triple sequence at the middle term
  have hexact : (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) _).Exact :=
    (relChains_triple_shortExact M Kᶜ ({z} : Set M)ᶜ hsub).homology_exact₂ i
  have hrange := ShortComplex.Exact.moduleCat_range_eq_ker hexact
  have hf0 : HomologicalComplex.homologyMap S.f i = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_src h1 _
  have hrange0 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f i)).range = ⊥ := by
    rw [hf0]
    exact LinearMap.range_zero
  have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g i)).ker = ⊥ := by
    rw [← hrange, hrange0]
  have hinj : Function.Injective
      ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g i)) :=
    LinearMap.ker_eq_bot.mp hker
  haveI hsub3 : Subsingleton ↥(S.X₃.homology i) :=
    ModuleCat.isZero_iff_subsingleton.mp h3
  have hsub2 : Subsingleton ↥(S.X₂.homology i) :=
    ⟨fun a b => hinj (Subsingleton.elim (α := ↥(S.X₃.homology i)) _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub2

end

end Work.Cohomology
