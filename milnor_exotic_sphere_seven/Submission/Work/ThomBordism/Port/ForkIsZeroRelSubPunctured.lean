-- Copied verbatim from `Submission.Work.Projective.GoodCp2.fork.isZero_relSubPunctured`, with imports re-routed:
-- the fork's own copy of `capped_localDegree_generator` is a *verbatim* duplicate of
-- `Submission.Work.Cohomology.capped_localDegree_generator`, and the latter is in the import
-- closure of `Submission.Work.ThomBordism.Interface` (via the Milnor chapter), so the two
-- cannot be combined: the import is re-routed to the original.  All declarations keep their
-- original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.capped_localDegree_generator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of `H_*(M∖{z}, M∖K)` for a coordinate closed ball `K`

The triple sequence of `A = Kᶜ ⊆ B = {z}ᶜ ⊆ M` (`tripleShort`, `relChains_triple_shortExact`) has
first term `C_*(M∖{z}, M∖K)` expressed as `coker (inclChainsSub M Kᶜ {z}ᶜ _)`.  This file shows
that this complex is acyclic, which is the input of `local_generator_ball`.

The proof is a transport: the vanishing of the *honest* relative chain complex
`relChains (TopCat.of {y | y ≠ z}) {y | (y : M) ∈ Kᶜ}` is `isZero_relChains_punctured_chart`
(excision + the chart homeomorphism + the Euclidean statement
`isZero_relChains_punctured_euclid`), and the two complexes differ only by the canonical
homeomorphism `Kᶜ ≅ {y : {y | y ≠ z} | (y : M) ∈ Kᶜ}` between the "ambient subset" and the
"subtype" models of `M∖K`; the isomorphism of cokernels is `cokernel.mapIso` (functoriality of the
cokernel under a morphism of the domain spaces), exactly as in `relChainsHomeomorphCompat`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The two models of the relative chain complex `C_*(M∖{z}, M∖K)` are isomorphic**: the
"restricted inclusion" model `coker (inclChainsSub M Kᶜ ({z}ᶜ) _)` and the "subspace" model
`relChains (TopCat.of {y | y ≠ z}) {y | (y : M) ∈ Kᶜ}`. -/
theorem relSubPunctured_homology_iso (M : TopCat) (z : M) (K : Set M) (hzK : z ∈ K) (i : ℕ) :
    Nonempty (((cokernel (inclChainsSub M Kᶜ ({z} : Set M)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))).homology i) ≅
      ((relChains (TopCat.of {y : M | y ≠ z})
        {y : ↥{y : M | y ≠ z} | (y : M) ∈ Kᶜ}).homology i)) := by
  let Zc : Set M := ({z} : Set M)ᶜ
  let Zs : Set M := {y : M | y ≠ z}
  let B : Set ↥Zs := {y | (y : M) ∈ Kᶜ}
  let hsub : Kᶜ ⊆ Zc := fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)
  have hzKc : z ∈ K := hzK
  -- the homeomorphism `↥(Kᶜ) ≃ₜ ↥B`
  let h1 : ↥(Kᶜ) ≃ₜ ↥B :=
    { toFun := fun y => ⟨⟨(y : M), fun hy => y.2 (hy ▸ hzKc)⟩, y.2⟩
      invFun := fun w => ⟨(w.1 : M), w.2⟩
      left_inv := fun y => by apply Subtype.ext; rfl
      right_inv := fun w => by apply Subtype.ext; apply Subtype.ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let h2 : ↥Zc ≃ₜ ↥Zs := Homeomorph.setCongr (Set.compl_singleton_eq z)
  let F := (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hsq : inclChainsSub M Kᶜ Zc hsub ≫ (F.mapIso (TopCat.isoOfHomeo h2)).hom =
      (F.mapIso (TopCat.isoOfHomeo h1)).hom ≫ inclChains (TopCat.of Zs) B := by
    rw [show inclChainsSub M Kᶜ Zc hsub = chainMap ℤ (TopCat.of ↥(Kᶜ)) (TopCat.of ↥Zc)
        (TopCat.ofHom ⟨fun x : ↥(Kᶜ) => ⟨(x : M), hsub x.2⟩,
          Continuous.subtype_mk (f := fun x : ↥(Kᶜ) => (x : M)) continuous_subtype_val
            (fun x => hsub x.2)⟩) from rfl,
      show inclChains (TopCat.of Zs) B = chainMap ℤ (TopCat.of ↥B) (TopCat.of ↥Zs)
        (subtypeIncl (TopCat.of Zs) B) from rfl,
      show (F.mapIso (TopCat.isoOfHomeo h1)).hom = chainMap ℤ (TopCat.of ↥(Kᶜ)) (TopCat.of ↥B)
        (TopCat.isoOfHomeo h1).hom from rfl,
      show (F.mapIso (TopCat.isoOfHomeo h2)).hom = chainMap ℤ (TopCat.of ↥Zc) (TopCat.of ↥Zs)
        (TopCat.isoOfHomeo h2).hom from rfl]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1

  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso
    (cokernel.mapIso (f := inclChainsSub M Kᶜ Zc hsub) (f' := inclChains (TopCat.of Zs) B)
      (F.mapIso (TopCat.isoOfHomeo h1)) (F.mapIso (TopCat.isoOfHomeo h2)) hsq)⟩

/-- **Vanishing of the relative homology of the punctured space, in the form used by the triple
sequence.**  For a coordinate closed ball `K = e⁻¹'(closedBall (e z) (r/2)) ∩ e.source` around `z`
(`e = chartAt _ z`, `Metric.ball (e z) r ⊆ e.target`), the complex
`coker (inclChainsSub M Kᶜ ({z}ᶜ) _)` (a model of `C_*(M∖{z}, M∖K)`) is acyclic. -/
theorem isZero_relSubPunctured (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    (hzK : z ∈ K) →
    ∀ i, CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub M Kᶜ ({z} : Set M)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))).homology i) := by
  intro e hball K hzK i
  have hsub : Kᶜ ⊆ ({z} : Set M)ᶜ :=
    fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)
  obtain ⟨eiso⟩ := relSubPunctured_homology_iso M z K hzK i
  refine IsZero.of_iso ?_ eiso
  -- the honest model is acyclic by the chart lemma
  have hz' : z ∈ e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source := by
    refine ⟨?_, mem_chart_source _ z⟩
    show e z ∈ Metric.closedBall (e z) (r/2)
    rw [Metric.mem_closedBall, dist_self]
    linarith
  exact isZero_relChains_punctured_chart N hN M z r hr (Metric.closedBall (e z) (r/2))
    (isCompact_closedBall _ _) (convex_closedBall _ _) hball
    (fun v hv => by rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hv; linarith)
    z hz' i

end

end Work.Cohomology
