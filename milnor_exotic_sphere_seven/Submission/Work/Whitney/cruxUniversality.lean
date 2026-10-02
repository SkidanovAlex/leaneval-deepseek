import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Whitney.cruxInputs
import Submission.Work.Whitney.cruxRelComap
import Submission.Work.Whitney.cruxPin_of_familyIso
import Submission.Work.Whitney.cruxModelPins
import Submission.Work.Gen.LineTensor
import Submission.Work.Gen.Coh_zero_eq_smul_oneH_of_constFibre
import Submission.Work.Whitney.tensorSliceIso
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.CohMap_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The crux family from the delta form, by the product argument

**Route.**  Let `REL(N,B,M)` be the δ-form of the ψ-analysis:

  `∃ δ : H⁰(B), c_{N-1}(lineSumCore N M) = deltaCup N M δ`.

The point of this file is that `REL` *alone* implies the crux family
`c_{N-1}(lineSumCore N M) = eSym N M (N-1)`, with no further geometry:

* take a model family `M₀` over a compact base `B₀` for which the crux is *known* by the top-class
  formula (`Work.Whitney.cruxModelPins`, the family `(ℓ,…,ℓ,ε)` over `ℂP^{N-1}`);
* over the product `B₀ × B` consider the external tensor product `M''ᵢ = pr₁^*M₀ᵢ ⊗ pr₂^*Mᵢ` and
  apply `REL` to it: `c_{N-1}(W'') = δ'' ⌣ eSym N M'' (N-1)`;
* restrict along the slice `ι_b : B₀ → B₀ × B`, `x ↦ (x,b)`: the sliced family is pointwise
  isomorphic to `M₀` (`Work.Whitney.tensorSliceIso`), so
  `(CohMap ι_b) δ''` satisfies the hypothesis of `Work.Whitney.cruxPin_of_familyIso`, giving
  `(CohMap ι_b) δ'' = 1` for every `b`; hence the value of `δ''` at every point of `B₀ × B` is `1`;
* restricting the relation for `M''` along the other slice `κ_x : B → B₀ × B` gives
  `c_{N-1}(W) = eSym N M (N-1)`, because the sliced family is pointwise isomorphic to `M`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The δ-form of the ψ-analysis**, as a `Prop` in the rank `N`: for every family of `N` complex
line bundles over a paracompact Hausdorff base there is a degree-`0` class `δ` with
`c_{N-1}(lineSumCore N M) = deltaCup N M δ`. -/
def CruxRel (N : ℕ) : Prop :=
  ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι : Type} [Fintype ι]
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
    ∃ δ : Work.Thom.Coh ℤ 0 B,
      Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
        = Work.Whitney.deltaCup N M δ

/-- **The degenerate case of an empty base**: the cohomology of an empty space vanishes, so both
sides of the crux identity live in a subsingleton. -/
theorem crux_of_isEmpty {B : Type} [TopologicalSpace B] [IsEmpty B] {ι : Type} [Fintype ι]
    (N : ℕ) (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
      = Work.Gen.eSym N M (N - 1) :=
  @Subsingleton.elim _ (Work.Thom.subsingleton_Coh_of_isEmpty ‹IsEmpty B› (2 * (N - 1))) _ _

/-- **`CruxRel` in the degenerate rank `0`.**  Here `deltaCup 0 M δ = δ`, so the relation is the
triviality `c_0 = 1`. -/
theorem cruxRel_zero : CruxRel 0 := by
  intro B _ _ _ ι _ M
  refine ⟨Work.Cohomology.oneH ℤ (Work.Whitney.ssB B), ?_⟩
  rw [Work.Thom.chernClass_zero_eq_oneH, Work.Whitney.deltaCup]
  simp only [Work.Gen.eSym_zero, Work.Thom.cohTransport_self, Work.Cohomology.cupH'_one_left,
    Work.LerayHirsch.eqRec_eq_cohTransport]
  change Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) = Work.Gen.eSym 0 M 0
  rw [Work.Gen.eSym_zero]
  exact (Work.Thom.cohTransport_self _ _).symm

/-- **The product argument.**  The δ-form in every rank implies the crux family. -/
theorem hcrux_of_rel (hrel : ∀ N, CruxRel N) :
    ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι]
      (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1) := by
  intro n B _ hpar ht2 ι _ M
  rcases n with _ | _ | N
  · -- `n = 0`
    show Work.Thom.chernClass 0 0 (Work.LerayHirsch.lineSumCore 0 M) = Work.Gen.eSym 0 M 0
    rw [Work.Thom.chernClass_zero_eq_oneH, Work.Gen.eSym_zero]
    exact (Work.Thom.cohTransport_self _ _).symm
  · -- `n = 1`
    show Work.Thom.chernClass 1 0 (Work.LerayHirsch.lineSumCore 1 M) = Work.Gen.eSym 1 M 0
    rw [Work.Thom.chernClass_zero_eq_oneH, Work.Gen.eSym_one_class]
    exact (Work.Thom.cohTransport_self _ _).symm
  · -- `n = N + 2 ≥ 2`
    by_cases hB : Nonempty B
    · obtain ⟨B₀, hT₀, hP₀, hT2₀, hC₀, hPC₀, ι₀, hF₀, M₀, hM₀, hfree, hspan⟩ :=
        cruxModelPins (N + 2) (by omega)
      letI : TopologicalSpace B₀ := hT₀
      letI : ParacompactSpace B₀ := hP₀
      letI : T2Space B₀ := hT2₀
      letI : CompactSpace B₀ := hC₀
      letI : PathConnectedSpace B₀ := hPC₀
      letI : Fintype ι₀ := hF₀
      -- the product family
      let M'' : Fin (N + 2) → VectorBundleCore ℂ (B₀ × B) (EuclideanSpace ℂ (Fin 1)) (ι₀ × ι) :=
        fun i => Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
          (Work.Thom.bundleComap (M i) ContinuousMap.snd)
      obtain ⟨δ'', hδ''⟩ := hrel (N + 2) M''
      -- nonempty model base
      haveI : Nonempty B₀ := inferInstance
      -- the first slice
      have key : ∀ b : B,
          (Work.Thom.CohMap
            (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
            ℤ 0).hom δ'' = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B₀) := by
        intro b
        let ιb : C(B₀, B₀ × B) := ContinuousMap.prodMk (ContinuousMap.id B₀)
          (ContinuousMap.const B₀ b)
        let Nb : Fin (N + 2) → VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) (ι₀ × ι) :=
          fun i => Work.Thom.bundleComap (M'' i) ιb
        have hrelb := cruxRel_comap M'' ιb δ'' hδ''
        have hiso : ∀ i, Nonempty (Work.Thom.BundleIso (Nb i) (M₀ i)) := fun i =>
          (tensorSliceIso (N + 2) M₀ M b (Classical.choice inferInstance)).1 i
        exact cruxPin_of_familyIso (N + 2) (by omega) Nb M₀ hiso hM₀ hfree hspan
          ((Work.Thom.CohMap ιb ℤ 0).hom δ'') hrelb
      -- hence `δ'' = 1`: its value at every point is `1`
      have hδ''one : δ'' = Work.Cohomology.oneH ℤ (Work.Whitney.ssB (B₀ × B)) := by
        refine Work.Thom.ptEv_ext (fun y => ?_)
        obtain ⟨x, b⟩ := y
        have hp : Work.Thom.ptEv x ((Work.Thom.CohMap
              (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
              ℤ 0).hom δ'') = Work.Thom.ptEv (x, b) δ'' := by
          simpa using Work.Thom.ptEv_pullback
            (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b)) x δ''
        rw [← hp, key b]
        simp
      -- the second slice
      obtain ⟨x₀⟩ := ‹Nonempty B₀›
      let κ : C(B, B₀ × B) := ContinuousMap.prodMk (ContinuousMap.const B x₀) (ContinuousMap.id B)
      let Mx : Fin (N + 2) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) (ι₀ × ι) :=
        fun i => Work.Thom.bundleComap (M'' i) κ
      have hrelx := cruxRel_comap M'' κ δ'' hδ''
      rw [hδ''one, Work.Thom.CohMap_oneH] at hrelx
      rw [Work.Whitney.deltaCup, Work.Whitney.cohTransport_cupH'_oneH_left] at hrelx
      -- the sliced family is pointwise isomorphic to `M`
      have hiso' : ∀ i, Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap (M'' i) κ)
          (M i)) := fun i =>
        (tensorSliceIso (N + 2) M₀ M (Classical.choice hB) x₀).2 i
      obtain ⟨e⟩ := nonempty_bundleIso_lineSumCore_family (N + 2)
        (fun i => Work.Thom.bundleComap (M'' i) κ) M hiso'
      rw [Work.Thom.chernClass_BundleIso
          (Work.LerayHirsch.lineSumCore (N + 2) (fun i => Work.Thom.bundleComap (M'' i) κ))
          (Work.LerayHirsch.lineSumCore (N + 2) M) e,
        eSym_familyIso (fun i => Work.Thom.bundleComap (M'' i) κ) M hiso' (N + 2 - 1)] at hrelx
      exact hrelx
    · haveI : IsEmpty B := not_nonempty_iff.mp hB
      exact crux_of_isEmpty (N + 2) M

end

end Work.Whitney
