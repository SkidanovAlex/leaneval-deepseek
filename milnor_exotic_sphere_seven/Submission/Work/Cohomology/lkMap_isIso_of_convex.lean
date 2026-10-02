import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.isZero_relChains_punctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local homology of a compact convex set is that of any of its points

For `D ⊆ ℝ^N` a nonempty compact convex set (`N ≥ 1`) and `x ∈ D` the inclusion of the pair
`(ℝ^N, ℝ^N ∖ D) ⟶ (ℝ^N, ℝ^N ∖ {x})` (which is the map of complements `ℝ^N ∖ D ⊆ ℝ^N ∖ {x}`)
induces a bijection on top relative homology

`H_N(ℝ^N, ℝ^N ∖ D) ⟶ H_N(ℝ^N, ℝ^N ∖ {x})`,

i.e. on the "stage map" `LK N D ⟶ LK N {x}` of the local homology of `D`.

This is the statement that the local homology of `D` is concentrated at (any) one of its points,
and is the input identifying the various models of the local homology of a convex coordinate set
in the Poincaré-duality development.

The proof is the long exact sequence of the triple `Dᶜ ⊆ {x}ᶜ ⊆ ℝ^N` (`tripleShort`,
`relChains_triple_shortExact`):

`H_N(ℝ^N∖{x}, ℝ^N∖D) ⟶ H_N(ℝ^N, ℝ^N∖D) ⟶ H_N(ℝ^N, ℝ^N∖{x}) ⟶ H_{N-1}(ℝ^N∖{x}, ℝ^N∖D)`,

whose outer terms vanish: `H_*(ℝ^N∖{x}, ℝ^N∖D) = 0` because the radial projection away from `x`
(i.e. `ℝ^N ∖ D ≃ ℝ^N ∖ {x}`, `isZero_relChains_punctured`) is a homotopy equivalence.  Hence the
middle map is both injective (exactness at `H_N(ℝ^N, ℝ^N∖D)`) and surjective (exactness at
`H_N(ℝ^N, ℝ^N∖{x})`, its cokernel embedding into `H_{N-1}(ℝ^N∖{x}, ℝ^N∖D) = 0`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem lkMap_isIso_of_convex {N : ℕ} (hN : 1 ≤ N)
    {D : Set (EuclideanSpace ℝ (Fin N))} (hDc : IsCompact D) (hDv : Convex ℝ D)
    (hDne : D.Nonempty) {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ D) :
    Function.Bijective (Work.Cohomology.lkMap (N := N) (Set.singleton_subset_iff.mpr hx)) := by
  let X : TopCat := TopCat.of (EuclideanSpace ℝ (Fin N))
  have hsub : Dᶜ ⊆ ({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ :=
    fun y hy hxz => hy (Set.mem_singleton_iff.mp hxz ▸ hx)
  -- the triple `Dᶜ ⊆ {x}ᶜ ⊆ ℝ^N`, whose middle map is `lkMap`
  let S := Work.Cohomology.tripleShort X Dᶜ ({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ hsub
  have hSE : S.ShortExact := Work.Cohomology.relChains_triple_shortExact X Dᶜ _ hsub
  -- the first term `C_*(ℝ^N∖{x}, ℝ^N∖D)` is acyclic
  have hzero : ∀ i, IsZero (S.X₁.homology i) := by
    intro i
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso X x D hx i
    exact IsZero.of_iso (Work.Cohomology.isZero_relChains_punctured N hN x D hDc hDv hx i) eiso
  -- the middle map of the triple is `lkMap`
  have hlkm : Work.Cohomology.lkMap (N := N) (Set.singleton_subset_iff.mpr hx)
      = (HomologicalComplex.homologyMap S.g N).hom := by
    rw [Work.Cohomology.lkMap, Work.Cohomology.tripleShort_g]
    rfl
  -- injectivity: exactness at `H_N(ℝ^N, ℝ^N∖D)`, where the incoming map vanishes
  let K₂ : ShortComplex (ModuleCat ℤ) := ShortComplex.mk (HomologicalComplex.homologyMap S.f N)
    (HomologicalComplex.homologyMap S.g N) (by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])
  have hK₂ : K₂.Exact := hSE.homology_exact₂ N
  have hf0 : K₂.f = 0 := IsZero.eq_zero_of_src (hzero N) _
  have hmono : Mono K₂.g := hK₂.mono_g hf0
  -- surjectivity: exactness at `H_N(ℝ^N, ℝ^N∖{x})`, whose outgoing connecting map lands in
  -- the vanishing `H_{N-1}(ℝ^N∖{x}, ℝ^N∖D)`
  have hij : (ComplexShape.down ℕ).Rel N (N - 1) := by
    show (N - 1) + 1 = N
    exact Nat.sub_add_cancel hN
  let K₃ : ShortComplex (ModuleCat ℤ) := ShortComplex.mk (HomologicalComplex.homologyMap S.g N)
    (hSE.δ N (N - 1) hij) (hSE.comp_δ N (N - 1) hij)
  have hK₃ : K₃.Exact := hSE.homology_exact₃ N (N - 1) hij
  have hδ0 : K₃.g = 0 := IsZero.eq_zero_of_tgt (hzero (N - 1)) _
  have hepi : Epi K₃.f := hK₃.epi_f hδ0
  rw [hlkm]
  exact ⟨(ModuleCat.mono_iff_injective K₂.g).mp hmono,
    (ModuleCat.epi_iff_surjective K₃.f).mp hepi⟩

end

end Work.Cohomology
