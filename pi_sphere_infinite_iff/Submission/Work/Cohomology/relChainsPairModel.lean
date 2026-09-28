import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localCohomology

/-!
# The two models of the relative chain complex of a pair, and the triple sequence

For subsets `A ⊆ B ⊆ M` of a topological space the relative chain complex of the pair `(B,A)` has
two models:

* the "restricted inclusion" model `coker (inclChainsSub M A B h)`, the cokernel of the chain map
  `C_*(A) ⟶ C_*(B)` induced by the inclusion, which is the first term of the short exact sequence
  of the *triple* `A ⊆ B ⊆ M` (`tripleShort`, `relChains_triple_shortExact`), and
* the "subspace" model `relChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}`.

`coker_inclChainsSub_homology_iso` identifies their homologies.

`homology_iso_of_triple` reads off the long exact sequence of the triple: if the relative homology
of the *larger* set `B` vanishes in degrees `i` and `i+1`, then `H_i(M, M∖A)` is the homology of
the restricted inclusion model of the pair `(B,A)`.

## Main results

* `coker_inclChainsSub_homology_iso`;
* `homology_iso_of_triple`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-- **The two models of the relative chain complex of a pair `(B,A)`**: the "restricted inclusion"
model `coker (inclChainsSub M A B h)` and the "subspace" model
`relChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}` are isomorphic on homology. -/
theorem coker_inclChainsSub_homology_iso {A B : Set M} (hAB : A ⊆ B) (i : ℕ) :
    Nonempty ((cokernel (inclChainsSub M A B hAB)).homology i ≅
      ((relChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}).homology i)) := by
  let A' : Set ↥B := {y | (y : M) ∈ A}
  let h1 : ↥A ≃ₜ ↥A' :=
    { toFun := fun a => ⟨⟨(a : M), hAB a.2⟩, a.2⟩
      invFun := fun w => ⟨(w.1 : M), w.2⟩
      left_inv := fun a => by apply Subtype.ext; rfl
      right_inv := fun w => by apply Subtype.ext; apply Subtype.ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let F := (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hsq : inclChainsSub M A B hAB
      = (F.mapIso (TopCat.isoOfHomeo h1)).hom ≫ inclChains (TopCat.of ↥B) A' := by
    rw [show inclChainsSub M A B hAB = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (TopCat.ofHom ⟨fun x : ↥A => ⟨(x : M), hAB x.2⟩, continuous_subtype_val.subtype_mk _⟩)
        from rfl,
      show (F.mapIso (TopCat.isoOfHomeo h1)).hom = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥A')
        (TopCat.isoOfHomeo h1).hom from rfl,
      show inclChains (TopCat.of ↥B) A' = chainMap ℤ (TopCat.of ↥A') (TopCat.of ↥B)
        (subtypeIncl (TopCat.of ↥B) A') from rfl]
    rw [← Functor.map_comp]
    congr 1
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso
    (cokernel.mapIso (f := inclChainsSub M A B hAB) (f' := inclChains (TopCat.of ↥B) A')
      (F.mapIso (TopCat.isoOfHomeo h1)) (Iso.refl _) hsq)⟩

/-- If the relative homology of the larger set `T` of the triple `S ⊆ T ⊆ M` vanishes in degrees
`i` and `i+1`, then `H_i(M, M∖S)` is isomorphic to the homology of the "restricted inclusion"
model of the pair `(T,S)`. -/
theorem homology_iso_of_triple {S T : Set M} (hST : S ⊆ T) (i : ℕ)
    (h0 : IsZero ((relChains M T).homology i))
    (h1 : IsZero ((relChains M T).homology (i + 1))) :
    Nonempty ((relChains M S).homology i ≅ (cokernel (inclChainsSub M S T hST)).homology i) := by
  let SEX : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := tripleShort M S T hST
  have hSEX : SEX.ShortExact := relChains_triple_shortExact M S T hST
  have hg0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.g i) = 0 := by
    rw [IsZero.eq_zero_of_tgt (show IsZero (SEX.X₃.homology i) from h0)
      (HomologicalComplex.homologyMap SEX.g i)]
    exact ModuleCat.hom_zero
  have hex2 := hSEX.homology_exact₂ i
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.f i)) = ⊤ := by
    rw [ShortComplex.Exact.moduleCat_range_eq_ker hex2, hg0, LinearMap.ker_zero]
  have hepi : Epi (HomologicalComplex.homologyMap SEX.f i) := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    have hy : y ∈ LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.f i)) := by
      rw [hrange]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hy
  have hd0 : ModuleCat.Hom.hom (hSEX.δ (i + 1) i (by simp [ComplexShape.down])) = 0 := by
    rw [IsZero.eq_zero_of_src (show IsZero (SEX.X₃.homology (i+1)) from h1)
      (hSEX.δ (i + 1) i (by simp [ComplexShape.down]))]
    exact ModuleCat.hom_zero
  have hex1 := hSEX.homology_exact₁ (i + 1) i (by simp [ComplexShape.down])
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap SEX.f i)) = ⊥ := by
    have h := ShortComplex.Exact.moduleCat_range_eq_ker hex1
    rw [hd0, LinearMap.range_zero] at h
    exact h.symm
  have hmono : Mono (HomologicalComplex.homologyMap SEX.f i) := by
    rw [ModuleCat.mono_iff_injective]
    exact LinearMap.ker_eq_bot.mp hker
  haveI : IsIso (HomologicalComplex.homologyMap SEX.f i) := isIso_of_mono_of_epi _
  exact ⟨(asIso (HomologicalComplex.homologyMap SEX.f i)).symm⟩

end

end Work.Cohomology
