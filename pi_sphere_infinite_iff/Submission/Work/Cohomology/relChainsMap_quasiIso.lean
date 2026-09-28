import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mvComp
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.homologyPairShortExact
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChains_compat
import Submission.Work.Cohomology.excisionAux
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits


namespace Work.Cohomology

noncomputable section

set_option maxHeartbeats 1600000 in
/-- Excision in the form of relative small chains: for open `U, A ⊆ X` with `U ∪ A = X`, the
inclusion of pairs `(U, U ∩ A) → (X, A)` is a quasi-isomorphism on relative singular homology.

`Work.Cohomology.relChainsMap X U A` is defined in `Submission/Work/Cohomology/localHomology.lean`.
Route: let `P` be the pushout `(C(U) ⊕ C(A))/{(x,-x)}`. The map `τ₂ : P → C(X)`, `[(u,a)] ↦ i_U u + i_A a`
is a quasi-isomorphism (it identifies `P` with `smallChains U A`: use `pushChain_gen`,
`isSmallChain_gen`, `smallToSing_gen`, `mem_of_gen`, `smallToSing_f_injective` and
`smallChains_homology_iso`), and `0 → C(A) → P → C(U, U∩A) → 0` is short exact. Then apply
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` to the morphism of short exact
sequences `hPairShort X A → (0 → C(A) → P → C(U,U∩A) → 0)` with `τ₁ = 𝟙` and `τ₂` as above.
The non-elementary input is `range (C(U) → C(X)) ⊓ range (C(A) → C(X)) = range (C(U∩A) → C(X))`;
prove it with the projections `π_σ` of `SSet.isColimitChainComplexXCofan` (checks on generators via
`SSet.chainComplex_hom_ext`), the idempotent on generators
`gen σ ↦ if σ factors through U∩A then gen σ else 0`,
and `ModuleCat.coprodIsoDirectSum` with `DirectSum.ext_component` for
"equal coordinates implies equal elements". -/
theorem relChainsMap_quasiIso (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) n) := by
  have hcov' : A ∪ U = Set.univ := by rw [Set.union_comm]; exact hcov
  let A' : Set U := {x : U | (x : X) ∈ A}
  let u : singularChains ℤ (TopCat.of A) ⟶ smallChains A U := smallOfU A U
  let w : smallChains A U ⟶ singularChains ℤ X := smallToSing A U
  have huw : u ≫ w = inclChains X A := smallOfU_comp_smallToSing A U
  have huw' : u ≫ w = (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := mono_smallOfU A U
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (inclChains X A)
      = cokernel.π u ≫ cokernel.map u (inclChains X A) (𝟙 _) w huw'
    exact (cokernel_π_map u (inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact smallChains_homology_iso A U hA hU hcov' n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := smallChains_homology_iso A U hA hU hcov' j
      infer_instance
  obtain ⟨e, he⟩ := cokerSmallOfU_iso_relChains_compat X A U
  have key : cokernel.π (smallOfU A U) ≫ τ₃ = w ≫ cokernel.π (inclChains X A) :=
    cokernel_π_map u (inclChains X A) (𝟙 _) w huw'
  have hfac : relChainsMap X U A = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) A'))).1
    calc cokernel.π (inclChains (TopCat.of U) A') ≫ relChainsMap X U A
        = chainMap ℤ (TopCat.of U) X (subtypeIncl X U) ≫ cokernel.π (inclChains X A) :=
          cokernel_π_relChainsMap X U A
      _ = inclChains X U ≫ cokernel.π (inclChains X A) := rfl
      _ = (smallOfV A U ≫ w) ≫ cokernel.π (inclChains X A) := by
            rw [smallOfV_comp_smallToSing]
      _ = smallOfV A U ≫ (w ≫ cokernel.π (inclChains X A)) := Category.assoc _ _ _
      _ = smallOfV A U ≫ (cokernel.π (smallOfU A U) ≫ τ₃) := by rw [key]
      _ = (smallOfV A U ≫ cokernel.π (smallOfU A U)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) e.hom
  exact inferInstance

end

end Work.Cohomology
