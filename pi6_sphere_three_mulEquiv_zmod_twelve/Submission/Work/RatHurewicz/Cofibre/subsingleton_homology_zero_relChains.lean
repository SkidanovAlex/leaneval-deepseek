import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero

/-!
# The zeroth relative homology of a pair `(X, A)` with `X` path connected and `A` nonempty

For a path connected space `X` and a nonempty subset `A ⊆ X`, the relative singular homology
`H₀(X, A; ℤ)` vanishes.  Equivalently: the inclusion of chains `C_*(A) ⟶ C_*(X)` induces an
epimorphism (in fact an isomorphism, since both spaces are connected) `H₀(A) → H₀(X)`.

The proof is the standard one, using the long exact sequence of the pair

`H₀(A) --f--> H₀(X) --g--> H₀(X,A)`

(`Work.Cohomology.hPair_exact₂`), which is exact at `H₀(X)`:

* `f` is an epimorphism: the degree-`0` augmentation `ε : H₀(-;ℤ) ⟶ ℤ` is natural
  (`Work.Cohomology.epsilonNaturality`) and an isomorphism for the path connected space `X`; for
  the nonempty space `A` it is an epimorphism, because for a `0`-simplex `x` of `A` the composite
  `ℤ → H₀(A) → ℤ` obtained from `SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε` is the
  identity.  Hence `f = ε_A ≫ ε_X⁻¹` is an epimorphism.
* exactness at `H₀(X)` then forces `g = 0`, and `g` is an epimorphism, being induced on `H₀` by the
  degreewise surjective projection `C_*(X) ⟶ C_*(X,A)`
  (`Work.ThreeConnected.Excision.epi_homologyMap_cokernel_pi_zero`); an epimorphism which is zero
  has zero target (`Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero`).

This is the degree-`0` companion of `Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.RatHurewicz.Cofibre

noncomputable section

/-- **The degree-`0` augmentation of a nonempty space is an epimorphism.**  A `0`-simplex `x` of a
simplicial set `X` produces a section `ℤ → H₀(X)` of the augmentation on homology
(`SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε`), so the augmentation has a right inverse as
soon as `X` has a `0`-simplex. -/
theorem epi_homology₀ε_of_nonempty_sset (Xs : SSet) [Nonempty (Xs _⦋0⦌)] :
    Epi (Xs.homology₀ε (ModuleCat.of ℤ ℤ)) := by
  obtain ⟨x⟩ := ‹Nonempty (Xs _⦋0⦌)›
  have h := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (X := Xs) (R := ModuleCat.of ℤ ℤ) x
  haveI hE : Epi (HomologicalComplex.homologyπ (Xs.chainComplex (ModuleCat.of ℤ ℤ)) 0 ≫
      Xs.homology₀ε (ModuleCat.of ℤ ℤ)) := CategoryTheory.epi_of_epi_fac h
  exact CategoryTheory.epi_of_epi
    (HomologicalComplex.homologyπ (Xs.chainComplex (ModuleCat.of ℤ ℤ)) 0)
    (Xs.homology₀ε (ModuleCat.of ℤ ℤ))

/-- **The degree-`0` augmentation of a nonempty topological space is an epimorphism.**  This is the
`TopCat` form of `epi_homology₀ε_of_nonempty_sset`, transported along
`TopCat.toSSetObj₀Equiv : toSSet.obj X _⦋0⦌ ≃ X`. -/
theorem epi_singularHomology₀ε_of_nonempty (X : TopCat) [Nonempty X] :
    Epi (X.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
  haveI : Nonempty ((TopCat.toSSet.obj X) _⦋0⦌) :=
    ⟨X.toSSetObj₀Equiv.symm (Classical.choice ‹Nonempty X›)⟩
  exact epi_homology₀ε_of_nonempty_sset (TopCat.toSSet.obj X)

/-- **`H₀(A) ⟶ H₀(X)` is an epimorphism for `X` path connected and `A` nonempty.**  Since the
augmentation is natural and an isomorphism for the path connected space `X`, this map is the
composite `ε_A ≫ ε_X⁻¹` of an epimorphism with an isomorphism. -/
theorem epi_homologyMap_inclChains_zero (X : TopCat) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] :
    Epi (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0) := by
  haveI : IsIso (X.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hA : Epi ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) :=
    epi_singularHomology₀ε_of_nonempty (TopCat.of A)
  have hnat : HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0
      ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ)
      = (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ) :=
    Work.Cohomology.epsilonNaturality (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)
  have hF : HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0
      = (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)
        ≫ CategoryTheory.inv (X.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hF]
  infer_instance

theorem subsingleton_homology_zero_relChains (X : TopCat) (A : Set X) [PathConnectedSpace X] [Nonempty A] : Subsingleton ↑((Work.Cohomology.relChains X A).homology 0) := by
  -- `H₀(A) ⟶ H₀(X)` is surjective, so exactness of the pair sequence at `H₀(X)` makes
  -- `H₀(X) ⟶ H₀(X,A)` the zero map.
  haveI hf : Epi (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0) :=
    epi_homologyMap_inclChains_zero X A
  have hker : LinearMap.ker (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) 0).hom = ⊤ := by
    rw [← ShortComplex.Exact.moduleCat_range_eq_ker (Work.Cohomology.hPair_exact₂ X A 0)]
    exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hf)
  have hg0 : HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.ker (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) 0).hom := by
      rw [hker]; trivial
    exact hx
  -- that map is also an epimorphism (the projection to the cokernel is degreewise surjective), and
  -- an epimorphism which is zero has a zero target.
  exact ModuleCat.subsingleton_of_isZero
    (Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
      (Work.Cohomology.inclChains X A) hg0)

end

end Work.RatHurewicz.Cofibre
