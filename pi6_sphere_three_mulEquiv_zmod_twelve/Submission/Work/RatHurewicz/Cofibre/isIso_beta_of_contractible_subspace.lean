import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.epsilonNaturality

/-!
# The middle map of the pair sequence is an isomorphism for a contractible subspace

For a topological space `X`, a subset `A ⊆ X` with `A` contractible and `X` path connected, the
map

`βₙ : Hₙ(X) ⟶ Hₙ(X,A)`,

the middle morphism `homologyMap (cokernel.π (inclChains X A)) n` of the long exact sequence of the
pair `(X,A)` (`Work.Cohomology.hPair_exact₁/₂/₃`), is an isomorphism in every degree `n ≠ 0`.

The proof is the standard chase: since `A` is contractible, `Hⱼ(A) = 0` for `j > 0`
(`Work.Cohomology.homologyContractible`), so

* `βₙ` is injective for `n ≥ 1`, because `ker βₙ = im (Hₙ(A) → Hₙ(X)) = 0`;
* `βₙ` is surjective for `n ≥ 2`, because `im βₙ = ker (Hₙ(X,A) → Hₙ₋₁(A))` and `Hₙ₋₁(A) = 0`;
* `β₁` is surjective, because `im β₁ = ker (H₁(X,A) → H₀(A))` and the connecting map vanishes:
  its image is the kernel of `H₀(A) → H₀(X)`, which is zero by naturality of the augmentation `ε`
  (`Work.Cohomology.epsilonNaturality`) together with `A` being path connected (a contractible
  space is path connected) and the augmentation of a path connected space being an isomorphism.

The same argument was used for the punctured cone in
`Work.RatHurewicz.Cofibre.isIso_beta_cofibreV`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz.Cofibre

noncomputable section

/-- **The positive-degree homology of a contractible subspace vanishes.** -/
theorem isZero_homology_of_contractible_subspace (X : TopCat) (A : Set X) [ContractibleSpace A]
    (j : ℕ) (hj : 0 < j) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology j) :=
  Work.Cohomology.homologyContractible j hj

/-- **`H₀(A) ⟶ H₀(X)` is injective for `A` contractible and `X` path connected.**  Both `H₀`s
augment isomorphically onto `ℤ` and the augmentation is natural, so the map is an isomorphism. -/
theorem mono_h0_inclChains_of_contractible (X : TopCat) (A : Set X) [ContractibleSpace A]
    [PathConnectedSpace X] :
    Mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0) := by
  haveI hεA : IsIso ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  have hmonoA : Mono ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  have hnat := Work.Cohomology.epsilonNaturality (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)
  haveI : Mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0
      ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := hnat.symm ▸ hmonoA
  exact mono_of_mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) 0)
    (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))

/-- **Injectivity of `βₙ = Hₙ(X) ⟶ Hₙ(X,A)` for `n ≠ 0`.**  Exactness of the pair sequence at
`Hₙ(X)` together with `Hₙ(A) = 0`. -/
theorem mono_beta_of_contractible_subspace (X : TopCat) (A : Set X) [ContractibleSpace A]
    (n : ℕ) (hn : n ≠ 0) :
    Mono (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) n) := by
  have hf : HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n = 0 :=
    (isZero_homology_of_contractible_subspace X A n (Nat.pos_of_ne_zero hn)).eq_of_src _ 0
  exact (ShortComplex.exact_iff_mono _ hf).mp (Work.Cohomology.hPair_exact₂ X A n)

/-- **Surjectivity of `βₙ = Hₙ(X) ⟶ Hₙ(X,A)` for `n ≠ 0`.**  For `n ≥ 2` the connecting map
`Hₙ(X,A) ⟶ Hₙ₋₁(A)` vanishes because its target is a positive-degree homology of the contractible
space `A`; for `n = 1` it vanishes because `H₀(A) ⟶ H₀(X)` is injective.  Exactness of the pair
sequence at `Hₙ(X,A)` then makes `βₙ` an epimorphism. -/
theorem epi_beta_of_contractible_subspace (X : TopCat) (A : Set X) [ContractibleSpace A]
    [PathConnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    Epi (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · -- `n = 1`: the connecting map into `H₀(A)` is zero.
    have hδ : Work.Cohomology.hPairδ X A 0 = 0 := by
      have hEx := Work.Cohomology.hPair_exact₁ X A 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains X A) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp (mono_h0_inclChains_of_contractible X A)
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    exact (ShortComplex.exact_iff_epi _ hδ).mp (Work.Cohomology.hPair_exact₃ X A 0)
  · -- `n ≥ 2`: the connecting map vanishes because its target has vanishing homology.
    have hδ : Work.Cohomology.hPairδ X A (m + 1) = 0 :=
      (isZero_homology_of_contractible_subspace X A (m + 1) (by omega)).eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hδ).mp (Work.Cohomology.hPair_exact₃ X A (m + 1))

theorem isIso_beta_of_contractible_subspace (X : TopCat) (A : Set X) [ContractibleSpace A] [PathConnectedSpace X] (n : ℕ) (hn : n ≠ 0) : CategoryTheory.IsIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) n) := by
  haveI := mono_beta_of_contractible_subspace X A n hn
  haveI := epi_beta_of_contractible_subspace X A n hn
  exact isIso_of_mono_of_epi _

end

end Work.RatHurewicz.Cofibre
