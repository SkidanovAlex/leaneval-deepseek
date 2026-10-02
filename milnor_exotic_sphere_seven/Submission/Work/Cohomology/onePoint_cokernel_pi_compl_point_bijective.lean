import Mathlib
import Submission.Work.Cohomology.localHomology_top_free_onePoint
import Submission.Work.Cohomology.onePointSpace_compl_point_homeo
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereHomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The positive-degree singular homology of the complement of a point of the one-point
compactification of `ℝ^N` vanishes.**  The complement of a point is homeomorphic to `ℝ^N`
(`onePointSpace_compl_point_homeo`), which is contractible, so its homology vanishes in every
positive degree. -/
theorem isZero_homology_onePoint_compl_point {N : ℕ} (hN : 1 ≤ N)
    (pt : OnePoint (EuclideanSpace ℝ (Fin N))) (k : ℕ) (hk : 0 < k) :
    IsZero ((singularChains ℤ
      (TopCat.of ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))))).homology k) := by
  obtain ⟨φ⟩ := onePointSpace_compl_point_homeo N hN pt
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv φ.toHomotopyEquiv k
  exact IsZero.of_iso (X := (singularChains ℤ
      (TopCat.of ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))))).homology k)
    (homologyContractible (X := TopCat.of (EuclideanSpace ℝ (Fin N))) k hk) e

/-- **If the homology of `A` vanishes in degrees `n` and `n - 1`, the map
`Hₙ(X) ⟶ Hₙ(X,A)` of the pair `(X,A)` is bijective.**  This is the long exact sequence of the
pair: it is injective because it is preceded by `Hₙ(A) = 0`, and surjective because it is followed
by `Hₙ₋₁(A) = 0`. -/
theorem homologyMap_cokernel_pi_bijective_of_isZero (X : TopCat) (A : Set X) (n : ℕ)
    (hn : 1 ≤ n)
    (h1 : IsZero ((singularChains ℤ (TopCat.of A)).homology n))
    (h2 : IsZero ((singularChains ℤ (TopCat.of A)).homology (n - 1))) :
    Function.Bijective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) n)) := by
  have hinj : Function.Injective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) n)) := by
    have hf : HomologicalComplex.homologyMap (inclChains X A) n = 0 := h1.eq_of_src _ 0
    haveI : Mono (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) n) :=
      (ShortComplex.exact_iff_mono _ hf).mp (hPair_exact₂ X A n)
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hsurj : Function.Surjective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) n)) := by
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hg : hPairδ X A (n - 1) = 0 := h2.eq_of_tgt _ 0
    haveI : Epi (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n - 1 + 1)) :=
      (ShortComplex.exact_iff_epi _ hg).mp (hPair_exact₃ X A (n - 1))
    have h : Function.Surjective (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n - 1 + 1))) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    rwa [hsub] at h
  exact ⟨hinj, hsurj⟩

theorem onePoint_cokernel_pi_compl_point_bijective {N : ℕ} (hN : 2 ≤ N)
    (pt : OnePoint (EuclideanSpace ℝ (Fin N))) :
    Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N))))
        ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))))) N)) := by
  refine homologyMap_cokernel_pi_bijective_of_isZero
    (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N))))
    ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))) N (by omega) ?_ ?_
  · exact isZero_homology_onePoint_compl_point (by omega) pt N (by omega)
  · exact isZero_homology_onePoint_compl_point (by omega) pt (N - 1) (by omega)

end

end Work.Cohomology
