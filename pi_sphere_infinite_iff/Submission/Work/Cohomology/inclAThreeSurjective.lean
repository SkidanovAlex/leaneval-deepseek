import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homology_prod_contractible

set_option synthInstance.maxHeartbeats 400000

/-!
# Surjectivity of `H₃(inclA)`

For the pair `(S³ × D⁴, S³ × S³)` of `sphere3DiscPairDefs`, the inclusion `inclA` of the sphere
bundle `PairAT = S³ × S³` into the total space `PairXT = S³ × D⁴` induces a **surjection**

  `H₃(inclA) : H₃(S³ × S³) ⟶ H₃(S³ × D⁴)`,

which is the statement needed (together with the injectivity of `H₃` of the pair of projections,
`pjPairInjectiveThree`) to identify `ker H₃(inclA) ≅ ℤ`.

The proof is the elementary "isomorphism + section" argument from the design notes:

* the first projection `pj1X : S³ × D⁴ ⟶ S³` is a homotopy equivalence — `D⁴` is contractible —
  so `Hₙ(pj1X)` is an isomorphism (`homologyEquiv`), in particular injective;
* `pj1A : S³ × S³ ⟶ S³` is split by the section `x ↦ (x, y₀)`; hence `Hₙ(pj1A)` is surjective;
* the two are related by `inclA ≫ pj1X = pj1A` (`pj1A_eq_incl_pj1X`), i.e. on homology
  `Hₙ(pj1A) = Hₙ(pj1X) ∘ Hₙ(inclA)`; surjectivity of `Hₙ(pj1A)` together with injectivity of
  `Hₙ(pj1X)` forces `Hₙ(inclA)` to be surjective.

Everything is proved at the level of the singular chain complexes, so no additional theory is
needed beyond the basic functoriality of `singularChains` and `homologyMap`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

/-- The first projection `pj1X : S³ × D⁴ ⟶ S³` is a homotopy equivalence (the disc `D⁴` is
contractible), so it induces an isomorphism on singular homology in every degree. -/
theorem isIso_homologyMap_pj1X (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) n) := by
  -- `D⁴` is contractible
  haveI : ContractibleSpace ↥Disc4T :=
    Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩
  -- choose a base point of the disc and a nullhomotopy of the identity
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic ↥Disc4T
  -- the section `x ↦ (x, y₀)` of `pj1X`
  let inv : C(↥Sph3T, ↥Sph3T × ↥Disc4T) :=
    ContinuousMap.prodMk (ContinuousMap.id ↥Sph3T) (ContinuousMap.const ↥Sph3T y₀)
  let g : Sph3T ⟶ PairXT := TopCat.ofHom inv
  -- `g ≫ pj1X = 𝟙`, so this pair gives a homotopy equivalence
  have hr_eq : ContinuousMap.fst.comp inv = ContinuousMap.id ↥Sph3T := by
    ext x; rfl
  have hright : (ContinuousMap.fst.comp inv).Homotopic (ContinuousMap.id ↥Sph3T) :=
    hr_eq ▸ (ContinuousMap.Homotopic.refl _)
  -- `pj1X ≫ g` is `(x, d) ↦ (x, y₀)`, homotopic to the identity via the contraction of the disc
  have hmain : ((ContinuousMap.id ↥Sph3T).prodMap
      (ContinuousMap.const ↥Disc4T y₀)).Homotopic
      ((ContinuousMap.id ↥Sph3T).prodMap (ContinuousMap.id ↥Disc4T)) :=
    (ContinuousMap.Homotopic.refl (ContinuousMap.id ↥Sph3T)).prodMap hy₀.symm
  have h1eq : (ContinuousMap.prodMk (ContinuousMap.id ↥Sph3T)
      (ContinuousMap.const ↥Sph3T y₀)).comp ContinuousMap.fst =
      (ContinuousMap.id ↥Sph3T).prodMap (ContinuousMap.const ↥Disc4T y₀) := by
    ext p <;> simp [ContinuousMap.prodMap_apply, Prod.map]
  have h2eq : (ContinuousMap.id ↥Sph3T).prodMap (ContinuousMap.id ↥Disc4T) =
      ContinuousMap.id (↥Sph3T × ↥Disc4T) := by
    ext p <;> simp [ContinuousMap.prodMap_apply, Prod.map]
  have hleft : (inv.comp ContinuousMap.fst).Homotopic (ContinuousMap.id _) := by
    simpa [inv, h1eq, h2eq.symm] using hmain
  let e : ContinuousMap.HomotopyEquiv (↥Sph3T × ↥Disc4T) ↥Sph3T :=
    ContinuousMap.HomotopyEquiv.mk ContinuousMap.fst inv hleft hright
  have h1 : TopCat.Homotopy (pj1X ≫ g) (𝟙 PairXT) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ pj1X) (𝟙 Sph3T) := e.right_inv.some
  exact homologyEquiv ℤ PairXT Sph3T pj1X g h1 h2 n

theorem inclAThreeSurjective :
    Function.Surjective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 3)) := by
  -- `H₃` of the projection `S³ × D⁴ ⟶ S³` is an isomorphism, hence injective
  haveI hisoX : IsIso (HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) 3) :=
    isIso_homologyMap_pj1X 3
  have hinjX : Function.Injective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) 3)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  -- `H₃` of the projection `pj1A : S³ × S³ ⟶ S³` is surjective, since `pj1A` has a section
  have hsurjA : Function.Surjective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A) 3)) := by
    -- a base point of `S³`, viewed in the disc
    let e₀ : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1
    have he₀_sphere : e₀ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; simp [e₀]
    have he₀_ball : e₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; simp [e₀]
    let x₀ : ↥Sph3T := ⟨e₀, he₀_sphere⟩
    let y₀ : ↥Disc4T := ⟨e₀, he₀_ball⟩
    let a₀ : ↥PairAT := ⟨(x₀, y₀), by
      show ((y₀ : ↥Disc4T) : EuclideanSpace ℝ (Fin 4)) ∈ Metric.sphere 0 1
      exact he₀_sphere⟩
    -- the section `x ↦ (x, y₀)` of `pj1A`
    let sec : C(↥Sph3T, ↥PairAT) :=
      ⟨fun x => ⟨(x, a₀.1.2), a₀.2⟩,
       Continuous.subtype_mk
        (ContinuousMap.prodMk (ContinuousMap.id ↥Sph3T)
          (ContinuousMap.const ↥Sph3T a₀.1.2)).continuous
        (fun x => a₀.2)⟩
    let s : Sph3T ⟶ TopCat.of ↑PairAT := TopCat.ofHom sec
    have hsec : s ≫ pj1A = 𝟙 Sph3T := by
      apply TopCat.hom_ext; ext x; rfl
    have hcompsec : chainMap ℤ Sph3T (TopCat.of ↑PairAT) s ≫
        chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A = 𝟙 (singularChains ℤ Sph3T) := by
      simp only [chainMap]
      rw [← Functor.map_comp, hsec]
      simp
    have hhomsec : HomologicalComplex.homologyMap (chainMap ℤ Sph3T (TopCat.of ↑PairAT) s) 3 ≫
        HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A) 3 = 𝟙 _ := by
      rw [← HomologicalComplex.homologyMap_comp, hcompsec, HomologicalComplex.homologyMap_id]
    intro z
    refine ⟨ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (chainMap ℤ Sph3T (TopCat.of ↑PairAT) s) 3) z, ?_⟩
    have h := congrArg ModuleCat.Hom.hom hhomsec
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    simpa using DFunLike.congr_fun h z
  -- functoriality: `H₃(pj1A) = H₃(pj1X) ∘ H₃(inclA)`
  have hchain : inclChains PairXT PairAT ≫ chainMap ℤ PairXT Sph3T pj1X =
      chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A := by
    simp only [inclChains, chainMap]
    rw [← Functor.map_comp, pj1A_eq_incl_pj1X]
    rfl
  have hhom : HomologicalComplex.homologyMap (inclChains PairXT PairAT) 3 ≫
      HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) 3 =
      HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A) 3 := by
    rw [← HomologicalComplex.homologyMap_comp, hchain]
  have hfun : ∀ x, ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) 3)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 3) x) =
      ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↑PairAT) Sph3T pj1A) 3) x := by
    intro x
    have h := congrArg ModuleCat.Hom.hom hhom
    rw [ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h x
  -- the conclusion
  intro z
  obtain ⟨a, ha⟩ := hsurjA (ModuleCat.Hom.hom
    (HomologicalComplex.homologyMap (chainMap ℤ PairXT Sph3T pj1X) 3) z)
  refine ⟨a, ?_⟩
  apply hinjX
  rw [hfun a]
  exact ha

end

end Work.Cohomology
