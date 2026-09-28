import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.sphereInUnitHomologyIso
import Submission.Work.Cohomology.reducedH0SphereInUnitOne
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyOne

set_option synthInstance.maxHeartbeats 400000

/-!
# The top relative cohomology of the disk pair `(Dⁿ, Sⁿ⁻¹)`

We compute `Hⁿ(Dⁿ, Sⁿ⁻¹; ℤ) ≅ ℤ` for `n ≥ 1`, the cohomological companion of
`Work.Cohomology.diskPairHomologyTop`.

The proof uses the long exact sequence of the pair in cohomology
(`Work.Cohomology.pairδ`, `pair_exact₁`, `pair_exact₃`):

* for `n ≥ 2`, the outer terms `Hⁿ(Dⁿ)` and `Hⁿ⁻¹(Dⁿ)` vanish because `Dⁿ` is contractible, so
  the connecting map `pairδ : Hⁿ⁻¹(Sⁿ⁻¹) ⟶ Hⁿ(Dⁿ,Sⁿ⁻¹)` is an isomorphism, and the source is the
  top cohomology of the sphere `Sⁿ⁻¹`;
* for `n = 1` the sequence reads `H⁰(D¹) ⟶ H⁰(S⁰) ⟶ H¹(D¹,S⁰) ⟶ H¹(D¹) = 0`, so `H¹(D¹,S⁰)` is
  the cokernel of the restriction `H⁰(D¹) ⟶ H⁰(S⁰)`; the source is `ℤ` (the ball is
  path-connected) and the target is `ℤ²` (the two-point space `S⁰`), and the map is the diagonal.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The closed unit ball `Dⁿ` is contractible (it is a nonempty convex subset of `ℝⁿ`). -/
theorem diskUnit_isContractible (n : ℕ) : ContractibleSpace (diskUnit n) :=
  Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩

/-! ## The connecting map of the pair when the outer terms vanish -/

/-- **The connecting map of the pair is an isomorphism when the outer terms vanish.**

If `H^{m+1}(X) = 0` and `H^m(X) = 0`, then in the exact sequence

`H^m(X) ⟶ H^m(A) --δ--> H^{m+1}(X,A) ⟶ H^{m+1}(X)`

of the pair `(X,A)` the connecting map `δ = pairδ ℤ X A m` is both injective and surjective. -/
theorem pairδ_isIso (X : TopCat) (A : Set X) (m : ℕ)
    (h1 : IsZero (singularCohomology ℤ (m + 1) X)) (h2 : IsZero (singularCohomology ℤ m X)) :
    IsIso (pairδ ℤ X A m) := by
  have hmono : Mono (pairδ ℤ X A m) := by
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (restr ℤ X A) m)
        (pairδ ℤ X A m) (pair_comp_δ ℤ X A m)).f = 0 := h2.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp (pair_exact₃ ℤ X A m)
  have hepi : Epi (pairδ ℤ X A m) := by
    have hg : (ShortComplex.mk (pairδ ℤ X A m)
        (HomologicalComplex.homologyMap (relIncl ℤ X A) (m + 1))
        (pairδ_comp ℤ X A m)).g = 0 := h1.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (pair_exact₁ ℤ X A m)
  exact isIso_of_mono_of_epi _


/-! ## Elementary facts about the disc `D¹` and the sphere `S⁰` -/

/-- `D¹` is path-connected (it is a nonempty convex subset of `ℝ¹`). -/
theorem diskUnitOne_pathConnected : PathConnectedSpace (diskUnit 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1).isPathConnected
      ⟨0, by simp [Metric.mem_closedBall]⟩)

/-- **`S⁰ = sphereInUnit 1` has exactly two path components** (the two points `±e₀`). -/
theorem sphereInUnit_one_twoComponents :
    ∃ a b : ↥(sphereInUnit 1),
      (∀ z : ↥(sphereInUnit 1), Joined z a ∨ Joined z b) ∧ ¬ Joined a b :=
  ⟨ptOne, ptNegOne,
    fun z => by
      rcases eq_ptOne_or z with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]),
    not_joined⟩

/-! ## The cohomology of the model sphere -/

/-- The cohomology of `Sⁿ⁻¹ ⊆ Dⁿ` agrees with that of the standard model `Sⁿ⁻¹ = sphTop n`. -/
theorem sphereInUnitCohomologyIso (n k : ℕ) :
    Nonempty (singularCohomology ℤ k (TopCat.of (sphereInUnit n)) ≅
      singularCohomology ℤ k (sphTop n)) := by
  have he : ContinuousMap.HomotopyEquiv ↥(sphereInUnit n) ↥(sphSet n) :=
    ((sphereInUnitHomeomorph n).trans (Homeomorph.setCongr (sphereSet_eq n).symm).symm).toHomotopyEquiv
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv he k
  exact ⟨e⟩

/-! ## Degree one: the relative group as a cokernel -/

/-- **`H¹(X,A)` is the cokernel of the restriction `H⁰(X) ⟶ H⁰(A)`** when `H¹(X) = 0`. -/
theorem relCohomologyOne_iso_coker (X : TopCat) (A : Set X)
    (h : IsZero (singularCohomology ℤ 1 X)) :
    Nonempty ((relComplex ℤ X A).homology 1 ≅
      cokernel (singularCohomologyMap ℤ (TopCat.of A) X (subtypeIncl X A) 0)) := by
  -- the connecting map is an epimorphism, because its target `H¹(X)` vanishes
  have hδepi : Epi (pairδ ℤ X A 0) := by
    have hg : (ShortComplex.mk (pairδ ℤ X A 0)
        (HomologicalComplex.homologyMap (relIncl ℤ X A) 1)
        (pairδ_comp ℤ X A 0)).g = 0 := h.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (pair_exact₁ ℤ X A 0)
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (pairδ ℤ X A 0)) :=
    (ModuleCat.epi_iff_surjective _).mp hδepi
  -- and its kernel is the image of the restriction
  have hrange : (ModuleCat.Hom.hom
        (singularCohomologyMap ℤ (TopCat.of A) X (subtypeIncl X A) 0)).range
      = (ModuleCat.Hom.hom (pairδ ℤ X A 0)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (pair_exact₃ ℤ X A 0)
  have hex : Function.Exact
      (ModuleCat.Hom.hom (singularCohomologyMap ℤ (TopCat.of A) X (subtypeIncl X A) 0))
      (ModuleCat.Hom.hom (pairδ ℤ X A 0)) :=
    LinearMap.exact_iff.mpr hrange.symm
  -- the epimorphism `pairδ` with kernel the image of the restriction exhibits `H¹(X,A)` as the
  -- cokernel of the restriction
  exact ⟨IsColimit.coconePointUniqueUpToIso
    (ModuleCat.isColimitCokernelCofork
      (singularCohomologyMap ℤ (TopCat.of A) X (subtypeIncl X A) 0) (pairδ ℤ X A 0) hex hsurj)
    (colimit.isColimit _)⟩


/-! ## The two cases of the computation -/

/-- **The `n = 1` case**, given the computation of the cokernel of the restriction `H⁰(D¹) ⟶ H⁰(S⁰)`
by the general two-component lemma. -/
theorem diskPairCohomologyOne_aux
    (h : Nonempty (cokernel (singularCohomologyMap ℤ (TopCat.of (sphereInUnit 1)) (diskUnit 1)
      (subtypeIncl (diskUnit 1) (sphereInUnit 1)) 0) ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty ((relComplex ℤ (diskUnit 1) (sphereInUnit 1)).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
  haveI : ContractibleSpace (diskUnit 1) := diskUnit_isContractible 1
  have hz : IsZero (singularCohomology ℤ 1 (diskUnit 1)) := contractible ℤ (diskUnit 1) 0
  obtain ⟨e1⟩ := relCohomologyOne_iso_coker (diskUnit 1) (sphereInUnit 1) hz
  obtain ⟨e2⟩ := h
  exact ⟨e1 ≪≫ e2⟩


/-- **The main computation, conditional on the two base-case inputs.** -/
theorem diskPairCohomologyTop_aux
    (hOne : Nonempty (cokernel (singularCohomologyMap ℤ (TopCat.of (sphereInUnit 1)) (diskUnit 1)
      (subtypeIncl (diskUnit 1) (sphereInUnit 1)) 0) ≅ ModuleCat.of ℤ ℤ))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (((relComplex ℤ (diskUnit n) (sphereInUnit n)).homology n) ≅ ModuleCat.of ℤ ℤ) := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    exact diskPairCohomologyOne_aux hOne
  · haveI : ContractibleSpace (diskUnit n) := diskUnit_isContractible n
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hz1 : IsZero (singularCohomology ℤ (n - 1 + 1) (diskUnit n)) :=
      contractible ℤ (diskUnit n) (n - 1)
    have hz2 : IsZero (singularCohomology ℤ (n - 1) (diskUnit n)) := by
      have hh := contractible ℤ (diskUnit n) (n - 2)
      rwa [show n - 2 + 1 = n - 1 from by omega] at hh
    haveI : IsIso (pairδ ℤ (diskUnit n) (sphereInUnit n) (n - 1)) :=
      pairδ_isIso (diskUnit n) (sphereInUnit n) (n - 1) hz1 hz2
    obtain ⟨e1⟩ := sphereInUnitCohomologyIso n (n - 1)
    obtain ⟨e2⟩ := sphereCohomology_aux (n - 1) (by omega)
    rw [hsub] at e2
    have key : Nonempty
        (HomologicalComplex.homology (relComplex ℤ (diskUnit n) (sphereInUnit n)) (n - 1 + 1)
          ≅ ModuleCat.of ℤ ℤ) :=
      ⟨(asIso (pairδ ℤ (diskUnit n) (sphereInUnit n) (n - 1))).symm ≪≫ e1 ≪≫ e2⟩
    rw [hsub] at key
    exact key


/-! ## The cokernel of a pullback from a path-connected space to a two-component space

This is the degree-`0` input of the `n = 1` case: if `Y` is path-connected and `Z` has exactly two
path components, then the pullback `H⁰(Y) ⟶ H⁰(Z)` has cokernel `ℤ`.  The proof exhibits the
surjection `Δ : H⁰(Z) ⟶ ℤ` given by the difference of the evaluations at the two components (a
class of `H⁰(Z)` is a functional on the `0`-chains which is constant on path components) and shows
that its kernel is the image of the pullback.
-/

section TwoComponentCokernel

variable {Y : TopCat} [PathConnectedSpace Y]

/-- The `0`-simplex of `Z` at a point. -/
noncomputable def pointSimplex (Z : TopCat) (z : Z) :
    (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObj₀Equiv (X := Z)).symm z

lemma pointSimplex_coe (Z : TopCat) (z : Z) :
    TopCat.toSSetObj₀Equiv (X := Z) (pointSimplex Z z) = z :=
  Equiv.apply_symm_apply _ _

lemma toSSetObj₀Equiv_map {X Y : TopCat} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv (X := Y)
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) s)
      = f (TopCat.toSSetObj₀Equiv (X := X) s) := by
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObj₀Equiv_apply]
  rfl

lemma map_pointSimplex {X Y : TopCat} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) (pointSimplex X x)
      = pointSimplex Y (f x) := by
  apply (TopCat.toSSetObj₀Equiv (X := Y)).injective
  rw [toSSetObj₀Equiv_map, pointSimplex_coe, pointSimplex_coe]

/-- **The indicator of the path component of `z`**: the `0`-cochain of `Z` which is `1` on the
component of `z` and `0` on all others. -/
noncomputable def indicMor (Z : TopCat) (z : Z) :
    ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of ℤ ℤ)).X 0 ⟶ ModuleCat.of ℤ ℤ := by
  classical
  exact SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z) (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
      if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0)

/-- The linear functional underlying the component indicator. -/
noncomputable def indicCochain (Z : TopCat) (z : Z) : Cochain ℤ (TopCat.toSSet.obj Z) 0 :=
  (indicMor Z z).hom

theorem indicMor_comp_d (Z : TopCat) (z : Z) :
    ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫ indicMor Z z = 0 := by
  classical
  rw [show indicMor Z z = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
      (ModuleCat.of ℤ ℤ) ≫
      Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl]
  rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]

theorem indic_cocycle (Z : TopCat) (z : Z) :
    cochainDiff ℤ (TopCat.toSSet.obj Z) (indicCochain Z z) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (indicMor_comp_d Z z)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  show (indicCochain Z z).comp
    (((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom = 0
  exact h

theorem indic_gen_of_mem (Z : TopCat) (z : Z)
    (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)))
    (hc : SSet.π₀.mk s = SSet.π₀.mk (pointSimplex Z z)) :
    genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z z) s = 1 := by
  classical
  have h1 : ModuleCat.Hom.hom (indicMor Z z) =
      (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0))).comp
      (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ))) := by
    rw [show indicMor Z z = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
          if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl,
      ModuleCat.hom_comp]
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ)))
        ((ModuleCat.Hom.hom ((TopCat.toSSet.obj Z).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s)) 1)
      = (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := TopCat.toSSet.obj Z)
        (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  change ModuleCat.Hom.hom (indicMor Z z)
      (((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = 1
  rw [h1]
  simp only [LinearMap.comp_apply]
  rw [h2]
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s = SSet.π₀.mk (pointSimplex Z z) then
          𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h3]
  simp [hc]

theorem indic_gen_of_not_mem (Z : TopCat) (z : Z)
    (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)))
    (hc : SSet.π₀.mk s ≠ SSet.π₀.mk (pointSimplex Z z)) :
    genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z z) s = 0 := by
  classical
  have h1 : ModuleCat.Hom.hom (indicMor Z z) =
      (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0))).comp
      (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ))) := by
    rw [show indicMor Z z = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
          if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl,
      ModuleCat.hom_comp]
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj Z)
        (ModuleCat.of ℤ ℤ)))
        ((ModuleCat.Hom.hom ((TopCat.toSSet.obj Z).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s)) 1)
      = (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := TopCat.toSSet.obj Z)
        (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  change ModuleCat.Hom.hom (indicMor Z z)
      (((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = 0
  rw [h1]
  simp only [LinearMap.comp_apply]
  rw [h2]
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s = SSet.π₀.mk (pointSimplex Z z) then
          𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ (TopCat.toSSet.obj Z) =>
        if c = SSet.π₀.mk (pointSimplex Z z) then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h3]
  simp [hc]

theorem pi0_pointSimplex_ne (Z : TopCat) (a b : Z) (h : ¬ Joined a b) :
    SSet.π₀.mk (pointSimplex Z b) ≠ SSet.π₀.mk (pointSimplex Z a) := by
  intro hh
  have h2 := Sph1.joined_of_pi0_mk_eq (X := Z) hh
  rw [pointSimplex_coe, pointSimplex_coe] at h2
  exact h h2.symm

/-- Evaluation of a `0`-cochain of `Z` at the `0`-simplex over the point `z`. -/
noncomputable def evalAt (Z : TopCat) (z : Z) : Cochain ℤ (TopCat.toSSet.obj Z) 0 →ₗ[ℤ] ℤ where
  toFun α := genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z z)
  map_add' α β := by simp [genEval]
  map_smul' c α := by simp [genEval]

/-- The difference of the evaluations at the two chosen points. -/
noncomputable def diffCochain (Z : TopCat) (a b : Z) :
    Cochain ℤ (TopCat.toSSet.obj Z) 0 →ₗ[ℤ] ℤ :=
  evalAt Z a - evalAt Z b

theorem diffCochain_apply (Z : TopCat) (a b : Z) (α : Cochain ℤ (TopCat.toSSet.obj Z) 0) :
    diffCochain Z a b α = genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a)
      - genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z b) := by
  rw [diffCochain, LinearMap.sub_apply]
  rfl

/-- The difference of the evaluations, as a map out of the cycles of degree `0`. -/
noncomputable def diffK (Z : TopCat) (a b : Z) :
    (SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).cycles 0 ⟶ ModuleCat.of ℤ ℤ :=
  (SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).iCycles 0 ≫ ModuleCat.ofHom (diffCochain Z a b)

theorem diffK_toCycles (Z : TopCat) (a b : Z) :
    (SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).toCycles ((ComplexShape.up ℕ).prev 0) 0
      ≫ diffK Z a b = 0 := by
  rw [HomologicalComplex.toCycles_eq_zero (K := SSetCochainComplex ℤ (TopCat.toSSet.obj Z))
      (i := (ComplexShape.up ℕ).prev 0) (j := 0) (by simp [ComplexShape.up_Rel]), zero_comp]

/-- **The difference of the evaluations at the two components**, as a map on `H⁰(Z)`. -/
noncomputable def twoCompDelta (Z : TopCat) (a b : Z) :
    singularCohomology ℤ 0 Z ⟶ ModuleCat.of ℤ ℤ :=
  descH ℤ (TopCat.toSSet.obj Z) 0 (diffK Z a b) (diffK_toCycles Z a b)

theorem twoCompDelta_classOf (Z : TopCat) (a b : Z) (α : Cochain ℤ (TopCat.toSSet.obj Z) 0)
    (hα : cochainDiff ℤ (TopCat.toSSet.obj Z) α = 0) :
    (twoCompDelta Z a b).hom (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα)
      = diffCochain Z a b α := by
  have hkey := homologyπ_descH ℤ (TopCat.toSSet.obj Z) 0 (diffK Z a b) (diffK_toCycles Z a b)
  have h2 := congrArg (fun (k : (SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).cycles 0
      ⟶ ModuleCat.of ℤ ℤ) => k.hom (cocycleOf ℤ (TopCat.toSSet.obj Z) α hα)) hkey
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [show (diffK Z a b).hom (cocycleOf ℤ (TopCat.toSSet.obj Z) α hα)
      = diffCochain Z a b α from by
    rw [diffK, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      iCycles_cocycleOf]
    rfl] at h2
  exact h2

theorem twoCompDelta_surjective (Z : TopCat) (a b : Z) (hnot : ¬ Joined a b) :
    Function.Surjective (twoCompDelta Z a b).hom := by
  intro y
  refine ⟨cohomologyClassOf ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a) (by
    rw [show cochainDiff ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a)
        = y • cochainDiff ℤ (TopCat.toSSet.obj Z) (indicCochain Z a) from by
      ext x
      simp [cochainDiff, LinearMap.smul_apply]]
    rw [indic_cocycle, smul_zero]), ?_⟩
  rw [twoCompDelta_classOf Z a b _ _, diffCochain_apply]
  have hA : genEval ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a) (pointSimplex Z a) = y := by
    have h1 : genEval ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a) (pointSimplex Z a)
        = y • genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z a) (pointSimplex Z a) := by
      simp [genEval, LinearMap.smul_apply]
    rw [h1, show genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z a) (pointSimplex Z a) = 1 from
      indic_gen_of_mem Z a (pointSimplex Z a) rfl]
    simp
  have hB : genEval ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a) (pointSimplex Z b) = 0 := by
    have h1 : genEval ℤ (TopCat.toSSet.obj Z) (y • indicCochain Z a) (pointSimplex Z b)
        = y • genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z a) (pointSimplex Z b) := by
      simp [genEval, LinearMap.smul_apply]
    rw [h1, show genEval ℤ (TopCat.toSSet.obj Z) (indicCochain Z a) (pointSimplex Z b) = 0 from
      indic_gen_of_not_mem Z a (pointSimplex Z b) (pi0_pointSimplex_ne Z a b hnot)]
    simp
  rw [hA, hB, sub_zero]

/-- The pullback of a cochain, evaluated at a generator. -/
theorem pullback_genEval {X Y : TopCat} (f : X ⟶ Y) (α : Cochain ℤ (TopCat.toSSet.obj Y) 0)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    genEval ℤ (TopCat.toSSet.obj X)
        (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α) s
      = genEval ℤ (TopCat.toSSet.obj Y) α
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) s) := by
  rw [genEval, genEval, LinearMap.dualMap_apply]
  congr 1
  have h := congrArg (fun (k : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).X 0) => (ModuleCat.Hom.hom k) 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f)
      (ModuleCat.of ℤ ℤ) s)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **The pullback kills `Δ`**: the image of the restriction from a path-connected space lies in the
kernel of the difference of the evaluations. -/
theorem range_le_ker_twoCompDelta {Z : TopCat} (f : Z ⟶ Y) (a b : Z) :
    LinearMap.range (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0))
      ≤ (twoCompDelta Z a b).hom.ker := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj Y) 0 y
  rw [LinearMap.mem_ker]
  rw [show (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0))
        (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) α hα)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
          (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α) _
      from singularCohomologyMap_classOf ℤ f α hα]
  rw [twoCompDelta_classOf Z a b _ _, diffCochain_apply, sub_eq_zero,
    pullback_genEval f α (pointSimplex Z a), pullback_genEval f α (pointSimplex Z b),
    map_pointSimplex f a, map_pointSimplex f b]
  exact Sph1.genEval_congr_of_joined (X := Y) (f := α) hα (PathConnectedSpace.joined (f a) (f b))

/-- A dual linear map is linear in its argument. -/
lemma dualMap_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (l : M →ₗ[ℤ] N) (c : ℤ) (φ : N →ₗ[ℤ] ℤ) : l.dualMap (c • φ) = c • l.dualMap φ := by
  ext x
  simp [LinearMap.dualMap_apply, LinearMap.smul_apply]

/-- **The kernel of `Δ` is contained in the image of the pullback.** -/
theorem ker_le_range_twoCompDelta {Z : TopCat} (f : Z ⟶ Y) (a b : Z)
    (hjoin : ∀ z : Z, Joined z a ∨ Joined z b) (hnot : ¬ Joined a b) :
    (twoCompDelta Z a b).hom.ker
      ≤ LinearMap.range (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0)) := by
  intro x hx
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj Z) 0 x
  rw [LinearMap.mem_ker] at hx
  rw [twoCompDelta_classOf Z a b α hα, diffCochain_apply, sub_eq_zero] at hx
  have heq : genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a)
      = genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z b) := hx
  -- a `0`-cocycle is constant on the path components of `Z`
  have hconst : α = genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a)
      • unitCochain ℤ (TopCat.toSSet.obj Z) := by
    apply genEval_ext
    intro s
    have hpt : genEval ℤ (TopCat.toSSet.obj Z) α s
        = genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a) := by
      rcases hjoin (TopCat.toSSetObj₀Equiv (X := Z) s) with h | h
      · have hh := Sph1.genEval_congr_of_joined (X := Z) (f := α) hα h
        simpa only [pointSimplex, Equiv.symm_apply_apply] using hh
      · have hh := Sph1.genEval_congr_of_joined (X := Z) (f := α) hα h
        rw [show (TopCat.toSSetObj₀Equiv (X := Z)).symm (TopCat.toSSetObj₀Equiv s) = s from
          Equiv.symm_apply_apply _ _] at hh
        exact hh.trans heq.symm
    rw [hpt]
    have hval : genEval ℤ (TopCat.toSSet.obj Z)
        (genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a)
          • unitCochain ℤ (TopCat.toSSet.obj Z)) s
        = genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a) := by
      rw [Sph1.genEval_zsmul, genEval_unitCochain, smul_eq_mul, mul_one]
    rw [hval]
  -- the pullback of the unit class of `Y` is the unit class of `Z`
  have hunit : (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0))
      (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) (unitCochain ℤ (TopCat.toSSet.obj Y))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj Y)))
      = cohomologyClassOf ℤ (TopCat.toSSet.obj Z) (unitCochain ℤ (TopCat.toSSet.obj Z))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj Z)) := by
    rw [show (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0))
        (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) (unitCochain ℤ (TopCat.toSSet.obj Y))
          (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj Y)))
        = cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
            (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap
              (unitCochain ℤ (TopCat.toSSet.obj Y))) _
        from singularCohomologyMap_classOf ℤ f _ _]
    exact cohomologyClassOf_congr ℤ (TopCat.toSSet.obj Z)
      (Sph1.unitCochain_dualMap (TopCat.toSSet.map f)) _ _
  refine ⟨cohomologyClassOf ℤ (TopCat.toSSet.obj Y)
    ((genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a))
      • unitCochain ℤ (TopCat.toSSet.obj Y)) (by
        rw [show cochainDiff ℤ (TopCat.toSSet.obj Y)
            ((genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a))
              • unitCochain ℤ (TopCat.toSSet.obj Y))
            = (genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a))
              • cochainDiff ℤ (TopCat.toSSet.obj Y) (unitCochain ℤ (TopCat.toSSet.obj Y)) from by
          ext x
          simp [cochainDiff, LinearMap.smul_apply]]
        rw [cochainDiff_unitCochain, smul_zero]), ?_⟩
  rw [show (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0))
        (cohomologyClassOf ℤ (TopCat.toSSet.obj Y)
          ((genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a))
            • unitCochain ℤ (TopCat.toSSet.obj Y)) _)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
          (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap
            ((genEval ℤ (TopCat.toSSet.obj Z) α (pointSimplex Z a))
              • unitCochain ℤ (TopCat.toSSet.obj Y))) _
      from singularCohomologyMap_classOf ℤ f _ _]
  exact cohomologyClassOf_congr ℤ (TopCat.toSSet.obj Z) (by
    rw [dualMap_smul, Sph1.unitCochain_dualMap, hconst.symm]) _ _

/-- **The cokernel of the pullback from a path-connected space to a two-component space is `ℤ`.** -/
theorem cokernel_twoComponents {Z : TopCat} (f : Z ⟶ Y) (a b : Z)
    (hjoin : ∀ z : Z, Joined z a ∨ Joined z b) (hnot : ¬ Joined a b) :
    Nonempty (cokernel (singularCohomologyMap ℤ Z Y f 0) ≅ ModuleCat.of ℤ ℤ) := by
  have hle1 := range_le_ker_twoCompDelta (Y := Y) f a b
  have hle2 := ker_le_range_twoCompDelta (Y := Y) f a b hjoin hnot
  have hker : (twoCompDelta Z a b).hom.ker
      = (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0)).range := le_antisymm hle2 hle1
  have hfac : singularCohomologyMap ℤ Z Y f 0 ≫ twoCompDelta Z a b = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    exact hle1 (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  let g : cokernel (singularCohomologyMap ℤ Z Y f 0) ⟶ ModuleCat.of ℤ ℤ :=
    cokernel.desc (singularCohomologyMap ℤ Z Y f 0) (twoCompDelta Z a b) hfac
  have hgπ : cokernel.π (singularCohomologyMap ℤ Z Y f 0) ≫ g = twoCompDelta Z a b :=
    cokernel.π_desc _ _ _
  have hgval : ∀ y : ↑(singularCohomology ℤ 0 Z),
      g.hom ((cokernel.π (singularCohomologyMap ℤ Z Y f 0)).hom y) = (twoCompDelta Z a b).hom y := by
    intro y
    have := congrArg (fun (k : singularCohomology ℤ 0 Z ⟶ ModuleCat.of ℤ ℤ) =>
      k.hom y) hgπ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  haveI hEpi : Epi g := by
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := twoCompDelta_surjective Z a b hnot z
    exact ⟨(cokernel.π (singularCohomologyMap ℤ Z Y f 0)).hom y, by rw [hgval]; exact hy⟩
  haveI hMono : Mono g := by
    rw [ModuleCat.mono_iff_injective]
    intro u v huv
    have hπ : Function.Surjective (cokernel.π (singularCohomologyMap ℤ Z Y f 0)).hom :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨y, rfl⟩ := hπ v
    rw [hgval, hgval] at huv
    have hmem : x - y ∈ (ModuleCat.Hom.hom (singularCohomologyMap ℤ Z Y f 0)).range := by
      rw [← hker, LinearMap.mem_ker, map_sub, huv, sub_self]
    obtain ⟨w, hw⟩ := hmem
    have hzero : (cokernel.π (singularCohomologyMap ℤ Z Y f 0)).hom (x - y) = 0 := by
      rw [← hw]
      have hcond := cokernel.condition (singularCohomologyMap ℤ Z Y f 0)
      have := congrArg (fun (k : singularCohomology ℤ 0 Y
        ⟶ cokernel (singularCohomologyMap ℤ Z Y f 0)) => k.hom w) hcond
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at this
      exact this
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  haveI : IsIso g := isIso_of_mono_of_epi g
  exact ⟨asIso g⟩

end TwoComponentCokernel


/-! ## The main theorem -/

theorem diskPairCohomologyTop (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (((Work.Cohomology.relComplex ℤ (Work.Cohomology.diskUnit n)
      (Work.Cohomology.sphereInUnit n)).homology n) ≅ ModuleCat.of ℤ ℤ) := by
  haveI : PathConnectedSpace (diskUnit 1) := diskUnitOne_pathConnected
  obtain ⟨a, b, hjoin, hnot⟩ := sphereInUnit_one_twoComponents
  exact diskPairCohomologyTop_aux
    (cokernel_twoComponents (Y := diskUnit 1) (f := subtypeIncl (diskUnit 1) (sphereInUnit 1))
      a b hjoin hnot)
    n hn

end

end Work.Cohomology
