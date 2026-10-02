import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.CompatTrans.sph3Disc_relCapPair_kronH_mixed
import Submission.Work.Cohomology.CompatTrans.sphere3DiscPairHomology
-- dropped (tainted, unused)
-- dropped (tainted, unused)
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.cohomology_prod_contractible
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.homotopyEquiv_prod_fst
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Endgame.VkClean.restrCupGenerator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Unimodularity of the relative cap product of `(S³ × D⁴, S³ × S³)`

Target: `Work.Cohomology.sph3Disc_relCapPair_unimodular` (see the doc-string below).

The file contains

* the elementary `ℤ`-linear algebra used at the very end (generators of a `ℤ`-module isomorphic to
  `ℤ`, functionals vs. generators, ...);
* the vanishing of `H⁶`, `H⁷` of `S³ × D⁴` (from `S³ × D⁴ ≃ S³`);
* the **reduction** `relCapPair_surjective_of_restr_cup_generator`: the "external product" crux
  (there is a degree-`3` class `b` of `S³ × D⁴` and a degree-`3` class `β` of the sphere bundle such
  that the Alexander–Whitney product of the restriction of `b` with `β` *generates* `H⁶` of the
  sphere bundle) implies unimodularity of the relative cap product;
* the target itself, which is the reduction applied to the crux.

The mathematical content of the reduction: with `Eval : H⁷(X,A) ≅ Hom(H₇(X,A), ℤ)` the universal
coefficient evaluation, the mixed cap/cup identity (`sph3Disc_relCapPair_kronH_mixed`) reads
`⟨b, u ⌢ c⟩ = Eval (μ(b,u)) c`; the derivation rule (`pairDelta_mixedCup_general`) identifies
`μ(b, pairδ β)` with `± pairδ (restr b ⌣ β)`, and `pairδ : H⁶(A) ⟶ H⁷(X,A)` is an isomorphism.
So `u ↦ ⟨b, u ⌢ ·⟩` is onto `Hom(H₇(X,A),ℤ)`, and since the `⌢`-pairing with a generator of
`H₇(X,A)` is onto we can prescribe `⟨b, u ⌢ w⟩ = 1`; then `⟨b, -⟩ : H₃(X) → ℤ` is injective
(`H₃(X) ≅ ℤ`) and the surjectivity of `u ↦ u ⌢ w` follows.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-! ## 1. Elementary linear algebra over `ℤ` -/

lemma span_eq_top_of_iso {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) {x : M} (hx : Submodule.span ℤ {x} = ⊤) :
    Submodule.span ℤ {e x} = ⊤ := by
  have h1 : Submodule.map (e : M →ₗ[ℤ] N) (Submodule.span ℤ {x}) = Submodule.span ℤ {e x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

lemma span_neg_singleton {D : Type*} [AddCommGroup D] [Module ℤ D] (y : D) :
    Submodule.span ℤ ({-y} : Set D) = Submodule.span ℤ ({y} : Set D) := by
  rw [← Set.neg_singleton y, Submodule.span_neg]

lemma span_symm_one' {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ ({e.symm 1} : Set M) = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff]
  intro v
  exact ⟨e v, e.injective (by simp [map_smul])⟩

lemma smul_symm_one {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ) (x : M) :
    (e x) • e.symm 1 = x :=
  e.injective (by simp [map_smul])

lemma surjective_eval_symm_one {C : Type*} [AddCommGroup C] [Module ℤ C] (eC : C ≃ₗ[ℤ] ℤ) :
    Function.Surjective (fun ψ : C →ₗ[ℤ] ℤ => ψ (eC.symm 1)) := by
  intro m
  refine ⟨m • (eC : C →ₗ[ℤ] ℤ), ?_⟩
  show (m • (eC : C →ₗ[ℤ] ℤ)) (eC.symm 1) = m
  rw [LinearMap.smul_apply]
  simp

/-- A nonzero functional on a `ℤ`-module isomorphic to `ℤ` is injective. -/
lemma injective_of_ne_zero_hom {D : Type*} [AddCommGroup D] [Module ℤ D] (eD : D ≃ₗ[ℤ] ℤ)
    {φ : D →ₗ[ℤ] ℤ} (hφ : φ ≠ 0) : Function.Injective φ := by
  intro x y hxy
  have hsub : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hgen : φ (eD.symm 1) ≠ 0 := by
    intro h0
    apply hφ
    ext z
    rw [← smul_symm_one eD z]
    simp [h0]
  have hkey : eD (x - y) = 0 := by
    have h4 : (eD (x - y)) * φ (eD.symm 1) = 0 := by
      have h5 := hsub
      rw [← smul_symm_one eD (x - y)] at h5
      simpa using h5
    exact (mul_eq_zero.mp h4).resolve_right hgen
  have h5 : x - y = 0 := by
    rw [← smul_symm_one eD (x - y), hkey]
    simp
  exact sub_eq_zero.mp h5

/-- A nonzero linear map into `ℤ` is nonzero at some point. -/
lemma exists_apply_ne_zero {M : Type*} [AddCommGroup M] [Module ℤ M] {f : M →ₗ[ℤ] ℤ}
    (hf : f ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra h
  push_neg at h
  exact hf (LinearMap.ext h)

/-! ## 2. The cohomology of `S³ × D⁴` vanishes in degrees `6` and `7` -/

lemma isZero_Coh_PairXT_six_seven (k : ℕ) (h0 : k ≠ 0) (h3 : k ≠ 3) :
    IsZero (singularCohomology ℤ k PairXT) := by
  obtain ⟨e1⟩ := cohomologyIso_of_homotopyEquiv
    (Homeomorph.prodComm ↥Sph3T ↥Disc4T).toHomotopyEquiv k
  obtain ⟨e2⟩ := cohomology_prod_contractible ℤ Disc4T Sph3T k
  exact Limits.IsZero.of_iso (sphereCohomologyZero 3 k (by norm_num) h0 h3) (e1 ≪≫ e2)

/-- The cup product appearing in the crux. -/
abbrev cruxCup (b : singularCohomology ℤ 3 PairXT) (β : singularCohomology ℤ 3 (TopCat.of PairAT)) :
    singularCohomology ℤ 6 (TopCat.of PairAT) :=
  cupH' ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3) b) β

/-- Any functional on a `ℤ`-module isomorphic to `ℤ` is a multiple of the isomorphism. -/
lemma hom_eq_smul_of_span_symm_one {D : Type*} [AddCommGroup D] [Module ℤ D] (eD : D ≃ₗ[ℤ] ℤ)
    (φ : D →ₗ[ℤ] ℤ) : φ = (φ (eD.symm 1)) • (eD : D →ₗ[ℤ] ℤ) := by
  ext x
  rw [← smul_symm_one eD x]
  simp [mul_comm]

/-- An element whose image under an isomorphism `D ≅ ℤ` is `±1` generates. -/
lemma span_eq_top_of_eval_eq_pm_one {D : Type*} [AddCommGroup D] [Module ℤ D]
    (eD : D ≃ₗ[ℤ] ℤ) {x : D} (hx : eD x = 1 ∨ eD x = -1) :
    Submodule.span ℤ {x} = ⊤ := by
  rcases hx with h | h
  · have h1 : x = eD.symm 1 := eD.injective (by rw [h]; simp)
    rw [h1, span_symm_one' eD]
  · have h1 : x = -eD.symm 1 := eD.injective (by rw [map_neg, LinearEquiv.apply_symm_apply, h])
    rw [h1, span_neg_singleton, span_symm_one' eD]

/-- **The reduction.**  The "external product" crux for the trivial disc bundle over `S³` implies
unimodularity of the relative cap product of the pair `(S³ × D⁴, S³ × S³)`. -/
theorem relCapPair_surjective_of_restr_cup_generator
    (h : ∃ (b : singularCohomology ℤ 3 PairXT) (β : singularCohomology ℤ 3 (TopCat.of PairAT)),
      Submodule.span ℤ {cruxCup b β} = ⊤) :
    ∃ w : (relChains PairXT PairAT).homology 7,
      Function.Surjective (fun u : relCohomology ℤ PairXT PairAT 4 =>
        relCapPair PairXT PairAT 4 3 u w) := by
  obtain ⟨b, β, hgen⟩ := h
  have hfreeRel : ∀ k, Module.Free ℤ ↥((relChains PairXT PairAT).homology k) := by
    intro k
    obtain ⟨ek⟩ := sphere3DiscPairHomology k
    haveI : Module.Free ℤ
        ↥(ModuleCat.of ℤ (Fin ((if k = 4 then 1 else 0) + (if k = 7 then 1 else 0)) → ℤ)) :=
      inferInstance
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (uctIsoToLinearEquiv ek).symm
  obtain ⟨e, he⟩ := uctDual_evaluation (relChains PairXT PairAT)
    (relChainsProjective PairXT PairAT) hfreeRel 7
  have hmix := sph3Disc_relCapPair_kronH_mixed PairXT PairAT e he
  -- the identification `H⁷(X,A) ≅ Hom(H₇(X,A), ℤ)`
  haveI hHomIso : IsIso (HomologicalComplex.homologyMap (relDualComplexIso PairXT PairAT).hom 7) :=
    IsIso.mk ⟨HomologicalComplex.homologyMap (relDualComplexIso PairXT PairAT).inv 7, by
        rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
          HomologicalComplex.homologyMap_id],
      by rw [← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
          HomologicalComplex.homologyMap_id]⟩
  have hhom_bij : Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relDualComplexIso PairXT PairAT).hom 7)) :=
    ConcreteCategory.bijective_of_isIso _
  have hhom_surj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relDualComplexIso PairXT PairAT).hom 7)) := hhom_bij.2
  have hhom_inj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relDualComplexIso PairXT PairAT).hom 7)) := hhom_bij.1
  let EvalM : relCohomology ℤ PairXT PairAT 7 ⟶
      ModuleCat.of ℤ (↥((relChains PairXT PairAT).homology 7) →ₗ[ℤ] ℤ) :=
    HomologicalComplex.homologyMap (relDualComplexIso PairXT PairAT).hom 7 ≫ e.hom
  have hEval_surj : Function.Surjective (ModuleCat.Hom.hom EvalM) :=
    (ConcreteCategory.bijective_of_isIso e.hom).2.comp hhom_surj
  have hEval_inj : Function.Injective (ModuleCat.Hom.hom EvalM) :=
    (ConcreteCategory.bijective_of_isIso e.hom).1.comp hhom_inj
  have hEval_apply : ∀ ψ, ModuleCat.Hom.hom EvalM ψ = ModuleCat.Hom.hom e.hom
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (relDualComplexIso PairXT PairAT).hom 7) ψ) := fun ψ => rfl
  -- the generating class `pairδ 6 (cruxCup b β)`
  have hZ7 : IsZero (singularCohomology ℤ 7 PairXT) :=
    isZero_Coh_PairXT_six_seven 7 (by norm_num) (by norm_num)
  have hZ6 : IsZero (singularCohomology ℤ 6 PairXT) :=
    isZero_Coh_PairXT_six_seven 6 (by norm_num) (by norm_num)
  haveI hδ6 : IsIso (pairδ ℤ PairXT PairAT 6) := pairδ_isIso PairXT PairAT 6 hZ7 hZ6
  have e6_eq : ∀ y : ↥(singularCohomology ℤ 6 (TopCat.of PairAT)),
      (asIso (pairδ ℤ PairXT PairAT 6)).toLinearEquiv y = pairδ ℤ PairXT PairAT 6 y :=
    fun y => rfl
  have hspan6 : Submodule.span ℤ {pairδ ℤ PairXT PairAT 6 (cruxCup b β)} = ⊤ := by
    have h1 := span_eq_top_of_iso (asIso (pairδ ℤ PairXT PairAT 6)).toLinearEquiv hgen
    rwa [e6_eq] at h1
  -- the derivation rule
  have hder := Work.Sph3Disc.pairDelta_mixedCup_general PairXT PairAT 3 3 b β
  have hder' : pairδ ℤ PairXT PairAT 6 (cruxCup b β)
      = ((-1 : ℤ) ^ 3) • (mixedCup PairXT PairAT 3 4 b (pairδ ℤ PairXT PairAT 3 β)) := hder
  have hmu_eq : mixedCup PairXT PairAT 3 4 b (pairδ ℤ PairXT PairAT 3 β)
      = - (pairδ ℤ PairXT PairAT 6 (cruxCup b β)) := by
    rw [show ((-1 : ℤ) ^ 3) = -1 from by norm_num] at hder'
    have h2 : - (mixedCup PairXT PairAT 3 4 b (pairδ ℤ PairXT PairAT 3 β))
        = pairδ ℤ PairXT PairAT 6 (cruxCup b β) := by
      simpa using hder'.symm
    exact neg_eq_iff_eq_neg.mp h2
  have hspan_mu : Submodule.span ℤ {mixedCup PairXT PairAT 3 4 b (pairδ ℤ PairXT PairAT 3 β)}
      = ⊤ := by
    rw [hmu_eq, span_neg_singleton]
    exact hspan6
  have hmu_onto : Function.Surjective (mixedCup PairXT PairAT 3 4 b) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan_mu, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact LinearMap.mem_range.mpr ⟨pairδ ℤ PairXT PairAT 3 β, rfl⟩
  -- the generator `w ∈ H₇(X,A)` and surjectivity of the composite pairing
  obtain ⟨eC⟩ := RelA_seven_iso_int
  let eCL : ↥(RelA 7) ≃ₗ[ℤ] ℤ := eC.toLinearEquiv
  let w : (relChains PairXT PairAT).homology 7 := eCL.symm 1
  have hev : Function.Surjective (fun ψ : ↥((relChains PairXT PairAT).homology 7) →ₗ[ℤ] ℤ => ψ w) :=
    surjective_eval_symm_one eCL
  have hcomp : Function.Surjective (fun u : ↥(relCohomology ℤ PairXT PairAT 4) =>
      kronH ℤ (TopCat.toSSet.obj PairXT) 3 b (relCapPair PairXT PairAT 4 3 u w)) := by
    intro m
    obtain ⟨ψ, hψ⟩ := hev m
    obtain ⟨v, hv⟩ := hEval_surj ψ
    obtain ⟨u, hu⟩ := hmu_onto v
    refine ⟨u, ?_⟩
    calc kronH ℤ (TopCat.toSSet.obj PairXT) 3 b (relCapPair PairXT PairAT 4 3 u w)
        = ModuleCat.Hom.hom EvalM (mixedCup PairXT PairAT 3 4 b u) w := hmix b u w
      _ = ModuleCat.Hom.hom EvalM v w := by rw [hu]
      _ = ψ w := by rw [hv]
      _ = m := hψ
  obtain ⟨u₀, hu₀⟩ : ∃ u : ↥(relCohomology ℤ PairXT PairAT 4),
      kronH ℤ (TopCat.toSSet.obj PairXT) 3 b (relCapPair PairXT PairAT 4 3 u w) = 1 :=
    hcomp 1
  -- `⟨b, -⟩ : H₃(X) → ℤ` is nonzero, hence injective
  obtain ⟨eD⟩ := HX_iso_three
  let eDL : ↥(HX 3) ≃ₗ[ℤ] ℤ := eD.toLinearEquiv
  have hκ_ne : kronH ℤ (TopCat.toSSet.obj PairXT) 3 b ≠ 0 := by
    intro h0
    have h1 : kronH ℤ (TopCat.toSSet.obj PairXT) 3 b (relCapPair PairXT PairAT 4 3 u₀ w) = 0 := by
      rw [h0]; rfl
    rw [hu₀] at h1
    exact one_ne_zero h1
  have hκ_inj : Function.Injective (kronH ℤ (TopCat.toSSet.obj PairXT) 3 b) :=
    injective_of_ne_zero_hom eDL hκ_ne
  -- conclusion
  refine ⟨w, ?_⟩
  intro d
  obtain ⟨u, hu⟩ := hcomp (kronH ℤ (TopCat.toSSet.obj PairXT) 3 b d)
  exact ⟨u, hκ_inj hu⟩

/-- **Unimodularity of the relative cap product of the trivial disc-bundle pair
`(S³ × D⁴, S³ × S³)`.**

Here `PairXT = S³ × D⁴` is the total space of the trivial rank-`4` disc bundle over `S³` and
`PairAT = S³ × S³ = S³ × ∂D⁴` its unit sphere bundle.  The relative homology and cohomology of this
pair are `ℤ` in degrees `4` and `7` and vanish otherwise, so the relative cap product

`⌢ : H⁴(PairXT,PairAT;ℤ) × H₇(PairXT,PairAT;ℤ) ⟶ H₃(PairXT;ℤ)`

is a pairing of free rank-`1` `ℤ`-modules.  The assertion is that it is *split* (hence, since the
groups are `ℤ`, an isomorphism): there is a class `w ∈ H₇(PairXT,PairAT;ℤ)` such that the partially
applied map `u ↦ u ⌢ w` is surjective.

This is the Poincaré–Lefschetz duality of the *trivial* disc bundle over `S³` (the "overlap" case of
the two-chart computation of the disc bundle over `S⁴`), and it is the input
`Work.Cohomology.Crux.vk_relCapPair_surjective` uses to transfer surjectivity from the overlap to
`(Vk(-2), Mk(-2))`.

Available ingredients (all sorry-free in the workspace):
* `Work.Cohomology.sph3Disc_relCapPair_kronH_mixed` — the mixed cap/cup identity
  `⟨b, u ⌢ c⟩ = e(mixedCup b u)(c)` for `b ∈ H³(X)`, `u ∈ H⁴(X,A)`, `c ∈ H₇(X,A)`
  (`e` the universal-coefficient evaluation);
* `Work.Cohomology.H3X_iso_int` (`H³(S³ × D⁴) ≅ ℤ`) and the generator facts of
  `Submission/Work/Cohomology/sph3Disc_capPair_nonzero.lean`;
* `Work.Cohomology.mixedCup` and its naturality (`Work.Sph3Disc.pairDelta_mixedCup_general`);
* `Work.Cohomology.uctDual_evaluation` (universal coefficients) and
  `Work.Cohomology.Compat.relCapPair_kronH_eq` (the `(n,0)` evaluation of the relative pairing),
  `Work.Cohomology.Crux.relCapPair_zero_ne_zero_of_ne_zero` (the `(n,0)` non-degeneracy);
* the (co)homology computations of the pair (`sphere3DiscPairHomology`,
  `Work.Cohomology.sphere3DiscPair`); `Work.Cohomology.homology_prod_sphere` /
  `cohomology_prod_sphere` and `Work.Cohomology.homology_prod_contractible` for products with `S³`.

(Compatibility: the import closure must avoid `Submission.Work.Cohomology.dualZ` and
`Submission.Work.Cohomology.prodSphereAux`.) -/
theorem sph3Disc_relCapPair_unimodular :
    ∃ w : (Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7,
      Function.Surjective (fun u : Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT
        Work.Cohomology.PairAT 4 =>
        Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 u w) := by
  exact relCapPair_surjective_of_restr_cup_generator sph3Disc_restr_cup_generator

end

end Work.Cohomology
