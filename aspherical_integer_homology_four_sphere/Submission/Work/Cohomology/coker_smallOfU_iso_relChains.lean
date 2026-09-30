import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.cokerSmallAux
import Submission.Work.Cohomology.cokerSmallLemmas
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.inclChains_comp_smallOfV
import Submission.Work.Cohomology.mem_range_incl_of_smallOfV_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

variable {X : TopCat}

/-- The relative small chains of the cover `{A,V}` are the relative chains of `(V, A∩V)`:
for arbitrary `A V : Set X` the cokernel of `smallOfU A V : C_*(A) → smallChains A V` is
canonically isomorphic to `relChains (TopCat.of V) {x : V | (x : X) ∈ A}`.  No hypothesis on
`A, V` is needed (this is simplicial algebra, not topology).

Proof plan.  Put `u := smallOfU A V`, `v := smallOfV A V`, `A' := {x : V | (x : X) ∈ A}`,
`incl := inclChains (TopCat.of V) A'`, `πu := cokernel.π u`, `θ := v ≫ πu`.
(a) `u ≫ smallToSing A V = inclChains X A` and `v ≫ smallToSing A V = inclChains X V`
    (functoriality of `SSet.chainComplexMap` plus the definitions of `smallOfU`/`smallOfV`
    via `smallLiftU`/`smallLiftV`; note `subtypeIncl = inclUX`).
(b) `incl ≫ v = w ≫ u` where `w : C_*(A') ⟶ C_*(A)` is induced by
    `⟨fun x => ⟨x.1.1, x.2⟩, _⟩ : TopCat.of A' ⟶ TopCat.of A`; check it on generators using
    `SSet.chainComplex_hom_ext`, `iota_smallOfU`, `iota_smallOfV` (both sides send the generator of
    a simplex of `A'` to the generator of the same small simplex of `X`).  Hence `incl ≫ θ = 0`.
(c) Every `d : (smallChains A V).X n` equals `u a - v b` for some `a : C_n(A)`, `b : C_n(V)`:
    `Work.Cohomology.mv_degreewise A V n` (Submission/Work/Cohomology/mv_shortExact.lean) gives
    degreewise short exactness of the Mayer–Vietoris sequence, whose middle map is
    `mvRight A V = biprod.desc (smallOfU A V) (-(smallOfV A V))`; apply
    `ModuleCat.epi_iff_surjective` to `(mvRight A V).f n`.
(d) The short complex `S := ShortComplex.mk incl θ hθ` is short exact: `Mono incl` from
    `mono_chainMap_subtypeIncl`; `Epi θ` via `Preadditive.epi_iff_cancel_zero`: given `ψ` with
    `θ ≫ ψ = 0`, set `L := πu ≫ ψ`; then `u ≫ L = 0` (since `u ≫ πu = 0`) and `v ≫ L = 0` (the
    hypothesis), so `L = 0` by `HomologicalComplex.hom_ext` together with (c), and then `ψ = 0`
    because `πu` is epi.  Exactness: use `HomologicalComplex.exact_of_degreewise_exact` and
    `ShortComplex.moduleCat_exact_iff`, i.e. for `x` with `(πu.f n) (v.f n x) = 0` produce `y` with
    `(incl.f n) y = x`.  For this, first get the general fact
    `(cokernel.π u).f n x = 0 ↔ ∃ y, (u.f n) y = x` from `ShortComplex.exact_cokernel u`, its
    `.map` along `HomologicalComplex.eval _ _ n` and `ShortComplex.moduleCat_exact_iff`; then
    prove the key elementwise statement `v x ∈ range u → x ∈ range incl`: apply `smallToSing A V`
    and (a) to get `(inclChains X A) y = (inclChains X V) x`, whence (as a linear map on `C_n(V)`)
    `x = (chainRetract ℤ X V n).hom ((inclChains X A).f n y)` by `chainRetract_spec`; so `x` lies in
    the range of `ρ := (inclChains X A).f n ≫ (chainRetract ℤ X V n).hom`.  Finally
    `range ρ ≤ range (incl.f n)`: apply `Work.Cohomology.mem_of_gen` to the space `TopCat.of A` and
    the preimage under `ρ` of `range (incl.f n)`; a generator `gen τ` (`τ` a simplex of `A`) maps
    to `chainRetract ℤ X V n (gen X n (toSSet.map (subtypeIncl X A) τ))`, which by the definition of
    `chainRetract` and `Cofan.IsColimit.fac` is either `0` or `gen τ'` for the simplex `τ'` of `V`
    with `toSSet.map (subtypeIncl X V) τ' = toSSet.map (subtypeIncl X A) τ`; in the latter case the
    image of `τ'` in `X` lies in `A`, so `τ'` factors through `A'` by
    `exists_map_inclUX_of_range_subset` (Submission/Work/Cohomology/smallLift_cov.lean), and
    `gen τ' ∈ range (incl.f n)` by `SSet.ι_chainComplexMap_f`.
(e) Conclude: `ShortComplex.ShortExact.gIsCokernel` applied to `S` and to
    `Work.Cohomology.hPairShort_shortExact (TopCat.of V) A'` shows that `cokernel u` and
    `relChains (TopCat.of V) A'` are both colimits of cokernel coforks of the same morphism `incl`,
    so `IsColimit.coconePointUniqueUpToIso` yields the required isomorphism. -/
theorem coker_smallOfU_iso_relChains (X : TopCat) (A V : Set X) :
    Nonempty (CategoryTheory.Limits.cokernel (smallOfU A V) ≅
      relChains (TopCat.of V) (setOf (fun x : V => (x : X) ∈ A))) := by
  -- the naturality square `incl ≫ v = w ≫ u`, hence `incl ≫ θ = 0`
  have htheta : inclChains (TopCat.of V) (relSubset A V) ≫
      (smallOfV A V ≫ CategoryTheory.Limits.cokernel.π (smallOfU A V)) = 0 := by
    rw [← Category.assoc, inclChains_comp_smallOfV X A V, Category.assoc,
      CategoryTheory.Limits.cokernel.condition, comp_zero]
  -- the comparison map `C_*(V, V ∩ A) ⟶ cokernel (smallOfU A V)`
  let phi : CategoryTheory.Limits.cokernel (inclChains (TopCat.of V) (relSubset A V)) ⟶
      CategoryTheory.Limits.cokernel (smallOfU A V) :=
    CategoryTheory.Limits.cokernel.desc (inclChains (TopCat.of V) (relSubset A V))
      (smallOfV A V ≫ CategoryTheory.Limits.cokernel.π (smallOfU A V)) htheta
  have hphi : CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of V) (relSubset A V)) ≫ phi
      = smallOfV A V ≫ CategoryTheory.Limits.cokernel.π (smallOfU A V) :=
    CategoryTheory.Limits.cokernel.π_desc _ _ _
  have hphi_apply : ∀ (n : ℕ) (x : (singularChains ℤ (TopCat.of V)).X n),
      (phi.f n) ((CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of V) (relSubset A V))).f n x)
        = (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n ((smallOfV A V).f n x) := by
    intro n x
    have hmor : (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of V) (relSubset A V))).f n
        ≫ phi.f n
        = (smallOfV A V).f n ≫ (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n := by
      have h := congrArg (fun (g : singularChains ℤ (TopCat.of V) ⟶
          CategoryTheory.Limits.cokernel (smallOfU A V)) => g.f n) hphi
      simpa only [HomologicalComplex.comp_f] using h
    have h2 := congrArg (fun (g : (singularChains ℤ (TopCat.of V)).X n ⟶
        (CategoryTheory.Limits.cokernel (smallOfU A V)).X n) => g x) hmor
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  -- surjectivity, using that every small chain is `u a - v b`
  have hsurj : ∀ n, Function.Surjective ((phi.f n).hom) := by
    intro n z
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
      ((CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n)).1 inferInstance z
    obtain ⟨a, b, hab⟩ := exists_smallOfU_sub_smallOfV A V n c
    refine ⟨-((CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of V) (relSubset A V))).f n b), ?_⟩
    rw [map_neg, hphi_apply]
    rw [← hc, ← hab]
    have hzero : (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n
        ((smallOfU A V).f n a) = 0 := by
      have hcomp : ((smallOfU A V) ≫ CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n
          = (smallOfU A V).f n ≫ (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n :=
        HomologicalComplex.comp_f _ _ n
      have hz : (0 : singularChains ℤ (TopCat.of A) ⟶
          CategoryTheory.Limits.cokernel (smallOfU A V)).f n
          = (smallOfU A V).f n ≫ (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n := by
        rw [← hcomp, CategoryTheory.Limits.cokernel.condition]
      have h2 := congrArg (fun (g : (singularChains ℤ (TopCat.of A)).X n ⟶
          (CategoryTheory.Limits.cokernel (smallOfU A V)).X n) => g a) hz
      simpa using h2.symm
    rw [map_sub, hzero, zero_sub]
  -- injectivity, using the key elementwise statement
  have hker : ∀ n (y : (CategoryTheory.Limits.cokernel
      (inclChains (TopCat.of V) (relSubset A V))).X n), (phi.f n) y = 0 → y = 0 := by
    intro n y hy
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective
      ((CategoryTheory.Limits.cokernel.π
        (inclChains (TopCat.of V) (relSubset A V))).f n)).1 inferInstance y
    have h1 : (CategoryTheory.Limits.cokernel.π (smallOfU A V)).f n
        ((smallOfV A V).f n x) = 0 := by
      rw [← hphi_apply n x, hx]
      exact hy
    obtain ⟨y', hy'⟩ := (cokernel_pi_f_eq_zero_iff (smallOfU A V) n
      ((smallOfV A V).f n x)).1 h1
    obtain ⟨z, hz⟩ := mem_range_incl_of_smallOfV_eq A V n hy'.symm
    rw [← hx, ← hz]
    have hcomp : ((inclChains (TopCat.of V) (relSubset A V)) ≫ CategoryTheory.Limits.cokernel.π
        (inclChains (TopCat.of V) (relSubset A V))).f n
        = (inclChains (TopCat.of V) (relSubset A V)).f n ≫
          (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of V) (relSubset A V))).f n :=
      HomologicalComplex.comp_f _ _ n
    have hz0 : (0 : singularChains ℤ (TopCat.of (relSubset A V)) ⟶
        CategoryTheory.Limits.cokernel (inclChains (TopCat.of V) (relSubset A V))).f n
        = (inclChains (TopCat.of V) (relSubset A V)).f n ≫
          (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of V) (relSubset A V))).f n := by
      rw [← hcomp, CategoryTheory.Limits.cokernel.condition]
    have h2 := congrArg (fun (g : (singularChains ℤ (TopCat.of (relSubset A V))).X n ⟶
        (CategoryTheory.Limits.cokernel
          (inclChains (TopCat.of V) (relSubset A V))).X n) => g z) hz0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2.symm
  have hinj : ∀ n, Function.Injective ((phi.f n).hom) := by
    intro n y y' h
    have h1 : (phi.f n) (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h2 := hker n (y - y') h1
    exact sub_eq_zero.mp h2
  haveI : Epi phi := HomologicalComplex.epi_of_epi_f phi
    (fun n => (ModuleCat.epi_iff_surjective _).2 (hsurj n))
  haveI : Mono phi := HomologicalComplex.mono_of_mono_f phi
    (fun n => (ModuleCat.mono_iff_injective _).2 (hinj n))
  haveI : IsIso phi := isIso_of_mono_of_epi phi
  exact ⟨(asIso phi).symm⟩

end

end Work.Cohomology
