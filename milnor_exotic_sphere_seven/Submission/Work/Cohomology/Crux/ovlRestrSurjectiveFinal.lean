import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.resSurjectiveVkDefs
import Submission.Work.Cohomology.Endgame.ovlCohomologyGroups
import Submission.Work.Cohomology.Endgame.transgression_identity_overlap
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.Crux.cruxDelta7_isIso
import Submission.Work.Cohomology.Crux.ovlRestrSurjCompat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` is surjective

`X = Vk (-2)` is the total space of Milnor's rank-`4` disc bundle over `S⁴`, `A = Mk (-2)` its unit
sphere bundle, and `U`, `V` the two chart images of the two-chart clutching description of `X`; the
overlap is `W = U ∩ V`.

Both groups involved are `ℤ` (`Work.Cohomology.Crux.vk_chartPair_group`,
`Work.Cohomology.Endgame.ovlCohomologyGroups`), so surjectivity of the restriction map coincides
with the unitality of the *Lefschetz duality* pairing of the disc bundle `D(ξ)`:
`u ↦ u ⌢ c` is onto `H₄(X;ℤ)` for a suitable relative fundamental class `c`
(`Work.Cohomology.Endgame.surjective_of_pairing_identity`, the sharp form of the transgression
reduction).

The identity used is `Work.Cohomology.Endgame.transgression_identity_overlap` (the Mayer--Vietoris
transgression identity, Hatcher's Lemma 3.36, for the two-chart cover of `Vk (-2)`), which relates
the relative cap product of `(X,A)` to that of the overlap `(W, W ∩ A)` through the connecting
isomorphisms `T₀` (relative) and `U₀` (absolute): every class of `H₄(X)` determines the pairing on
the overlap, and the overlap pairing pairs `H⁴(W,W∩A) ≅ ℤ` with `H₇(W,W∩A)` onto `H₃(W) ≅ ℤ`.
-/

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- `H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2); ℤ) ≃ ℤ`. -/
theorem ovlCohomFour : Nonempty (relCohomology ℤ vkOvl vkOvlA 4 ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := Endgame.ovlCohomologyGroups 4
  have h : ((if (4:ℕ) = 4 then 1 else 0) + if (4:ℕ) = 7 then 1 else 0) = 1 := by norm_num
  rw [h] at e
  exact ⟨(e.toLinearEquiv).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)⟩

/-- `H₃(U ∩ V; ℤ) ≃ ℤ`. -/
theorem ovlHomologyThree : Nonempty ((singularChains ℤ vkOvl).homology 3 ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e₁⟩ := homologyIso_of_homotopyEquiv (Work.Milnor.homotopyEquiv_inter_sphere (-2)).some 3
  obtain ⟨e₂⟩ := sphereHomologyTop 3 (by norm_num)
  exact ⟨(e₁ ≪≫ e₂).toLinearEquiv⟩

/-- The Mayer--Vietoris transgression identity for the two-chart cover of `Vk(-2)`. -/
theorem transgressionID :
    ∃ (T₀ : (relChains vkPairX vkPairA).homology 8 ≃ₗ[ℤ]
            (relChains (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV)).homology 7)
      (U₀ : (singularChains ℤ vkPairX).homology 4 ≃ₗ[ℤ]
            (singularChains ℤ (TopCat.of ↥(vkU ∩ vkV))).homology 3),
      ∀ (a : relCohomology ℤ vkPairX vkPairA 4)
        (c : (relChains vkPairX vkPairA).homology 8),
        U₀ (relCapPair vkPairX vkPairA 4 4 a c)
          = relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3
              ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV)
                  vkPairA (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom a) (T₀ c)
        ∨ U₀ (relCapPair vkPairX vkPairA 4 4 a c)
          = - relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3
              ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV)
                  vkPairA (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom a) (T₀ c) := by
  have hrel : (ComplexShape.down ℕ).Rel 4 3 := by simp [ComplexShape.down]
  haveI hδmv : IsIso ((mvSmall_shortExact vkU vkV).δ 4 3 hrel) :=
    ShortComplex.ShortExact.isIso_δ (mvSmall_shortExact vkU vkV) 4 3 hrel
      (vkSabs_X₂_homology_isZero 4 (by norm_num)) (vkSabs_X₂_homology_isZero 3 (by norm_num))
  exact Endgame.transgression_identity_overlap vkPairX vkPairA vkU vkV vkU_isOpen vkV_isOpen
    vkU_union_vkV cruxDelta7_isIso hrel hδmv

/-- A surjective additive map out of a copy of `ℤ` to `ℤ` is injective. -/
lemma injective_of_surjective_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (f : M →+ ℤ) (hf : Function.Surjective f) :
    Function.Injective f := by
  set g : ℤ →+ ℤ := f.comp (e.symm : ℤ →ₗ[ℤ] M).toAddMonoidHom with hgdef
  have hg1 : ∀ n : ℤ, g n = n * g 1 := by
    intro n
    have h := map_zsmul g n (1 : ℤ)
    rw [smul_eq_mul, mul_one] at h
    exact h
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨m, hm⟩ := hf z
    refine ⟨e m, ?_⟩
    change f ((e.symm : ℤ →ₗ[ℤ] M) (e m)) = z
    rw [show (e.symm : ℤ →ₗ[ℤ] M) (e m) = m from e.symm_apply_apply m, hm]
  obtain ⟨t, ht⟩ := hsurj 1
  have h2 : t * g 1 = 1 := by rw [← hg1 t, ht]
  have hK : g 1 = 1 ∨ g 1 = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (u := g 1) (v := t) (by rw [mul_comm]; exact h2)
  have hK' : (∀ n : ℤ, g n = n) ∨ (∀ n : ℤ, g n = -n) := by
    rcases hK with hK | hK
    · left; intro n; rw [hg1 n, hK, mul_one]
    · right; intro n; rw [hg1 n, hK, mul_neg, mul_one]
  intro x y hxy
  have hgx : g (e x) = f x := by
    change f ((e.symm : ℤ →ₗ[ℤ] M) (e x)) = f x
    rw [show (e.symm : ℤ →ₗ[ℤ] M) (e x) = x from e.symm_apply_apply x]
  have hgy : g (e y) = f y := by
    change f ((e.symm : ℤ →ₗ[ℤ] M) (e y)) = f y
    rw [show (e.symm : ℤ →ₗ[ℤ] M) (e y) = y from e.symm_apply_apply y]
  have hsame : g (e x) = g (e y) := by rw [hgx, hgy, hxy]
  rcases hK' with h | h
  · have hxy' : e x = e y := by rw [← h (e x), hsame, h (e y)]
    exact e.injective hxy'
  · have hxy' : -(e x) = -(e y) := by rw [← h (e x), hsame, h (e y)]
    exact e.injective (neg_injective hxy')

/-- A surjective additive map out of a copy of `ℤ` to a copy of `ℤ` is injective
(generalised codomain). -/
lemma injective_of_surjective_int' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (eM : M ≃ₗ[ℤ] ℤ) (eN : N ≃ₗ[ℤ] ℤ)
    (f : M →+ N) (hf : Function.Surjective f) : Function.Injective f := by
  set g : ℤ →+ ℤ := (eN : N →ₗ[ℤ] ℤ).toAddMonoidHom.comp
      (f.comp (eM.symm : ℤ →ₗ[ℤ] M).toAddMonoidHom) with hgdef
  have hcomp : ∀ z : ℤ, g z = eN (f ((eM.symm : ℤ →ₗ[ℤ] M) z)) := fun z => rfl
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨m, hm⟩ := hf ((eN.symm : ℤ →ₗ[ℤ] N) z)
    refine ⟨eM m, ?_⟩
    rw [hcomp, show (eM.symm : ℤ →ₗ[ℤ] M) (eM m) = m from eM.symm_apply_apply m, hm]
    exact eN.apply_symm_apply z
  have hginj : Function.Injective g :=
    injective_of_surjective_int (e := LinearEquiv.refl ℤ ℤ) g hsurj
  intro x y hxy
  have h1 : g (eM x) = eN (f x) := by
    rw [hcomp, show (eM.symm : ℤ →ₗ[ℤ] M) (eM x) = x from eM.symm_apply_apply x]
  have h2 : g (eM y) = eN (f y) := by
    rw [hcomp, show (eM.symm : ℤ →ₗ[ℤ] M) (eM y) = y from eM.symm_apply_apply y]
  have hsame : g (eM x) = g (eM y) := by rw [h1, h2, hxy]
  exact eM.injective (hginj hsame)

/-- **The target from the Lefschetz-duality surjectivity of the pair `(Vk(-2), Mk(-2))`.**

Given `c ∈ H₈(Vk,Mk)` for which `u ↦ u ⌢ c` is onto `H₄(Vk)`, the Mayer--Vietoris transgression
identity (with the connecting maps isomorphisms) and the unimodularity of the overlap pairing force
the restriction `H⁴(Vk,Mk) → H⁴(U∩V, (U∩V)∩Mk)` to be surjective. -/
theorem ovlRestrSurjective_of_duality
    (hc : ∃ c : (relChains vkPairX vkPairA).homology 8,
      Function.Surjective (fun u : relCohomology ℤ vkPairX vkPairA 4 =>
        relCapPair vkPairX vkPairA 4 4 u c)) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap ℤ vkOvlA vkPairA (subtypeIncl vkPairX (vkU ∩ vkV))
        (fun x hx => hx)) 4)) := by
  obtain ⟨eD⟩ := ovlCohomFour
  obtain ⟨eN⟩ := ovlHomologyThree
  obtain ⟨T₀, U₀, hid⟩ := transgressionID
  obtain ⟨c, hc⟩ := hc
  -- The overlap pairing with the fixed class `T₀ c`, as an additive map.
  set Q : relCohomology ℤ vkOvl vkOvlA 4 →+ (singularChains ℤ vkOvl).homology 3 :=
    { toFun := fun β =>
        relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3 β (T₀ c)
      map_zero' := by simp
      map_add' := fun x y => by simp [map_add] }
    with hQdef
  have hQ : ∀ β : relCohomology ℤ vkOvl vkOvlA 4,
      Q β = relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3 β (T₀ c) :=
    fun β => rfl
  -- Step 1: `Q ∘ ρ` is onto `H₃(U ∩ V)`.
  have h3 : Function.Surjective (fun a : relCohomology ℤ vkPairX vkPairA 4 =>
      Q ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV) vkPairA
        (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom a)) := by
    intro y
    obtain ⟨m, hm⟩ := U₀.surjective y
    obtain ⟨a, ha⟩ := hc m
    have ha' : relCapPair vkPairX vkPairA 4 4 a c = m := ha
    have hy : U₀ (relCapPair vkPairX vkPairA 4 4 a c) = y := by rw [ha', hm]
    rcases hid a c with h | h
    · refine ⟨a, ?_⟩
      show Q _ = y
      rw [hQ]
      exact h.symm.trans hy
    · refine ⟨-a, ?_⟩
      show Q _ = y
      rw [hQ]
      have hneg : -(relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3
          ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV) vkPairA
            (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom a) (T₀ c)) = y :=
        h.symm.trans hy
      have hmap : (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV)
          vkPairA (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom (-a)
          = - (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV)
          vkPairA (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4).hom a := map_neg _ _
      rw [hmap, map_neg, LinearMap.neg_apply, hneg]
  have hQsurj : Function.Surjective Q := fun y => by
    obtain ⟨a, ha⟩ := h3 y
    exact ⟨_, ha⟩
  have hinj : Function.Injective Q := injective_of_surjective_int' eD eN Q hQsurj
  intro β
  obtain ⟨a, ha⟩ := h3 (Q β)
  refine ⟨a, hinj ?_⟩
  exact ha


/-- **The requested statement**: the restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))`
is surjective.  This is `Work.Cohomology.Crux.ovlRestrSurjCompat` (the collar/excision proof). -/
theorem ovlRestrSurjectiveFinal :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ Work.Cohomology.Crux.vkOvlA Work.Cohomology.vkPairA
        (Work.Cohomology.subtypeIncl Work.Cohomology.vkPairX
          (Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
        (fun x hx => hx)) 4)) :=
  Work.Cohomology.Crux.ovlRestrSurjCompat

end

end Work.Cohomology.Crux
