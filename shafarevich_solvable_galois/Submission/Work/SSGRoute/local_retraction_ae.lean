import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_idele_defs
import Submission.NK.HassePrinciple.localUnits_h2_injective
import Submission.NK.HassePrinciple.exists_fixed_uniformizer_localAutHom
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
import Submission.Work.SSGRoute.finite_not_isUnramifiedAt_primes
import Submission.Work.SSGRoute.hasLocalRetraction_ofInfinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Almost everywhere splitting of the local valuation sequence

For a finite Galois extension `K/k` of number fields and a place `w` of `K`, the inclusion
`𝒪_wˣ ↪ K_wˣ` of the local units into the local field's units is a morphism of representations of
the decomposition group `D_w = Gal(K/k)_w`.  We prove here that it admits a `D_w`-equivariant
retraction for all but finitely many `w` (`local_retraction_ae`).

The two ingredients are:

* at an *unramified* finite place the extension of completions `K_w/k_v` is unramified, so a
  uniformizer `π` of the base local field `k_v` is a uniformizer of `K_w` which is fixed by every
  local automorphism attached to `D_w` (`NK.HassePrinciple.exists_fixed_uniformizer_localAutHom`);
  the retraction is then the "unit part" map `u ↦ u · π ^ (adicVal u)`, equivariant because `π` is
  fixed and the valuation is `D_w`-invariant;

* only finitely many finite places of `K` are ramified over `k`
  (`Work.SSGRoute.finite_not_isUnramifiedAt_primes`), and the archimedean places are handled
  separately (`Work.SSGRoute.hasLocalRetraction_ofInfinite`).
-/

namespace Work.SSGRoute

open CategoryTheory Representation
open NK.GlobalCFT
open SSGRoute.PTExt
open scoped NumberField WithZero

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

noncomputable section

/-! ## The unit part of a local unit -/

/-- The `adicVal` of a power of a uniformizer `π` with `v π = exp (-1)` is `-n`. -/
theorem adicVal_zpow (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1)) (n : ℤ) :
    NK.HassePrinciple.adicVal K q ((π ^ n : (q.adicCompletion K)ˣ) : q.adicCompletion K) = -n := by
  rw [NK.HassePrinciple.adicVal, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ,
    ← WithZero.exp_zsmul, WithZero.log_exp]
  simp

/-- The unit part `u · π ^ (adicVal u)` of a local unit lies in the local units. -/
theorem mul_zpow_adicVal_mem_localUnits
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1)) (u : (q.adicCompletion K)ˣ) :
    u * π ^ (NK.HassePrinciple.adicVal K q (u : q.adicCompletion K)) ∈
      Place.localUnits K (Place.ofFinite q) := by
  rw [NK.HassePrinciple.mem_localUnits_iff_adicVal_eq_zero, NK.HassePrinciple.adicVal_mul,
    adicVal_zpow K q π hπ]
  ring

/-- **The unit part map** `K_qˣ → 𝒪_qˣ`, `u ↦ u · π ^ (adicVal u)`, for a uniformizer `π`. -/
noncomputable def localUnitPartHom
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1)) :
    (q.adicCompletion K)ˣ →* ↥(Place.localUnits K (Place.ofFinite q)) where
  toFun u := ⟨u * π ^ (NK.HassePrinciple.adicVal K q (u : q.adicCompletion K)),
    mul_zpow_adicVal_mem_localUnits K q π hπ u⟩
  map_one' := by
    apply Subtype.ext
    show (1 : (q.adicCompletion K)ˣ) * π ^ NK.HassePrinciple.adicVal K q
      ((1 : (q.adicCompletion K)ˣ) : q.adicCompletion K) = 1
    rw [NK.HassePrinciple.adicVal_one, zpow_zero, mul_one]
  map_mul' u v := by
    apply Subtype.ext
    show (u * v) * π ^ NK.HassePrinciple.adicVal K q
        (((u * v : (q.adicCompletion K)ˣ) : q.adicCompletion K))
      = (u * π ^ NK.HassePrinciple.adicVal K q ((u : (q.adicCompletion K)ˣ) : q.adicCompletion K))
        * (v * π ^ NK.HassePrinciple.adicVal K q
            ((v : (q.adicCompletion K)ˣ) : q.adicCompletion K))
    rw [NK.HassePrinciple.adicVal_mul, zpow_add]
    ac_rfl

/-- The unit part map is the identity on the local units. -/
theorem localUnitPartHom_apply_self
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1))
    (u : ↥(Place.localUnits K (Place.ofFinite q))) :
    localUnitPartHom K q π hπ (u : (q.adicCompletion K)ˣ) = u := by
  apply Subtype.ext
  show (u : (q.adicCompletion K)ˣ) * π ^ NK.HassePrinciple.adicVal K q
      ((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) = (u : (q.adicCompletion K)ˣ)
  rw [(NK.HassePrinciple.mem_localUnits_iff_adicVal_eq_zero q
    (u : (q.adicCompletion K)ˣ)).mp u.2, zpow_zero, mul_one]

/-- A power of a `D_w`-fixed uniformizer is fixed by the action on the local units. -/
theorem localUnitsEquiv_zpow_uniformizer
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπfix : ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localAutHom (K := k) (Place.ofFinite q) σ (π : q.adicCompletion K)
        = (π : q.adicCompletion K))
    (σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q)) (n : ℤ) :
    NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ (π ^ n) = π ^ n := by
  apply Units.ext
  rw [NK.HassePrinciple.coe_localUnitsEquiv, Units.val_zpow_eq_zpow_val, map_zpow₀, hπfix σ]

/-- **Equivariance of the unit part map**: for a `D_w`-fixed uniformizer `π` the unit part map
commutes with the action of the decomposition group. -/
theorem localUnitPartHom_equivariant
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1))
    (hπfix : ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localAutHom (K := k) (Place.ofFinite q) σ (π : q.adicCompletion K)
        = (π : q.adicCompletion K))
    (σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q)) (u : (q.adicCompletion K)ˣ) :
    localUnitPartHom K q π hπ
        (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u)
      = ⟨NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
            ((localUnitPartHom K q π hπ u : ↥(Place.localUnits K (Place.ofFinite q))) :
              (q.adicCompletion K)ˣ),
          (NK.HassePrinciple.localUnitsEquiv_mem (K := k) (Place.ofFinite q) σ _).mpr
            (localUnitPartHom K q π hπ u).2⟩ := by
  apply Subtype.ext
  show NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u
      * π ^ NK.HassePrinciple.adicVal K q
          ((NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u :
            (q.adicCompletion K)ˣ) : q.adicCompletion K)
    = NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
        ((u * π ^ NK.HassePrinciple.adicVal K q (u : q.adicCompletion K) :
          (q.adicCompletion K)ˣ))
  rw [map_mul, localUnitsEquiv_zpow_uniformizer k K q π hπfix σ,
    NK.HassePrinciple.adicVal_localUnitsEquiv]

/-! ## The retraction at an unramified finite place -/

/-- The uniformizer of the base local field, made into a uniformizer of `K_q` and fixed by the
decomposition group; it exists as soon as `q` is unramified over `k`. -/
noncomputable def fixedUniformizer (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    (q.adicCompletion K)ˣ :=
  Classical.choose (NK.HassePrinciple.exists_fixed_uniformizer_localAutHom (K := k) (L := K)
    Q q hq he)

theorem fixedUniformizer_val (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (fixedUniformizer k K Q q hq he : q.adicCompletion K) = WithZero.exp (-1) :=
  (Classical.choose_spec (NK.HassePrinciple.exists_fixed_uniformizer_localAutHom (K := k) (L := K)
    Q q hq he)).1

theorem fixedUniformizer_fixed (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localAutHom (K := k) (Place.ofFinite q) σ
          (fixedUniformizer k K Q q hq he : q.adicCompletion K)
        = (fixedUniformizer k K Q q hq he : q.adicCompletion K) :=
  (Classical.choose_spec (NK.HassePrinciple.exists_fixed_uniformizer_localAutHom (K := k) (L := K)
    Q q hq he)).2

/-- **The `D_q`-equivariant retraction of `𝒪_qˣ ↪ K_qˣ` attached to a `D_q`-fixed uniformizer
`π` of `K_q`.** -/
noncomputable def localRetractionOfFixed
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1))
    (hπfix : ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localAutHom (K := k) (Place.ofFinite q) σ (π : q.adicCompletion K)
        = (π : q.adicCompletion K)) :
    localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q) :=
  Rep.ofHom
    { toFun := (localUnitPartHom K q π hπ).toAdditive
      map_add' := map_add _
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (localUnitPartHom K q π hπ).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (localUnitPartHom K q π hπ
              (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
                (Additive.toMul x)))
          = Additive.ofMul ⟨NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
                ((localUnitPartHom K q π hπ (Additive.toMul x) :
                  ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ),
              (NK.HassePrinciple.localUnitsEquiv_mem (K := k) (Place.ofFinite q) σ _).mpr
                (localUnitPartHom K q π hπ (Additive.toMul x)).2⟩
        rw [localUnitPartHom_equivariant k K q π hπ hπfix σ (Additive.toMul x)] }

/-- The retraction of `localRetractionOfFixed` is a left inverse of the local unit inclusion. -/
theorem localRetractionOfFixed_incl_comp
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (q.adicCompletion K)ˣ)
    (hπ : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion K) = WithZero.exp (-1))
    (hπfix : ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localAutHom (K := k) (Place.ofFinite q) σ (π : q.adicCompletion K)
        = (π : q.adicCompletion K)) :
    NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (Place.ofFinite q) ≫
        localRetractionOfFixed k K q π hπ hπfix
      = 𝟙 (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change Additive.ofMul ((localUnitPartHom K q π hπ)
      (((Additive.toMul x : ↥(Place.localUnits K (Place.ofFinite q))) :
        (q.adicCompletion K)ˣ))) = x
  rw [localUnitPartHom_apply_self K q π hπ (Additive.toMul x)]
  rfl

/-- **An unramified finite place admits a `D_q`-equivariant retraction.** -/
theorem hasLocalRetraction_of_ramificationIdx_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (he : q.asIdeal.ramificationIdx (𝓞 k) = 1) :
    HasLocalRetraction k K (Place.ofFinite q) :=
  ⟨localRetractionOfFixed k K q (fixedUniformizer k K Q q hq he)
      (fixedUniformizer_val k K Q q hq he) (fixedUniformizer_fixed k K Q q hq he),
    localRetractionOfFixed_incl_comp k K q (fixedUniformizer k K Q q hq he)
      (fixedUniformizer_val k K Q q hq he) (fixedUniformizer_fixed k K Q q hq he)⟩

/-! ## The value of a retraction on the local units -/

/-- The value of a morphism of representations `r : K_qˣ ⟶ 𝒪_qˣ` on a local unit, as a local
unit. -/
noncomputable def retractValueFun
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)) (u : (q.adicCompletion K)ˣ) :
    ↥(Place.localUnits K (Place.ofFinite q)) :=
  Additive.toMul (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u))

/-- The underlying additive map of the value map. -/
theorem retractValueFun_apply_linearMap
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)) (u : (q.adicCompletion K)ˣ) :
    r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)
      = Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q))) (retractValueFun k K q r u) :=
  rfl


/-- The value map of a morphism of representations is multiplicative. -/
theorem retractValueFun_mul
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)) (u v : (q.adicCompletion K)ˣ) :
    retractValueFun k K q r (u * v) = retractValueFun k K q r u * retractValueFun k K q r v := by
  have hkey : r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) (u * v))
      = r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)
        + r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) v) :=
    (congrArg (fun z : (localUnitsK (k := k) (K := K) (Place.ofFinite q)).V =>
        r.hom.toLinearMap z) (ofMul_mul u v)).trans (map_add _ _ _)
  exact (congrArg (fun x : (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).V =>
      Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q))) x) hkey).trans
    (toMul_add (α := ↥(Place.localUnits K (Place.ofFinite q))) _ _)

/-- The value map of a morphism of representations sends `1` to `1`. -/
theorem retractValueFun_one
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)) :
    retractValueFun k K q r 1 = 1 := by
  have hkey : r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) 1) = 0 :=
    (congrArg (fun z : (localUnitsK (k := k) (K := K) (Place.ofFinite q)).V =>
        r.hom.toLinearMap z) (ofMul_one (α := ((q.adicCompletion K)ˣ)))).trans (map_zero _)
  exact (congrArg (fun x : (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).V =>
      Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q))) x) hkey).trans
    (toMul_zero (α := ↥(Place.localUnits K (Place.ofFinite q))))

/-- A retraction of the local unit inclusion fixes the local units. -/
theorem retractValueFun_apply_localUnits
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q))
    (hr : NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (Place.ofFinite q) ≫ r
      = 𝟙 (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)))
    (u : ↥(Place.localUnits K (Place.ofFinite q))) :
    retractValueFun k K q r (u : (q.adicCompletion K)ˣ) = u := by
  set x : (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).V :=
    Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q))) u with hx
  have h : (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (Place.ofFinite q) ≫ r) x = x := by
    rw [hr, Rep.id_apply]
  rw [Rep.comp_apply] at h
  have h1 : r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ))
      (u : (q.adicCompletion K)ˣ))
      = Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q))) u := by
    rw [show (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (Place.ofFinite q)) x
      = ((Additive.ofMul (α := ((q.adicCompletion K)ˣ)) (u : (q.adicCompletion K)ˣ))
          : (localUnitsK (k := k) (K := K) (Place.ofFinite q)).V) from rfl] at h
    rw [hx] at h
    exact h
  exact (congrArg (fun x : (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).V =>
      Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q))) x) h1).trans
    (toMul_ofMul (α := ↥(Place.localUnits K (Place.ofFinite q))) u)

/-- **The value map of a retraction is equivariant** for the action of the decomposition group. -/
theorem retractValueFun_equivariant
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : localUnitsK (k := k) (K := K) (Place.ofFinite q) ⟶
      NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q))
    (σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q)) (u : (q.adicCompletion K)ˣ) :
    retractValueFun k K q r
        (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u)
      = ⟨NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
            ((retractValueFun k K q r u : ↥(Place.localUnits K (Place.ofFinite q))) :
              (q.adicCompletion K)ˣ),
          (NK.HassePrinciple.localUnitsEquiv_mem (K := k) (Place.ofFinite q) σ _).mpr
            (retractValueFun k K q r u).2⟩ := by
  have h : r.hom.toLinearMap ((localUnitsK (k := k) (K := K) (Place.ofFinite q)).ρ σ
        (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u))
      = (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).ρ σ
        (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)) :=
    LinearMap.congr_fun (r.hom.isIntertwining' σ)
      (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)
  rw [show (localUnitsK (k := k) (K := K) (Place.ofFinite q)).ρ σ
      (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)
    = Additive.ofMul (α := ((q.adicCompletion K)ˣ))
        (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u) from rfl] at h
  rw [show r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)
    = Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
        (Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
          (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u))) from rfl] at h
  rw [show (NK.HassePrinciple.localUnitsSubRep k K (Place.ofFinite q)).ρ σ
      (Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
        (Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
          (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u))))
    = Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
        ⟨NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
            ((Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
              (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u)) :
                ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ),
          (NK.HassePrinciple.localUnitsEquiv_mem (K := k) (Place.ofFinite q) σ _).mpr
            (Additive.toMul (α := ↥(Place.localUnits K (Place.ofFinite q)))
              (r.hom.toLinearMap (Additive.ofMul (α := ((q.adicCompletion K)ˣ)) u))).2⟩
    from rfl] at h
  exact (Additive.ofMul (α := ↥(Place.localUnits K (Place.ofFinite q)))).injective
    ((retractValueFun_apply_linearMap k K q r
      (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ u)).symm.trans h)

/-! ## A retraction forces unramifiedness -/

/-- **The existence of a `D_q`-equivariant retraction of `𝒪_qˣ ↪ K_qˣ` forces `q` to be
unramified over `k`.** -/
theorem isUnramifiedAt_of_hasLocalRetraction
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : HasLocalRetraction k K (Place.ofFinite q)) :
    Work.LocalFields.IsUnramifiedAt k q := by
  classical
  obtain ⟨r, hr⟩ := h
  -- a uniformizer of the local field `K_q`
  obtain ⟨π₀, hπ₀, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one q
  have hπ₀ne : (π₀ : q.adicCompletion K) ≠ 0 := by
    intro h0
    have h1 : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (0 : q.adicCompletion K) = WithZero.exp (-1 : ℤ) := by rw [← h0]; exact hπ₀
    rw [map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let π : (q.adicCompletion K)ˣ := Units.mk0 (π₀ : q.adicCompletion K) hπ₀ne
  have hπval : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (π : q.adicCompletion K) = WithZero.exp (-1 : ℤ) := hπ₀
  -- its image under the retraction
  let c : ↥(Place.localUnits K (Place.ofFinite q)) := retractValueFun k K q r π
  have hcval : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((c : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ) = 1 :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := q)).mp c.2
  -- the `D_q`-fixed uniformizer `π / r π`
  let a : (q.adicCompletion K)ˣ :=
    π / ((c : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ)
  have haval : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (a : q.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [Units.val_div_eq_div_val, map_div₀, hπval, hcval, div_one]
  have hafix : ∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (Place.ofFinite q),
      NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ a = a := by
    intro σ
    set w : (q.adicCompletion K)ˣ :=
      π⁻¹ * NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ π with hw
    have hwmem : w ∈ Place.localUnits K (Place.ofFinite q) := by
      rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, hw, Units.val_mul,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀,
        NK.HassePrinciple.localUnitsEquiv_valued (K := k) q σ π]
      exact inv_mul_cancel₀ (by rw [hπval]; exact WithZero.exp_ne_zero)
    let w' : ↥(Place.localUnits K (Place.ofFinite q)) := ⟨w, hwmem⟩
    have hwcoe : (w' : (q.adicCompletion K)ˣ) = w := rfl
    have hπσ : NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ π = π * w := by
      rw [hw]; group
    have hcσ : NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
          ((retractValueFun k K q r π : ↥(Place.localUnits K (Place.ofFinite q))) :
            (q.adicCompletion K)ˣ)
        = ((retractValueFun k K q r π : ↥(Place.localUnits K (Place.ofFinite q))) :
            (q.adicCompletion K)ˣ) * w := by
      have h2 : ((retractValueFun k K q r
            (NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ π)
            : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ)
          = NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
              ((retractValueFun k K q r π : ↥(Place.localUnits K (Place.ofFinite q))) :
                (q.adicCompletion K)ˣ) :=
        congrArg (fun z : ↥(Place.localUnits K (Place.ofFinite q)) =>
          (z : (q.adicCompletion K)ˣ)) (retractValueFun_equivariant k K q r σ π)
      rw [← h2, hπσ, retractValueFun_mul, ← hwcoe]
      rw [retractValueFun_apply_localUnits k K q r hr w', Subgroup.coe_mul]
    show NK.HassePrinciple.localUnitsEquiv (K := k) (Place.ofFinite q) σ
        (π / ((c : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ))
      = π / ((c : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ)
    rw [map_div, hπσ,
      show ((c : ↥(Place.localUnits K (Place.ofFinite q))) : (q.adicCompletion K)ˣ)
        = ((retractValueFun k K q r π : ↥(Place.localUnits K (Place.ofFinite q))) :
            (q.adicCompletion K)ˣ) from rfl, hcσ]
    rw [mul_div_mul_right_eq_div]
  -- the prime of `𝓞 k` below `q`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (𝓞 k), Ideal.IsPrime.under _ _, Ideal.under_ne_bot _ q.ne_bot⟩
  have hQ : q.asIdeal.LiesOver Q.asIdeal := Ideal.over_under q.asIdeal
  haveI : q.asIdeal.LiesOver Q.asIdeal := hQ
  -- the fixed uniformizer comes from the base local field
  have hfix : ∀ (σ : K ≃ₐ[k] K)
      (hσ : σ • NK.GlobalCFT.Place.ofFinite q = NK.GlobalCFT.Place.ofFinite q),
      Units.map (NK.GlobalCFT.Place.localRingEquiv σ (NK.GlobalCFT.Place.ofFinite q)).toMonoidHom a
        = hσ.symm ▸ a :=
    (localUnitsEquiv_fixed_iff_ringEquiv_fixed k K q a).mp hafix
  obtain ⟨y, hy⟩ := NK.GlobalCFT.Inclusion.glp_localFixed_finite (K := k) (L := K) hQ a hfix
  -- the valuation of the image is the `e`-th power
  have hval : WithZero.exp (-1 : ℤ)
      = (Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion k)) ^ (q.asIdeal.ramificationIdx (𝓞 k)) := by
    rw [← haval, ← hy, NK.GlobalCFT.Inclusion.glp_localAlgebraMapUnits_ofFinite hQ,
      Units.coe_map]
    exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hQ
      (y : Q.adicCompletion k)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (R := Q.adicCompletion k)
      (Γ₀ := WithZero (Multiplicative ℤ)) (y : Q.adicCompletion k) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero y))).symm⟩
  rw [hm, ← WithZero.exp_nsmul] at hval
  have h1 : (-1 : ℤ) = (q.asIdeal.ramificationIdx (𝓞 k)) • m := WithZero.exp_injective hval
  have h2 : ((q.asIdeal.ramificationIdx (𝓞 k) : ℕ) : ℤ) * m = -1 := by
    rw [← nsmul_eq_mul]; exact h1.symm
  have h3 : q.asIdeal.ramificationIdx (𝓞 k) = 1 := by
    refine Nat.dvd_one.mp (Int.ofNat_dvd.mp ?_)
    exact ⟨-m, by rw [mul_neg, h2]; norm_num⟩
  rw [Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one (K := k) (L := K) Q q,
    Ideal.ramificationIdxIn_eq_ramificationIdx (G := K ≃ₐ[k] K) Q.asIdeal q.asIdeal]
  exact h3

/-- **An unramified finite place has a `D_q`-equivariant retraction.** -/
theorem hasLocalRetraction_of_isUnramifiedAt
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Work.LocalFields.IsUnramifiedAt k q) :
    HasLocalRetraction k K (Place.ofFinite q) := by
  classical
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (𝓞 k), Ideal.IsPrime.under _ _, Ideal.under_ne_bot _ q.ne_bot⟩
  have hQ : q.asIdeal.LiesOver Q.asIdeal := Ideal.over_under q.asIdeal
  haveI : q.asIdeal.LiesOver Q.asIdeal := hQ
  have h1 : Q.asIdeal.ramificationIdxIn (𝓞 K) = 1 :=
    (Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one (K := k) (L := K) Q q).mp h
  have h2 : q.asIdeal.ramificationIdx (𝓞 k) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (G := K ≃ₐ[k] K) Q.asIdeal q.asIdeal]
    exact h1
  exact hasLocalRetraction_of_ramificationIdx_one k K Q q hQ h2

/-- **Almost everywhere splitting of the local valuation sequence**: for all but finitely many
places `w` of `K` the inclusion `𝒪_wˣ ↪ K_wˣ` admits a `D_w`-equivariant retraction. -/
theorem local_retraction_ae (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] :
    {w : NK.GlobalCFT.Place K | ¬ Work.SSGRoute.HasLocalRetraction k K w}.Finite := by
  classical
  have hfin : (NK.GlobalCFT.Place.ofFinite ''
      {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        ¬ Work.LocalFields.IsUnramifiedAt k q}).Finite :=
    (Work.SSGRoute.finite_not_isUnramifiedAt_primes k K).image _
  refine Set.Finite.subset hfin ?_
  intro w hw
  rcases w with v | q
  · exact absurd (Work.SSGRoute.hasLocalRetraction_ofInfinite k K v) hw
  · exact ⟨q, fun hunr => hw (hasLocalRetraction_of_isUnramifiedAt k K q hunr), rfl⟩

end

end Work.SSGRoute
