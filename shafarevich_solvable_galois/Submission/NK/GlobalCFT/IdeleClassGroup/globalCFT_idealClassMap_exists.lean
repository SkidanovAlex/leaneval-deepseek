import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ideal class map on the idèle class group

For a number field `K` the ideal class map `C_K = 𝕀 K ⧸ Kˣ →* Cl(K)` sends an idèle to the class
of its attached fractional ideal.  Its kernel is the image of the idèles which are local units at
every finite place (`Idele.integralIdeles`), and it is surjective: every fractional ideal class is
represented by an idèle.

This file constructs the map and proves the two properties.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K : Type*} [Field K] [NumberField K]

/-- The fractional ideal attached to a product of idèles is the product of the fractional
ideals. -/
theorem idealOf_mul (x y : Idele K) : idealOf (x * y) = idealOf x * idealOf y := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := idealOf (x * y)) (idealOf_ne_zero (x * y)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := idealOf x * idealOf y)
        (mul_ne_zero (idealOf_ne_zero x) (idealOf_ne_zero y))]
  refine finprod_congr fun q => ?_
  rw [count_idealOf (x * y) q, exp_mul,
    FractionalIdeal.count_mul K q (idealOf_ne_zero x) (idealOf_ne_zero y),
    count_idealOf x q, count_idealOf y q]

/-- The fractional ideal attached to the trivial idèle is trivial. -/
theorem idealOf_one : idealOf (1 : Idele K) = 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := idealOf (1 : Idele K)) (idealOf_ne_zero 1),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := (1 : FractionalIdeal (𝓞 K)⁰ K)) one_ne_zero]
  refine finprod_congr fun q => ?_
  rw [count_idealOf, exp_one, FractionalIdeal.count_one]

/-- The fractional ideal attached to the inverse idèle is the inverse fractional ideal. -/
theorem idealOf_inv (x : Idele K) : idealOf x⁻¹ = (idealOf x)⁻¹ := by
  have h2 : idealOf x * idealOf x⁻¹ = 1 := by
    rw [← idealOf_mul, mul_inv_cancel, idealOf_one]
  exact eq_inv_of_mul_eq_one_right h2

/-- The fractional ideal attached to a principal idèle is the principal fractional ideal. -/
theorem idealOf_principalIdele (k : Kˣ) :
    idealOf (principalIdele K k) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := idealOf (principalIdele K k)) (idealOf_ne_zero _),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K))
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero k))]
  refine finprod_congr fun q => ?_
  rw [count_idealOf, exp_principalIdele,
    NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq q (Units.ne_zero k)]

/-- An idèle has trivial attached fractional ideal iff it is a local unit at every finite
place. -/
theorem idealOf_eq_one_iff (x : Idele K) : idealOf x = 1 ↔ x ∈ integralIdeles K := by
  constructor
  · intro h
    rw [mem_integralIdeles]
    intro v hv
    rw [Place.isFinite_iff] at hv
    obtain ⟨q, rfl⟩ := hv
    rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, exp_val]
    have h0 : exp q x = 0 := by
      rw [← count_idealOf, h, FractionalIdeal.count_one]
    rw [h0, neg_zero, WithZero.exp_zero]
  · intro hx
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
          (I := idealOf x) (idealOf_ne_zero x),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := (1 : FractionalIdeal (𝓞 K)⁰ K)) one_ne_zero]
    refine finprod_congr fun q => ?_
    rw [count_idealOf, FractionalIdeal.count_one, exp_eq_zero_of_mem_localUnits (x := x)
      ((mem_integralIdeles.mp hx) (Place.ofFinite q) (Place.isFinite_ofFinite q))]

end Idele

namespace IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- Two non-zero fractional ideals with the same `q`-adic orders of vanishing are equal. -/
theorem fractionalIdeal_eq_of_count_eq {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) (h : ∀ q, FractionalIdeal.count K q I = FractionalIdeal.count K q J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := I) hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 K) (K := K)
        (I := J) hJ]
  refine finprod_congr fun q => ?_
  rw [h q]

/-! ### A unit of the local field with prescribed valuation -/

/-- A local uniformizer, regarded as a unit of the local field at the finite place `q`. -/
noncomputable def unifUnit (K : Type*) [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) : (q.adicCompletion K)ˣ :=
  Units.map (algebraMap K (q.adicCompletion K))
    (Units.mk0 (uniformizer K q) (uniformizer_ne_zero K q))

theorem unifUnit_coe (q : HeightOneSpectrum (𝓞 K)) :
    ((unifUnit K q : (q.adicCompletion K)ˣ) : q.adicCompletion K)
      = algebraMap K (q.adicCompletion K) (uniformizer K q) := by
  rw [unifUnit, Units.coe_map, Units.val_mk0]
  rfl

theorem valued_unifUnit (q : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((unifUnit K q : (q.adicCompletion K)ˣ) : q.adicCompletion K)
      = WithZero.exp (-1) := by
  rw [unifUnit_coe]
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q
    (uniformizer K q)).trans (uniformizer_spec K q)

theorem valued_unifUnit_zpow (q : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Valued.v (((unifUnit K q ^ n : (q.adicCompletion K)ˣ) : q.adicCompletion K))
      = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_unifUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

/-! ### An idèle with prescribed `q`-adic exponents -/

/-- The idèle which is `1` at every archimedean place and the `f q`-th power of a local
uniformizer at the finite place `q`.  The condition `hf` is exactly the restricted product
condition. -/
noncomputable def ideleOfFun (K : Type*) [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) → ℤ) (hf : ∀ᶠ q in Filter.cofinite, f q = 0) : Idele K :=
  ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => unifUnit K q ^ (f q), by
      classical
      rw [Filter.eventually_cofinite]
      refine ((Filter.eventually_cofinite.mp hf).toFinset.image Place.ofFinite).finite_toSet.subset ?_
      intro v hv
      match v with
      | Sum.inl w => exact absurd (Place.mem_localUnits_ofInfinite (w := w) (x := 1)) hv
      | Sum.inr q =>
          refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
          rw [Set.Finite.mem_toFinset]
          intro hq
          exact hv (by
            change unifUnit K q ^ (f q) ∈ Place.localUnits K (Place.ofFinite q)
            rw [hq, zpow_zero]
            exact Subgroup.one_mem _)⟩

theorem exp_ideleOfFun (f : HeightOneSpectrum (𝓞 K) → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (q : HeightOneSpectrum (𝓞 K)) :
    Idele.exp q (ideleOfFun K f hf) = f q := by
  rw [Idele.exp_def]
  have h1 : ((ideleOfFun K f hf (Place.ofFinite q)) : q.adicCompletion K)
      = ((unifUnit K q ^ (f q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) := rfl
  rw [h1, valued_unifUnit_zpow, WithZero.log_exp, neg_neg]

theorem count_idealOf_ideleOfFun (f : HeightOneSpectrum (𝓞 K) → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q (Idele.idealOf (ideleOfFun K f hf)) = f q := by
  rw [Idele.count_idealOf, exp_ideleOfFun]

/-- Every non-zero fractional ideal is the ideal attached to some idèle. -/
theorem idealOf_surjective (K : Type*) [Field K] [NumberField K] :
    ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∃ x : Idele K, Idele.idealOf x = (I : FractionalIdeal (𝓞 K)⁰ K) := by
  intro I
  refine ⟨ideleOfFun K (fun q => FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.finite_factors (K := K) (I := (I : FractionalIdeal (𝓞 K)⁰ K))), ?_⟩
  exact fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) I.ne_zero (fun q => by
    rw [Idele.count_idealOf, exp_ideleOfFun])

/-! ### The ideal class map -/

/-- The idèle group maps to the group of non-zero fractional ideals. -/
noncomputable def idealOfUnitHom (K : Type*) [Field K] [NumberField K] :
    Idele K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun x := Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x)
  map_one' := Units.ext (by rw [Units.val_mk0, Units.val_one, Idele.idealOf_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, Idele.idealOf_mul])

@[simp] theorem idealOfUnitHom_apply (x : Idele K) :
    idealOfUnitHom K x = Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x) := rfl

/-- The class of the fractional ideal attached to an idèle. -/
noncomputable def idealClassMap (K : Type*) [Field K] [NumberField K] :
    Idele K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (idealOfUnitHom K)

@[simp] theorem idealClassMap_apply (x : Idele K) :
    idealClassMap K x
      = ClassGroup.mk K (Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x)) := rfl

theorem idealClassMap_principalIdele (k : Kˣ) :
    idealClassMap K (Idele.principalIdele K k) = 1 := by
  rw [idealClassMap_apply]
  have h : Units.mk0 (Idele.idealOf (Idele.principalIdele K k)) (Idele.idealOf_ne_zero _)
      = Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K))
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero k)) :=
    Units.ext (by rw [Units.val_mk0, Units.val_mk0, Idele.idealOf_principalIdele])
  rw [h, ClassGroup.mk_eq_one_iff]
  exact ⟨(k : K), by rw [Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩

theorem idealClassMap_eq_one_of_mem_integralIdeles {x : Idele K}
    (hx : x ∈ Idele.integralIdeles K) : idealClassMap K x = 1 := by
  rw [idealClassMap_apply]
  have h : Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x) = (1 : _ˣ) :=
    Units.ext (by rw [Units.val_mk0, Units.val_one, (Idele.idealOf_eq_one_iff x).mpr hx])
  rw [h, map_one]

/-- The kernel of the ideal class map consists of the idèles whose attached fractional ideal is
principal, i.e. of the subgroup generated by the integral idèles and the principal idèles. -/
theorem idealClassMap_eq_one_iff (x : Idele K) :
    idealClassMap K x = 1 ↔
      x ∈ Idele.integralIdeles K ⊔ Idele.principalSubgroup K := by
  constructor
  · intro h
    have h' : ClassGroup.mk K
        (Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x)) = 1 := by
      rwa [idealClassMap_apply] at h
    have hI : ((Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule (𝓞 K) K).IsPrincipal :=
      (ClassGroup.mk_eq_one_iff
        (I := Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x))).mp h'
    obtain ⟨a, ha⟩ := hI.principal
    have hxa : Idele.idealOf x = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      apply Subtype.coe_injective
      simpa only [FractionalIdeal.val_eq_coe, FractionalIdeal.coe_spanSingleton,
        Units.val_mk0] using ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Idele.idealOf_ne_zero x (by rw [hxa, FractionalIdeal.spanSingleton_zero])
    set a' : Kˣ := Units.mk0 a ha0 with ha'
    have hpa : Idele.idealOf (Idele.principalIdele K a')
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      rw [Idele.idealOf_principalIdele, ha', Units.val_mk0]
    refine Subgroup.mem_sup.mpr
      ⟨x * (Idele.principalIdele K a')⁻¹, ?_, Idele.principalIdele K a', ⟨a', rfl⟩, ?_⟩
    · refine (Idele.idealOf_eq_one_iff _).mp ?_
      rw [Idele.idealOf_mul, Idele.idealOf_inv, hpa, hxa]
      exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha0)
    · group
  · intro h
    have hle : Idele.integralIdeles K ⊔ Idele.principalSubgroup K ≤ (idealClassMap K).ker := by
      rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [MonoidHom.mem_ker]
        exact idealClassMap_eq_one_of_mem_integralIdeles hy
      · intro y hy
        rw [MonoidHom.mem_ker]
        rw [Idele.mem_principalSubgroup] at hy
        obtain ⟨k, rfl⟩ := hy
        exact idealClassMap_principalIdele k
    exact hle h

theorem ker_idealClassMap (K : Type*) [Field K] [NumberField K] :
    (idealClassMap K).ker = Idele.integralIdeles K ⊔ Idele.principalSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker]
  exact idealClassMap_eq_one_iff x

theorem map_principalSubgroup_eq_bot (K : Type*) [Field K] [NumberField K] :
    (Idele.principalSubgroup K).map (mk K) = ⊥ := by
  change (Idele.principalSubgroup K).map
    (QuotientGroup.mk' (Idele.principalSubgroup K)) = ⊥
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem map_ker_idealClassMap (K : Type*) [Field K] [NumberField K] :
    (idealClassMap K).ker.map (mk K) = (Idele.integralIdeles K).map (mk K) := by
  rw [ker_idealClassMap, Subgroup.map_sup, map_principalSubgroup_eq_bot, sup_bot_eq]

/-! ### The induced map on the idèle class group -/

/-- The ideal class map, descended to the idèle class group. -/
noncomputable def idealClassHom (K : Type*) [Field K] [NumberField K] :
    IdeleClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (Idele.principalSubgroup K) (idealClassMap K)
    (fun x hx => by
      rw [MonoidHom.mem_ker]
      rw [Idele.mem_principalSubgroup] at hx
      obtain ⟨k, rfl⟩ := hx
      exact idealClassMap_principalIdele k)

theorem ker_idealClassHom (K : Type*) [Field K] [NumberField K] :
    (idealClassHom K).ker = (Idele.integralIdeles K).map (mk K) := by
  rw [idealClassHom, QuotientGroup.ker_lift]
  exact map_ker_idealClassMap K

/-! ### Surjectivity -/

theorem classGroup_mk_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := by
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) c
  exact ⟨FractionalIdeal.mk0 K I, by rw [ClassGroup.mk_mk0 (K := K) I]; exact hI⟩

theorem idealOfUnitHom_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (idealOfUnitHom K) := by
  intro I
  obtain ⟨x, hx⟩ := idealOf_surjective K I
  exact ⟨x, by rw [idealOfUnitHom_apply]; exact Units.ext (by rw [Units.val_mk0]; exact hx)⟩

theorem idealClassMap_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (idealClassMap K) := by
  intro c
  obtain ⟨I, hI⟩ := classGroup_mk_surjective K c
  obtain ⟨x, hx⟩ := idealOfUnitHom_surjective K I
  refine ⟨x, ?_⟩
  have h2 : Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x) = I := by
    rw [← idealOfUnitHom_apply x]; exact hx
  rw [idealClassMap_apply, h2, hI]

theorem idealClassHom_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (idealClassHom K) :=
  QuotientGroup.lift_surjective_of_surjective (Idele.principalSubgroup K) (idealClassMap K)
    (idealClassMap_surjective K) _

/-- **The ideal class map on the idèle class group.**  There is a surjective homomorphism from
`C_K = 𝕀 K ⧸ Kˣ` onto the ideal class group of `K` whose kernel is the image of the idèles which
are local units at every finite place. -/
theorem globalCFT_idealClassMap_exists {K : Type*} [Field K] [NumberField K] :
    ∃ (f : NK.GlobalCFT.IdeleClassGroup K →* ClassGroup (NumberField.RingOfIntegers K)),
      f.ker = (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ∧
        Function.Surjective f :=
  ⟨idealClassHom K, ker_idealClassHom K, idealClassHom_surjective K⟩

end IdeleClassGroup

end NK.GlobalCFT
