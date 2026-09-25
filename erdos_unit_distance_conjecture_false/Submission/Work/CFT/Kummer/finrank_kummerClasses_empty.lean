import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.finrank_unitsModPow

/-!
# The `𝔽_p`-dimension of `V_∅/K^{×p}`

For a number field `K` and a prime `p` this file proves the classical exact-sequence computation

`dim_{𝔽_p} V_∅/K^{×p} = dim_{𝔽_p} Cl_K[p] + r + δ_{K,p}`,

where

* `V_∅ = {x ∈ Kˣ | (x) = 𝔞^p for some fractional ideal 𝔞}` is the Selmer group at the empty set
  (`selmerGroupAt K p ∅`),
* `Cl_K[p]` is the `p`-torsion of the class group (`classGroupTorsion K p`),
* `r = NumberField.Units.rank K` is the rank of the unit group,
* `δ_{K,p} = deltaK K p` is `1` iff `K` contains a primitive `p`-th root of unity.

The proof is the standard one.  Sending `x ∈ V_∅` to the class of a fractional ideal `𝔞` with
`𝔞^p = (x)` (well defined because `p`-th roots of fractional ideals of a Dedekind domain are
unique) gives a surjection `V_∅ → Cl_K[p]` whose kernel modulo `K^{×p}` is
`𝒪_Kˣ/(𝒪_Kˣ)^p`; the latter has `p ^ (r + δ)` elements, by Dirichlet's unit theorem and the
finiteness of the class number (`Work.CFT.Kummer.finrank_unitsModPow` and
`card_units_quotient_pthPower` below).  Counting cardinalities of the resulting groups gives the
dimension formula.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-! ## `p`-th roots of fractional ideals of a Dedekind domain -/

section Dedekind

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- Two `p`-th roots of a nonzero fractional ideal of a Dedekind domain agree: the monoid of
fractional ideals is free abelian, hence torsion-free, and this is visible through the valuations
`FractionalIdeal.count`. -/
theorem FractionalIdeal.pow_inj [IsDedekindDomain R] {I J : FractionalIdeal R⁰ F} (hI : I ≠ 0)
    (hJ : J ≠ 0) {p : ℕ} (hp : 0 < p) (h : I ^ p = J ^ p) : I = J := by
  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count F v I = FractionalIdeal.count F v J := by
    intro v
    have h1 : (p : ℤ) * FractionalIdeal.count F v I =
        (p : ℤ) * FractionalIdeal.count F v J := by
      have h2 := congrArg (FractionalIdeal.count F v) h
      rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at h2
      exact_mod_cast h2
    exact mul_left_cancel₀ (by exact_mod_cast hp.ne') h1
  calc I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ F) ^ FractionalIdeal.count F v I :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI).symm
    _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ F) ^ FractionalIdeal.count F v J := by
        apply finprod_congr; intro v; rw [hcount v]
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ

/-- The unit-group version of `FractionalIdeal.pow_inj`. -/
theorem FractionalIdeal.units_pow_inj [IsDedekindDomain R] {I J : (FractionalIdeal R⁰ F)ˣ}
    {p : ℕ} (hp : 0 < p) (h : I ^ p = J ^ p) : I = J := by
  refine Units.ext (FractionalIdeal.pow_inj (Units.ne_zero I) (Units.ne_zero J) hp ?_)
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

/-- A unit of `R` generates the whole ring as a fractional ideal: `(u) = 1`. -/
theorem FractionalIdeal.spanSingleton_algebraMap_units [IsDedekindDomain R]
    [Module.IsTorsionFree R F] (u : Rˣ) :
    FractionalIdeal.spanSingleton R⁰ (algebraMap R F (u : R)) = 1 := by
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨u⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def]
  simp

/-- If a unit of the fraction field is a `p`-th power of an element of the fraction field and its
`p`-th power is the image of a unit of `R`, then it is the image of a unit of `R`. -/
theorem exists_units_of_pow_eq_algebraMap_unit [IsDedekindDomain R] [Module.IsTorsionFree R F]
    {p : ℕ} (hp : 0 < p) {w : Fˣ} {u : Rˣ} (h : (w : F) ^ p = algebraMap R F (u : R)) :
    ∃ u' : Rˣ, (algebraMap R F (u' : R) : F) = (w : F) := by
  have hsp : FractionalIdeal.spanSingleton R⁰ (w : F) ^ p = (1 : FractionalIdeal R⁰ F) := by
    have h1 : FractionalIdeal.spanSingleton R⁰ ((w : F) ^ p) = 1 := by
      rw [h]; exact FractionalIdeal.spanSingleton_algebraMap_units u
    rw [← h1, ← FractionalIdeal.spanSingleton_pow]
  have hne : FractionalIdeal.spanSingleton R⁰ (w : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero w)
  have hne1 : (1 : FractionalIdeal R⁰ F) ≠ 0 := by
    rw [← FractionalIdeal.spanSingleton_one]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr one_ne_zero
  have heq : FractionalIdeal.spanSingleton R⁰ (w : F) = 1 :=
    FractionalIdeal.pow_inj hne hne1 hp (by rw [hsp, one_pow])
  have h2 : FractionalIdeal.spanSingleton R⁰ (w : F) = FractionalIdeal.spanSingleton R⁰ (1 : F) := by
    rw [heq, FractionalIdeal.spanSingleton_one]
  obtain ⟨z, hz⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).mp h2
  rw [Units.smul_def, Algebra.smul_def] at hz
  refine ⟨z⁻¹, ?_⟩
  have hz' : algebraMap R F (z : R) * algebraMap R F ((z⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hzne : algebraMap R F (z : R) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hz; exact one_ne_zero hz.symm
  exact mul_left_cancel₀ hzne (by rw [hz', hz])

/-- An invertible fractional ideal represents the trivial class in the class group iff it is
generated by a single element of the fraction field. -/
theorem ClassGroup.mk_eq_one_iff_spanSingleton [IsDomain R] {I : (FractionalIdeal R⁰ F)ˣ} :
    ClassGroup.mk F I = 1 ↔
      ∃ c : F, (I : FractionalIdeal R⁰ F) = FractionalIdeal.spanSingleton R⁰ c := by
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]

end Dedekind

/-! ## The Kummer group at the empty set of places -/

section Main

variable (K : Type*) [Field K] [NumberField K] (p : ℕ)

/-- Membership in `V_∅ = selmerGroupAt K p ∅`: the local conditions are vacuous. -/
lemma mem_selmerGroupAt_empty_iff {x : Kˣ} :
    x ∈ selmerGroupAt K p ∅ ↔ ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K,
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) = I ^ p := by
  rw [mem_selmerGroupAt, mem_selmerGroup]
  simp

/-- `V_∅`, the Selmer group at the empty set of places. -/
abbrev KummerV : Subgroup Kˣ := selmerGroupAt K p ∅

/-- The subgroup `K^{×p}` inside `V_∅`. -/
abbrev KummerP : Subgroup ↥(KummerV K p) :=
  (pthPowerSubgroup Kˣ p).comap (KummerV K p).subtype

/-- `V_∅/K^{×p}`, whose `Additive` is `kummerClasses K p ∅`. -/
abbrev KummerQ : Type _ := ↥(KummerV K p) ⧸ KummerP K p

/-- `𝒪_Kˣ/(𝒪_Kˣ)^p`, whose `Additive` is `unitsModPow K p`. -/
abbrev KummerB : Type _ := (𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p

/-- The units of `𝒪_K`, viewed as units of `K`. -/
abbrev unitsInK : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom

/-- The image of `𝒪_Kˣ` in `Kˣ`. -/
abbrev unitsSubgroup : Subgroup Kˣ := (unitsInK K).range

/-- An element of `A ⊔ B` which lies in `A`. -/
lemma mem_sup_of_mem_left {G : Type*} [CommGroup G] {A B : Subgroup G} {x : G} (h : x ∈ A) :
    x ∈ A ⊔ B := Subgroup.mem_sup.mpr ⟨x, h, 1, one_mem B, mul_one x⟩

/-- An element of `A ⊔ B` which lies in `B`. -/
lemma mem_sup_of_mem_right {G : Type*} [CommGroup G] {A B : Subgroup G} {x : G} (h : x ∈ B) :
    x ∈ A ⊔ B := Subgroup.mem_sup.mpr ⟨1, one_mem A, x, h, one_mul x⟩

/-! ### The `p`-th root ideal of an element of `V_∅` -/

noncomputable def rootIdealFn (x : ↥(KummerV K p)) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ((mem_selmerGroupAt_empty_iff K p).mp x.2).choose

lemma rootIdealFn_spec (x : ↥(KummerV K p)) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((x : Kˣ) : K) =
      rootIdealFn K p x ^ p :=
  ((mem_selmerGroupAt_empty_iff K p).mp x.2).choose_spec

lemma rootIdealFn_ne_zero (hp : p.Prime) (x : ↥(KummerV K p)) : rootIdealFn K p x ≠ 0 := by
  intro h0
  have hspec := rootIdealFn_spec K p x
  rw [h0, zero_pow hp.ne_zero] at hspec
  rw [FractionalIdeal.spanSingleton_eq_zero_iff] at hspec
  exact Units.ne_zero (x : Kˣ) hspec

/-- The invertible fractional ideal generated by a unit of `K`. -/
def spanUnit (c : Kˣ) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
  Units.mk0 (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero c))

@[simp] theorem spanUnit_coe (c : Kˣ) :
    (spanUnit K c : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K) := rfl

@[simp] theorem spanUnit_one : spanUnit K 1 = 1 := by
  refine Units.ext ?_
  simp

theorem spanUnit_mul (c d : Kˣ) : spanUnit K (c * d) = spanUnit K c * spanUnit K d := by
  refine Units.ext ?_
  simp only [spanUnit_coe, Units.val_mul, FractionalIdeal.spanSingleton_mul_spanSingleton]

/-- A chosen `p`-th root of the principal ideal `(x)`, for `x ∈ V_∅`. -/
noncomputable def rootIdeal (hp : p.Prime) (x : ↥(KummerV K p)) :
    (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
  Units.mk0 (rootIdealFn K p x) (rootIdealFn_ne_zero K p hp x)

lemma rootIdeal_pow (hp : p.Prime) (x : ↥(KummerV K p)) :
    rootIdeal K p hp x ^ p = spanUnit K (x : Kˣ) := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, rootIdeal, Units.val_mk0]
  exact (rootIdealFn_spec K p x).symm

/-- The map `V_∅ → (fractional ideals)`, `x ↦` a `p`-th root of `(x)`, is a monoid homomorphism
by uniqueness of `p`-th roots. -/
noncomputable def rootIdealHom (hp : p.Prime) :
    ↥(KummerV K p) →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ where
  toFun := rootIdeal K p hp
  map_one' := by
    refine FractionalIdeal.units_pow_inj (p := p) hp.pos ?_
    rw [rootIdeal_pow, one_pow]
    simp
  map_mul' x y := by
    refine FractionalIdeal.units_pow_inj (p := p) hp.pos ?_
    show rootIdeal K p hp (x * y) ^ p = (rootIdeal K p hp x * rootIdeal K p hp y) ^ p
    rw [mul_pow, rootIdeal_pow, rootIdeal_pow, rootIdeal_pow, ← spanUnit_mul, Subgroup.coe_mul]

/-! ### The map `V_∅ → Cl_K[p]` -/

/-- The class of `x ∈ V_∅` in the `p`-torsion of the class group. -/
noncomputable def toClassGroup (hp : p.Prime) : ↥(KummerV K p) →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (rootIdealHom K p hp)

lemma toClassGroup_pow_eq_one (hp : p.Prime) (x : ↥(KummerV K p)) :
    toClassGroup K p hp x ^ p = 1 := by
  show (ClassGroup.mk K (rootIdeal K p hp x)) ^ p = 1
  rw [← map_pow, rootIdeal_pow K p hp x]
  exact (ClassGroup.mk_eq_one_iff_spanSingleton (F := K)).mpr
    ⟨((x : Kˣ) : K), by rw [spanUnit, Units.val_mk0]⟩

lemma toClassGroup_mem (hp : p.Prime) (x : ↥(KummerV K p)) :
    toClassGroup K p hp x ∈ classGroupP K p := toClassGroup_pow_eq_one K p hp x

/-- The map `V_∅ → Cl_K[p]`. -/
noncomputable def toClassGroupP (hp : p.Prime) :
    ↥(KummerV K p) →* ↥(classGroupP K p) :=
  (toClassGroup K p hp).codRestrict (classGroupP K p) (toClassGroup_mem K p hp)

@[simp] theorem toClassGroupP_coe (hp : p.Prime) (x : ↥(KummerV K p)) :
    ((toClassGroupP K p hp x : ClassGroup (𝓞 K))) = ClassGroup.mk K (rootIdeal K p hp x) := rfl

lemma unitsInK_mem (u : (𝓞 K)ˣ) : unitsInK K u ∈ KummerV K p := by
  rw [mem_selmerGroupAt_empty_iff]
  refine ⟨1, ?_⟩
  rw [one_pow]
  exact FractionalIdeal.spanSingleton_algebraMap_units u

/-- **The kernel of `V_∅ → Cl_K[p]`**: the elements `x = u · y^p` with `u ∈ 𝒪_Kˣ`. -/
lemma toClassGroupP_eq_one_iff (hp : p.Prime) (x : ↥(KummerV K p)) :
    toClassGroupP K p hp x = 1 ↔ (x : Kˣ) ∈ unitsSubgroup K ⊔ pthPowerSubgroup Kˣ p := by
  constructor
  · intro hx
    have hx1 : (toClassGroupP K p hp x : ClassGroup (𝓞 K)) = 1 := by
      have h := congrArg Subtype.val hx
      simpa using h
    rw [toClassGroupP_coe] at hx1
    obtain ⟨c, hc⟩ := (ClassGroup.mk_eq_one_iff_spanSingleton (F := K)).mp hx1
    have hsp1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((x : Kˣ) : K) =
        (rootIdeal K p hp x : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ p := by
      rw [← Units.val_pow_eq_pow_val, rootIdeal_pow, spanUnit, Units.val_mk0]
    have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((x : Kˣ) : K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c ^ p) := by
      rw [hsp1, hc, ← FractionalIdeal.spanSingleton_pow]
    obtain ⟨z, hz⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).mp hsp
    rw [Units.smul_def, Algebra.smul_def] at hz
    have hzz : algebraMap (𝓞 K) K (z : 𝓞 K) *
        algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hz_ne : algebraMap (𝓞 K) K (z : 𝓞 K) ≠ 0 := fun h0 =>
      one_ne_zero (by rw [← hzz, h0, zero_mul])
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 : (c : K) ^ p = 0 := by rw [h0, zero_pow hp.ne_zero]
      rw [← hz] at h1
      exact mul_ne_zero hz_ne (Units.ne_zero (x : Kˣ)) h1
    refine Subgroup.mem_sup.mpr ⟨unitsInK K z⁻¹, ⟨z⁻¹, rfl⟩,
      (Units.mk0 c hc0) ^ p, mem_pthPowerSubgroup.mpr ⟨Units.mk0 c hc0, rfl⟩, ?_⟩
    have key : ((x : Kˣ) : K) = algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * c ^ p := by
      have hzz' : algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          algebraMap (𝓞 K) K (z : 𝓞 K) = 1 := by rw [mul_comm]; exact hzz
      have h2 : algebraMap (𝓞 K) K (z : 𝓞 K) * ((x : Kˣ) : K) = c ^ p := hz
      calc ((x : Kˣ) : K) = (algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
              algebraMap (𝓞 K) K (z : 𝓞 K)) * ((x : Kˣ) : K) := by rw [hzz', one_mul]
        _ = algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
              (algebraMap (𝓞 K) K (z : 𝓞 K) * ((x : Kˣ) : K)) := by rw [mul_assoc]
        _ = algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * c ^ p := by rw [h2]
    refine Units.ext ?_
    rw [Units.val_mul, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact key.symm
  · intro hx
    obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := hy
    obtain ⟨w', rfl⟩ := mem_pthPowerSubgroup.mp hw
    have hcoe : ((x : Kˣ) : K) = algebraMap (𝓞 K) K (u : 𝓞 K) * ((w' : K) ^ p) := by
      have h := congrArg (fun t : Kˣ => (t : K)) hyw.symm
      simpa [Units.val_mul, Units.coe_map] using h
    have hroot : rootIdeal K p hp x = spanUnit K w' := by
      refine FractionalIdeal.units_pow_inj (p := p) hp.pos ?_
      rw [rootIdeal_pow]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, spanUnit_coe, spanUnit_coe]
      rw [hcoe, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.spanSingleton_algebraMap_units, one_mul, ← FractionalIdeal.spanSingleton_pow]
    refine Subtype.ext ?_
    show ClassGroup.mk K (rootIdeal K p hp x) = 1
    rw [hroot]
    exact (ClassGroup.mk_eq_one_iff_spanSingleton (F := K)).mpr
      ⟨((w' : Kˣ) : K), by rw [spanUnit, Units.val_mk0]⟩

lemma kummerToClassGroup_le (hp : p.Prime) :
    KummerP K p ≤ (toClassGroupP K p hp).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  exact (toClassGroupP_eq_one_iff K p hp x).mpr
    (mem_sup_of_mem_right (Subgroup.mem_comap.mp hx))

/-- The induced map `V_∅/K^{×p} → Cl_K[p]`. -/
noncomputable def kummerToClassGroup (hp : p.Prime) :
    KummerQ K p →* ↥(classGroupP K p) :=
  QuotientGroup.lift (KummerP K p) (toClassGroupP K p hp) (kummerToClassGroup_le K p hp)

@[simp] lemma kummerToClassGroup_mk (hp : p.Prime) (x : ↥(KummerV K p)) :
    kummerToClassGroup K p hp (QuotientGroup.mk' (KummerP K p) x) = toClassGroupP K p hp x := by
  rw [kummerToClassGroup, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

lemma kummerToClassGroup_surj_aux (hp : p.Prime)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ)
    (hI : ClassGroup.mk K I ∈ classGroupP K p) :
    ∃ y : KummerQ K p, kummerToClassGroup K p hp y = ⟨ClassGroup.mk K I, hI⟩ := by
  have hI' : (ClassGroup.mk K I) ^ p = 1 := hI
  have hIp : ClassGroup.mk K (I ^ p) = 1 := by rw [map_pow, hI']
  obtain ⟨c, hc⟩ := (ClassGroup.mk_eq_one_iff_spanSingleton (F := K)).mp hIp
  have hc0 : c ≠ 0 := by
    intro h0
    have hunit : IsUnit (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c) := by
      rw [← hc, Units.val_pow_eq_pow_val]
      exact IsUnit.pow p ⟨I, rfl⟩
    rw [h0, FractionalIdeal.spanSingleton_zero] at hunit
    exact hunit.ne_zero rfl
  let w : Kˣ := Units.mk0 c hc0
  have hwc : (w : K) = c := Units.val_mk0 hc0
  have hwmem : w ∈ KummerV K p := by
    refine (mem_selmerGroupAt_empty_iff K p).mpr
      ⟨(I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), ?_⟩
    rw [hwc, ← hc, Units.val_pow_eq_pow_val]
  refine ⟨QuotientGroup.mk' (KummerP K p) (⟨w, hwmem⟩ : ↥(KummerV K p)), ?_⟩
  rw [kummerToClassGroup_mk]
  refine Subtype.ext ?_
  show ClassGroup.mk K (rootIdeal K p hp ⟨w, hwmem⟩) = ClassGroup.mk K I
  have hroot : rootIdeal K p hp (⟨w, hwmem⟩ : ↥(KummerV K p)) = I := by
    refine FractionalIdeal.units_pow_inj (p := p) hp.pos ?_
    rw [rootIdeal_pow]
    refine Units.ext ?_
    rw [spanUnit_coe, hwc, hc]
  rw [hroot]

lemma kummerToClassGroup_surjective (hp : p.Prime) :
    Function.Surjective (kummerToClassGroup K p hp) := by
  intro y
  obtain ⟨d, hd⟩ := y
  have key := ClassGroup.induction K
    (P := fun d => ∀ hd : d ∈ classGroupP K p,
      ∃ y : KummerQ K p, kummerToClassGroup K p hp y = ⟨d, hd⟩)
    (fun I hI => kummerToClassGroup_surj_aux K p hp I hI) d
  obtain ⟨y', hy'⟩ := key hd
  exact ⟨y', hy'⟩

/-! ### The map `𝒪_Kˣ/(𝒪_Kˣ)^p → V_∅/K^{×p}` -/

noncomputable def unitsToV : (𝓞 K)ˣ →* ↥(KummerV K p) where
  toFun u := ⟨unitsInK K u, unitsInK_mem K p u⟩
  map_one' := by ext; simp [unitsInK]
  map_mul' u v := by ext; simp [unitsInK, map_mul]

noncomputable def unitsToVQ : (𝓞 K)ˣ →* KummerQ K p :=
  (QuotientGroup.mk' (KummerP K p)).comp (unitsToV K p)

@[simp] lemma unitsToVQ_apply (u : (𝓞 K)ˣ) :
    unitsToVQ K p u = (QuotientGroup.mk' (KummerP K p)) (unitsToV K p u) := rfl

lemma unitsToQ_le : pthPowerSubgroup (𝓞 K)ˣ p ≤ (unitsToVQ K p).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, unitsToVQ_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  obtain ⟨v, hv⟩ := mem_pthPowerSubgroup.mp hu
  refine mem_pthPowerSubgroup.mpr ⟨unitsInK K v, ?_⟩
  show (unitsInK K v) ^ p = unitsInK K u
  rw [← hv, map_pow]

/-- The natural map `𝒪_Kˣ/(𝒪_Kˣ)^p → V_∅/K^{×p}`. -/
noncomputable def unitsToQ : KummerB K p →* KummerQ K p :=
  QuotientGroup.lift (pthPowerSubgroup (𝓞 K)ˣ p) (unitsToVQ K p) (unitsToQ_le K p)

@[simp] lemma unitsToQ_mk (u : (𝓞 K)ˣ) :
    unitsToQ K p (QuotientGroup.mk' (pthPowerSubgroup (𝓞 K)ˣ p) u) = unitsToVQ K p u := by
  rw [unitsToQ, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

lemma unitsToQ_injective (hp : p.Prime) : Function.Injective (unitsToQ K p) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro b hb
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (pthPowerSubgroup (𝓞 K)ˣ p) b
  rw [MonoidHom.mem_ker, unitsToQ_mk, unitsToVQ_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_comap] at hb
  obtain ⟨v, hv⟩ := mem_pthPowerSubgroup.mp hb
  have hvK : (v : K) ^ p = ((unitsToV K p u : Kˣ) : K) := by
    rw [← Units.val_pow_eq_pow_val, hv]; rfl
  obtain ⟨u', hu'⟩ := exists_units_of_pow_eq_algebraMap_unit (F := K) hp.pos (u := u)
    (by rw [hvK]; rfl)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pthPowerSubgroup]
  refine ⟨u', ?_⟩
  have h3 : (algebraMap (𝓞 K) K ((u' ^ p : (𝓞 K)ˣ) : 𝓞 K)) =
      algebraMap (𝓞 K) K (u : 𝓞 K) := by
    have hv' : (v : K) ^ p = (unitsInK K u : K) := congrArg (fun t : Kˣ => (t : K)) hv
    rw [Units.val_pow_eq_pow_val, map_pow, hu', hv']
    exact Units.coe_map (algebraMap (𝓞 K) K).toMonoidHom u
  exact Units.ext (IsFractionRing.injective (𝓞 K) K h3)

lemma unitsToQ_range_eq_ker (hp : p.Prime) :
    (unitsToQ K p).range = (kummerToClassGroup K p hp).ker := by
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (pthPowerSubgroup (𝓞 K)ˣ p) b
    rw [MonoidHom.mem_ker, unitsToQ_mk, unitsToVQ_apply, kummerToClassGroup_mk]
    exact (toClassGroupP_eq_one_iff K p hp _).mpr
      (mem_sup_of_mem_left (MonoidHom.mem_range.mpr ⟨u, rfl⟩))
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (KummerP K p) y
    rw [kummerToClassGroup_mk] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp ((toClassGroupP_eq_one_iff K p hp x).mp hy)
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨t, ht⟩ := mem_pthPowerSubgroup.mp hb
    rw [← ht] at hab
    refine ⟨QuotientGroup.mk' (pthPowerSubgroup (𝓞 K)ˣ p) u, ?_⟩
    rw [unitsToQ_mk, unitsToVQ_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_comap]
    refine mem_pthPowerSubgroup.mpr ⟨t, ?_⟩
    show t ^ p = (unitsInK K u)⁻¹ * (x : Kˣ)
    rw [← hab]
    group

noncomputable def unitsEquivKer (hp : p.Prime) :
    KummerB K p ≃ ↥((kummerToClassGroup K p hp).ker) :=
  Equiv.ofBijective
    ((unitsToQ K p).codRestrict _ (fun b => by
      rw [← unitsToQ_range_eq_ker K p hp]; exact ⟨b, rfl⟩)) (by
    constructor
    · intro a b hab
      exact unitsToQ_injective K p hp (Subtype.ext_iff.mp hab)
    · rintro ⟨y, hy⟩
      rw [← unitsToQ_range_eq_ker K p hp] at hy
      obtain ⟨b, hb⟩ := hy
      exact ⟨b, Subtype.ext hb⟩)

end Main

/-! ## Cardinality of `(𝒪_Kˣ)/(𝒪_Kˣ)^p` -/

/-- `(𝒪_Kˣ)/(𝒪_Kˣ)^p` has `p ^ (NumberField.Units.rank K + deltaK K p)` elements, by Dirichlet's
unit theorem and the finiteness of the class number. -/
theorem card_units_quotient_pthPower (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (hp : p.Prime) :
    Nat.card ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p) =
      p ^ (NumberField.Units.rank K + deltaK K p) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hT : Nat.card (NumberField.Units.torsion K ⧸
      pthPowerSubgroup (NumberField.Units.torsion K) p) = p ^ deltaK K p := by
    rw [card_quotient_powMonoidHom (NumberField.Units.torsion K) p, card_torsionPowKer K p hp]
  have h1 : Nat.card ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)
      = Nat.card ((NumberField.Units.torsion K ×
          (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) ⧸
          pthPowerSubgroup (NumberField.Units.torsion K ×
            (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) p) :=
    Nat.card_congr (QuotientGroup.congr _ _ (unitsMulEquiv K)
      (map_pthPowerSubgroup_mulEquiv (unitsMulEquiv K) p)).toEquiv.symm
  rw [h1, pthPowerSubgroup_prod]
  rw [Nat.card_congr (QuotientGroup.prodMulEquiv (pthPowerSubgroup (NumberField.Units.torsion K) p)
    (pthPowerSubgroup ((Fin (NumberField.Units.rank K) → Multiplicative ℤ)) p)).toEquiv]
  rw [Nat.card_prod, hT, card_pi_multInt_quotient _ p hp, Fintype.card_fin, ← pow_add,
    Nat.add_comm]

/-! ## The dimension formula -/
/-- **The Kummer-theoretic rank formula for `V_∅`**: the exact sequence
`1 → 𝒪_Kˣ/(𝒪_Kˣ)^p → V_∅/K^{×p} → Cl_K[p] → 1`
gives `dim_{𝔽_p} V_∅/K^{×p} = dim_{𝔽_p} Cl_K[p] + (r₁+r₂-1) + δ_{K,p}`. -/
theorem finrank_kummerClasses_empty (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Module.finrank (ZMod p) (Work.CFT.Kummer.kummerClasses K p ∅) =
      Module.finrank (ZMod p) (Work.CFT.Kummer.classGroupTorsion K p) +
        NumberField.Units.rank K + Work.CFT.Kummer.deltaK K p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cardinalities of the three groups
  have hcardB : Nat.card (KummerB K p) = p ^ (NumberField.Units.rank K + deltaK K p) :=
    card_units_quotient_pthPower K p hp
  have hcardC : Nat.card ↥(classGroupP K p) =
      p ^ Module.finrank (ZMod p) (classGroupTorsion K p) := by
    have h : Fintype.card (classGroupTorsion K p) =
        Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (classGroupTorsion K p) :=
      Module.card_eq_pow_finrank
    rw [ZMod.card p, ← Nat.card_eq_fintype_card] at h
    exact (Nat.card_congr Additive.ofMul.symm).trans h
  -- The exact sequence: `V_∅/K^{×p}` has as many elements as `Cl_K[p] × 𝒪_Kˣ/(𝒪_Kˣ)^p`
  have hcardQ : Nat.card (KummerQ K p) = Nat.card ↥(classGroupP K p) * Nat.card (KummerB K p) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (kummerToClassGroup K p hp).ker
    have h2 : Nat.card (KummerQ K p ⧸ (kummerToClassGroup K p hp).ker) =
        Nat.card ↥(classGroupP K p) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (kummerToClassGroup K p hp)).toEquiv,
        MonoidHom.range_eq_top.mpr (kummerToClassGroup_surjective K p hp)]
      exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    have h3 : Nat.card ↥((kummerToClassGroup K p hp).ker) = Nat.card (KummerB K p) :=
      (Nat.card_congr (unitsEquivKer K p hp)).symm
    rw [h1, h2, h3]
  have hcardQ' : Nat.card (kummerClasses K p ∅) =
      Nat.card ↥(classGroupP K p) * Nat.card (KummerB K p) :=
    (Nat.card_congr Additive.ofMul.symm).trans hcardQ
  -- Finiteness, so that `Nat.card` is `p ^ finrank`
  have hneB : Nat.card (KummerB K p) ≠ 0 := by rw [hcardB]; exact pow_ne_zero _ hp.ne_zero
  have hneC : Nat.card ↥(classGroupP K p) ≠ 0 := by
    rw [hcardC]; exact pow_ne_zero _ hp.ne_zero
  haveI : Finite (KummerQ K p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact mul_ne_zero hneC hneB)
  haveI : Fintype (KummerQ K p) := Fintype.ofFinite _
  have hcardKC : Nat.card (kummerClasses K p ∅) =
      p ^ Module.finrank (ZMod p) (kummerClasses K p ∅) := by
    have h : Fintype.card (kummerClasses K p ∅) =
        Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (kummerClasses K p ∅) :=
      Module.card_eq_pow_finrank
    rw [ZMod.card p, ← Nat.card_eq_fintype_card] at h
    exact h
  have hcalc : Nat.card (kummerClasses K p ∅) =
      p ^ (Module.finrank (ZMod p) (classGroupTorsion K p) + NumberField.Units.rank K +
        deltaK K p) := by
    rw [hcardQ', hcardC, hcardB, ← pow_add, add_assoc]
  refine Nat.pow_right_injective hp.two_le ?_
  exact hcardKC.symm.trans hcalc

end Work.CFT.Kummer
