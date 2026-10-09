import Mathlib
import Submission.NK.LocalAnabelian.Kummer.Bridge
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer character of a class `a ∈ kˣ/(kˣ)^p`

Let `k` be a field containing a primitive `p`-th root of unity `ζ` (`p` a prime) and let
`K'` be a separable closure of `k`.  For a unit `a ∈ kˣ` and a `p`-th root `α ∈ K'` of `a`,
the **Kummer character** of `a` is the continuous homomorphism

  `χ_a : Gal(K'/k) → 𝔽_p^*,   σ ↦ (the exponent `i` such that `σ α = ζ^i α`)`.

It is independent of the choice of `α` and only depends on the class of `a` in `kˣ/(kˣ)^p`;
`χ_a = 1` if and only if `a` is a `p`-th power.  This is the map underlying the identification
`kˣ/(kˣ)^p ≃ Hom_cont(Gal(K'/k), 𝔽_p)` of Kummer theory.
-/

set_option linter.style.haveILetI false

open scoped Pointwise

open IntermediateField Polynomial

namespace Work.SSGRoute

noncomputable section

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K'] [IsSepClosure k K']
variable {p : ℕ} [Fact p.Prime] {ζ : k}

/-! ## The chosen `p`-th root -/

/-- Every unit of `k` has a `p`-th root in any separable closure, provided `k` contains a
primitive `p`-th root of unity. -/
theorem exists_pow_eq_algebraMap (hζ : IsPrimitiveRoot ζ p) (a : kˣ) :
    ∃ α : K', α ^ p = algebraMap k K' (a : k) := by
  haveI : IsSepClosed K' := IsSepClosure.sep_closed k
  have hchar : p ≠ ringChar k :=
    NK.LocalAnabelian.Kummer.pow_ne_ringChar_of_isPrimitiveRoot p (Fact.out : p.Prime) hζ
  have hpk : ((p : ℕ) : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := k) (Fact.out : p.Prime) hchar.symm
  have hsep : (X ^ p - C ((a : kˣ) : k)).Separable :=
    separable_X_pow_sub_C (a : k) hpk (by simp)
  have hdeg : (X ^ p - C ((a : kˣ) : k)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (Fact.out : p.Prime).pos]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨α, hα⟩ := IsSepClosed.exists_aeval_eq_zero K' (X ^ p - C ((a : kˣ) : k)) hdeg hsep
  refine ⟨α, ?_⟩
  rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at hα
  exact hα

/-- The Kummer field `k(a^{1/p})`, re-exported in this namespace. -/
abbrev kummerField (p : ℕ) (a : kˣ) : IntermediateField k K' :=
  NK.LocalAnabelian.kummerField (K' := K') p a

variable (hζ : IsPrimitiveRoot ζ p)

/-- A chosen `p`-th root of the unit `a` inside the separable closure `K'`. -/
def kRoot (a : kˣ) : K' := Classical.choose (exists_pow_eq_algebraMap (K' := K') hζ a)

theorem kRoot_pow (a : kˣ) : (kRoot (K' := K') hζ a) ^ p = algebraMap k K' (a : k) :=
  Classical.choose_spec (exists_pow_eq_algebraMap (K' := K') hζ a)

theorem kRoot_ne_zero (a : kˣ) : kRoot (K' := K') hζ a ≠ 0 := by
  intro h
  have h1 : (0 : K') = algebraMap k K' (a : k) := by
    rw [← kRoot_pow hζ a, h, zero_pow (Fact.out : p.Prime).ne_zero]
  have h2 : (0 : k) = (a : k) := (RingHom.injective (algebraMap k K')) (by simpa using h1.symm)
  exact a.ne_zero h2.symm

/-! ## The `p`-th roots of unity and their identification with `Multiplicative (ZMod p)` -/

/-- The primitive `p`-th root of unity `ζ`, viewed as a unit of `K'`. -/
def zetaUnit (hζ : IsPrimitiveRoot ζ p) : K'ˣ :=
  Units.mk0 (algebraMap k K' ζ) (fun h =>
    hζ.ne_zero (Nat.Prime.ne_zero (Fact.out : p.Prime))
      ((RingHom.injective (algebraMap k K')) (by simpa using h)))

theorem zetaUnit_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (zetaUnit (K' := K') hζ) p := by
  have h : IsPrimitiveRoot (((zetaUnit (K' := K') hζ : K'ˣ) : K')) p := by
    rw [show ((zetaUnit (K' := K') hζ : K'ˣ) : K') = algebraMap k K' ζ from rfl]
    exact hζ.map_of_injective (RingHom.injective (algebraMap k K'))
  exact (IsPrimitiveRoot.coe_units_iff (ζ := zetaUnit (K' := K') hζ)).mp h

/-- The identification of the `p`-th roots of unity in `K'` with `Multiplicative (ZMod p)`
sending `ζ ^ i` to the class of `i`. -/
def zmodPowEquiv (hζ : IsPrimitiveRoot ζ p) :
    Subgroup.zpowers (zetaUnit (K' := K') hζ) ≃* Multiplicative (ZMod p) :=
  (zetaUnit_isPrimitiveRoot hζ).zmodEquivZPowers.symm.toMultiplicativeRight

/-! ## The ratio `σ α / α` -/

/-- The ratio `σ α / α` for the chosen root `α = kRoot a`, as a unit of `K'`. -/
def kRatio (a : kˣ) (σ : K' ≃ₐ[k] K') : K'ˣ :=
  Units.mk0 (σ (kRoot (K' := K') hζ a) / kRoot (K' := K') hζ a)
    (div_ne_zero (fun h => kRoot_ne_zero hζ a (σ.injective (by rw [h, map_zero])))
      (kRoot_ne_zero hζ a))

@[simp] theorem kRatio_coe (a : kˣ) (σ : K' ≃ₐ[k] K') :
    (kRatio hζ a σ : K') = σ (kRoot (K' := K') hζ a) / kRoot (K' := K') hζ a := rfl

theorem kRatio_pow_eq_one (a : kˣ) (σ : K' ≃ₐ[k] K') : (kRatio hζ a σ) ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, kRatio_coe, Units.val_one, div_pow, ← map_pow, kRoot_pow hζ a,
    AlgEquiv.commutes σ (a : k)]
  exact div_self ((map_ne_zero_iff _ (RingHom.injective _)).mpr (Units.ne_zero a))

theorem kRatio_mem (a : kˣ) (σ : K' ≃ₐ[k] K') :
    kRatio hζ a σ ∈ Subgroup.zpowers (zetaUnit (K' := K') hζ) := by
  rw [(zetaUnit_isPrimitiveRoot hζ).zpowers_eq]
  exact (mem_rootsOfUnity p _).mpr (kRatio_pow_eq_one hζ a σ)

/-- The ratio `σ α / α` is a `p`-th root of unity in the image of `k`. -/
theorem kRatio_mem_range (a : kˣ) (σ : K' ≃ₐ[k] K') :
    (kRatio hζ a σ : K') ∈ Set.range (algebraMap k K') := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : kRatio hζ a σ ∈ rootsOfUnity p K' := by
    rw [← (zetaUnit_isPrimitiveRoot hζ).zpowers_eq]; exact kRatio_mem hζ a σ
  have hp1 : (kRatio hζ a σ : K') ^ p = 1 := by
    have h := (mem_rootsOfUnity p (kRatio hζ a σ)).mp hmem
    have := congrArg (fun u : K'ˣ => (u : K')) h
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  obtain ⟨i, -, hi⟩ :=
    (hζ.map_of_injective (RingHom.injective (algebraMap k K'))).eq_pow_of_pow_eq_one hp1
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/-- Elements of the image of `k` are fixed by `Gal(K'/k)`. -/
theorem kRatio_fixed (a : kˣ) (τ σ : K' ≃ₐ[k] K') :
    σ (kRatio hζ a τ : K') = (kRatio hζ a τ : K') := by
  obtain ⟨c, hc⟩ := kRatio_mem_range hζ a τ
  rw [← hc, AlgEquiv.commutes]

/-- **Independence of the choice of `p`-th root.**  For any nonzero `p`-th root `α` of `a`,
the ratio `σ α / α` agrees with the one computed from the chosen root. -/
theorem kRatio_eq_of_root (a : kˣ) (σ : K' ≃ₐ[k] K') (α : K')
    (hα : α ^ p = algebraMap k K' (a : k)) (hα0 : α ≠ 0) :
    kRatio (K' := K') hζ a σ =
      Units.mk0 (σ α / α)
        (div_ne_zero (fun h => hα0 (σ.injective (by rw [h, map_zero]))) hα0) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hβ0 : kRoot (K' := K') hζ a ≠ 0 := kRoot_ne_zero hζ a
  have hβp : (kRoot (K' := K') hζ a) ^ p = algebraMap k K' (a : k) := kRoot_pow hζ a
  have ha0 : ((a : kˣ) : k) ≠ 0 := Units.ne_zero a
  have hr : ((kRoot (K' := K') hζ a) / α) ^ p = 1 := by
    rw [div_pow, hβp, hα, div_self ((map_ne_zero_iff _ (RingHom.injective _)).mpr ha0)]
  have hrrange : (kRoot (K' := K') hζ a) / α ∈ Set.range (algebraMap k K') := by
    obtain ⟨i, -, hi⟩ :=
      (hζ.map_of_injective (RingHom.injective (algebraMap k K'))).eq_pow_of_pow_eq_one hr
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  have hfix : σ ((kRoot (K' := K') hζ a) / α) = (kRoot (K' := K') hζ a) / α := by
    obtain ⟨c, hc⟩ := hrrange
    rw [← hc, AlgEquiv.commutes]
  have hβeq : kRoot (K' := K') hζ a = ((kRoot (K' := K') hζ a) / α) * α :=
    (div_mul_cancel₀ _ hα0).symm
  have hratio0 : ((kRoot (K' := K') hζ a) / α) ≠ 0 := div_ne_zero hβ0 hα0
  apply Units.ext
  rw [kRatio_coe, Units.val_mk0]
  rw [hβeq, map_mul, hfix]
  field_simp

/-- The ratio is multiplicative in `σ`. -/
theorem kRatio_mul (a : kˣ) (σ τ : K' ≃ₐ[k] K') :
    kRatio hζ a (σ * τ) = kRatio hζ a σ * kRatio hζ a τ := by
  have hα0 : kRoot (K' := K') hζ a ≠ 0 := kRoot_ne_zero hζ a
  have hfix : σ (kRatio hζ a τ : K') = (kRatio hζ a τ : K') := kRatio_fixed hζ a τ σ
  have hτ : τ (kRoot (K' := K') hζ a) = (kRatio hζ a τ : K') * kRoot (K' := K') hζ a := by
    rw [kRatio_coe, div_mul_cancel₀ _ hα0]
  apply Units.ext
  rw [kRatio_coe, Units.val_mul, kRatio_coe, kRatio_coe]
  show σ (τ (kRoot (K' := K') hζ a)) / kRoot (K' := K') hζ a = _
  rw [hτ, map_mul, hfix]
  field_simp

/-- The ratio is multiplicative in `a`: it is additive in the exponent. -/
theorem kRatio_mul_of (a b : kˣ) (σ : K' ≃ₐ[k] K') :
    kRatio hζ (a * b) σ = kRatio hζ a σ * kRatio hζ b σ := by
  have ha0 : kRoot (K' := K') hζ a ≠ 0 := kRoot_ne_zero hζ a
  have hb0 : kRoot (K' := K') hζ b ≠ 0 := kRoot_ne_zero hζ b
  have hα : (kRoot (K' := K') hζ a * kRoot (K' := K') hζ b) ^ p =
      algebraMap k K' ((a * b : kˣ) : k) := by
    rw [mul_pow, kRoot_pow hζ a, kRoot_pow hζ b, ← map_mul, Units.val_mul]
  rw [kRatio_eq_of_root hζ (a * b) σ (kRoot (K' := K') hζ a * kRoot (K' := K') hζ b) hα
    (mul_ne_zero ha0 hb0)]
  apply Units.ext
  rw [Units.val_mk0, Units.val_mul, kRatio_coe, kRatio_coe, map_mul]
  field_simp

/-- If `a` is a `p`-th power then its ratio is trivial. -/
theorem kRatio_eq_one_of_mem_powSubgroup (a : kˣ) (ha : a ∈ NK.LocalAnabelian.powSubgroup p k)
    (σ : K' ≃ₐ[k] K') : kRatio hζ a σ = 1 := by
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
  rw [powMonoidHom_apply] at hb
  have hb0 : (b : k) ≠ 0 := Units.ne_zero b
  have hb' : (algebraMap k K' (b : k)) ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr hb0
  have hα : (algebraMap k K' (b : k)) ^ p = algebraMap k K' (a : k) := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hb]
  rw [kRatio_eq_of_root hζ a σ (algebraMap k K' (b : k)) hα hb']
  apply Units.ext
  rw [Units.val_mk0, Units.val_one, AlgEquiv.commutes σ (b : k), div_self hb']

/-! ## The Kummer character -/

/-- The character `χ_a : Gal(K'/k) → 𝔽_p^*`. -/
def kChar (hζ : IsPrimitiveRoot ζ p) (a : kˣ) : (K' ≃ₐ[k] K') →* Multiplicative (ZMod p) :=
  (zmodPowEquiv hζ).toMonoidHom.comp
    (MonoidHom.mk' (fun σ => ⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩)
      (fun σ τ => Subtype.ext (kRatio_mul hζ a σ τ)))

@[simp] theorem kChar_apply (a : kˣ) (σ : K' ≃ₐ[k] K') :
    kChar (K' := K') hζ a σ = zmodPowEquiv hζ ⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ := rfl

theorem kChar_mul (a b : kˣ) : kChar (K' := K') hζ (a * b) = kChar (K' := K') hζ a * kChar (K' := K') hζ b := by
  apply MonoidHom.ext
  intro σ
  have h : (⟨kRatio hζ (a * b) σ, kRatio_mem hζ (a * b) σ⟩ :
        Subgroup.zpowers (zetaUnit (K' := K') hζ)) =
      ⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ * ⟨kRatio hζ b σ, kRatio_mem hζ b σ⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact kRatio_mul_of hζ a b σ
  simp only [kChar_apply, MonoidHom.mul_apply]
  rw [← map_mul, h]

theorem kChar_eq_one_of_mem_powSubgroup (a : kˣ) (ha : a ∈ NK.LocalAnabelian.powSubgroup p k) :
    kChar (K' := K') hζ a = 1 := by
  ext σ
  rw [kChar_apply, MonoidHom.one_apply]
  have h1 : (⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ :
      Subgroup.zpowers (zetaUnit (K' := K') hζ)) = 1 :=
    Subtype.ext (kRatio_eq_one_of_mem_powSubgroup hζ a ha σ)
  rw [h1, map_one]

/-- `χ_a = 1` if and only if `a` is a `p`-th power. -/
theorem kChar_eq_one_iff (a : kˣ) : kChar (K' := K') hζ a = 1 ↔ a ∈ NK.LocalAnabelian.powSubgroup p k := by
  refine ⟨fun h => ?_, fun h => kChar_eq_one_of_mem_powSubgroup (K' := K') hζ a h⟩
  haveI : IsGalois k K' := inferInstance
  have hfix : ∀ σ : K' ≃ₐ[k] K', σ (kRoot (K' := K') hζ a) = kRoot (K' := K') hζ a := by
    intro σ
    have hσ : kChar (K' := K') hζ a σ = 1 := by rw [h]; rfl
    rw [kChar_apply] at hσ
    have h2 : (⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ :
        Subgroup.zpowers (zetaUnit (K' := K') hζ)) = 1 :=
      (zmodPowEquiv hζ).injective (by rw [hσ, map_one])
    have h3 : kRatio hζ a σ = 1 := by simpa using Subtype.ext_iff.mp h2
    have h5 : σ (kRoot (K' := K') hζ a) / kRoot (K' := K') hζ a = 1 := by
      have h6 := congrArg (fun u : K'ˣ => (u : K')) h3
      rw [kRatio_coe, Units.val_one] at h6
      exact h6
    exact (div_eq_one_iff_eq (kRoot_ne_zero hζ a)).mp h5
  have hbot : kRoot (K' := K') hζ a ∈ (⊥ : IntermediateField k K') := by
    rw [← InfiniteGalois.fixedField_bot (k := k) (K := K')]
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact hfix σ
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hbot
  have hc0 : c ≠ 0 := fun hc0 => kRoot_ne_zero hζ a (by rw [← hc, hc0, map_zero])
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
  apply (RingHom.injective (algebraMap k K'))
  rw [map_pow, hc, kRoot_pow hζ a]

/-! ## Local constancy -/

/-- The root `kRoot a` is integral over `k`, so `k⟮kRoot a⟯` is finite over `k`. -/
theorem finiteDimensional_adjoin_kRoot (a : kˣ) :
    FiniteDimensional k ↥(k⟮kRoot (K' := K') hζ a⟯) := by
  have hint : IsIntegral k (kRoot (K' := K') hζ a) :=
    IsIntegral.of_pow (Fact.out : p.Prime).pos
      (by rw [kRoot_pow hζ a]; exact isIntegral_algebraMap)
  have hfr : Module.finrank k ↥(k⟮kRoot (K' := K') hζ a⟯) =
      (minpoly k (kRoot (K' := K') hζ a)).natDegree :=
    IntermediateField.adjoin.finrank hint
  exact FiniteDimensional.of_finrank_pos (by rw [hfr]; exact minpoly.natDegree_pos hint)

/-- A Galois automorphism fixing `kRoot a` acts trivially on `χ_a`. -/
theorem kChar_eq_one_of_mem_fixingSubgroup (a : kˣ) {σ : K' ≃ₐ[k] K'}
    (hσ : σ ∈ (k⟮kRoot (K' := K') hζ a⟯).fixingSubgroup) : kChar (K' := K') hζ a σ = 1 := by
  have hfix : σ (kRoot (K' := K') hζ a) = kRoot (K' := K') hζ a :=
    (IntermediateField.mem_fixingSubgroup_iff (K := k⟮kRoot (K' := K') hζ a⟯) σ).mp hσ _
      (IntermediateField.mem_adjoin_simple_self k _)
  have hr : kRatio hζ a σ = 1 := by
    apply Units.ext
    rw [kRatio_coe, hfix]
    exact div_self (kRoot_ne_zero hζ a)
  rw [kChar_apply,
    show (⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ : Subgroup.zpowers (zetaUnit (K' := K') hζ)) = 1
      from Subtype.ext hr, map_one]

theorem kChar_locallyConstant (a : kˣ) :
    IsLocallyConstant (kChar (K' := K') hζ a : (K' ≃ₐ[k] K') → Multiplicative (ZMod p)) := by
  haveI : FiniteDimensional k ↥(k⟮kRoot (K' := K') hζ a⟯) := finiteDimensional_adjoin_kRoot hζ a
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨σ • ((k⟮kRoot (K' := K') hζ a⟯).fixingSubgroup : Set (K' ≃ₐ[k] K')), ?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (k⟮kRoot (K' := K') hζ a⟯)).smul σ
  · exact ⟨1, (k⟮kRoot (K' := K') hζ a⟯).fixingSubgroup.one_mem, by simp⟩
  · intro σ' hσ'
    rcases hσ' with ⟨τ, hτ, rfl⟩
    change kChar (K' := K') hζ a (σ * τ) = kChar (K' := K') hζ a σ
    rw [map_mul, kChar_eq_one_of_mem_fixingSubgroup (K' := K') hζ a hτ, mul_one]

/-- The Kummer character as a homomorphism `kˣ →* lcHoms p Gal(K'/k)`. -/
def kCharHom (hζ : IsPrimitiveRoot ζ p) : kˣ →* ↥(lcHoms p (K' ≃ₐ[k] K')) where
  toFun a := ⟨kChar (K' := K') hζ a, kChar_locallyConstant (K' := K') hζ a⟩
  map_one' := Subtype.ext (kChar_eq_one_of_mem_powSubgroup (K' := K') hζ 1 (by
    rw [NK.LocalAnabelian.powSubgroup]
    exact MonoidHom.mem_range.mpr ⟨1, by simp [powMonoidHom_apply]⟩))
  map_mul' a b := Subtype.ext (kChar_mul (K' := K') hζ a b)


/-- The character as a multiplicative function of the class `a`. -/
def kCharAsHom (hζ : IsPrimitiveRoot ζ p) :
    kˣ →* ((K' ≃ₐ[k] K') →* Multiplicative (ZMod p)) where
  toFun a := kChar (K' := K') hζ a
  map_one' := kChar_eq_one_of_mem_powSubgroup (K' := K') hζ 1 (by
    rw [NK.LocalAnabelian.powSubgroup]
    exact MonoidHom.mem_range.mpr ⟨1, by simp [powMonoidHom_apply]⟩)
  map_mul' := kChar_mul hζ

theorem kChar_pow (a : kˣ) (m : ℕ) :
    kChar (K' := K') hζ (a ^ m) = (kChar (K' := K') hζ a) ^ m := by
  have := map_pow (kCharAsHom (K' := K') hζ) a m
  simpa [kCharAsHom] using this

/-- `χ_a σ = 1` iff `σ` fixes the chosen `p`-th root of `a`. -/
theorem kChar_eq_one_iff_root (a : kˣ) (σ : K' ≃ₐ[k] K') :
    kChar hζ a σ = 1 ↔ σ (kRoot (K' := K') hζ a) = kRoot (K' := K') hζ a := by
  constructor
  · intro h
    rw [kChar_apply] at h
    have h2 : (⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ :
        Subgroup.zpowers (zetaUnit (K' := K') hζ)) = 1 :=
      (zmodPowEquiv hζ).injective (by rw [h, map_one])
    have h3 : kRatio hζ a σ = 1 := by simpa using Subtype.ext_iff.mp h2
    have h6 := congrArg (fun u : K'ˣ => (u : K')) h3
    rw [kRatio_coe, Units.val_one] at h6
    exact (div_eq_one_iff_eq (kRoot_ne_zero hζ a)).mp h6
  · intro h
    rw [kChar_apply]
    have hr : kRatio hζ a σ = 1 := by
      apply Units.ext
      rw [kRatio_coe, h]
      exact div_self (kRoot_ne_zero hζ a)
    rw [show (⟨kRatio hζ a σ, kRatio_mem hζ a σ⟩ : Subgroup.zpowers (zetaUnit (K' := K') hζ)) = 1
      from Subtype.ext hr, map_one]

end

end Work.SSGRoute
