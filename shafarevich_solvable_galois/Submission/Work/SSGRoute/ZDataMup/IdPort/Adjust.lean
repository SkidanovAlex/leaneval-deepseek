import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.NK.CFTLib.ARL.IdeleCongruenceLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The adjustment of idèles for an ideal modulus, and the map `θ`

This file develops the ideal-modulus analogue of the construction of
`Submission/NK/CFTLib/ArtinReciprocityIdeal/indexIdealCoprimeLeNormClassIndex.lean`:

* `congruenceSubgroup_eq_congruenceSubgroupId` — for a principal modulus `(m)`, `m > 0`, the
  congruence subgroup of `CoreId.lean` is the congruence subgroup of `NK.CFTLib.Arl`;
* `congruenceSubgroupId_mono` — the congruence subgroup is monotone in the modulus;
* `exists_adjust_congruenceSubgroupId` — every idèle can be adjusted by a principal idèle into
  `U(𝔪)` (weak approximation, reduced to the natural-number case);
* `thetaIdFun`, `thetaId` — the map `𝕀 K →* (fractional ideals) ⧸ P(𝔪)·𝔑(𝔪)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.IdPort
open NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The congruence subgroup of a principal modulus -/

/-- The `𝔭`-adic value of a positive natural number `m` is the level `exp (-count)` of its
principal ideal. -/
lemma valued_natCast_eq_exp_neg_count_span (m : ℕ) (hm : 0 < m)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((m : ℕ) : 𝔭.adicCompletion K)
      = WithZero.exp (-(FractionalIdeal.count K 𝔭
          (Ideal.span {(m : 𝓞 K)} : FractionalIdeal (𝓞 K)⁰ K) : ℤ)) := by
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  rw [show ((m : ℕ) : 𝔭.adicCompletion K)
      = algebraMap K (𝔭.adicCompletion K) (m : K) from
    (map_natCast (algebraMap K (𝔭.adicCompletion K)) m).symm]
  rw [valued_algebraMap_eq_exp_neg_count_spanSingleton 𝔭 hmK,
    FractionalIdeal.coeIdeal_span_singleton,
    show (algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K)) = ((m : ℕ) : K) from (map_natCast _ m)]

/-- The principal ideal `(m)` of a positive natural number is nonzero. -/
lemma span_nat_ne_bot {m : ℕ} (hm : 0 < m) : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact Nat.cast_ne_zero.mpr hm.ne'

/-- **For a principal modulus `(m)`, `m > 0`, the two congruence subgroups agree.** -/
lemma congruenceSubgroup_eq_congruenceSubgroupId {m : ℕ} (hm : 0 < m) :
    NK.CFTLib.Arl.congruenceSubgroup K m = congruenceSubgroupId K (Ideal.span {(m : 𝓞 K)}) := by
  ext x
  rw [mem_congruenceSubgroupId]
  constructor
  · intro h
    refine ⟨fun 𝔭 h𝔭 => ?_, h.2⟩
    have hmem : (m : 𝓞 K) ∈ 𝔭.asIdeal :=
      (dvdPrime_span_iff 𝔭).mp
        ((dvdPrime_iff_one_le_count (span_nat_ne_bot hm) 𝔭).mpr h𝔭)
    change Valued.v (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
      ≤ WithZero.exp (-(FractionalIdeal.count K 𝔭
          (Ideal.span {(m : 𝓞 K)} : FractionalIdeal (𝓞 K)⁰ K) : ℤ))
    rw [← valued_natCast_eq_exp_neg_count_span m hm 𝔭]
    exact h.1 𝔭 hmem
  · intro h
    refine ⟨fun 𝔭 h𝔭 => ?_, h.2⟩
    rw [valued_natCast_eq_exp_neg_count_span m hm 𝔭]
    exact h.1 𝔭 ((dvdPrime_iff_one_le_count (span_nat_ne_bot hm) 𝔭).mp
        ((dvdPrime_span_iff 𝔭).mpr h𝔭))

/-- There is a positive natural number `m` whose principal ideal is contained in `𝔪`. -/
lemma exists_nat_span_le_of_ne_bot {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ m : ℕ, 0 < m ∧ Ideal.span {(m : 𝓞 K)} ≤ 𝔪 := by
  refine ⟨Ideal.absNorm 𝔪, ?_, ?_⟩
  · exact Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨𝔪, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using h𝔪)⟩
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.absNorm_mem 𝔪))

/-- **The congruence subgroup is monotone in the modulus.** -/
lemma congruenceSubgroupId_mono {𝔪 𝔫 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (h : 𝔪 ≤ 𝔫) :
    congruenceSubgroupId K 𝔪 ≤ congruenceSubgroupId K 𝔫 := by
  intro x hx
  rw [mem_congruenceSubgroupId] at hx ⊢
  refine ⟨fun 𝔭 h𝔭 => ?_, hx.2⟩
  have h0 : (𝔪 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero]
    simpa [Ideal.zero_eq_bot] using h𝔪
  have hle : (𝔪 : FractionalIdeal (𝓞 K)⁰ K) ≤ (𝔫 : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal (K := K)).mpr h
  have hcount : FractionalIdeal.count K 𝔭 (𝔫 : FractionalIdeal (𝓞 K)⁰ K)
      ≤ FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.count_mono (K := K) (v := 𝔭) h0 hle
  have h1 : 1 ≤ FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) := le_trans h𝔭 hcount
  refine le_trans (hx.1 𝔭 h1) ?_
  exact WithZero.exp_le_exp.mpr (by omega)

/-! ## The adjustment -/

/-- **The adjustment for an ideal modulus**: every idèle can be multiplied by a principal idèle so
as to become congruent to `1` modulo `𝔪`. -/
theorem exists_adjust_congruenceSubgroupId {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele K) :
    ∃ b : Kˣ, y * Idele.principalIdele K b ∈ congruenceSubgroupId K 𝔪 := by
  obtain ⟨m, hm, hle⟩ := exists_nat_span_le_of_ne_bot h𝔪
  obtain ⟨b, hb⟩ := NK.CFTLib.ARL.exists_adjust_congruenceSubgroup K m hm y
  refine ⟨b, congruenceSubgroupId_mono (span_nat_ne_bot hm) hle ?_⟩
  rwa [← congruenceSubgroup_eq_congruenceSubgroupId (K := K) hm]

/-- A chosen adjustment: for the idèle `y`, an element `b : Kˣ` with `y · (b) ∈ U(𝔪)`. -/
noncomputable def adjId (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (y : Idele K) : Kˣ :=
  Classical.choose (exists_adjust_congruenceSubgroupId (K := K) h𝔪 y)

lemma adjId_spec {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele K) :
    y * Idele.principalIdele K (adjId 𝔪 h𝔪 y) ∈ congruenceSubgroupId K 𝔪 :=
  Classical.choose_spec (exists_adjust_congruenceSubgroupId (K := K) h𝔪 y)

/-- The ratio of two congruent idèles which differ by a principal idèle is a congruent principal
idèle. -/
lemma mem_congruenceSubgroupId_of_mul_eq {𝔪 : Ideal (𝓞 K)} {x y : Idele K}
    (hx : x ∈ congruenceSubgroupId K 𝔪) (hy : y ∈ congruenceSubgroupId K 𝔪) {γ : Kˣ}
    (h : x = y * Idele.principalIdele K γ) :
    Idele.principalIdele K γ ∈ congruenceSubgroupId K 𝔪 := by
  have h' : Idele.principalIdele K γ = y⁻¹ * x := by rw [h]; group
  rw [h']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx

/-- The ideal of a principal idèle is the principal fractional ideal `(γ)`. -/
lemma idealOfUnitHom_principalIdele' (γ : Kˣ) :
    IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K γ) = spanUnitHom K γ := by
  refine Units.ext ?_
  rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, Idele.idealOf_principalIdele]
  rfl

/-! ## The map `θ` -/

/-- The subgroup `P(𝔪)·𝔑(𝔪)`. -/
noncomputable def rayNormClId (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (𝔪 : Ideal (𝓞 K)) : Subgroup (Frac K) :=
  principalRayClId K 𝔪 ⊔ normRayId (K := K) (L := L) 𝔪

/-- The class modulo `P(𝔪)·𝔑(𝔪)` of the ideal of `x·(b)`, for a chosen adjustment `b`. -/
noncomputable def thetaIdFun (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (x : Idele K) :
    Frac K ⧸ rayNormClId K L 𝔪 :=
  QuotientGroup.mk' (rayNormClId K L 𝔪)
    (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId 𝔪 h𝔪 x)))

/-- If `x·(c) ∈ U(𝔪)` then the class of `θ x` can be computed with the adjustment `c`. -/
lemma thetaIdFun_eq_mk {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) {x : Idele K} {c : Kˣ}
    (hc : x * Idele.principalIdele K c ∈ congruenceSubgroupId K 𝔪) :
    thetaIdFun (K := K) (L := L) 𝔪 h𝔪 x = QuotientGroup.mk' (rayNormClId K L 𝔪)
      (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K c)) := by
  have hdiv : Idele.principalIdele K (adjId 𝔪 h𝔪 x / c) ∈ congruenceSubgroupId K 𝔪 :=
    mem_congruenceSubgroupId_of_mul_eq (adjId_spec h𝔪 x) hc
      (by rw [MonoidHom.map_div, mul_assoc, mul_div_cancel])
  have hkey : IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId 𝔪 h𝔪 x))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K c)
        * spanUnitHom K (adjId 𝔪 h𝔪 x / c) := by
    rw [map_mul, map_mul, idealOfUnitHom_principalIdele', idealOfUnitHom_principalIdele',
      map_div, mul_assoc, mul_div_cancel]
  rw [thetaIdFun, hkey]
  have hmem : spanUnitHom K (adjId 𝔪 h𝔪 x / c) ∈ rayNormClId K L 𝔪 :=
    Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨_, hdiv, rfl⟩)
  have hmk : QuotientGroup.mk' (rayNormClId K L 𝔪) (spanUnitHom K (adjId 𝔪 h𝔪 x / c)) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_mul, hmk, ← map_one (QuotientGroup.mk' (rayNormClId K L 𝔪)), ← map_mul, mul_one]

lemma thetaIdFun_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    thetaIdFun (K := K) (L := L) 𝔪 h𝔪 1 = 1 := by
  rw [thetaIdFun_eq_mk (K := K) (L := L) h𝔪 (x := (1 : Idele K)) (c := 1)
    (by rw [one_mul, map_one]; exact Subgroup.one_mem _)]
  rw [one_mul, map_one, map_one]
  exact map_one (QuotientGroup.mk' (rayNormClId K L 𝔪))

/-- **`θ` kills the principal idèles.** -/
lemma thetaIdFun_principal_eq_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (α : Kˣ) :
    thetaIdFun (K := K) (L := L) 𝔪 h𝔪 (Idele.principalIdele K α) = 1 := by
  have hmem : spanUnitHom K (α * adjId 𝔪 h𝔪 (Idele.principalIdele K α)) ∈ rayNormClId K L 𝔪 :=
    Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨_, by
      rw [Subgroup.mem_comap, map_mul]
      exact adjId_spec h𝔪 _, rfl⟩)
  have hval : IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K α *
      Idele.principalIdele K (adjId 𝔪 h𝔪 (Idele.principalIdele K α)))
      = spanUnitHom K (α * adjId 𝔪 h𝔪 (Idele.principalIdele K α)) := by
    rw [← map_mul, idealOfUnitHom_principalIdele']
  rw [thetaIdFun, hval]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

/-- **`θ` is multiplicative.** -/
lemma thetaIdFun_mul {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (x y : Idele K) :
    thetaIdFun (K := K) (L := L) 𝔪 h𝔪 (x * y)
      = thetaIdFun (K := K) (L := L) 𝔪 h𝔪 x * thetaIdFun (K := K) (L := L) 𝔪 h𝔪 y := by
  have hcd : (x * y) * Idele.principalIdele K (adjId 𝔪 h𝔪 x * adjId 𝔪 h𝔪 y)
      ∈ congruenceSubgroupId K 𝔪 := by
    rw [map_mul]
    have h := mul_mem (adjId_spec h𝔪 x) (adjId_spec h𝔪 y)
    convert h using 1
    ac_rfl
  have harg : (x * y) * Idele.principalIdele K (adjId 𝔪 h𝔪 x * adjId 𝔪 h𝔪 y)
      = (x * Idele.principalIdele K (adjId 𝔪 h𝔪 x))
        * (y * Idele.principalIdele K (adjId 𝔪 h𝔪 y)) := by
    rw [map_mul]; ac_rfl
  have hkey : IdeleClassGroup.idealOfUnitHom K ((x * y) *
        Idele.principalIdele K (adjId 𝔪 h𝔪 x * adjId 𝔪 h𝔪 y))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId 𝔪 h𝔪 x))
        * IdeleClassGroup.idealOfUnitHom K (y * Idele.principalIdele K (adjId 𝔪 h𝔪 y)) := by
    rw [harg, map_mul]
  rw [thetaIdFun_eq_mk (K := K) (L := L) h𝔪 (x := x * y)
      (c := adjId 𝔪 h𝔪 x * adjId 𝔪 h𝔪 y) hcd, thetaIdFun, thetaIdFun, ← map_mul, hkey]

/-- **The map `θ : 𝕀 K →* (fractional ideals) ⧸ P(𝔪)·𝔑(𝔪)`.** -/
noncomputable def thetaId (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    Idele K →* (Frac K ⧸ rayNormClId K L 𝔪) where
  toFun := thetaIdFun 𝔪 h𝔪
  map_one' := thetaIdFun_one h𝔪
  map_mul' := thetaIdFun_mul h𝔪

lemma thetaId_apply {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (x : Idele K) :
    thetaId K L 𝔪 h𝔪 x = thetaIdFun 𝔪 h𝔪 x := rfl

/-- The kernel of `θ` contains the principal idèles. -/
lemma principalSubgroup_le_ker_thetaId {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Idele.principalSubgroup K ≤ (thetaId K L 𝔪 h𝔪).ker := by
  rintro x ⟨α, rfl⟩
  rw [MonoidHom.mem_ker, thetaId_apply]
  exact thetaIdFun_principal_eq_one (K := K) (L := L) h𝔪 α

end Work.SSGRoute.ZDataMup.IdPort
