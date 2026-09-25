import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.ARL.count_idealOf_normIdeleHom
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.CFTLib.ARL.Cyclic
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ARL.IdeleCongruenceLift
import Submission.NK.CFTLib.ARL.idealOf_mem_principalRay_sup_normIdeals
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
import Submission.NK.GlobalCFTdeep.secondInequality_unconditional

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## 1.  Bridges to the vocabulary of `NK.CFTLib.ARL` -/

/-- The principal fractional ideal `(a)` is the image of `a` under `unitsToIdealUnits`. -/
lemma spanUnit_eq_unitsToIdealUnits (a : Kˣ) :
    spanUnit a = NK.CFTLib.ARL.unitsToIdealUnits K a := by
  refine Units.ext ?_
  rw [coe_spanUnit, NK.CFTLib.ARL.unitsToIdealUnits_coe]

/-- A principal idèle lies in the congruence subgroup exactly when its underlying unit satisfies
the congruence-and-positivity condition `CongrOne`. -/
lemma principalIdele_mem_congruenceSubgroup_iff (m : ℕ) (a : Kˣ) :
    Idele.principalIdele K a ∈ NK.CFTLib.Arl.congruenceSubgroup K m ↔ CongrOne m a := by
  constructor
  · intro h
    exact ⟨fun 𝔭 h𝔭 => by
        simpa [NK.CFTLib.Arl.CongrAt, Idele.principalIdele_apply, Units.coe_map] using h.1 𝔭 h𝔭,
      fun w hw => by
        simpa [NK.CFTLib.Arl.PosAtReal, Idele.principalIdele_apply, Units.coe_map]
          using h.2 w hw⟩
  · intro h
    exact ⟨fun 𝔭 h𝔭 => by
        simpa [NK.CFTLib.Arl.CongrAt, Idele.principalIdele_apply, Units.coe_map] using h.1 𝔭 h𝔭,
      fun w => by
        simpa [NK.CFTLib.Arl.PosAtReal, Idele.principalIdele_apply, Units.coe_map]
          using h.2 w⟩

/-- The principal ray `P(m)` of `LangDefs` agrees with the ray `principalRay` of the `ARL`
development. -/
lemma principalRay_eq_ARL (m : ℕ) :
    principalRay K m = NK.CFTLib.ARL.principalRay K m := by
  rw [principalRay, NK.CFTLib.ARL.principalRay]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro A ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, (principalIdele_mem_congruenceSubgroup_iff (K := K) m a).mpr ha,
      (spanUnit_eq_unitsToIdealUnits a).symm⟩
  · rintro A ⟨a, ha, rfl⟩
    exact Subgroup.subset_closure ⟨a, (principalIdele_mem_congruenceSubgroup_iff (K := K) m a).mp ha,
      (spanUnit_eq_unitsToIdealUnits a).symm⟩

/-- A prime occurs in the factorisation of a nonzero ideal `I` exactly when it divides `I`. -/
lemma count_ne_zero_iff_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K 𝔭 (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔ 𝔭.asIdeal ∣ I := by
  rw [FractionalIdeal.count_coe K 𝔭 (by simpa [Ideal.zero_eq_bot] using hI)]
  rw [show ((↑((Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors) : ℤ) ≠ 0) ↔
      (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors ≠ 0 by simp]
  exact Associates.count_ne_zero_iff_dvd (by simpa [Ideal.zero_eq_bot] using hI) 𝔭.irreducible

/-- Coprimality of an integral ideal to `(m)` is the same condition in both normalisations of the
norm group. -/
lemma fracCoprime_idealUnit_iff (m : ℕ) {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) :
    FracCoprime (K := L) m (idealUnit I hI) ↔
      ∀ 𝔭 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔭.asIdeal → ¬ 𝔭.asIdeal ∣ I := by
  constructor
  · intro h 𝔭 h𝔭 hdvd
    have h0 := h 𝔭 h𝔭
    rw [show FractionalIdeal.count L 𝔭 (idealUnit I hI : FractionalIdeal (𝓞 L)⁰ L)
          = FractionalIdeal.count L 𝔭 (I : FractionalIdeal (𝓞 L)⁰ L) from rfl] at h0
    exact (count_ne_zero_iff_dvd (K := L) hI 𝔭).mpr hdvd h0
  · intro h 𝔭 h𝔭
    rw [show FractionalIdeal.count L 𝔭 (idealUnit I hI : FractionalIdeal (𝓞 L)⁰ L)
          = FractionalIdeal.count L 𝔭 (I : FractionalIdeal (𝓞 L)⁰ L) from rfl]
    by_contra hc
    exact h 𝔭 h𝔭 ((count_ne_zero_iff_dvd (K := L) hI 𝔭).mp hc)

/-- The norm group `𝔑(m)` of `LangDefs` agrees with the norm group `normIdeals` of the `ARL`
development. -/
lemma normRay_eq_normIdeals (m : ℕ) :
    normRay K L m = NK.CFTLib.ARL.normIdeals K L m := by
  rw [normRay, NK.CFTLib.ARL.normIdeals]
  congr 1
  ext A
  constructor
  · rintro ⟨I, hI, hcop, rfl⟩
    exact ⟨⟨I, hI, (fracCoprime_idealUnit_iff (L := L) m hI).mp hcop⟩, rfl⟩
  · rintro ⟨⟨I, hI, hcop⟩, rfl⟩
    exact ⟨I, hI, (fracCoprime_idealUnit_iff (L := L) m hI).mpr hcop, rfl⟩

/-- The group `I(m)` of `LangDefs` agrees with the group `Icoprime` of the `ARL` development. -/
lemma idealCoprimeGroup_eq_Icoprime (m : ℕ) :
    idealCoprimeGroup K m = NK.CFTLib.ARL.Icoprime K m := by
  ext A
  rw [mem_idealCoprimeGroup_iff, NK.CFTLib.ARL.mem_Icoprime]
  exact Iff.rfl

/-! ## 2.  The map `θ : 𝕀 K →* M ⧸ P(m)·𝔑(m)` -/

/-- The subgroup `P(m)·𝔑(m)` of the group of fractional ideals of `K`. -/
noncomputable def rayNorm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (m : ℕ) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  NK.CFTLib.ARL.principalRay K m ⊔ NK.CFTLib.ARL.normIdeals K L m

/-- A chosen `b : Kˣ` with `x · (b) ≡ 1` modulo `m`. -/
noncomputable def adjId (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (x : Idele K) : Kˣ :=
  NK.CFTLib.Arl.adjust (NK.CFTLib.Arl.congruenceSubgroup K m)
    (NK.CFTLib.ARL.exists_adjust_congruenceSubgroup K m hm) x

lemma adjId_spec (m : ℕ) (hm : 0 < m) (x : Idele K) :
    x * Idele.principalIdele K (adjId K m hm x) ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
  NK.CFTLib.Arl.adjust_spec _ _ x

/-- An idèle of the congruence subgroup has an ideal coprime to `(m)`. -/
lemma mem_Icoprime_of_mem_congruence {m : ℕ} {z : Idele K}
    (hz : z ∈ NK.CFTLib.Arl.congruenceSubgroup K m) :
    IdeleClassGroup.idealOfUnitHom K z ∈ NK.CFTLib.ARL.Icoprime K m := by
  rw [NK.CFTLib.ARL.mem_Icoprime]
  intro 𝔭 h𝔭
  rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]
  exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hz 𝔭 h𝔭

/-- If `x · (b) ≡ 1 ≡ x · (c)` then the change of adjustment does not change the class of the
ideal modulo `P(m)·𝔑(m)`. -/
lemma mk'_rayNorm_mul_principalRay (m : ℕ) {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ NK.CFTLib.Arl.congruenceSubgroup K m)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    QuotientGroup.mk' (rayNorm K L m) (𝔞 * NK.CFTLib.ARL.unitsToIdealUnits K γ)
      = QuotientGroup.mk' (rayNorm K L m) 𝔞 := by
  have hmem : NK.CFTLib.ARL.unitsToIdealUnits K γ ∈ rayNorm K L m :=
    Subgroup.mem_sup_left (NK.CFTLib.ARL.unitsToIdealUnits_mem_principalRay (K := K) m hγ)
  have hmem' : QuotientGroup.mk' (rayNorm K L m) (NK.CFTLib.ARL.unitsToIdealUnits K γ) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (NK.CFTLib.ARL.unitsToIdealUnits K γ)).mpr hmem
  rw [map_mul, hmem', ← map_one (QuotientGroup.mk' (rayNorm K L m)), ← map_mul, mul_one]

/-- **The map `θ`**: the class, modulo `P(m)·𝔑(m)`, of the ideal of `x·(b)`, where `b ∈ Kˣ` is
chosen with `x·(b) ≡ 1` modulo `m`. -/
noncomputable def thetaFun (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (m : ℕ) (hm : 0 < m) (x : Idele K) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ rayNorm K L m :=
  QuotientGroup.mk' (rayNorm K L m)
    (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId K m hm x)))

/-- `θ` does not depend on the chosen adjustment. -/
lemma thetaFun_eq_mk (m : ℕ) (hm : 0 < m) {x : Idele K} {c : Kˣ}
    (hc : x * Idele.principalIdele K c ∈ NK.CFTLib.Arl.congruenceSubgroup K m) :
    thetaFun K L m hm x = QuotientGroup.mk' (rayNorm K L m)
      (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K c)) := by
  have hdiv : Idele.principalIdele K (adjId K m hm x / c) ∈
      NK.CFTLib.Arl.congruenceSubgroup K m :=
    NK.CFTLib.ARL.mem_inf_congruence_of_mul_eq (adjId_spec (K := K) m hm x) hc
      (γ := adjId K m hm x / c) (by rw [MonoidHom.map_div, mul_assoc, mul_div_cancel])
  have hkey : IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId K m hm x))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K c)
        * NK.CFTLib.ARL.unitsToIdealUnits K (adjId K m hm x / c) := by
    rw [map_mul, map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele,
      NK.CFTLib.ARL.idealOfUnitHom_principalIdele, MonoidHom.map_div, mul_assoc, mul_div_cancel]
  rw [thetaFun, hkey]
  exact mk'_rayNorm_mul_principalRay (K := K) (L := L) m hdiv
    (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K c))

lemma thetaFun_one (m : ℕ) (hm : 0 < m) : thetaFun K L m hm 1 = 1 := by
  rw [thetaFun_eq_mk (K := K) (L := L) m hm (x := (1 : Idele K)) (c := 1)
    (by rw [one_mul, map_one]; exact Subgroup.one_mem _)]
  rw [one_mul, map_one, map_one]
  exact map_one (QuotientGroup.mk' (rayNorm K L m))

/-- **`θ` kills the principal idèles.** -/
lemma thetaFun_principal_eq_one (m : ℕ) (hm : 0 < m) (α : Kˣ) :
    thetaFun K L m hm (Idele.principalIdele K α) = 1 := by
  have hmem : NK.CFTLib.ARL.unitsToIdealUnits K (α * adjId K m hm (Idele.principalIdele K α))
      ∈ rayNorm K L m :=
    Subgroup.mem_sup_left (NK.CFTLib.ARL.unitsToIdealUnits_mem_principalRay (K := K) m (by
      have h := adjId_spec (K := K) m hm (Idele.principalIdele K α)
      rwa [← map_mul] at h))
  have hval : IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K α *
      Idele.principalIdele K (adjId K m hm (Idele.principalIdele K α)))
      = NK.CFTLib.ARL.unitsToIdealUnits K (α * adjId K m hm (Idele.principalIdele K α)) := by
    rw [← map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele]
  rw [thetaFun, hval]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

/-- **`θ` kills the idèlic norms.** -/
lemma thetaFun_norm_eq_one (m : ℕ) (hm : 0 < m) (y : Idele L) :
    thetaFun K L m hm (Idele.normIdeleHom K L y) = 1 := by
  have hmem : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y *
      Idele.principalIdele K (adjId K m hm (Idele.normIdeleHom K L y))) ∈ rayNorm K L m := by
    rw [IdeleClassGroup.idealOfUnitHom_apply]
    exact NK.CFTLib.ARL.idealOf_mem_principalRay_sup_normIdeals (K := K) (L := L) hm
      (adjId_spec (K := K) m hm (Idele.normIdeleHom K L y)) rfl
  rw [thetaFun]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

/-- **`θ` is multiplicative.** -/
lemma thetaFun_mul (m : ℕ) (hm : 0 < m) (x y : Idele K) :
    thetaFun K L m hm (x * y) = thetaFun K L m hm x * thetaFun K L m hm y := by
  have hcd : (x * y) * Idele.principalIdele K (adjId K m hm x * adjId K m hm y)
      ∈ NK.CFTLib.Arl.congruenceSubgroup K m := by
    rw [map_mul]
    have h := mul_mem (adjId_spec (K := K) m hm x) (adjId_spec (K := K) m hm y)
    convert h using 1
    ac_rfl
  have harg : (x * y) * Idele.principalIdele K (adjId K m hm x * adjId K m hm y)
      = (x * Idele.principalIdele K (adjId K m hm x))
        * (y * Idele.principalIdele K (adjId K m hm y)) := by
    rw [map_mul]
    ac_rfl
  have hkey : IdeleClassGroup.idealOfUnitHom K ((x * y) *
        Idele.principalIdele K (adjId K m hm x * adjId K m hm y))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjId K m hm x))
        * IdeleClassGroup.idealOfUnitHom K (y * Idele.principalIdele K (adjId K m hm y)) := by
    rw [harg, map_mul]
  rw [thetaFun_eq_mk (K := K) (L := L) m hm (x := x * y)
      (c := adjId K m hm x * adjId K m hm y) hcd, thetaFun, thetaFun, ← map_mul, hkey]

/-- **The map `θ : 𝕀 K →* M ⧸ P(m)·𝔑(m)`.** -/
noncomputable def theta (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (m : ℕ) (hm : 0 < m) :
    Idele K →* ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ rayNorm K L m) where
  toFun := thetaFun K L m hm
  map_one' := thetaFun_one (K := K) (L := L) m hm
  map_mul' := thetaFun_mul (K := K) (L := L) m hm

lemma theta_apply (m : ℕ) (hm : 0 < m) (x : Idele K) :
    theta K L m hm x = thetaFun K L m hm x := rfl

lemma theta_principal_eq_one (m : ℕ) (hm : 0 < m) (α : Kˣ) :
    theta K L m hm (Idele.principalIdele K α) = 1 :=
  thetaFun_principal_eq_one (K := K) (L := L) m hm α

lemma theta_norm_eq_one (m : ℕ) (hm : 0 < m) (y : Idele L) :
    theta K L m hm (Idele.normIdeleHom K L y) = 1 :=
  thetaFun_norm_eq_one (K := K) (L := L) m hm y

/-- The image of `θ` is the image of the ideals coprime to `m`. -/
lemma theta_range (m : ℕ) (hm : 0 < m) :
    (theta K L m hm).range
      = (NK.CFTLib.ARL.Icoprime K m).map (QuotientGroup.mk' (rayNorm K L m)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨_, mem_Icoprime_of_mem_congruence (adjId_spec (K := K) m hm x), ?_⟩
    rw [theta_apply]
    rfl
  · rintro ⟨𝔞, h𝔞, rfl⟩
    obtain ⟨z, hz, hzide⟩ :=
      NK.CFTLib.ARL.exists_idealOf_eq_of_mem_Icoprime (K := K) hm ⟨𝔞, h𝔞⟩
    have hzadj : Idele.principalIdele K (adjId K m hm z) ∈
        NK.CFTLib.Arl.congruenceSubgroup K m :=
      NK.CFTLib.ARL.mem_inf_congruence_of_mul_eq (x := z * Idele.principalIdele K (adjId K m hm z))
        (y := z) (adjId_spec (K := K) m hm z) hz (γ := adjId K m hm z) rfl
    have hmk : QuotientGroup.mk' (rayNorm K L m) (NK.CFTLib.ARL.unitsToIdealUnits K (adjId K m hm z))
        = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_sup_left (NK.CFTLib.ARL.unitsToIdealUnits_mem_principalRay (K := K) m hzadj))
    refine ⟨z, ?_⟩
    rw [theta_apply, thetaFun_eq_mk (K := K) (L := L) m hm (x := z) (c := adjId K m hm z)
      (adjId_spec (K := K) m hm z)]
    rw [show IdeleClassGroup.idealOfUnitHom K (z * Idele.principalIdele K (adjId K m hm z))
        = IdeleClassGroup.idealOfUnitHom K z * NK.CFTLib.ARL.unitsToIdealUnits K (adjId K m hm z) by
      rw [map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele]]
    have hzide' : IdeleClassGroup.idealOfUnitHom K z = 𝔞 := hzide
    rw [hzide', map_mul, hmk, ← map_one (QuotientGroup.mk' (rayNorm K L m)), ← map_mul, mul_one]

/-! ## 3.  The index computation -/

/-- The index of `P(m)·𝔑(m)` in `I(m)` equals the index of the kernel of `θ`. -/
lemma index_rayNorm_eq_ker_index (m : ℕ) (hm : 0 < m) :
    ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index
      = (theta K L m hm).ker.index := by
  have hfker : ((QuotientGroup.mk' (rayNorm K L m)).comp (NK.CFTLib.ARL.Icoprime K m).subtype).ker
      = (rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m) := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 : ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index
      = Nat.card ((NK.CFTLib.ARL.Icoprime K m)
          ⧸ ((QuotientGroup.mk' (rayNorm K L m)).comp
              (NK.CFTLib.ARL.Icoprime K m).subtype).ker) := by
    rw [Subgroup.index_eq_card, hfker]
  have h2 : (theta K L m hm).ker.index = Nat.card (theta K L m hm).range := by
    rw [Subgroup.index_eq_card]
    have hker'' : (theta K L m hm).rangeRestrict.ker = (theta K L m hm).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker'']
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (theta K L m hm).rangeRestrict
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)).toEquiv
  have h3 : Nat.card ((NK.CFTLib.ARL.Icoprime K m)
        ⧸ ((QuotientGroup.mk' (rayNorm K L m)).comp (NK.CFTLib.ARL.Icoprime K m).subtype).ker)
      = Nat.card (theta K L m hm).range := by
    have hsurj : Function.Surjective (((QuotientGroup.mk' (rayNorm K L m)).comp
        (NK.CFTLib.ARL.Icoprime K m).subtype).rangeRestrict) :=
      fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
    have hrange : ((QuotientGroup.mk' (rayNorm K L m)).comp
        (NK.CFTLib.ARL.Icoprime K m).subtype).range = (theta K L m hm).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        ← theta_range (K := K) (L := L) m hm]
    have hker' : ((QuotientGroup.mk' (rayNorm K L m)).comp
        (NK.CFTLib.ARL.Icoprime K m).subtype).rangeRestrict.ker
        = ((QuotientGroup.mk' (rayNorm K L m)).comp (NK.CFTLib.ARL.Icoprime K m).subtype).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker', Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hrange]
  rw [h1, h3, h2]

/-- The kernel of `θ` contains the principal idèles and the idèlic norms. -/
lemma principalSubgroup_sup_normImage_le_ker (m : ℕ) (hm : 0 < m) :
    (Idele.principalSubgroup K ⊔ Idele.normImage K L) ≤ (theta K L m hm).ker := by
  rw [Idele.normImage_eq_range]
  refine sup_le ?_ ?_
  · rintro x ⟨α, rfl⟩
    exact theta_principal_eq_one (K := K) (L := L) m hm α
  · rintro x ⟨y, rfl⟩
    exact theta_norm_eq_one (K := K) (L := L) m hm y

/-- The index of `Kˣ · N_{L/K} 𝕀 L` is the index of the norm subgroup of the idèle class group. -/
lemma index_principalSubgroup_sup_normImage (m : ℕ) :
    (Idele.principalSubgroup K ⊔ Idele.normImage K L).index
      = (Idele.normClassSubgroup K L).index := by
  rw [Subgroup.index_eq_card]
  exact (NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
    (K := K) (L := L)).symm

theorem indexIdealCoprimeLeNormClassIndex (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) (hm : 0 < m) :
    Nat.card (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m ⧸
        (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m))
      ≤ (NK.GlobalCFT.Idele.normClassSubgroup K L).index := by
  haveI hVfin : (Idele.principalSubgroup K ⊔ Idele.normImage K L).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by
      rw [index_principalSubgroup_sup_normImage (K := K) (L := L) m]
      exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := L))
  have hgoal : Nat.card (NK.CFTLib.ARL.Icoprime K m ⧸
        (rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m))
      ≤ (Idele.normClassSubgroup K L).index := by
    rw [← Subgroup.index_eq_card ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m))]
    rw [index_rayNorm_eq_ker_index (K := K) (L := L) m hm]
    exact le_trans (Subgroup.index_antitone
      (principalSubgroup_sup_normImage_le_ker (K := K) (L := L) m hm))
      (le_of_eq (index_principalSubgroup_sup_normImage (K := K) (L := L) m))
  rw [idealCoprimeGroup_eq_Icoprime (K := K) m, principalRay_eq_ARL (K := K) m,
    normRay_eq_normIdeals (K := K) (L := L) m]
  exact hgoal

end NK.CFTLib.ArtinReciprocityIdeal
