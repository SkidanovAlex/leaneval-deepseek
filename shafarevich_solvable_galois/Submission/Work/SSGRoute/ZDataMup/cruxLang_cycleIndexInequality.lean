import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.Work.SSGRoute.ZDataMup.CycleIdele
import Submission.Work.SSGRoute.ZDataMup.CycleAux
import Submission.Work.SSGRoute.ZDataMup.LT_CyclePort
import Submission.Work.SSGRoute.ZDataMup.cycleMemIcoprime_iff
import Submission.Work.SSGRoute.ZDataMup.cycleIdealCoprimeGroupEq
import Submission.Work.SSGRoute.ZDataMup.cycleMemNormGroupOf_iff
import Submission.Work.SSGRoute.ZDataMup.cycleMemNormImageOfCongr
import Submission.Work.SSGRoute.ZDataMup.cycleIdealOfMemRaySupNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.CFTLib.ARL.RelNormFI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal
open NK.GlobalCFT

namespace Cycle

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- The subgroup `P(c)·𝔑(c,cL)` of the group of fractional ideals of `K`, in the
idèle-image presentation. -/
noncomputable def rayNorm (c : Cycle K) (cL : Cycle L) : Subgroup (Frac K) :=
  c.rayOf ⊔ c.normGroupOf K L cL

/-- A chosen adjustment of an idèle into the congruence subgroup of a cycle. -/
noncomputable def adjOf (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (x : Idele K) : Kˣ :=
  Classical.choose (Cycle.exists_adjust c hlev x)

theorem adjOf_spec (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (x : Idele K) :
    x * Idele.principalIdele K (adjOf c hlev x) ∈ c.congrSubgroup :=
  Classical.choose_spec (Cycle.exists_adjust c hlev x)

/-- The ratio of two congruent idèles (when one is a principal multiple of the other) is a
congruent principal idèle. -/
theorem mem_inf_congrSubgroup_of_mul_eq (c : Cycle K) {x y : Idele K}
    (hx : x ∈ c.congrSubgroup) (hy : y ∈ c.congrSubgroup) {γ : Kˣ}
    (h : x = y * Idele.principalIdele K γ) :
    Idele.principalIdele K γ ∈ c.congrSubgroup := by
  have h' : Idele.principalIdele K γ = y⁻¹ * x := by rw [h]; group
  rw [h']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx

/-- Multiplying a class modulo `P(c)·𝔑(c,cL)` by the ideal of a principal idèle lying in the
congruence subgroup of `c` does not change it. -/
theorem mk'_rayNorm_mul_rayOf (c : Cycle K) (cL : Cycle L) {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ c.congrSubgroup) (𝔞 : Frac K) :
    QuotientGroup.mk' (rayNorm c cL) (𝔞 * NK.CFTLib.ARL.unitsToIdealUnits K γ) =
      QuotientGroup.mk' (rayNorm c cL) 𝔞 := by
  have hmem : NK.CFTLib.ARL.unitsToIdealUnits K γ ∈ rayNorm c cL :=
    Subgroup.mem_sup_left (Cycle.unitsToIdealUnits_mem_rayOf (c := c) hγ)
  have hmem' : QuotientGroup.mk' (rayNorm c cL)
      (NK.CFTLib.ARL.unitsToIdealUnits K γ) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (NK.CFTLib.ARL.unitsToIdealUnits K γ)).mpr hmem
  rw [map_mul, hmem', ← map_one (QuotientGroup.mk' (rayNorm c cL)), ← map_mul, mul_one]

/-- The class, modulo `P(c)·𝔑(c,cL)`, of the ideal of `x·(b)`, where `b` adjusts `x` into the
congruence subgroup of `c`. -/
noncomputable def thetaFun (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (x : Idele K) : Frac K ⧸ rayNorm c cL :=
  QuotientGroup.mk' (rayNorm c cL)
    (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjOf c hlev x)))

/-- `thetaFun` does not depend on the chosen adjustment. -/
theorem thetaFun_eq_mk (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    {x : Idele K} {b : Kˣ} (hb : x * Idele.principalIdele K b ∈ c.congrSubgroup) :
    thetaFun c cL hlev x = QuotientGroup.mk' (rayNorm c cL)
      (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K b)) := by
  have hdiv : Idele.principalIdele K (adjOf c hlev x / b) ∈ c.congrSubgroup :=
    mem_inf_congrSubgroup_of_mul_eq c (adjOf_spec c hlev x) hb
      (γ := adjOf c hlev x / b) (by rw [MonoidHom.map_div, mul_assoc, mul_div_cancel])
  have hkey : IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjOf c hlev x))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K b)
        * NK.CFTLib.ARL.unitsToIdealUnits K (adjOf c hlev x / b) := by
    rw [map_mul, map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele,
      NK.CFTLib.ARL.idealOfUnitHom_principalIdele, MonoidHom.map_div, mul_assoc, mul_div_cancel]
  rw [thetaFun, hkey]
  exact mk'_rayNorm_mul_rayOf c cL hdiv
    (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K b))

theorem thetaFun_one (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    thetaFun c cL hlev 1 = 1 := by
  rw [thetaFun_eq_mk c cL hlev (x := (1 : Idele K)) (b := 1)
    (by rw [one_mul, map_one]; exact Subgroup.one_mem _)]
  rw [one_mul, map_one, map_one]
  exact map_one (QuotientGroup.mk' (rayNorm c cL))

/-- `thetaFun` kills the principal idèles. -/
theorem thetaFun_principal_eq_one (c : Cycle K) (cL : Cycle L)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (α : Kˣ) :
    thetaFun c cL hlev (Idele.principalIdele K α) = 1 := by
  have hmem : NK.CFTLib.ARL.unitsToIdealUnits K (α * adjOf c hlev (Idele.principalIdele K α))
      ∈ rayNorm c cL := by
    have h := adjOf_spec c hlev (Idele.principalIdele K α)
    rw [← map_mul] at h
    exact Subgroup.mem_sup_left (Cycle.unitsToIdealUnits_mem_rayOf (c := c) h)
  have hval : IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K α *
      Idele.principalIdele K (adjOf c hlev (Idele.principalIdele K α)))
      = NK.CFTLib.ARL.unitsToIdealUnits K (α * adjOf c hlev (Idele.principalIdele K α)) := by
    rw [← map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele]
  show QuotientGroup.mk' (rayNorm c cL)
    (IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K α *
      Idele.principalIdele K (adjOf c hlev (Idele.principalIdele K α)))) = 1
  rw [hval]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

/-- The ideal of `N_{L/K}(y)·(b)`, where `b` adjusts `N_{L/K}(y)`, lies in `P(c)·𝔑(c,cL)`. -/
theorem norm_mul_adjOf_mem (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (y : Idele L) :
    IdeleClassGroup.idealOfUnitHom K
        (Idele.normIdeleHom K L y * Idele.principalIdele K
          (adjOf c hlev (Idele.normIdeleHom K L y))) ∈ rayNorm c cL := by
  obtain ⟨m, hm, hMK⟩ := Cycle.exists_auxModulus (K := K) c hlev
  have hsuppK : ∀ 𝔭 ∈ c.supp, (m : 𝓞 K) ∈ 𝔭.asIdeal := fun 𝔭 h𝔭 => (hMK 𝔭 h𝔭).1
  have hcmpK : ∀ 𝔭 ∈ c.supp, c.lev 𝔭 ≤ cycleLevel (K := K) m 𝔭 := fun 𝔭 h𝔭 => (hMK 𝔭 h𝔭).2
  have h := cycleIdealOfMemRaySupNorm c cL hbc m hm hlev hsuppK hcmpK
    (adjOf_spec c hlev (Idele.normIdeleHom K L y)) rfl
  rwa [← IdeleClassGroup.idealOfUnitHom_apply] at h

/-- `thetaFun` kills the idèlic norms. -/
theorem thetaFun_norm_eq_one (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (y : Idele L) :
    thetaFun c cL hlev (Idele.normIdeleHom K L y) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (norm_mul_adjOf_mem c cL hbc hlev y)

/-- `thetaFun` is multiplicative. -/
theorem thetaFun_mul (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (x y : Idele K) :
    thetaFun c cL hlev (x * y) = thetaFun c cL hlev x * thetaFun c cL hlev y := by
  have hcd : (x * y) * Idele.principalIdele K (adjOf c hlev x * adjOf c hlev y)
      ∈ c.congrSubgroup := by
    rw [map_mul]
    have h := mul_mem (adjOf_spec c hlev x) (adjOf_spec c hlev y)
    convert h using 1
    ac_rfl
  have harg : (x * y) * Idele.principalIdele K (adjOf c hlev x * adjOf c hlev y)
      = (x * Idele.principalIdele K (adjOf c hlev x))
        * (y * Idele.principalIdele K (adjOf c hlev y)) := by
    rw [map_mul]; ac_rfl
  have hkey : IdeleClassGroup.idealOfUnitHom K ((x * y) *
        Idele.principalIdele K (adjOf c hlev x * adjOf c hlev y))
      = IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjOf c hlev x))
        * IdeleClassGroup.idealOfUnitHom K (y * Idele.principalIdele K (adjOf c hlev y)) := by
    rw [harg, map_mul]
  rw [thetaFun_eq_mk c cL hlev (x := x * y) (b := adjOf c hlev x * adjOf c hlev y) hcd,
    thetaFun, thetaFun, ← map_mul, hkey]

/-- **The map `θ : 𝕀 K →* Frac K ⧸ P(c)·𝔑(c,cL)`.** -/
noncomputable def theta (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    Idele K →* (Frac K ⧸ rayNorm c cL) where
  toFun := thetaFun c cL hlev
  map_one' := thetaFun_one c cL hlev
  map_mul' := thetaFun_mul c cL hlev

lemma theta_apply (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (x : Idele K) : theta c cL hlev x = thetaFun c cL hlev x := rfl

lemma theta_principal_eq_one (c : Cycle K) (cL : Cycle L)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (α : Kˣ) :
    theta c cL hlev (Idele.principalIdele K α) = 1 :=
  thetaFun_principal_eq_one c cL hlev α

lemma theta_norm_eq_one (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (y : Idele L) :
    theta c cL hlev (Idele.normIdeleHom K L y) = 1 :=
  thetaFun_norm_eq_one c cL hbc hlev y

/-- The image of `θ` is the image of the ideals coprime to `c`. -/
lemma theta_range (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    (theta c cL hlev).range
      = (c.Icoprime).map (QuotientGroup.mk' (rayNorm c cL)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨IdeleClassGroup.idealOfUnitHom K
      (x * Idele.principalIdele K (adjOf c hlev x)), ?_, ?_⟩
    · exact (cycleMemIcoprime_iff c _).mpr
        ⟨x * Idele.principalIdele K (adjOf c hlev x), adjOf_spec c hlev x, rfl⟩
    · show QuotientGroup.mk' (rayNorm c cL)
        (IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjOf c hlev x)))
        = thetaFun c cL hlev x
      rfl
  · rintro ⟨𝔄, h𝔄, rfl⟩
    obtain ⟨z, hz, hzide⟩ := (cycleMemIcoprime_iff c 𝔄).mp h𝔄
    have hzadj : Idele.principalIdele K (adjOf c hlev z) ∈ c.congrSubgroup :=
      mem_inf_congrSubgroup_of_mul_eq c (adjOf_spec c hlev z) hz
        (γ := adjOf c hlev z) rfl
    have hmk : QuotientGroup.mk' (rayNorm c cL) (NK.CFTLib.ARL.unitsToIdealUnits K (adjOf c hlev z))
        = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_sup_left (Cycle.unitsToIdealUnits_mem_rayOf (c := c) hzadj))
    refine ⟨z, ?_⟩
    show thetaFun c cL hlev z = QuotientGroup.mk' (rayNorm c cL) 𝔄
    show QuotientGroup.mk' (rayNorm c cL)
        (IdeleClassGroup.idealOfUnitHom K (z * Idele.principalIdele K (adjOf c hlev z)))
      = QuotientGroup.mk' (rayNorm c cL) 𝔄
    rw [show IdeleClassGroup.idealOfUnitHom K (z * Idele.principalIdele K (adjOf c hlev z))
        = IdeleClassGroup.idealOfUnitHom K z * NK.CFTLib.ARL.unitsToIdealUnits K (adjOf c hlev z) by
      rw [map_mul, NK.CFTLib.ARL.idealOfUnitHom_principalIdele]]
    rw [hzide, map_mul, hmk, ← map_one (QuotientGroup.mk' (rayNorm c cL)), ← map_mul, mul_one]

/-- The index of `P(c)·𝔑(c,cL)` in `I(c)` equals the index of the kernel of `θ`. -/
lemma index_rayNorm_eq_ker_index (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ((rayNorm c cL).subgroupOf c.Icoprime).index = (theta c cL hlev).ker.index := by
  have hfker : ((QuotientGroup.mk' (rayNorm c cL)).comp c.Icoprime.subtype).ker
      = (rayNorm c cL).subgroupOf c.Icoprime := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 : ((rayNorm c cL).subgroupOf c.Icoprime).index
      = Nat.card (c.Icoprime ⧸ ((QuotientGroup.mk' (rayNorm c cL)).comp c.Icoprime.subtype).ker) := by
    rw [Subgroup.index_eq_card, hfker]
  have h2 : (theta c cL hlev).ker.index = Nat.card (theta c cL hlev).range := by
    rw [Subgroup.index_eq_card]
    have hker'' : (theta c cL hlev).rangeRestrict.ker = (theta c cL hlev).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker'']
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (theta c cL hlev).rangeRestrict
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)).toEquiv
  have h3 : Nat.card (c.Icoprime ⧸ ((QuotientGroup.mk' (rayNorm c cL)).comp c.Icoprime.subtype).ker)
      = Nat.card (theta c cL hlev).range := by
    have hsurj : Function.Surjective (((QuotientGroup.mk' (rayNorm c cL)).comp
        c.Icoprime.subtype).rangeRestrict) :=
      fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
    have hrange : ((QuotientGroup.mk' (rayNorm c cL)).comp c.Icoprime.subtype).range
        = (theta c cL hlev).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, ← theta_range c cL hbc hlev]
    have hker' : ((QuotientGroup.mk' (rayNorm c cL)).comp
        c.Icoprime.subtype).rangeRestrict.ker
        = ((QuotientGroup.mk' (rayNorm c cL)).comp c.Icoprime.subtype).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker', Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hrange]
  rw [h1, h3, h2]

/-- The kernel of `θ` contains the principal idèles and the idèlic norms. -/
lemma principalSubgroup_sup_normImage_le_ker (c : Cycle K) (cL : Cycle L)
    (hbc : c.IsBaseChange K L cL) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    (Idele.principalSubgroup K ⊔ Idele.normImage K L) ≤ (theta c cL hlev).ker := by
  rw [Idele.normImage_eq_range]
  refine sup_le ?_ ?_
  · rintro x ⟨α, rfl⟩
    exact theta_principal_eq_one c cL hlev α
  · rintro x ⟨y, rfl⟩
    exact theta_norm_eq_one c cL hbc hlev y

/-- **The kernel of `θ` is contained in `Kˣ·N_{L/K}𝕀 L`** (the idèle–ideal dictionary). -/
theorem theta_ker_le (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (hpos : ∀ 𝔭 ∈ c.supp, 0 < c.lev 𝔭)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (hadm : Cycle.IsAdmissible K L c) :
    (theta c cL hlev).ker ≤ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
  classical
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  set xb : Idele K := x * Idele.principalIdele K (adjOf c hlev x) with hxbdef
  have hxb : xb ∈ c.congrSubgroup := adjOf_spec c hlev x
  have hmem : IdeleClassGroup.idealOfUnitHom K xb ∈ rayNorm c cL := by
    have h := hx
    change QuotientGroup.mk' (rayNorm c cL) (IdeleClassGroup.idealOfUnitHom K xb) = 1 at h
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨𝔡, h𝔡, 𝔫, h𝔫, hprod⟩ :=
    Subgroup.mem_sup.mp (show IdeleClassGroup.idealOfUnitHom K xb
      ∈ c.rayOf ⊔ c.normGroupOf K L cL from hmem)
  obtain ⟨a, haU, haEq⟩ := Subgroup.mem_map.mp h𝔡
  have haU' : Idele.principalIdele K a ∈ c.congrSubgroup := Subgroup.mem_comap.mp haU
  obtain ⟨A, hA, hAeq⟩ := (cycleMemNormGroupOf_iff c cL 𝔫).mp h𝔫
  obtain ⟨y, hyA⟩ := IdeleClassGroup.idealOfUnitHom_surjective L A
  have hyid : Idele.idealOf y = (A : FractionalIdeal (𝓞 L)⁰ L) := by
    have h := congrArg (fun u : Frac L => (u : FractionalIdeal (𝓞 L)⁰ L)) hyA
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0] at h
    exact h
  have hNy : Idele.idealOf (Idele.normIdeleHom K L y) = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [NK.CFTLib.ARL.idealOf_normIdeleHom, hyid]
    rw [show NK.CFTLib.ARL.relNormFI (K := K) (L := L) (A : FractionalIdeal (𝓞 L)⁰ L)
        = ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A : Frac K) :
            FractionalIdeal (𝓞 K)⁰ K) from rfl, hAeq]
  have hNyU : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y) = 𝔫 := by
    refine Units.ext ?_
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, hNy]
  have hxbU : IdeleClassGroup.idealOfUnitHom K xb = 𝔡 * 𝔫 := hprod.symm
  set z : Idele K := xb * (Idele.principalIdele K a)⁻¹ * (Idele.normIdeleHom K L y)⁻¹ with hzdef
  have hzU : IdeleClassGroup.idealOfUnitHom K z = 1 := by
    rw [hzdef, map_mul, map_mul, map_inv, map_inv,
      NK.CFTLib.ARL.idealOfUnitHom_principalIdele, haEq, hxbU, hNyU]
    rw [mul_assoc 𝔡 𝔫 𝔡⁻¹, mul_comm 𝔫 𝔡⁻¹, ← mul_assoc 𝔡 𝔡⁻¹ 𝔫, mul_inv_cancel, one_mul,
      mul_inv_cancel]
  have hz : z.idealOf = 1 := by
    have h := congrArg (fun u : Frac K => (u : FractionalIdeal (𝓞 K)⁰ K)) hzU
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, Units.val_one] at h
    exact h
  have hzw : z * Idele.normIdeleHom K L y = xb * (Idele.principalIdele K a)⁻¹ := by
    rw [hzdef]; group
  have hcong : ∀ 𝔭 ∈ c.supp,
      c.CongrAt 𝔭 (z (Place.ofFinite 𝔭)
        * (Idele.normIdeleHom K L y) (Place.ofFinite 𝔭)) := by
    intro 𝔭 h𝔭
    have hmem' := Subgroup.mul_mem _ hxb (Subgroup.inv_mem _ haU')
    have h1 := hmem'.1 𝔭 h𝔭
    show c.CongrAt 𝔭 ((z * Idele.normIdeleHom K L y) (Place.ofFinite 𝔭))
    rw [hzw]
    exact h1
  have hposarch : ∀ w : InfinitePlace K,
      NK.CFTLib.Arl.PosAtReal w (z (Place.ofInfinite w)
        * (Idele.normIdeleHom K L y) (Place.ofInfinite w)) := by
    intro w
    have hmem' := Subgroup.mul_mem _ hxb (Subgroup.inv_mem _ haU')
    have h1 := hmem'.2 w
    show NK.CFTLib.Arl.PosAtReal w ((z * Idele.normIdeleHom K L y) (Place.ofInfinite w))
    rw [hzw]
    exact h1
  have hznorm : z ∈ Idele.normImage K L :=
    cycleMemNormImageOfCongr c hpos hram hadm z y hz hcong hposarch
  have hxb_decomp : xb = z * Idele.normIdeleHom K L y * Idele.principalIdele K a := by
    rw [hzdef]; group
  have hxb_mem : xb ∈ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
    rw [hxb_decomp]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hznorm) ?_)
      (Subgroup.mem_sup_left ?_)
    · rw [Idele.normImage_eq_range]
      exact Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    · exact Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩
  have hx_eq : x = xb * (Idele.principalIdele K (adjOf c hlev x))⁻¹ := by
    rw [hxbdef]; group
  rw [hx_eq]
  exact Subgroup.mul_mem _ hxb_mem
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩)))

end Cycle

theorem cruxLang_cycleIndexInequality
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (Gal(L/K))]
    (c : Work.SSGRoute.ZDataMup.Cycle K) (cL : Work.SSGRoute.ZDataMup.Cycle L)
    (hbc : Work.SSGRoute.ZDataMup.Cycle.IsBaseChange K L c cL)
    (hpos : ∀ 𝔭 ∈ c.supp, 0 < c.lev 𝔭)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (hadm : Work.SSGRoute.ZDataMup.Cycle.IsAdmissible K L c) :
    Module.finrank K L
      ≤ (Work.SSGRoute.ZDataMup.Cycle.principalRay c ⊔
          Work.SSGRoute.ZDataMup.Cycle.normRay K L c cL).relIndex
        (Work.SSGRoute.ZDataMup.Cycle.idealCoprimeGroup c) := by
  have hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭 := fun 𝔭 h𝔭 => hpos 𝔭 h𝔭
  have hker_le : (Cycle.theta c cL hlev).ker ≤ Idele.principalSubgroup K ⊔ Idele.normImage K L :=
    Cycle.theta_ker_le c cL hbc hlev hpos hram hadm
  have hker_ge : Idele.principalSubgroup K ⊔ Idele.normImage K L ≤ (Cycle.theta c cL hlev).ker :=
    Cycle.principalSubgroup_sup_normImage_le_ker c cL hbc hlev
  have hker_eq : (Cycle.theta c cL hlev).ker = Idele.principalSubgroup K ⊔ Idele.normImage K L :=
    le_antisymm hker_le hker_ge
  have hfin : Module.finrank K L
      = (c.principalRay ⊔ Cycle.normRay K L c cL).relIndex c.idealCoprimeGroup := by
    calc Module.finrank K L
        = (Idele.normClassSubgroup K L).index :=
          (NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L)).symm
      _ = (Idele.principalSubgroup K ⊔ Idele.normImage K L).index :=
          (NK.CFTLib.ArtinReciprocityIdeal.index_principalSubgroup_sup_normImage
            (K := K) (L := L) 1).symm
      _ = (Cycle.theta c cL hlev).ker.index := by rw [hker_eq]
      _ = ((Cycle.rayNorm c cL).subgroupOf c.Icoprime).index :=
          (Cycle.index_rayNorm_eq_ker_index c cL hbc hlev).symm
      _ = (c.principalRay ⊔ Cycle.normRay K L c cL).relIndex c.idealCoprimeGroup := by
          rw [Cycle.principalRay_eq_rayOf (c := c) hlev, Cycle.normRay_eq_normGroupOf c cL,
            cycleIdealCoprimeGroupEq c]
          rfl
  exact le_of_eq hfin

end Work.SSGRoute.ZDataMup
