import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.NodeS37.divisorOfClassRepresentative
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_twist_idele_emptyPos
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.smul_ideleOfIdeal_cong
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.smul_mem_congSubgroup_emptyPos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime in a prescribed ideal class which is not fixed by an involution

`Work.SSGRoute.ZDataTwo.TwoRec.exists_prime_in_class_not_fixed`: for a finite Galois extension
`k ⊆ K` of number fields, an involution `ρ ∈ Gal(K/k)`, a non-zero fractional ideal `A` of `K` and a
prime `𝔮` with `ρ𝔮 ≠ 𝔮`, there are a prime `Q'` of `𝓞 K` and `y ∈ Kˣ` with `(Q') = A·(y)`,
`Q' ≠ ρQ'` and `Q' ≠ ρ𝔮`.

This is the arithmetic input of the representative normalisation of Schmidt--Wingberg's p. 16
computation (their sentence *"By Čebotarev's density theorem there exists a prime ideal `Q` with
`Q ≠ Q^σ` such that `Q = A·(x)` with `x ∈ Kˣ`* in the proof of their Claim).

## Route

The proof uses the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` of a `ρ`-invariant modulus `𝔪` with
`pos = ∅` whose support contains the place `ρ𝔮`:

* `exists_twist_idele_emptyPos` provides an idèle `x` of ideal class `[A]` whose `ρ`-twist
  `ρ • x * x⁻¹` lies outside `Kˣ · U(𝔪)`;
* ray-class Čebotarev (`exists_prime_mem_rayClass`) produces a prime `Q'` with `𝔪.exps Q' = 0` whose
  ray class is the class of `x`; in particular `Q' ≠ ρ𝔮` and `(Q') = A·(y)` for some `y`;
* the `ρ`-stability of the congruence subgroup (`smul_mem_congSubgroup_emptyPos`) together with the
  fact that `ρ • (idèle of Q')` and the idèle of `ρQ'` differ by a congruence idèle supported at
  `ρQ' ∉ supp 𝔪` (`smul_ideleOfIdeal_cong`) shows that a `ρ`-fixed `Q'` would force the ray class
  of `x` to be `ρ`-fixed — contradicting the twist.  Hence `Q' ≠ ρQ'`.
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- The congruence idèles of a modulus are integral idèles. -/
lemma congSubgroup_le_integralIdeles (𝔪 : NK.NUV2.RouteB.Modulus K) :
    NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤ NK.GlobalCFT.Idele.integralIdeles K := by
  intro x hx
  rw [NK.GlobalCFT.Idele.mem_integralIdeles]
  intro v hv
  rw [NK.GlobalCFT.Place.isFinite_iff] at hv
  obtain ⟨q, rfl⟩ := hv
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact (hx.1 q).1

/-- The fractional ideal attached to the idèle of an ideal is that ideal. -/
lemma idealOf_ideleOfIdeal_eq (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    NK.GlobalCFT.Idele.idealOf (NK.HeckeL.ideleOfIdeal K I)
      = (I : FractionalIdeal (𝓞 K)⁰ K) := by
  refine NK.GlobalCFT.IdeleClassGroup.fractionalIdeal_eq_of_count_eq
    (NK.GlobalCFT.Idele.idealOf_ne_zero _) (FractionalIdeal.coeIdeal_ne_zero.mpr hI) fun q => ?_
  rw [NK.GlobalCFT.Idele.count_idealOf, NK.HeckeL.ideleOfIdeal,
    NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]

/-- **The class of the idèle of an ideal is the class of the ideal.** -/
lemma idealClassHom_mk_ideleOfIdeal (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    NK.GlobalCFT.IdeleClassGroup.idealClassHom K
        (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))
      = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ := by
  have h1 : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
        (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))
      = NK.GlobalCFT.IdeleClassGroup.idealClassMap K (NK.HeckeL.ideleOfIdeal K I) := rfl
  rw [h1, NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply]
  rw [show Units.mk0 (NK.GlobalCFT.Idele.idealOf (NK.HeckeL.ideleOfIdeal K I))
        (NK.GlobalCFT.Idele.idealOf_ne_zero _)
      = Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI) from
    Units.ext (by rw [Units.val_mk0, Units.val_mk0]; exact idealOf_ideleOfIdeal_eq I hI)]
  exact ClassGroup.mk_mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

/-- **Equal ideal classes give a principal quotient.**  If the ideal class of `A` and that of the
prime ideal `Q` agree, then `(Q) = A·(y)` for some `y ∈ Kˣ`. -/
lemma exists_unit_mul_of_class_eq {A : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0)
    (Q : Ideal (𝓞 K)) (hQ : Q ≠ 0)
    (h : ClassGroup.mk0 ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ⟩
      = ClassGroup.mk K (Units.mk0 A hA)) :
    ∃ y : Kˣ, (Q : FractionalIdeal (𝓞 K)⁰ K)
      = A * FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) := by
  classical
  set X : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 A hA * (Units.mk0 (Q : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hQ))⁻¹ with hX
  have hXval : (X : FractionalIdeal (𝓞 K)⁰ K)
      = A * (Q : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [hX, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  have hXclass : ClassGroup.mk K X = 1 := by
    rw [hX, map_mul, map_inv]
    have hQmk : ClassGroup.mk K (Units.mk0 (Q : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hQ))
        = ClassGroup.mk0 ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ⟩ :=
      ClassGroup.mk_mk0 K ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ⟩
    rw [hQmk, h, mul_inv_cancel]
  have hprinc : ((X : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal :=
    (ClassGroup.mk_eq_one_iff (I := X)).mp hXclass
  obtain ⟨a, ha⟩ := hprinc.principal
  have hXa : (X : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    apply Subtype.coe_injective
    simpa only [FractionalIdeal.val_eq_coe, FractionalIdeal.coe_spanSingleton, Units.val_mk0]
      using ha
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 : (X : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [hXa, h0, FractionalIdeal.spanSingleton_zero]
    exact Units.ne_zero X h1
  have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ a * (Q : FractionalIdeal (𝓞 K)⁰ K) = A := by
    rw [← hXa, hXval, mul_assoc,
      inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hQ), mul_one]
  have hQeq : (Q : FractionalIdeal (𝓞 K)⁰ K)
      = (FractionalIdeal.spanSingleton (𝓞 K)⁰ a)⁻¹ * A := by
    rw [← h1, inv_mul_cancel_left₀ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha0)]
  refine ⟨Units.mk0 a⁻¹ (inv_ne_zero ha0), ?_⟩
  rw [hQeq, mul_comm, Units.val_mk0, FractionalIdeal.spanSingleton_inv]

/-- Auxiliary computation in a commutative group: `a * b = d * (c * e)` gives
`a * c⁻¹ = d * e * b⁻¹`. -/
lemma mul_eq_mul_div_aux {G : Type*} [CommGroup G] {a b c d e : G}
    (h : a * b = d * (c * e)) : a * c⁻¹ = d * e * b⁻¹ := by
  have h1 : a * c⁻¹ * (c * b) = a * b := by rw [mul_assoc, inv_mul_cancel_left]
  have h2 : d * e * b⁻¹ * (c * b) = d * (c * e) := by
    rw [mul_assoc, ← mul_assoc (b⁻¹) c b, mul_comm (b⁻¹) c, mul_assoc, mul_assoc, inv_mul_cancel,
      mul_one, ← mul_assoc, mul_right_comm d e c, mul_assoc]
  exact mul_right_cancel (h1.trans (h.trans h2.symm))

theorem exists_prime_in_class_not_fixed {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ),
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
      Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
      ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (y : K)) := by
  classical
  -- ## 1. the twist: a modulus and an idèle whose class is `[A]` and whose twist escapes `U(𝔪)`
  obtain ⟨𝔪, x, hpos, hexp, hqne, hclass, htwist⟩ :=
    exists_twist_idele_emptyPos (k := k) (K := K) ρ hρ2 A hA 𝔮 hne
  -- ## 2. the congruence subgroup
  set U : Subgroup (NK.GlobalCFT.Idele K) := NK.NUV2.RouteB.CongSubgroup K 𝔪 with hU
  -- ## 3. Čebotarev: a prime with `𝔪.exps Q' = 0` whose ray class is that of `x`
  obtain ⟨Q', hQ'm, hQ'c⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass (K := K) 𝔪
      (NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk K U (NK.GlobalCFT.IdeleClassGroup.mk K x))
  have hQ'c' : NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk K U
        (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal))
      = NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk K U (NK.GlobalCFT.IdeleClassGroup.mk K x) :=
    hQ'c
  -- ## 4. the idèles of `Q'` and of `x·u₀` have the same class
  have hker : (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal))
      * (NK.GlobalCFT.IdeleClassGroup.mk K x)⁻¹
      ∈ Subgroup.map (NK.GlobalCFT.IdeleClassGroup.mk K) U := by
    rw [← NK.GlobalCFT.IdeleClassGroup.ker_rayClassGroupMk]
    rw [MonoidHom.mem_ker, map_mul, map_inv, hQ'c', mul_inv_cancel]
  obtain ⟨u₀, hu₀U, hu₀⟩ := Subgroup.mem_map.mp hker
  have hCeq : NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
      = NK.GlobalCFT.IdeleClassGroup.mk K (x * u₀) := by
    rw [map_mul, hu₀, ← mul_assoc,
      mul_right_comm (NK.GlobalCFT.IdeleClassGroup.mk K x)
        (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal))
        (NK.GlobalCFT.IdeleClassGroup.mk K x)⁻¹,
      mul_inv_cancel, one_mul]
  -- ## 5. the ideal class of the prime is the class of `A`
  have hprim : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
      (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal))
      = ClassGroup.mk0 ⟨Q'.asIdeal, mem_nonZeroDivisors_of_ne_zero Q'.ne_bot⟩ :=
    idealClassHom_mk_ideleOfIdeal Q'.asIdeal Q'.ne_bot
  have hu₀ker : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
      (NK.GlobalCFT.IdeleClassGroup.mk K u₀) = 1 := by
    rw [← MonoidHom.mem_ker, NK.GlobalCFT.IdeleClassGroup.ker_idealClassHom]
    exact Subgroup.mem_map.mpr ⟨u₀, congSubgroup_le_integralIdeles 𝔪 hu₀U, rfl⟩
  have hclassQ : ClassGroup.mk0 ⟨Q'.asIdeal, mem_nonZeroDivisors_of_ne_zero Q'.ne_bot⟩
      = ClassGroup.mk K (Units.mk0 A hA) := by
    have h2 : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
        (NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal))
        = NK.GlobalCFT.IdeleClassGroup.idealClassHom K
          (NK.GlobalCFT.IdeleClassGroup.mk K x) := by
      rw [hCeq]
      simp only [map_mul, hu₀ker, mul_one]
    rw [← hprim, h2, hclass]
  -- ## 6. the avoidance of `ρ𝔮`
  have havoid : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by
    intro h
    rw [h] at hQ'm
    exact hqne hQ'm
  -- ## 7. non-fixedness
  have hfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' := by
    intro hfix'
    -- the discrepancy is a congruence idèle at `ρQ' = Q'`
    have hdisc : (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
        * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ ∈ U := by
      have h := smul_ideleOfIdeal_cong ρ hρ2 𝔪 Q' hQ'm (by rw [hfix']; exact hQ'm)
      rwa [hfix'] at h
    -- `ρ`-stability of the congruence subgroup
    have hst : ∀ y ∈ U, ρ • y ∈ U := fun y hy =>
      smul_mem_congSubgroup_emptyPos ρ hρ2 𝔪 hpos hexp y hy
    -- the class identity `mk P = mk x * mk u₀`
    have hP : NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
        = NK.GlobalCFT.IdeleClassGroup.mk K x
          * NK.GlobalCFT.IdeleClassGroup.mk K u₀ := by
      rw [hCeq, map_mul]
    -- the discrepancy identity `ρ • P = d * P`
    have hdP : ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal
        = ((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
            * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹) * NK.HeckeL.ideleOfIdeal K Q'.asIdeal := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    -- the two class identities, and their combination
    have e2 : NK.GlobalCFT.IdeleClassGroup.mk K (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
        = NK.GlobalCFT.IdeleClassGroup.mk K (ρ • x)
          * NK.GlobalCFT.IdeleClassGroup.mk K (ρ • u₀) := by
      rw [← NK.GlobalCFT.IdeleClassGroup.smul_mk, hP, MulDistribMulAction.smul_mul,
        NK.GlobalCFT.IdeleClassGroup.smul_mk, NK.GlobalCFT.IdeleClassGroup.smul_mk]
    have e3 : NK.GlobalCFT.IdeleClassGroup.mk K
          (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
            * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹))
          * (NK.GlobalCFT.IdeleClassGroup.mk K x
            * NK.GlobalCFT.IdeleClassGroup.mk K u₀)
        = NK.GlobalCFT.IdeleClassGroup.mk K (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) := by
      rw [← hP, ← map_mul, ← hdP]
    have hAE : NK.GlobalCFT.IdeleClassGroup.mk K (ρ • x)
          * NK.GlobalCFT.IdeleClassGroup.mk K (ρ • u₀)
        = NK.GlobalCFT.IdeleClassGroup.mk K (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
            * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹))
          * (NK.GlobalCFT.IdeleClassGroup.mk K x
            * NK.GlobalCFT.IdeleClassGroup.mk K u₀) := e2.symm.trans e3.symm
    -- the key identity in the class group
    have key : NK.GlobalCFT.IdeleClassGroup.mk K ((ρ • x) * x⁻¹)
        = NK.GlobalCFT.IdeleClassGroup.mk K
          (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
            * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹) * u₀ * (ρ • u₀)⁻¹) := by
      simp only [map_mul, map_inv]
      exact mul_eq_mul_div_aux hAE
    -- hence the twist of `x` lies in `Kˣ · U(𝔪)`
    have hcU : (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
        * (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹) * u₀ * (ρ • u₀)⁻¹) ∈ U :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hdisc hu₀U)
        (Subgroup.inv_mem _ (hst u₀ hu₀U))
    have hmemU : NK.GlobalCFT.IdeleClassGroup.mk K ((ρ • x) * x⁻¹)
        ∈ U.map (NK.GlobalCFT.IdeleClassGroup.mk K) := by
      rw [key]
      exact Subgroup.mem_map.mpr
        ⟨_, hcU, rfl⟩
    have hmem : (ρ • x) * x⁻¹ ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔ U := by
      obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hmemU
      have hku : u⁻¹ * ((ρ • x) * x⁻¹) ∈ NK.GlobalCFT.Idele.principalSubgroup K :=
        NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff.mp hu
      rw [← mul_inv_cancel_left u ((ρ • x) * x⁻¹)]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huU) (Subgroup.mem_sup_left hku)
    exact htwist hmem
  -- ## 8. the principal generator
  obtain ⟨y, hy⟩ := exists_unit_mul_of_class_eq hA Q'.asIdeal Q'.ne_bot hclassQ
  exact ⟨Q', y, hfix, havoid, hy⟩

end Work.SSGRoute.ZDataTwo.TwoRec
