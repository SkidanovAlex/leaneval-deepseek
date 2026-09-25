import Mathlib
import Submission.NK.CFTLib.roquetteDefs
import Submission.NK.CFTLib.roquette_plan
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one
import Submission.NK.CFTLib.exp_normIdeleHom_eq_sum
import Submission.NK.CFTLib.exists_coprime_pow_powerOrder
import Submission.NK.CFTLib.exists_finsupp_of_mem_closure_image

open scoped nonZeroDivisors

set_option autoImplicit false
set_option linter.unusedVariables false
open NumberField IsDedekindDomain NK.GlobalCFT

namespace NK.CFTLib

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-! ### Elementary lemmas -/

/-- The pointwise unramified condition, from `IsUnramified`. -/
lemma ramificationIdx_eq_one_of_isUnramified (hunr : _root_.CFTLib.IsUnramified F K)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (_hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 := by
  rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
    (E := F) (K := K) q.asIdeal q.isPrime, hunr.1]
  intro h
  exact q.isPrime.ne_top (eq_top_iff.mpr (Ideal.dvd_iff_le.mp h))

variable {L : Type} [Field L] [NumberField L]

lemma exp_unit_pow (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (z : Idele L) (n : ℕ) : Idele.exp q (z ^ n) = n * Idele.exp q z := by
  rw [Idele.exp_def, Idele.exp_def]
  have h : ((z ^ n) (Place.ofFinite q) : q.adicCompletion L)
      = ((z (Place.ofFinite q) : q.adicCompletion L)) ^ n := rfl
  rw [h, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

lemma expUnit_eq_exp_principalIdele (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (a : Lˣ) :
    NK.GlobalCFTdeep.expUnit q a = Idele.exp q (Idele.principalIdele L a) := by
  rw [NK.GlobalCFTdeep.expUnit, Idele.exp_principalIdele]

lemma expUnit_pow (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (a : Lˣ) (n : ℕ) :
    NK.GlobalCFTdeep.expUnit q (a ^ n) = n * NK.GlobalCFTdeep.expUnit q a := by
  rw [expUnit_eq_exp_principalIdele, expUnit_eq_exp_principalIdele,
    show Idele.principalIdele L (a ^ n) = (Idele.principalIdele L a) ^ n from map_pow _ a n,
    exp_unit_pow]

/-! ### The primes above `T` -/

/-- The primes of `K` above the primes in `T`. -/
noncomputable def primesOverT (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  exact T.biUnion fun v => Place.primesOverFinite (K := F) (L := K) v

lemma mem_primesOverT {T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))}
    {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} :
    w ∈ primesOverT (F := F) (K := K) T ↔ ∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal := by
  classical
  rw [primesOverT, Finset.mem_biUnion]
  exact ⟨fun ⟨v, hv, hw⟩ => ⟨v, hv, (Place.mem_primesOverFinite (K := F) (L := K)).mp hw⟩,
    fun ⟨v, hv, hw⟩ => ⟨v, hv, (Place.mem_primesOverFinite (K := F) (L := K)).mpr hw⟩⟩

/-- If `q` is a prime of `F` outside `T`, then the sum over the primes of `K` above `q` with
coefficients supported on the primes above `T` vanishes. -/
lemma sum_primesOverFinite_mul_eq_zero
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →₀ ℤ)
    (hsupp : e.support ⊆ ↑(primesOverT (F := F) (K := K) T))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hq : Place.ofFinite q ∉ ({w : Place F | ∃ q' ∈ T, w = Place.ofFinite q'} : Set (Place F))) :
    ∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
      (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * e w = 0 := by
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwK : w.asIdeal.LiesOver q.asIdeal := (Place.mem_primesOverFinite (K := F) (L := K)).mp hw
  suffices h : e w = 0 by rw [h, mul_zero]
  by_contra hne
  have hwS : w ∈ primesOverT (F := F) (K := K) T := hsupp (Finsupp.mem_support_iff.mpr hne)
  obtain ⟨v, hvT, hwv⟩ := (mem_primesOverT (F := F) (K := K)).mp hwS
  have h1 : q.asIdeal = Ideal.under (NumberField.RingOfIntegers F) w.asIdeal := by
    haveI := hwK; exact Ideal.LiesOver.over
  have h2 : v.asIdeal = Ideal.under (NumberField.RingOfIntegers F) w.asIdeal := by
    haveI := hwv; exact Ideal.LiesOver.over
  have hqv : q = v := IsDedekindDomain.HeightOneSpectrum.ext (by rw [h1, h2])
  exact hq ⟨v, hvT, by rw [hqv]⟩

/-! ### From a class-group membership to an equation of fractional ideals -/

section ClassToIdeal

variable [FiniteDimensional F K]

/-- The class of a non-zero prime of `𝓞 K`, exactly as it appears in `CFTLib.ClassCond`. -/
noncomputable def primeIdealClass (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ClassGroup (NumberField.RingOfIntegers K) :=
  ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩

lemma primeIdealClass_eq_mk (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    primeIdealClass w
      = ClassGroup.mk K (Units.mk0 (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)) := by
  rw [primeIdealClass, ← ClassGroup.mk_mk0 K]
  refine congrArg (ClassGroup.mk K) (Units.ext ?_)
  rw [FractionalIdeal.coe_mk0, Units.val_mk0]

lemma classCond_set_subset
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    {d : ClassGroup (NumberField.RingOfIntegers K) |
        ∃ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal) ∧
            d = ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩}
      ⊆ primeIdealClass '' ((primesOverT (F := F) (K := K) T :
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Set _) := by
  rintro d ⟨w, ⟨v, hvT, hwv⟩, rfl⟩
  exact ⟨w, (mem_primesOverT (F := F) (K := K)).mpr ⟨v, hvT, hwv⟩, rfl⟩

/-- **The class-group computation**: for an idèle `y` of `K` and `m` such that every `m`-th power
of a class has `p`-power order, `(idealOf y)^m` differs from an element whose divisor is supported
on the primes above `T` by a principal ideal. -/
lemma exists_finsupp_idealOf_eq (p : ℕ)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hclass : _root_.CFTLib.ClassCond F K p T) (y : Idele K) (m : ℕ)
    (hm : ∀ c : ClassGroup (NumberField.RingOfIntegers K), ∃ k : ℕ, (c ^ m) ^ (p ^ k) = 1) :
    ∃ (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →₀ ℤ) (a : Kˣ),
      e.support ⊆ ↑(primesOverT (F := F) (K := K) T) ∧
      (Idele.idealOf y) ^ m = FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰ (a : K) *
        e.prod (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n) := by
  classical
  obtain ⟨k, hk⟩ := hm (IdeleClassGroup.idealClassMap K y)
  have hmem : (IdeleClassGroup.idealClassMap K y) ^ m ∈
      Subgroup.closure (primeIdealClass '' ((primesOverT (F := F) (K := K) T :
        Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Set _)) :=
    Subgroup.closure_mono (classCond_set_subset (F := F) (K := K) T)
      (hclass ((IdeleClassGroup.idealClassMap K y) ^ m) ⟨k, hk⟩)
  obtain ⟨e, hsupp, heq⟩ :=
    exists_finsupp_of_mem_closure_image (primesOverT (F := F) (K := K) T) (primeIdealClass (K := K)) hmem
  set U1 : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
    Units.mk0 ((Idele.idealOf y) ^ m) (pow_ne_zero m (Idele.idealOf_ne_zero y)) with hU1
  have hprodne : e.prod (fun w n =>
      (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n) ≠ 0 := by
    rw [Finsupp.prod_of_support_subset e hsupp
      (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)
      (fun w _ => zpow_zero _)]
    exact Finset.prod_ne_zero_iff.mpr fun w _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  set U2 : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
    Units.mk0 (e.prod (fun w n =>
      (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)) hprodne with hU2
  have hclass_eq : ClassGroup.mk K U1 = ClassGroup.mk K U2 := by
    have h1 : ClassGroup.mk K U1 = (IdeleClassGroup.idealClassMap K y) ^ m := by
      rw [IdeleClassGroup.idealClassMap_apply, ← map_pow]
      congr 1
      exact Units.ext (by rw [hU1, Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_mk0])
    have h2 : (∏ w ∈ primesOverT (F := F) (K := K) T, (primeIdealClass (K := K) w) ^ (e w))
        = ClassGroup.mk K U2 := by
      rw [Finset.prod_congr rfl fun w _ => by rw [primeIdealClass_eq_mk w, ← map_zpow],
        ← map_prod]
      refine congrArg (ClassGroup.mk K) (Units.ext ?_)
      rw [hU2, Units.val_mk0, Units.coe_prod, Finsupp.prod_of_support_subset e hsupp
        (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)
        (fun w _ => zpow_zero _)]
      exact Finset.prod_congr rfl fun w _ => by
        rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [h1, heq, h2]
  obtain ⟨a, ha⟩ := IdeleClassGroup.exists_units_mul_toPrincipalIdeal_eq_of_mk_eq hclass_eq
  refine ⟨e, a⁻¹, hsupp, ?_⟩
  have hcomm : toPrincipalIdeal (NumberField.RingOfIntegers K) K a⁻¹
      = (toPrincipalIdeal (NumberField.RingOfIntegers K) K a)⁻¹ :=
    map_inv (toPrincipalIdeal (NumberField.RingOfIntegers K) K) a
  have h2 : U1 = toPrincipalIdeal (NumberField.RingOfIntegers K) K a⁻¹ * U2 := by
    rw [hcomm, ← ha]
    rw [mul_comm (toPrincipalIdeal (NumberField.RingOfIntegers K) K a)⁻¹
      (U1 * toPrincipalIdeal (NumberField.RingOfIntegers K) K a), mul_assoc, mul_inv_cancel, mul_one]
  have h3 : (↑U1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
      = ↑(toPrincipalIdeal (NumberField.RingOfIntegers K) K a⁻¹ * U2 :
          (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) := by
    rw [h2]
  rw [hU1, Units.val_mk0, Units.val_mul, coe_toPrincipalIdeal, hU2, Units.val_mk0] at h3
  rw [Finsupp.prod_of_support_subset e hsupp
    (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)
    (fun w _ => zpow_zero _)]
  rw [Finsupp.prod_of_support_subset e hsupp
    (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)
    (fun w _ => zpow_zero _)] at h3
  exact h3

end ClassToIdeal

/-! ### The main theorem -/

theorem exists_pow_mem_TUnits_mul_unitsNorm (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (K ≃ₐ[F] K))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hunr : _root_.CFTLib.IsUnramified F K) (hT : _root_.CFTLib.SplitsAt F K T)
    (hclass : _root_.CFTLib.ClassCond F K p T) :
    ∃ m : ℕ, Nat.Coprime m p ∧
      ∀ x : Fˣ, x ∈ NK.CFTLib.normPrincipalPreimage F K →
        ∃ y : Fˣ, y ∈ NK.CFTLib.normPrincipalPreimage F K ∧
          y ∈ NK.GlobalCFTdeep.TUnits {w : NK.GlobalCFT.Place F |
            ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q} ∧
          ∃ z : Fˣ, z ∈ NK.CFTLib.unitsNormSubgroup F K ∧ x ^ m = y * z := by
  classical
  obtain ⟨m, hm_coprime, hm_pow⟩ := exists_coprime_pow_powerOrder K p
  refine ⟨m, hm_coprime, fun x hx => ?_⟩
  have hunrP : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        q.asIdeal.LiesOver Q.asIdeal → q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 :=
    fun Q q hq => ramificationIdx_eq_one_of_isUnramified hunr Q q hq
  have hx' : Idele.principalIdele F x ∈ Idele.normImage F K := by
    rw [normPrincipalPreimage] at hx
    exact (Subgroup.mem_comap).mp hx
  obtain ⟨y, hy⟩ := (Idele.mem_normImage).mp hx'
  have hNy : Idele.normIdeleHom F K y = Idele.principalIdele F x :=
    Idele.ext fun v => by rw [Idele.normIdeleHom_apply]; exact (hy v).symm
  obtain ⟨e, a, hsupp, hideal⟩ :=
    exists_finsupp_idealOf_eq (F := F) (K := K) p T hclass y m hm_pow
  set z : Fˣ := Units.map (Algebra.norm F : K →* F) a with hz
  have hzmem : z ∈ unitsNormSubgroup F K := by
    rw [unitsNormSubgroup]; exact ⟨a, rfl⟩
  refine ⟨x ^ m * z⁻¹, ?_, ?_, z, hzmem, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.pow_mem _ hx m) (Subgroup.inv_mem _ ?_)
    exact unitsNormSubgroup_le_normPrincipalPreimage F K hzmem
  · rw [NK.GlobalCFTdeep.mem_TUnits_iff_expUnit]
    intro q hq
    have h1 : NK.GlobalCFTdeep.expUnit q (x ^ m * z⁻¹)
        = m * NK.GlobalCFTdeep.expUnit q x - NK.GlobalCFTdeep.expUnit q z := by
      rw [NK.GlobalCFTdeep.expUnit_mul, expUnit_pow, NK.GlobalCFTdeep.expUnit_inv]
      ring
    rw [h1, expUnit_eq_exp_principalIdele (q := q) (a := x),
      expUnit_eq_exp_principalIdele (q := q) (a := z)]
    have hxexp : Idele.exp q (Idele.principalIdele F x) =
        ∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
          (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * Idele.exp w y := by
      rw [← hNy]
      exact exp_normIdeleHom_eq_sum F K hunrP y q
    have hzexp : Idele.exp q (Idele.principalIdele F z) =
        ∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
          (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
            Idele.exp w (Idele.principalIdele K a) := by
      rw [show Idele.principalIdele F z = Idele.normIdeleHom F K (Idele.principalIdele K a) from by
        rw [hz]
        exact (Idele.normIdeleHom_principalIdele (K := F) (L := K) a).symm]
      exact exp_normIdeleHom_eq_sum F K hunrP (Idele.principalIdele K a) q
    rw [hxexp, hzexp]
    have hkey : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        m * Idele.exp w y = Idele.exp w (Idele.principalIdele K a) + e w := by
      intro w
      have ha1 : Idele.exp w (Idele.principalIdele K a)
          = FractionalIdeal.count K w
              (FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰ (a : K)) := by
        rw [← Idele.count_idealOf (Idele.principalIdele K a) w, Idele.idealOf_principalIdele]
      have h2 : FractionalIdeal.count K w ((Idele.idealOf y) ^ m)
          = FractionalIdeal.count K w
              (FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰ (a : K)) + e w := by
        rw [hideal, FractionalIdeal.count_mul K w
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a)) ?hne,
          FractionalIdeal.count_finsuppProd]
        rw [Finsupp.prod_of_support_subset e hsupp
          (fun w n => (w.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ n)
          (fun w _ => zpow_zero _)]
        exact Finset.prod_ne_zero_iff.mpr fun w _ =>
          zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
      rw [ha1, ← h2, FractionalIdeal.count_pow, Idele.count_idealOf]
    have hsum : m * (∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
          (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * Idele.exp w y)
        - (∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
          (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
            Idele.exp w (Idele.principalIdele K a))
        = ∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
          (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * e w := by
      have h1 : m * (∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
            (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * Idele.exp w y)
          = ∑ w ∈ Place.primesOverFinite (K := F) (L := K) q,
            (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
              (Idele.exp w (Idele.principalIdele K a) + e w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [show (m : ℤ) * ((w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
              Idele.exp w y)
            = (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
              (m * Idele.exp w y) by ring, hkey w]
      rw [h1]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    rw [hsum]
    exact sum_primesOverFinite_mul_eq_zero T e hsupp q hq
  · rw [mul_assoc, inv_mul_cancel, mul_one]

end NK.CFTLib
