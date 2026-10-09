import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicAuxiliaryInstances
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionArith
import Submission.NK.CFTLib.IdeleHasse.Descent.localDictionaryAux
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionAux
import Submission.NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped NumberField

namespace NK.CFTLib.IdeleHasse.Descent

theorem localConditionOdd {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    (v₀ : NK.GlobalCFT.Place K) :
    ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E)
      (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E)
      (_ : IsScalarTower K L E) (_ : IsScalarTower K M E)
      (_ : FiniteDimensional K M) (_ : FiniteDimensional K E)
      (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M))
      (m : ℕ) (_ : 2 < m) (_ : IsCyclotomicExtension {m} K M),
      (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v₀ = NK.GlobalCFT.Place.ofFinite Q → (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal) ∧
      (∀ (x : Kˣ) (w : NK.GlobalCFT.Place M), NK.GlobalCFT.Place.LiesOver w v₀ →
        Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) := by
  classical
  rcases v₀ with w₀ | Q
  · -- ### `v₀` is archimedean
    obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, q, hqp, hq2, hcycExt, hgen, hloc⟩ :=
      NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite
        (K := K) (L := L) hcyc w₀
    exact ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, q, hq2, hcycExt, hgen,
      (fun Q' hQ' => absurd hQ' (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ _)),
      hloc⟩
  · -- ### `v₀` is finite
    have hNQ : 1 < Ideal.absNorm Q.asIdeal := by
      have h0 : Ideal.absNorm Q.asIdeal ≠ 0 :=
        fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
      have h1 : Ideal.absNorm Q.asIdeal ≠ 1 :=
        fun hc => Q.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp hc)
      omega
    -- the auxiliary prime `q`
    obtain ⟨q, hqprime, hqgt, hqdvd⟩ :=
      exists_prime_gt_orderOf_dvd (Ideal.absNorm Q.asIdeal) hNQ (Module.finrank K L)
        (Module.finrank_pos)
    have hqnodvd : ¬ q ∣ Ideal.absNorm Q.asIdeal := fun hd =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (by omega)) hd) (by omega)
    have hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) q :=
      (Nat.Prime.coprime_iff_not_dvd hqprime).mpr hqnodvd |>.symm
    have hq2 : 2 < q := by omega
    -- the cyclotomic auxiliary
    obtain ⟨M, hMf, hMN, hKM, hfdM, hgalM, hcycM, hcycExt, hME, hstKME, hgen, hgalE, hdiv⟩ :=
      cyclotomicAuxiliaryInstances (K := K) (L := L) q hqprime Q hcop
    haveI : FiniteDimensional M (CyclotomicField q L) :=
      Module.Finite.of_restrictScalars_finite K M (CyclotomicField q L)
    haveI : IsGalois M (CyclotomicField q L) := IsGalois.tower_top_of_isGalois K M _
    refine ⟨M, CyclotomicField q L, hMf, hMN, inferInstance, inferInstance, hKM,
      inferInstance, inferInstance, hME, inferInstance, hstKME, hfdM, inferInstance,
      hgalM, hgalE, hcycM, q, hq2, hcycExt, hgen, ?_, ?_⟩
    · -- ### the conductor is coprime to `Q`
      intro Q' hQ'
      have hQeq : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp hQ'
      rw [← hQeq]
      intro hmem
      have hle : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) ≤ Q.asIdeal := by
        rw [Ideal.span_singleton_le_iff_mem]; exact hmem
      have hdvd : Ideal.absNorm Q.asIdeal ∣ Ideal.absNorm (Ideal.span ({(q : 𝓞 K)})) :=
        Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_natCast] at hdvd
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Ideal.absNorm Q.asIdeal)
        (by omega)
      have hpq : p = q :=
        (hqprime.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow (hpdvd.trans hdvd))).resolve_left
          hp.ne_one
      have hq_dvd : q ∣ Ideal.absNorm Q.asIdeal := hpq ▸ hpdvd
      have h1 : q ∣ Nat.gcd (Ideal.absNorm Q.asIdeal) q := Nat.dvd_gcd hq_dvd (dvd_refl q)
      rw [hcop.gcd_eq_one] at h1
      exact hqprime.not_dvd_one h1
    · -- ### the local condition
      intro x w hw
      rcases hw with ⟨w', v', hw', hv', -⟩ | ⟨wl, Q', hwl, hQ', hwlQ⟩
      · exact absurd hv'
          (Ne.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v' Q))
      · subst hwl
        have hQeq : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp hQ'
        subst hQeq
        -- a prime of `E` above `wl`
        obtain ⟨ql, hql⟩ :=
          Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
            (K := M) (L := CyclotomicField q L) wl
        -- the divisibility `[L : K] ∣ f(wl | Q)`
        have hord : orderOf (ZMod.unitOfCoprime (Ideal.absNorm Q.asIdeal) hcop) =
            orderOf ((Ideal.absNorm Q.asIdeal : ℕ) : ZMod q) := by
          apply Nat.dvd_antisymm
          · rw [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val,
              Units.val_one, ZMod.coe_unitOfCoprime (Ideal.absNorm Q.asIdeal) hcop]
            exact pow_orderOf_eq_one _
          · rw [orderOf_dvd_iff_pow_eq_one,
              ← ZMod.coe_unitOfCoprime (Ideal.absNorm Q.asIdeal) hcop,
              ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
        have hdvdL : Module.finrank K L ∣ wl.asIdeal.inertiaDeg (𝓞 K) := by
          have h1 : orderOf ((Ideal.absNorm Q.asIdeal : ℕ) : ZMod q) ∣
              wl.asIdeal.inertiaDeg (𝓞 K) := by
            rw [← hord]
            exact hdiv wl hwlQ
          exact hqdvd.trans h1
        have hmem := mem_localNormFinite_of_cyclotomicAux (K := K) (L := L) (M := M)
          (E := CyclotomicField q L) hgen hqprime Q hcop wl hwlQ hdvdL ql hql x
        rw [localNormSubgroup_ofFinite_eq_range (F := CyclotomicField q L) wl ql hql]
        simpa only [NK.GlobalCFT.Place.localField_ofFinite] using hmem

end NK.CFTLib.IdeleHasse.Descent
