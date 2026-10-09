import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.ker_decompK_le_zpowers_frob
import Submission.NK.ChebotarevGeneral.isFrobAtPrime_under_of_isFrobAt
import Submission.NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **The `f`-th power of a Frobenius generates the decomposition group.**

Let `k ⊆ K ⊆ L` be number fields with `K/k` and `L/k` finite Galois, `q'` a prime of `𝓞 L`
unramified over both `k` and `K`, `d` an arithmetic Frobenius at `q'` for the extension `L/k`,
`f = [κ(q'∩K) : κ(q'∩k)]`, and `e ∈ Gal(L/K)` the automorphism with `e = d ^ f`.  Then `e`
generates the decomposition group of `q'` in `Gal(L/K)`. -/
theorem frob_pow_zpowers_decomp {k K L : Type} [Field k] [Field K] [Field L] [NumberField k]
    [NumberField K] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] [IsGalois K L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (d : L ≃ₐ[k] L)
    (e : L ≃ₐ[K] L) (f : ℕ)
    (hd : NK.Chebotarev.IsFrobAt (K := k) (L := L) q' d)
    (he : AlgEquiv.restrictScalars k e = d ^ f)
    (hf : f = (q'.asIdeal.under (NumberField.RingOfIntegers K)).inertiaDeg
      (NumberField.RingOfIntegers k))
    (hl : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (hu : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Subgroup.zpowers e = Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) q' := by
  -- The `f`-th power `e` of the Frobenius `d` (over `k`) is a Frobenius at `q'` for the
  -- extension `L/K`, because it induces the `#κ(q'∩K)`-th power map on the residue field.
  have hfe : NK.Chebotarev.IsFrobAt (K := K) (L := L) q' e := by
    rw [NK.Chebotarev.isFrobAt_def]
    intro x
    -- `e` and `d ^ f` have the same underlying function on `L`
    have hfun : ∀ y : L, e y = (d ^ f) y := fun y => by
      rw [← AlgEquiv.restrictScalars_apply k e y, he]
    have hfunc : ∀ y : NumberField.RingOfIntegers L,
        galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) e y =
        galRestrict (NumberField.RingOfIntegers k) k L
          (NumberField.RingOfIntegers L) (d ^ f) y :=
      fun y => NK.ChebotarevGeneral.galRestrict_eq_of_apply_eq (σ := d ^ f) (τ := e) hfun y
    -- the residue action of the Frobenius `d` over `k`
    have hPk : q'.asIdeal.LiesOver (q'.under (NumberField.RingOfIntegers k)).asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact ⟨rfl⟩
    have hres_k : ∀ y : NumberField.RingOfIntegers L,
        Ideal.Quotient.mk q'.asIdeal
            (galRestrict (NumberField.RingOfIntegers k) k L (NumberField.RingOfIntegers L) d y) =
          (Ideal.Quotient.mk q'.asIdeal y)
            ^ Nat.card (NumberField.RingOfIntegers k ⧸
                (q'.under (NumberField.RingOfIntegers k)).asIdeal) :=
      fun y => hd.mk_apply hPk y
    -- hence the residue action of `d ^ f` is the `(#κ(q'∩k)) ^ f`-th power map
    have hpow := Commons.NumberTheory.NumberField.residue_pow_galRestrict_pow
      (K := k) (L := L) (q'.under (NumberField.RingOfIntegers k)) q' d hres_k
    -- the prime `q' ∩ 𝓞 K` lies over `q' ∩ 𝓞 k`
    have hLiesKK : (q'.asIdeal.under (NumberField.RingOfIntegers K)).LiesOver
        (q'.asIdeal.under (NumberField.RingOfIntegers k)) :=
      Ideal.LiesOver.mk
        (Ideal.under_under (A := NumberField.RingOfIntegers k)
          (B := NumberField.RingOfIntegers K) q'.asIdeal).symm
    -- `#κ(q'∩K) = (#κ(q'∩k)) ^ f`
    have hcard := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg
      (K := k) (L := K) (q'.under (NumberField.RingOfIntegers k))
      (q'.under (NumberField.RingOfIntegers K)) hLiesKK
    have hexp : (Nat.card (NumberField.RingOfIntegers k ⧸
          (q'.under (NumberField.RingOfIntegers k)).asIdeal)) ^ f =
        Nat.card (NumberField.RingOfIntegers K ⧸
          (q'.under (NumberField.RingOfIntegers K)).asIdeal) := by
      rw [hf, ← IsDedekindDomain.HeightOneSpectrum.under_asIdeal
        (NumberField.RingOfIntegers K) q', hcard.symm]
    -- the defining congruence for the Frobenius of `L/K` at `q'`
    have h4 : Ideal.Quotient.mk q'.asIdeal
          (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) e x) =
        Ideal.Quotient.mk q'.asIdeal (x ^ Nat.card (NumberField.RingOfIntegers K ⧸
          (q'.under (NumberField.RingOfIntegers K)).asIdeal)) := by
      rw [hfunc x, hpow f x, hexp, map_pow]
    exact (Ideal.Quotient.eq).mp h4
  -- The decomposition group of an unramified prime is generated by its Frobenius.
  have hmain : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) q' =
      Subgroup.zpowers e :=
    NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := K) (N := L) q' e
      hu hfe
  exact hmain.symm

end Work.SSGcrux
