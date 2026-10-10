import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped WithZero

namespace Work.SSGRoute.ZDataTwo

/-- The valuation ring of a pullback valuation is the pullback of the valuation ring. -/
private theorem valuationSubring_comap_aux {K L Γ₀ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) (f : K →+* L) :
    (v.comap f).valuationSubring = v.valuationSubring.comap f := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ValuationSubring.mem_comap,
    Valuation.mem_valuationSubring_iff]

theorem not_exists_sq_val_of_odd_count
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (hA : A.comap (algebraMap K Ω) ≠ ⊤)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    (b : Kˣ)
    (hodd : Odd (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (b : K)))) :
    ¬ ∃ d : Kˣ, A.valuation (algebraMap K Ω (b : K)) =
      (A.valuation (algebraMap K Ω (d : K))) ^ 2 := by
  classical
  -- `w` is the valuation induced on `K` by `A`, and `v` the `𝔭`-adic valuation.
  set w : Valuation K A.ValueGroup := A.valuation.comap (algebraMap K Ω) with hw
  set v : Valuation K ℤᵐ⁰ := 𝔭.valuation K with hv
  have hw_apply : ∀ x : K, w x = A.valuation (algebraMap K Ω x) := fun x => by
    rw [hw, Valuation.comap_apply]
  -- `w` and `v` have the same valuation ring, hence are equivalent.
  have hsub : w.valuationSubring = v.valuationSubring := by
    have hwsub : w.valuationSubring = A.comap (algebraMap K Ω) := by
      rw [hw, valuationSubring_comap_aux A.valuation (algebraMap K Ω),
        ValuationSubring.valuationSubring_valuation]
    rw [hwsub, h𝔭, hv,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have heq : w.IsEquiv v := (Valuation.isEquiv_iff_valuationSubring w v).mpr hsub
  rintro ⟨d, hd⟩
  -- the square condition descends from `w` to the `𝔭`-adic valuation `v`
  have hpow : A.valuation (algebraMap K Ω ((d : K) ^ 2)) =
      (A.valuation (algebraMap K Ω (d : K))) ^ 2 := by
    rw [map_pow, Valuation.map_pow]
  have hd'' : w (b : K) = w ((d : K) ^ 2) := by
    rw [hw_apply (b : K), hw_apply ((d : K) ^ 2)]
    exact hd.trans hpow.symm
  have hv_eq : v (b : K) = (v (d : K)) ^ 2 := by
    have h := (heq.eq_iff (r := (b : K)) (s := (d : K) ^ 2)).mp hd''
    rwa [Valuation.map_pow] at h
  -- hence the `𝔭`-adic logarithm of `b` is even
  have hEven : Even ((v (b : K)).log) := by
    refine ⟨(v (d : K)).log, ?_⟩
    rw [hv_eq, WithZero.log_pow]
    ring
  -- while the `𝔭`-adic exponent `count = -log` is odd by hypothesis
  have hcount : FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
      = -((v (b : K)).log) := by
    rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log 𝔭 (Units.ne_zero b), hv]
  have hEvenC : Even (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (b : K))) := by
    rw [hcount]
    exact hEven.neg
  exact (Int.not_even_iff_odd.mpr hodd) hEvenC

end Work.SSGRoute.ZDataTwo
