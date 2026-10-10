import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Approximation

open IsDedekindDomain

/-- **A unit of a local completion which is not an `ℓ`-th power.**

For a number field `K`, a prime `ℓ`, and a finite prime `𝔮` of `K`, there is `u` in the unit group
of the completion `K_𝔮` (which, the completion being a field, is the group of all nonzero
elements) such that `u` is not the `ℓ`-th power of any unit.

The value group of the completion is `ℤᵐ⁰`, so a uniformizer `π` (with `v π = exp (-1)`) is such an
element: `v (x ^ ℓ) = (v x) ^ ℓ` and `-1` is not `ℓ` times an integer for the prime `ℓ`. -/
theorem exists_not_ellPow_unit_adicCompletion {K : Type*} [Field K] [NumberField K]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    ∃ u : (𝔮.adicCompletion K)ˣ, ∀ b : (𝔮.adicCompletion K)ˣ, b ^ ℓ ≠ u := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K 𝔮
  have hne : Valued.v (π : 𝔮.adicCompletion K) ≠ 0 := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe, hπ]
    exact WithZero.coe_ne_zero
  have hπ0 : (π : 𝔮.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hne
  refine ⟨Units.mk0 (π : 𝔮.adicCompletion K) hπ0, ?_⟩
  intro b hb
  have hC : ((b : (𝔮.adicCompletion K)ˣ) : 𝔮.adicCompletion K) ^ ℓ =
      (π : 𝔮.adicCompletion K) := by
    have := congrArg (fun x : (𝔮.adicCompletion K)ˣ => (x : 𝔮.adicCompletion K)) hb
    simpa using this
  have hval : (Valued.v (b : 𝔮.adicCompletion K)) ^ ℓ = WithZero.exp (-1 : ℤ) := by
    rw [← Valuation.map_pow]
    rw [hC, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  have hlog : (ℓ : ℤ) * (Valued.v (b : 𝔮.adicCompletion K)).log = -1 := by
    have := congrArg (fun z => z.log) hval
    rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at this
    exact this
  have hnat : ℓ * ((Valued.v (b : 𝔮.adicCompletion K)).log).natAbs = 1 := by
    have := congrArg Int.natAbs hlog
    simpa [Int.natAbs_mul, Int.natAbs_neg] using this
  exact hℓ.ne_one (Nat.eq_one_of_dvd_one ⟨_, hnat.symm⟩)

end NK.UchidaKummer.Approximation
