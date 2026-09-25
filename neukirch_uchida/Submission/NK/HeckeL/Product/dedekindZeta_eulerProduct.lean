import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal

open Filter Topology IsDedekindDomain NumberField
open scoped BigOperators

noncomputable section

namespace NK.HeckeL.Product

open Commons.NumberTheory.NumberField.DedekindZeta

/-- **The Euler product of the Dedekind zeta function** of a number field `K`, at a real
`s > 1`: the product of the local factors `(1 - N𝔮^{-s})⁻¹` over the finite places `𝔮` of `K`
equals the (real) value of the Dedekind zeta function. -/
theorem dedekindZeta_eulerProduct {K : Type*} [Field K] [NumberField K] {s : ℝ}
    (hs : 1 < s) :
    ∏' 𝔮 : NK.HeckeL.PrimeIdeal K,
        (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ =
      ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by
  have hspos : (0 : ℝ) < s := lt_trans zero_lt_one hs
  -- The local factors are positive
  have hposg : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 0 < localFactor K s 𝔭.asIdeal := by
    intro 𝔭
    rw [localFactor]
    exact inv_pos.mpr (by linarith [rpow_neg_absNorm_primeIdeal_lt_one hspos 𝔭])
  -- Their logarithms are summable
  have hsumlog : Summable (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      Real.log (localFactor K s 𝔭.asIdeal)) := summable_log_localFactor (K := K) hs
  have hmult : Multipliable (fun 𝔭 : HeightOneSpectrum (𝓞 K) => localFactor K s 𝔭.asIdeal) :=
    Real.multipliable_of_summable_log hposg hsumlog
  -- The Dedekind zeta function is positive on the real axis to the right of `1`
  have hRpos : 0 < (NumberField.dedekindZeta K (s : ℂ)).re := by
    have hmono : ∀ n : ℕ, 0 ≤ zetaTerm K s n := fun n =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hzt1 : zetaTerm K s 1 = 1 := by
      have hc := Commons.NumberTheory.NumberField.card_absNorm_eq_one (K := K)
      simp only [zetaTerm, hc, Nat.cast_one, Real.one_rpow, mul_one]
    rw [logEuler_dedekindZeta_re_eq_tsum (K := K) hs]
    exact Summable.tsum_pos (summable_zetaTerm (K := K) hs) hmono 1 (by rw [hzt1]; norm_num)
  -- The Euler product as a real number
  have hval : ∏' 𝔭 : HeightOneSpectrum (𝓞 K), localFactor K s 𝔭.asIdeal =
      (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← Real.exp_log hRpos, ← Real.rexp_tsum_eq_tprod hposg hsumlog]
    congr 1
    rw [← log_eulerProduct_primeIdeal K hs]
    exact tsum_congr fun 𝔭 => by rw [localFactor, Real.log_inv]
  have hbase : ∀ 𝔮 : NK.HeckeL.PrimeIdeal K,
      (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ =
        ((localFactor K s 𝔮.asIdeal : ℝ) : ℂ) := by
    intro 𝔮
    rw [localFactor, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  calc ∏' 𝔮 : NK.HeckeL.PrimeIdeal K,
        (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      = ∏' 𝔮 : NK.HeckeL.PrimeIdeal K, ((localFactor K s 𝔮.asIdeal : ℝ) : ℂ) :=
        tprod_congr hbase
    _ = ((∏' 𝔮 : NK.HeckeL.PrimeIdeal K, localFactor K s 𝔮.asIdeal : ℝ) : ℂ) :=
        (hmult.map_tprod Complex.ofRealHom Complex.continuous_ofReal).symm
    _ = ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by rw [hval]

end NK.HeckeL.Product
