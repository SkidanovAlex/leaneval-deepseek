/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

For a character `χ` of `Gal(L/K)` and a modulus `S`, the real part of the character-twisted
prime sum `∑_{𝔭 ∉ S} χ(Frob_𝔭) N𝔭^{-s}` differs from `log ‖L(s,χ)‖` by a quantity which stays
bounded as `s → 1⁺`.

The point is that `log ‖(1 - z)⁻¹‖` differs from `Re z` by `O(‖z‖²)`: the `k = 1` term of the
logarithm of the Euler product is exactly the prime sum, and all the higher terms are dominated
by `∑_𝔭 N𝔭^{-2s}`, which converges uniformly for `s ≥ 1`.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta

open NumberField IsDedekindDomain Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

namespace NK.HeckeL.Series

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The summand `χ(Frob_𝔭) · N𝔭^{-s}` of the character-twisted prime sum. -/
noncomputable def artinPrimeTerm (χ : Gal(L/K) →* ℂˣ) (s : ℝ)
    (𝔭 : NK.HeckeL.PrimeIdeal K) : ℂ :=
  (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
    (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

lemma artinPrimeSum_eq_tsum (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ)
    (s : ℝ) :
    NK.HeckeL.artinPrimeSum K L S χ s
      = ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, artinPrimeTerm χ s 𝔭.1 := rfl

lemma artinLSeries_eq_tprod (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ)
    (s : ℝ) :
    NK.HeckeL.artinLSeries K L S χ s
      = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          (1 - artinPrimeTerm χ s 𝔭.1)⁻¹ := rfl

lemma norm_artinPrimeTerm (χ : Gal(L/K) →* ℂˣ) (s : ℝ)
    (𝔭 : NK.HeckeL.PrimeIdeal K) :
    ‖artinPrimeTerm χ s 𝔭‖ = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  rw [artinPrimeTerm, norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one, one_mul]
  simp [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

lemma absNorm_primeIdeal_pos' (𝔭 : NK.HeckeL.PrimeIdeal K) :
    (0 : ℝ) < (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
  Commons.NumberTheory.NumberField.DedekindZeta.absNorm_primeIdeal_pos 𝔭

lemma two_le_absNorm_primeIdeal' (𝔭 : NK.HeckeL.PrimeIdeal K) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
  Commons.NumberTheory.NumberField.DedekindZeta.two_le_absNorm_primeIdeal 𝔭

/-- `(x^{-s})^2 = x^{-2s}`. -/
lemma sq_rpow_neg {x : ℝ} (hx : 0 < x) (s : ℝ) : (x ^ (-s)) ^ 2 = x ^ (-(2 * s)) := by
  rw [sq, ← Real.rpow_add hx]
  congr 1
  ring

lemma norm_artinPrimeTerm_le_half (χ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s)
    (𝔭 : NK.HeckeL.PrimeIdeal K) : ‖artinPrimeTerm χ s 𝔭‖ ≤ 1 / 2 := by
  have hN2 := two_le_absNorm_primeIdeal' (K := K) 𝔭
  rw [norm_artinPrimeTerm]
  have h1 : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hN2 (by linarith)
  have h2 : (2 : ℝ) ^ (-s) < 1 / 2 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num)
      (show -s < (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one, inv_eq_one_div] at h
    norm_num at h
    exact h
  linarith

lemma summable_artinPrimeTerm (χ : Gal(L/K) →* ℂˣ) (S : Finset (NK.HeckeL.PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => artinPrimeTerm χ s 𝔭.1) := by
  have h : Summable (fun 𝔭 : NK.HeckeL.PrimeIdeal K
      => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
    Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs
  have hf : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => ‖artinPrimeTerm χ s 𝔭.1‖) :=
    (h.subtype (fun 𝔭 => 𝔭 ∉ S)).congr (fun 𝔭 => (norm_artinPrimeTerm χ s 𝔭.1).symm)
  exact hf.of_norm

/-- The basic estimate: for `‖z‖ ≤ 1/2` the principal logarithm of `(1 - z)⁻¹` is within
`2‖z‖` of `0`. -/
lemma norm_Complex_log_inv_one_sub_le (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log ((1 - z)⁻¹)‖ ≤ 2 * ‖z‖ := by
  have hzlt : ‖z‖ < 1 := by linarith
  have hle := Complex.norm_log_one_sub_inv_sub_self_le (z := z) hzlt
  have hsplit : Complex.log ((1 - z)⁻¹) = (Complex.log ((1 - z)⁻¹) - z) + z := by ring
  rw [hsplit]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - ‖z‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hsq : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h2 : (1 - ‖z‖)⁻¹ / 2 ≤ 1 := by linarith
    calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 = ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) := by ring
      _ ≤ ‖z‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = ‖z‖ ^ 2 := by ring
  calc ‖(Complex.log ((1 - z)⁻¹) - z) + z‖
      ≤ ‖Complex.log ((1 - z)⁻¹) - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by linarith
    _ ≤ ‖z‖ ^ 2 + ‖z‖ := by linarith
    _ ≤ 2 * ‖z‖ := by nlinarith [norm_nonneg z, hz]

lemma summable_Complex_log_inv_one_sub (χ : Gal(L/K) →* ℂˣ)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)) := by
  have hg : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => 2 * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
    ((Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs).mul_left 2).subtype
      (fun 𝔭 => 𝔭 ∉ S)
  refine Summable.of_norm_bounded hg (fun 𝔭 => ?_)
  have h2 := norm_Complex_log_inv_one_sub_le (artinPrimeTerm χ s 𝔭.1)
    (norm_artinPrimeTerm_le_half χ hs 𝔭.1)
  rwa [norm_artinPrimeTerm χ s 𝔭.1] at h2

/-- The logarithm of the norm of the Artin `L`-series is the sum of the logarithms of the norms
of its Euler factors. -/
lemma log_norm_artinLSeries_eq_tsum' (χ : Gal(L/K) →* ℂˣ)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    Real.log ‖NK.HeckeL.artinLSeries K L S χ s‖
      = ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          Real.log ‖(1 - artinPrimeTerm χ s 𝔭.1)⁻¹‖ := by
  have hsumm := summable_Complex_log_inv_one_sub χ S hs
  have hne : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      (1 - artinPrimeTerm χ s 𝔭.1)⁻¹ ≠ 0 := by
    intro 𝔭
    exact inv_ne_zero (sub_ne_zero.mpr (fun h => by
      have hzle := norm_artinPrimeTerm_le_half χ hs 𝔭.1
      rw [← h, norm_one] at hzle
      norm_num at hzle))
  have hval : ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        (1 - artinPrimeTerm χ s 𝔭.1)⁻¹
      = Complex.exp (∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)) :=
    (Complex.hasProd_of_hasSum_log hne hsumm.hasSum).tprod_eq
  rw [artinLSeries_eq_tprod, hval, Complex.norm_exp, Real.log_exp, Complex.re_tsum hsumm]
  exact tsum_congr (fun 𝔭 => Complex.log_re _)

/-- The pointwise bound: `‖log (1-z)⁻¹ - z‖ ≤ N𝔭^{-2s}` for `z = χ(Frob_𝔭) N𝔭^{-s}`. -/
lemma norm_artinPrimeTerm_sub_log_le (χ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s)
    (𝔭 : NK.HeckeL.PrimeIdeal K) :
    ‖artinPrimeTerm χ s 𝔭 - Complex.log ((1 - artinPrimeTerm χ s 𝔭)⁻¹)‖
      ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 * s)) := by
  have hzlt : ‖artinPrimeTerm χ s 𝔭‖ < 1 := by
    rw [norm_artinPrimeTerm]
    exact Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (by linarith) 𝔭
  have hle := Complex.norm_log_one_sub_inv_sub_self_le (z := artinPrimeTerm χ s 𝔭) hzlt
  rw [norm_sub_rev]
  have hhalf : ‖artinPrimeTerm χ s 𝔭‖ ≤ 1 / 2 := norm_artinPrimeTerm_le_half χ hs 𝔭
  have hinv : (1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - ‖artinPrimeTerm χ s 𝔭‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hsq : ‖artinPrimeTerm χ s 𝔭‖ ^ 2 * (1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ / 2
      ≤ ‖artinPrimeTerm χ s 𝔭‖ ^ 2 := by
    have h2 : (1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ / 2 ≤ 1 := by linarith
    calc ‖artinPrimeTerm χ s 𝔭‖ ^ 2 * (1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ / 2
        = ‖artinPrimeTerm χ s 𝔭‖ ^ 2 * ((1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ / 2) := by ring
      _ ≤ ‖artinPrimeTerm χ s 𝔭‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = ‖artinPrimeTerm χ s 𝔭‖ ^ 2 := by ring
  have hsq2 : ‖artinPrimeTerm χ s 𝔭‖ ^ 2
      = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 * s)) := by
    rw [norm_artinPrimeTerm]
    exact sq_rpow_neg (absNorm_primeIdeal_pos' 𝔭) s
  calc ‖Complex.log ((1 - artinPrimeTerm χ s 𝔭)⁻¹) - artinPrimeTerm χ s 𝔭‖
      ≤ ‖artinPrimeTerm χ s 𝔭‖ ^ 2 * (1 - ‖artinPrimeTerm χ s 𝔭‖)⁻¹ / 2 := hle
    _ ≤ ‖artinPrimeTerm χ s 𝔭‖ ^ 2 := hsq
    _ = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 * s)) := hsq2

theorem re_artinPrimeSum_sub_log_isBigO {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    (fun s : ℝ => (NK.HeckeL.artinPrimeSum K L S χ s).re -
      Real.log ‖NK.HeckeL.artinLSeries K L S χ s‖)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  refine Asymptotics.IsBigO.of_bound
    (∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1mem
  have hs1 : (1 : ℝ) < s := hs1mem
  have hzsum : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => artinPrimeTerm χ s 𝔭.1) := summable_artinPrimeTerm χ S hs1
  have hlogsum : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)) :=
    summable_Complex_log_inv_one_sub χ S hs1
  have hzre : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => (artinPrimeTerm χ s 𝔭.1).re) :=
    Summable.of_norm_bounded hzsum.norm (fun 𝔭 => by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)
  have hlogre : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => (Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re) :=
    Summable.of_norm_bounded hlogsum.norm (fun 𝔭 => by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)
  have key : (NK.HeckeL.artinPrimeSum K L S χ s).re
        - Real.log ‖NK.HeckeL.artinLSeries K L S χ s‖
      = ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          (artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re := by
    rw [artinPrimeSum_eq_tsum, log_norm_artinLSeries_eq_tsum' χ S hs1]
    rw [Complex.re_tsum hzsum]
    rw [tsum_congr (fun 𝔭 => (Complex.log_re _).symm)]
    rw [← Summable.tsum_sub hzre hlogre]
    exact tsum_congr (fun 𝔭 => (Complex.sub_re _ _).symm)
  have hsumN2 : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ))) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K
      (by norm_num : (1 : ℝ) < 2)).subtype (fun 𝔭 => 𝔭 ∉ S)
  have hbnd : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      ‖(artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re‖
        ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
    intro 𝔭
    have h1 := norm_artinPrimeTerm_sub_log_le χ hs1 𝔭.1
    have h2 : (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 * s))
        ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by linarith [two_le_absNorm_primeIdeal' (K := K) 𝔭.1])
        (by linarith)
    rw [Real.norm_eq_abs]
    calc |(artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re|
        ≤ ‖artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 * s)) := h1
      _ ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ)) := h2
  have hsum1 : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}
      => ‖(artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re‖) :=
    Summable.of_norm_bounded hsumN2 (fun 𝔭 => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hbnd 𝔭)
  have keybound : ‖∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        (artinPrimeTerm χ s 𝔭.1 - Complex.log ((1 - artinPrimeTerm χ s 𝔭.1)⁻¹)).re‖
      ≤ ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
    (norm_tsum_le_tsum_norm hsum1).trans (Summable.tsum_le_tsum hbnd hsum1 hsumN2)
  rw [key]
  simpa using keybound

end NK.HeckeL.Series
