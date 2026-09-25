/-
The logarithm of the Artin `L`-series is the sum of the logarithms of its Euler factors.

`log ‖∏_𝔭 f 𝔭‖ = ∑_𝔭 log ‖f 𝔭‖` for an Euler product `∏_𝔭 f 𝔭` whose factors are `1 + o(1)`
with `∑ ‖f 𝔭 - 1‖ < ∞`; the factors here are `artinEulerFactor χ s 𝔭 = (1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹`
and `∑_𝔭 ‖χ(Frob_𝔭) N𝔭^{-s}‖ = ∑_𝔭 N𝔭^{-s} < ∞` for `s > 1`.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum

open NumberField IsDedekindDomain
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

namespace NK.HeckeL.Series

/-! ## The logarithmic identity for an Euler product -/

/-- For a family `f` of nonzero complex numbers with `∑ ‖f i - 1‖ < ∞`, the logarithm of the norm
of the infinite product `∏ i, f i` is the sum of the logarithms of the norms of the factors. -/
theorem log_norm_tprod_eq_tsum_log_norm {ι : Type*} {f : ι → ℂ}
    (hs : Summable fun i => ‖f i - 1‖) (hne : ∀ i, f i ≠ 0) :
    Real.log ‖∏' i, f i‖ = ∑' i, Real.log ‖f i‖ := by
  have hlog : Summable fun i => Real.log ‖f i‖ := by
    have h := Summable.summable_log_norm_one_add (f := fun i => f i - 1) (by simpa using hs)
    simpa using h
  have hmul : Multipliable f := by
    have h := multipliable_one_add_of_summable (R := ℂ) (f := fun i => f i - 1) (by simpa using hs)
    simpa using h
  rw [hmul.norm_tprod, ← Real.rexp_tsum_eq_tprod (fun i => norm_pos_iff.mpr (hne i)) hlog,
    Real.log_exp]

/-! ## Elementary estimates for the factors `(1 - z)⁻¹` with `‖z‖ ≤ 1/2` -/

/-- The algebraic identity `(1 - z)⁻¹ - 1 = z (1 - z)⁻¹`, valid when `1 - z ≠ 0`. -/
theorem logNorm_inv_one_sub_sub_one_eq {z : ℂ} (hz : 1 - z ≠ 0) :
    (1 - z)⁻¹ - 1 = z * (1 - z)⁻¹ := by
  field_simp
  ring

/-- For `‖z‖ ≤ 1/2` the factor `(1 - z)⁻¹` is within `2‖z‖` of `1`. -/
theorem logNorm_norm_inv_one_sub_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹ - 1‖ ≤ 2 * ‖z‖ := by
  have hge : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    simp only [norm_one] at h
    linarith [norm_nonneg z]
  have hnorm : ‖(1 - z)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc ‖(1 : ℂ) - z‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) hge
      _ = 2 := by norm_num
  rw [logNorm_inv_one_sub_sub_one_eq (norm_pos_iff.mp (by linarith)), norm_mul]
  calc ‖z‖ * ‖(1 - z)⁻¹‖ ≤ ‖z‖ * 2 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
    _ = 2 * ‖z‖ := by ring

/-- For `‖z‖ ≤ 1/2` the factor `(1 - z)⁻¹` is nonzero. -/
theorem logNorm_inv_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : (1 - z)⁻¹ ≠ 0 := by
  have hge : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    simp only [norm_one] at h
    linarith [norm_nonneg z]
  exact inv_ne_zero (norm_pos_iff.mp (by linarith))

/-! ## The Artin Euler factors -/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The `𝔭`-th term `χ(Frob_𝔭) N𝔭^{-s}`, whose complementary inverse gives the Artin Euler factor
at `𝔭`. -/
noncomputable def logNorm_artinTerm (χ : Gal(L/K) →* ℂˣ) (s : ℝ) (𝔭 : PrimeIdeal K) : ℂ :=
  (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
    (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-- The Artin Euler factor at `𝔭` is the inverse of `1 - logNorm_artinTerm χ s 𝔭`. -/
theorem logNorm_artinEulerFactor_eq_inv (χ : Gal(L/K) →* ℂˣ) (s : ℝ) (𝔭 : PrimeIdeal K) :
    artinEulerFactor (K := K) (L := L) χ s 𝔭 = (1 - logNorm_artinTerm χ s 𝔭)⁻¹ := rfl

/-- The norm of the `𝔭`-th term is `N𝔭^{-s}`. -/
theorem logNorm_norm_artinTerm (χ : Gal(L/K) →* ℂˣ) (s : ℝ) (𝔭 : PrimeIdeal K) :
    ‖logNorm_artinTerm (K := K) (L := L) χ s 𝔭‖ = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  rw [logNorm_artinTerm, norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one, one_mul]
  simp [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- A prime ideal has absolute norm at least `2`. -/
theorem logNorm_two_le_absNorm (𝔭 : PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr 𝔭.isPrime.ne_top
  omega

/-- For `s > 1` and a prime ideal `𝔭`, `N𝔭^{-s} ≤ 1/2`. -/
theorem logNorm_absNorm_rpow_neg_le_half (𝔭 : PrimeIdeal K) {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hN' : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast logNorm_two_le_absNorm 𝔭
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 2 ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hN' (by linarith)
    _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The Dirichlet series `∑_𝔭 ‖logNorm_artinTerm χ s 𝔭‖` over the primes outside `S` is
summable: it is the prime-ideal zeta sum `∑_𝔭 N𝔭^{-s}` of `K`, which converges for `s > 1`. -/
theorem logNorm_summable_norm_artinTerm (S : Finset (PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ‖logNorm_artinTerm (K := K) (L := L) χ s 𝔭.1‖) := by
  have h : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype _
  exact h.congr fun 𝔭 => (logNorm_norm_artinTerm χ s 𝔭.1).symm

/-! ## The main identity -/

/-- **The logarithm of the Artin `L`-series** is the sum of the logarithms of the norms of its
Euler factors. -/
theorem log_norm_artinLSeries_eq_tsum {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Real.log ‖NK.HeckeL.artinLSeries K L S χ s‖ =
      ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        Real.log ‖NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1‖ := by
  rw [show NK.HeckeL.artinLSeries K L S χ s
      = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, artinEulerFactor (K := K) (L := L) χ s 𝔭.1
      from rfl]
  have hle : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      ‖logNorm_artinTerm (K := K) (L := L) χ s 𝔭.1‖ ≤ 1 / 2 :=
    fun 𝔭 => by rw [logNorm_norm_artinTerm]; exact logNorm_absNorm_rpow_neg_le_half 𝔭.1 hs
  have hbound : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      ‖artinEulerFactor (K := K) (L := L) χ s 𝔭.1 - 1‖
        ≤ 2 * ‖logNorm_artinTerm (K := K) (L := L) χ s 𝔭.1‖ := by
    intro 𝔭
    rw [logNorm_artinEulerFactor_eq_inv]
    exact logNorm_norm_inv_one_sub_sub_one_le (hle 𝔭)
  have hsumb : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ‖artinEulerFactor (K := K) (L := L) χ s 𝔭.1 - 1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      ((logNorm_summable_norm_artinTerm (K := K) (L := L) S χ hs).mul_left 2)
  have hne : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      artinEulerFactor (K := K) (L := L) χ s 𝔭.1 ≠ 0 := by
    intro 𝔭
    rw [logNorm_artinEulerFactor_eq_inv]
    exact logNorm_inv_one_sub_ne_zero (hle 𝔭)
  exact log_norm_tprod_eq_tsum_log_norm hsumb hne

end NK.HeckeL.Series
