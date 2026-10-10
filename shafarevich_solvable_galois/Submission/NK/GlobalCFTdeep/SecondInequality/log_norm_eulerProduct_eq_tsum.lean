import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace NK.GlobalCFTdeep.SecondInequality

/-!
# The logarithm of the Euler product is the sum of the logarithms of its factors

`log ‖∏' 𝔭, (1 - χ(b 𝔭) N𝔭^{-s})⁻¹‖ = ∑' 𝔭, -log ‖1 - χ(b 𝔭) N𝔭^{-s}‖`
over the primes `𝔭 ∉ S`, for `s > 1`.

The infinite product converges because the factors are `1 + o(1)` with
`∑_𝔭 ‖χ(b 𝔭) N𝔭^{-s}‖ = ∑_𝔭 N𝔭^{-s} < ∞` (`s > 1`), the values of the character `χ` of the
finite group `B` all have norm `1`, and `N𝔭 ≥ 2` forces `N𝔭^{-s} ≤ 1/2` so that
`‖(1 - z)⁻¹ - 1‖ ≤ 2 ‖z‖`.  The generic product-logarithm identity is
`NK.HeckeL.Series.log_norm_tprod_eq_tsum_log_norm`.
-/

variable {K : Type*} [Field K] [NumberField K]

/-- The norm of the prime term `χ(b 𝔭) N𝔭^{-s}` is the prime weight `N𝔭^{-s}`: the character of
the finite group `B` takes values of norm `1`. -/
theorem norm_primeTerm {B : Type*} [Group B] [Finite B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ)
    (s : ℝ) (𝔭 : PrimeIdeal K) : ‖primeTerm b χ s 𝔭‖ = primeWeight s 𝔭 := by
  rw [primeTerm_def, norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ _, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (primeWeight_nonneg s 𝔭)]

/-- A prime ideal of `𝓞 K` has absolute norm at least `2`. -/
theorem two_le_absNorm (𝔭 : PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr 𝔭.isPrime.ne_top
  omega

/-- For `s > 1` and a prime ideal `𝔭`, the prime weight satisfies `N𝔭^{-s} ≤ 1/2`. -/
theorem primeWeight_le_half (𝔭 : PrimeIdeal K) {s : ℝ} (hs : 1 < s) :
    primeWeight s 𝔭 ≤ 1 / 2 := by
  rw [primeWeight_def]
  have hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast two_le_absNorm 𝔭
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 2 ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)
    _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The negative logarithm of the norm of the prime term is the logarithm of the norm of the
Euler factor. -/
theorem negLogEulerFactor_eq_log_norm_eulerFactor {B : Type*} [Monoid B] (b : PrimeIdeal K → B)
    (χ : B →* ℂˣ) (s : ℝ) (𝔭 : PrimeIdeal K) :
    negLogEulerFactor b χ s 𝔭 = Real.log ‖eulerFactor b χ s 𝔭‖ := by
  rw [negLogEulerFactor_def, eulerFactor_def, norm_inv, Real.log_inv]

/-- For `s > 1` the Euler factor `(1 - χ(b 𝔭) N𝔭^{-s})⁻¹` does not vanish. -/
theorem eulerFactor_ne_zero {B : Type*} [Group B] [Finite B] (b : PrimeIdeal K → B)
    (χ : B →* ℂˣ) {s : ℝ} (hs : 1 < s) (𝔭 : PrimeIdeal K) :
    eulerFactor b χ s 𝔭 ≠ 0 := by
  rw [eulerFactor_def]
  exact NK.HeckeL.Series.logNorm_inv_one_sub_ne_zero
    (by rw [norm_primeTerm]; exact primeWeight_le_half 𝔭 hs)

/-- For `s > 1` the differences `‖eulerFactor b χ s 𝔭 - 1‖` over the primes outside `S` are
summable: they are dominated by `2 · N𝔭^{-s}` and `∑_𝔭 N𝔭^{-s}` converges. -/
theorem summable_norm_eulerFactor_sub_one {B : Type*} [Group B] [Finite B]
    (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K)) (χ : B →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => ‖eulerFactor b χ s 𝔭.1 - 1‖) := by
  have hbase : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => ‖primeTerm b χ s 𝔭.1‖) := by
    have h := (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype
      (fun 𝔭 : PrimeIdeal K => 𝔭 ∉ S)
    exact h.congr (fun 𝔭 => (norm_primeTerm b χ s 𝔭.1).symm)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun 𝔭 => ?_) (hbase.mul_left 2)
  rw [eulerFactor_def]
  exact NK.HeckeL.Series.logNorm_norm_inv_one_sub_sub_one_le
    (by rw [norm_primeTerm]; exact primeWeight_le_half 𝔭.1 hs)

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.log_norm_eulerProduct_eq_tsum`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs` (which defines `primeWeight`,
-- `primeTerm`, `eulerFactor`, `eulerProduct`, `negLogEulerFactor`).
--
-- The generic lemma `NK.HeckeL.Series.log_norm_tprod_eq_tsum_log_norm` in the workspace proves
-- `Real.log ‖∏' i, f i‖ = ∑' i, Real.log ‖f i‖` for `Summable (fun i => ‖f i - 1‖)` and nonzero
-- factors; and `NK.Chebotarev.norm_monoidHom_units_apply_eq_one` gives `‖χ g‖ = 1` for finite
-- groups.  `Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum` gives
-- `Summable (fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))` for `1 < s`.
theorem log_norm_eulerProduct_eq_tsum {K : Type*} [Field K] [NumberField K] {B : Type*} [Group B]
    [Finite B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K)) (χ : B →* ℂˣ) {s : ℝ}
    (hs : 1 < s) :
    Real.log ‖eulerProduct b S χ s‖ =
      ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, negLogEulerFactor b χ s 𝔭.1 := by
  rw [eulerProduct_def]
  rw [NK.HeckeL.Series.log_norm_tprod_eq_tsum_log_norm
    (f := fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => eulerFactor b χ s 𝔭.1)
    (summable_norm_eulerFactor_sub_one b S χ hs)
    (fun 𝔭 => eulerFactor_ne_zero b χ hs 𝔭.1)]
  exact tsum_congr fun 𝔭 => (negLogEulerFactor_eq_log_norm_eulerFactor b χ s 𝔭.1).symm

end NK.GlobalCFTdeep.SecondInequality
