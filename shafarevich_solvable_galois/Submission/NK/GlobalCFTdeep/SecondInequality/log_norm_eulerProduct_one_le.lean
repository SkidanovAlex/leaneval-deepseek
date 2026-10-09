import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

namespace NK.GlobalCFTdeep.SecondInequality

open NK.HeckeL

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.log_norm_eulerProduct_one_le`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs` (and hence `NK.HeckeL.All`).
--
-- The trivial character of `B` gives the classical Euler product
-- `eulerProduct b S 1 s = ∏'_{𝔭 ∉ S} (1 - N𝔭^{-s})⁻¹`, whose logarithm grows like
-- `log (1/(s-1))`.  The route taken here is:
--
-- * `log ‖eulerProduct b S 1 s‖ = ∑'_{𝔭 ∉ S} -log (1 - N𝔭^{-s})` for `s > 1`, via the generic
--   `NK.HeckeL.Series.log_norm_tprod_eq_tsum_log_norm` (the factors are `1 + O(N𝔭^{-s})` and
--   `∑ N𝔭^{-s} < ∞`); note that for `χ = 1` no finiteness of `B` is needed, only multiplicativity;
-- * every term is nonnegative, so dropping the finitely many primes in `S` only decreases the sum:
--   `∑'_{𝔭 ∉ S} ≤ ∑'_𝔭` (`Summable.sum_add_tsum_compl`);
-- * `∑'_𝔭 -log (1 - N𝔭^{-s}) = log ζ_K(s)`
--   (`Commons.NumberField.DedekindZeta.log_eulerProduct_primeIdeal`);
-- * `log ζ_K(s) + log (s-1) → log Res_{s=1} ζ_K`
--   (`Commons.NumberField.DedekindZeta.tendsto_log_add_log_sub_one`), i.e.
--   `log ζ_K(s) ≤ log (1/(s-1)) + C` eventually near `1⁺`.

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero prime ideal of `𝓞 K` has absolute norm at least `2`. -/
theorem primeIdeal_two_le_absNorm (𝔭 : PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr 𝔭.isPrime.ne_top
  omega

/-- For `s > 1` the weight `N𝔭^{-s}` of a prime ideal is at most `1/2`. -/
theorem primeWeight_le_half_of_one_lt (𝔭 : PrimeIdeal K) {s : ℝ} (hs : 1 < s) :
    primeWeight s 𝔭 ≤ 1 / 2 := by
  rw [primeWeight_def]
  have hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast primeIdeal_two_le_absNorm 𝔭
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 2 ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)
    _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The Euler factor of the trivial character is the classical factor `(1 - N𝔭^{-s})⁻¹`. -/
theorem eulerFactor_one_eq_inv {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (s : ℝ)
    (𝔭 : PrimeIdeal K) :
    eulerFactor b 1 s 𝔭 = (1 - ((primeWeight s 𝔭 : ℝ) : ℂ))⁻¹ := by
  rw [eulerFactor_def, primeTerm_def, MonoidHom.one_apply, Units.val_one, one_mul]

/-- **The logarithm of the Euler product of the trivial character** is the sum of
`-log (1 - N𝔭^{-s})` over the primes outside `S`, for `s > 1`. -/
theorem log_norm_eulerProduct_one_eq_tsum {B : Type*} [Monoid B] (b : PrimeIdeal K → B)
    (S : Finset (PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    Real.log ‖eulerProduct b S 1 s‖ =
      ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, -Real.log (1 - primeWeight (K := K) s 𝔭.1) := by
  have hnorm : ∀ 𝔭 : PrimeIdeal K, ‖(((primeWeight (K := K) s 𝔭 : ℝ)) : ℂ)‖ =
      primeWeight (K := K) s 𝔭 :=
    fun 𝔭 => by rw [Complex.norm_real, Real.norm_of_nonneg (primeWeight_nonneg (K := K) s 𝔭)]
  have hsumm : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ‖eulerFactor b 1 s 𝔭.1 - 1‖) := by
    have hbase : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
        primeWeight (K := K) s 𝔭.1) := by
      have h := (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
        (K := K) hs).subtype (fun 𝔭 : PrimeIdeal K => 𝔭 ∉ S)
      exact h.congr (fun 𝔭 => (primeWeight_def s 𝔭.1))
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun 𝔭 => ?_) (hbase.mul_left 2)
    rw [eulerFactor_one_eq_inv]
    have h := NK.HeckeL.Series.logNorm_norm_inv_one_sub_sub_one_le
      (z := ((primeWeight (K := K) s 𝔭.1 : ℝ) : ℂ)) ?_
    · rwa [hnorm 𝔭.1] at h
    · rw [hnorm 𝔭.1]; exact primeWeight_le_half_of_one_lt 𝔭.1 hs
  have hne : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, eulerFactor b 1 s 𝔭.1 ≠ 0 := by
    intro 𝔭
    rw [eulerFactor_one_eq_inv]
    exact NK.HeckeL.Series.logNorm_inv_one_sub_ne_zero
      (by rw [hnorm 𝔭.1]; exact primeWeight_le_half_of_one_lt 𝔭.1 hs)
  rw [eulerProduct_def, NK.HeckeL.Series.log_norm_tprod_eq_tsum_log_norm hsumm hne]
  refine tsum_congr fun 𝔭 => ?_
  rw [eulerFactor_one_eq_inv, norm_inv, Real.log_inv]
  congr 1
  rw [show (1 : ℂ) - ((primeWeight (K := K) s 𝔭.1 : ℝ) : ℂ)
      = ((1 - primeWeight (K := K) s 𝔭.1 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  linarith [primeWeight_le_half_of_one_lt 𝔭.1 hs]

/-- The logarithmic Dedekind-zeta bound: `log ζ_K(s) ≤ log (1/(s-1)) + C` eventually at `1⁺`. -/
theorem exists_eventually_log_dedekindZeta_re_le :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) ≤ Real.log (1 / (s - 1)) + C := by
  refine ⟨|Real.log (NumberField.dedekindZeta_residue K)| + 1, ?_⟩
  have ht := Commons.NumberTheory.NumberField.DedekindZeta.tendsto_log_add_log_sub_one K
  have hev : ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1)
        < Real.log (NumberField.dedekindZeta_residue K) + 1 :=
    ht.eventually (eventually_lt_nhds (lt_add_one _))
  filter_upwards [hev, self_mem_nhdsWithin] with s _ hs
  have hlog : Real.log (1 / (s - 1)) = -Real.log (s - 1) := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  have := le_abs_self (Real.log (NumberField.dedekindZeta_residue K))
  linarith

theorem log_norm_eulerProduct_one_le {K : Type*} [Field K] [NumberField K] {B : Type*} [Monoid B]
    (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Real.log ‖eulerProduct b S 1 s‖ ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, hC₁⟩ := exists_eventually_log_dedekindZeta_re_le (K := K)
  refine ⟨C₁, ?_⟩
  filter_upwards [hC₁, self_mem_nhdsWithin] with s hC hs
  have hs1 : 1 < s := Set.mem_Ioi.mp hs
  have hbridge : (∑' x : ↑(((S : Set (PrimeIdeal K))ᶜ) : Set (PrimeIdeal K)),
        -Real.log (1 - primeWeight (K := K) s ↑x))
      = ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          -Real.log (1 - primeWeight (K := K) s 𝔭.1) := rfl
  have hsumm : Summable (fun 𝔭 : PrimeIdeal K => -Real.log (1 - primeWeight (K := K) s 𝔭)) :=
    (Commons.NumberTheory.NumberField.DedekindZeta.summable_log_one_sub_primeIdeal
      (K := K) hs1).congr (fun 𝔭 => by rw [primeWeight_def])
  have hsplit := hsumm.sum_add_tsum_compl (s := S)
  have hnonneg : 0 ≤ ∑ x ∈ S, -Real.log (1 - primeWeight (K := K) s x) :=
    Finset.sum_nonneg fun x _ => by
      exact neg_nonneg.mpr
        (Real.log_nonpos (by linarith [primeWeight_le_half_of_one_lt x hs1])
          (by linarith [primeWeight_nonneg (K := K) s x]))
  have hle : (∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
        -Real.log (1 - primeWeight (K := K) s 𝔭.1))
      ≤ ∑' 𝔭 : PrimeIdeal K, -Real.log (1 - primeWeight (K := K) s 𝔭) := by
    rw [← hbridge]
    calc (∑' x : ↑(((S : Set (PrimeIdeal K))ᶜ) : Set (PrimeIdeal K)),
          -Real.log (1 - primeWeight (K := K) s ↑x))
        ≤ ∑ x ∈ S, -Real.log (1 - primeWeight (K := K) s x)
            + ∑' x : ↑(((S : Set (PrimeIdeal K))ᶜ) : Set (PrimeIdeal K)),
                -Real.log (1 - primeWeight (K := K) s ↑x) := le_add_of_nonneg_left hnonneg
      _ = ∑' x : PrimeIdeal K, -Real.log (1 - primeWeight (K := K) s x) := hsplit
  have hz : (∑' 𝔭 : PrimeIdeal K, -Real.log (1 - primeWeight (K := K) s 𝔭))
      = Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) := by
    rw [← Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal K hs1]
    exact tsum_congr fun 𝔭 => by rw [primeWeight_def]
  calc Real.log ‖eulerProduct b S 1 s‖
      = ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          -Real.log (1 - primeWeight (K := K) s 𝔭.1) :=
        log_norm_eulerProduct_one_eq_tsum b S hs1
    _ ≤ ∑' 𝔭 : PrimeIdeal K, -Real.log (1 - primeWeight (K := K) s 𝔭) := hle
    _ = Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) := hz
    _ ≤ Real.log (1 / (s - 1)) + C₁ := hC

end NK.GlobalCFTdeep.SecondInequality
