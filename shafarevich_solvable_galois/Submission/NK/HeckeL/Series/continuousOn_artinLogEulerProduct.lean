import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter

noncomputable section

namespace NK.HeckeL.Series

/-! ## Preparatory estimates -/

/-- A nonzero prime ideal of the ring of integers of a number field has absolute norm at least
`2`. -/
lemma two_le_absNorm_primeIdeal {K : Type*} [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h =>
    𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h =>
    𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- The modulus of a character value times a prime power: `‖χ(𝔭) N𝔭^{-s}‖ ≤ N𝔭^{-c}` for
`1 < c ≤ s`, `N𝔭 ≥ 2` and `‖χ(𝔭)‖ ≤ 1`. -/
lemma norm_mul_rpow_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c ≤ s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ n ^ (-c) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ = ‖a‖ * n ^ (-s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  rw [hnorm]
  calc ‖a‖ * n ^ (-s) ≤ 1 * n ^ (-s) := by gcongr
    _ = n ^ (-s) := one_mul _
    _ ≤ n ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- The same bound, strict, for `s > c > 1`. -/
lemma norm_mul_rpow_lt_half {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ < 1 / 2 := by
  refine lt_of_le_of_lt (norm_mul_rpow_le hn a ha hc hcs.le) ?_
  have h1 : n ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
  have h2 : (2 : ℝ) ^ (-c) < 1 / 2 := by
    have h3 := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num)).mpr
      (show (-c : ℝ) < (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one] at h3
    have h4 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  linarith

/-- The logarithmic Euler factor at a single prime is bounded by `(3/2) * N𝔭^{-c}` on
`(c, ∞)`, for `c > 1`. -/
lemma norm_neg_log_one_sub_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) :
    ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤ (3 / 2) * n ^ (-c) := by
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ 1 / 2 :=
    (norm_mul_rpow_lt_half hn a ha hc hcs).le
  have hlog : ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤
      (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := by
    have h1 := Complex.norm_log_one_add_half_le_self
      (z := -(a * ((n ^ (-s) : ℝ) : ℂ))) (by rw [norm_neg]; exact hnorm)
    rwa [← sub_eq_add_neg, norm_neg] at h1
  calc ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖
      = ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ := norm_neg _
    _ ≤ (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := hlog
    _ ≤ (3 / 2) * n ^ (-c) := by
        gcongr
        exact norm_mul_rpow_le hn a ha hc hcs.le

/-- Continuity of a single logarithmic Euler factor on `(s₀, ∞)` for `s₀ > 1`. -/
lemma continuousOn_logEulerTerm (n : ℝ) (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {s₀ : ℝ}
    (hs₀ : 1 < s₀) :
    ContinuousOn (fun s : ℝ => -Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))) (Set.Ioi s₀) := by
  have hnpos : n ≠ 0 := by linarith
  have hcont : ContinuousOn (fun s : ℝ => 1 - a * ((n ^ (-s) : ℝ) : ℂ)) (Set.Ioi s₀) :=
    (continuous_const.sub (continuous_const.mul <|
      Complex.continuous_ofReal.comp <|
        (Real.continuous_const_rpow hnpos).comp continuous_neg)).continuousOn
  refine (hcont.clog fun s hs => ?_).neg
  have hlt : ‖-(a * ((n ^ (-s) : ℝ) : ℂ))‖ < 1 := by
    rw [norm_neg]
    exact lt_of_lt_of_le (norm_mul_rpow_lt_half hn a ha hs₀ hs) (by norm_num)
  have := Complex.mem_slitPlane_of_norm_lt_one hlt
  simpa [sub_eq_add_neg] using this

/-! ## Continuity of the logarithmic Euler product -/

theorem continuousOn_artinLogEulerProduct {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi 1) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  have hnorm_one : ∀ g : Gal(L/K), ‖(χ g : ℂ)‖ = 1 := fun g =>
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g
  have key : ∀ c : ℝ, 1 < c →
      ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi c) := by
    intro c hc
    simp only [NK.HeckeL.artinLogEulerProduct]
    refine continuousOn_tsum
      (u := fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        (3 / 2) * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-c)) ?_ ?_ ?_
    · intro 𝔭
      refine continuousOn_logEulerTerm (Ideal.absNorm 𝔭.1.asIdeal : ℝ)
        (by exact_mod_cast two_le_absNorm_primeIdeal 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc
    · have hsum : Summable (fun 𝔭 : NK.HeckeL.PrimeIdeal K =>
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-c)) :=
        Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hc
      exact (hsum.mul_left (3 / 2)).subtype (fun 𝔭 => 𝔭 ∉ S)
    · intro 𝔭 s hs
      exact norm_neg_log_one_sub_le (by exact_mod_cast two_le_absNorm_primeIdeal 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc hs
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨c, h1c, hcx⟩ := exists_between (show (1 : ℝ) < x from hx)
  exact ⟨Set.Ioi c, isOpen_Ioi, hcx, by
    rw [Set.Ioi_inter_Ioi, max_eq_right h1c.le]
    exact key c h1c⟩

end NK.HeckeL.Series
