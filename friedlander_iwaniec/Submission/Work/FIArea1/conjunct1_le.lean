import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.Helpers
import Submission.Work.FIArea1.conj1_divisor_sum
import Submission.Work.FIArea1.count_annulus
import Submission.Work.FIArea1.noncoprime_count

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary helper: a sum of constant indicator terms -/

/-- `∑_{w ∈ s} (if p w then c else 0) = c · #{w ∈ s : p w}`. -/
lemma conj1_sum_ite_const {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (∑ x ∈ s, (if p x then c else 0)) = c * ((s.filter p).card : ℝ) := by
  have h : (∑ x ∈ s, (if p x then c else 0)) = ∑ x ∈ s, c * (if p x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : p x <;> simp [hp]
  rw [h, ← Finset.mul_sum, Finset.sum_boole]

/-! ## 1. `B* − B` as a double sum over the non-coprime pairs -/

/-- **The difference of the two bilinear forms.**  Removing the coprimality constraint means
dropping exactly the non-coprime pairs:

  `B* − B = Σ_{w ∈ annM} Σ_{z ∈ boxN} (if (w,z) = 1 then 0 else −β_z Z(wz))`. -/
lemma conj1_Bstar_sub_Bfree (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) :
    Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β
      = ∑ w ∈ Work.FITop3.annM Pa, ∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime w z then 0 else -(β z * Work.FITop3.Zc w z)) := by
  rw [Work.FITop3.Bstar, Work.FITop3.Bfree, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases h : Work.FIPlan.GaussCoprime w z <;> simp [h]

/-- **Triangle inequality, `‖Z‖ ≤ 2` and the swap of the two sums.**  The norm of the difference
is at most `Σ_z 2‖β_z‖ · #{w ∈ annM : ¬(w,z) = 1, Z(wz) ≠ 0}`. -/
lemma conj1_norm_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) :
    ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖
      ≤ ∑ z ∈ Work.FITop.boxN Pa, (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ) := by
  rw [conj1_Bstar_sub_Bfree]
  have hsum : (∑ w ∈ Work.FITop3.annM Pa, ∑ z ∈ Work.FITop.boxN Pa,
        (if ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0 then 2 * ‖β z‖ else 0))
      = ∑ z ∈ Work.FITop.boxN Pa, (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z hz => ?_
    exact conj1_sum_ite_const (Work.FITop3.annM Pa)
      (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0) (2 * ‖β z‖)
  rw [← hsum]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun w _hw => norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun w _hw => Finset.sum_le_sum fun z _hz => ?_
  by_cases h1 : Work.FIPlan.GaussCoprime w z
  · have hnot : ¬ (¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0) := by tauto
    rw [if_pos h1, if_neg hnot]
    simp
  · by_cases h2 : Work.FITop3.Zc w z = 0
    · have hnot : ¬ (¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0) := by
        intro hh; exact hh.2 h2
      rw [if_neg h1, if_neg hnot, norm_neg, h2, mul_zero, norm_zero]
    · have hpos : ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0 := ⟨h1, h2⟩
      rw [if_neg h1, if_pos hpos, norm_neg, norm_mul]
      have hle := Zc_norm_le_two w z
      nlinarith [norm_nonneg (β z), norm_nonneg (Work.FITop3.Zc w z)]

/-- `800 · (MN)^{1/4}(1 + √M/(Pz√N)) ≥ 0`, the numerical coefficient of the estimate. -/
lemma conj1_factor_nonneg (Pa : Work.FITop.Params) :
    0 ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
        * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))) := by
  have h1 : (0 : ℝ) ≤ Pa.M := by linarith [Pa.hM1]
  have h2 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h3 : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have : (0 : ℕ) < Pa.Pz := by linarith [Pa.hP2]
    exact_mod_cast this
  have h6 : 0 ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have h7 : 0 ≤ Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N) := by positivity
  have : 0 ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
      * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)) := mul_nonneg h6 (by linarith)
  linarith

/-- **The reduction of (5.10) to the counting bound.**  If for every `z` with `β z ≠ 0` the
number of `w ∈ annM` that are not coprime to `z` and for which `Z(wz) ≠ 0` is at most
`400 (MN)^{1/4}(1+√M/(Pz√N)) ω(|z|²)` (`conjunct1_count`), then

  `‖B* − B‖ ≤ 800 (MN)^{1/4}(1+√M/(Pz√N)) · Σ_{z: β_z ≠ 0} ‖β_z‖ ω(|z|²)`.

(The factor `2` of the triangle inequality and the factor `400` of the count give `800`; `Z(wz) ≠ 0`
implies `Re(wz) = c²`, which is what the counting set of `conjunct1_count` records.) -/
lemma conj1_diff_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hcount : ∀ z : GaussianInt, β z ≠ 0 →
      (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
            * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
    (_hβ : Work.FITop3.IsBetaCoeff Pa φ β) :
    ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖
      ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
        * ∑ z ∈ Work.FITop.boxN Pa,
            (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
  refine (conj1_norm_le Pa β).trans ?_
  have hpt : ∀ z ∈ Work.FITop.boxN Pa,
      (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ)
      ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
    intro z _hz
    have hsub : ((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0))
        ⊆ ((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)) := by
      intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.1, Zc_ne_zero_imp_sq w z hw.2.2⟩
    have hcard : ((((Work.FITop3.annM Pa).filter
            (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
              Work.FITop3.Zc w z ≠ 0)).card : ℝ))
        ≤ ((((Work.FITop3.annM Pa).filter
            (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
              ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsub
    by_cases hz0 : β z = 0
    · simp [hz0]
    · have hnc := hcount z hz0
      rw [if_pos hz0]
      calc (2 * ‖β z‖) * ((((Work.FITop3.annM Pa).filter
              (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ))
          ≤ (2 * ‖β z‖) * (400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
              * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
              * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hcard.trans hnc
        _ = 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
                * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
              * (‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := by ring
  calc ∑ z ∈ Work.FITop.boxN Pa, (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ)
      ≤ ∑ z ∈ Work.FITop.boxN Pa, 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * ∑ z ∈ Work.FITop.boxN Pa,
              (if β z ≠ 0 then
                ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]

/-! ## 2. `β` vanishes for small `N` (the case `N ≤ 4/3`, where `(log N)³` degenerates) -/

/-- `θ ≤ 1`: the smoothing parameter (4.15) is `< 1` because `log x ≥ log 3 > 1` and `A' > 0`. -/
lemma conj1_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by
    have : (0 : ℕ) < Pa.x := by linarith [Pa.hx]
    exact_mod_cast this
  have hx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le hx0]
    have : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by positivity
    linarith [Pa.hA, Pa.hA']
  exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)

/-- **If `N ≤ 4/3` then `β` vanishes identically.**  Indeed `β z ≠ 0` forces `InPolarBox Pa φ z`,
i.e. an *integer* `n = |z|²` with `N < n ≤ (1+θ)N ≤ 2N ≤ 8/3`; as `n ≥ 2` this forces `n = 2`,
which `NoSmallPrimes Pa z` forbids (`2 ≤ Pz`). -/
lemma conj1_beta_eq_zero_of_small_N (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (hN : Pa.N ≤ 4 / 3) : ∀ z, β z = 0 := by
  intro z
  by_contra hz
  obtain ⟨-, hbox, hns⟩ := beta_ne_zero_structure hβ hz
  obtain ⟨-, hNlt, hNle, -, -⟩ := hbox
  have hn2 : 2 ≤ Work.FIPlan.gnorm z := by
    have h1 : (1 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith [Pa.hN1]
    have : (1 : ℕ) < Work.FIPlan.gnorm z := by exact_mod_cast h1
    omega
  have hnle : Work.FIPlan.gnorm z ≤ 2 := by
    have hθ1 := conj1_theta_le_one Pa
    have h2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
      have h3 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [Pa.hN1]
      linarith [hNle, h3]
    have h3 : (Work.FIPlan.gnorm z : ℝ) < 3 := by nlinarith [hN, h2]
    have : Work.FIPlan.gnorm z < 3 := by exact_mod_cast h3
    omega
  have hn : Work.FIPlan.gnorm z = 2 := le_antisymm hnle hn2
  have hcontra := hns 2 Nat.prime_two Pa.hP2
  rw [hn] at hcontra
  exact hcontra dvd_rfl

/-! ## 3. The final real arithmetic of (5.10) -/

/-- `(MN)^{1/4}·N = M^{1/4}N^{5/4}`. -/
lemma conj1_rpow_nat (M N : ℝ) (hM : 0 ≤ M) (hN : 0 < N) :
    (M * N) ^ ((1 : ℝ) / 4) * N = M ^ ((1 : ℝ) / 4) * N ^ ((5 : ℝ) / 4) := by
  rw [Real.mul_rpow hM hN.le]
  have h : N ^ ((1 : ℝ) / 4) * N = N ^ ((5 : ℝ) / 4) := by
    nth_rewrite 2 [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    norm_num
  rw [mul_assoc, h]

/-- `(MN)^{1/4}·N·√M/(Pz√N) = Pz^{-1}M^{3/4}N^{3/4}`. -/
lemma conj1_rpow_inv (M N Pz : ℝ) (hM : 0 < M) (hN : 0 < N) :
    (M * N) ^ ((1 : ℝ) / 4) * N * (Real.sqrt M / (Pz * Real.sqrt N))
      = Pz⁻¹ * M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) := by
  rw [Real.mul_rpow hM.le hN.le, Real.sqrt_eq_rpow M, Real.sqrt_eq_rpow N]
  have hM' : M ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 2) = M ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hM]; norm_num
  have hN' : N ^ ((1 : ℝ) / 4) * N / N ^ ((1 : ℝ) / 2) = N ^ ((3 : ℝ) / 4) := by
    have h1 : N ^ ((1 : ℝ) / 4) * N = N ^ ((5 : ℝ) / 4) := by
      nth_rewrite 2 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]
      norm_num
    rw [h1, ← Real.rpow_sub hN]
    norm_num
  rw [show (M ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4)) * N
        * (M ^ ((1 : ℝ) / 2) / (Pz * N ^ ((1 : ℝ) / 2)))
      = ((M ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 2))
          * (N ^ ((1 : ℝ) / 4) * N / N ^ ((1 : ℝ) / 2))) / Pz from by ring]
  rw [hM', hN']
  ring

/-- **The numerical content of (5.10)**:
`(MN)^{1/4}(1 + √M/(Pz√N))·N·L ≤ (M^{1/4}N^{5/4} + Pz^{-1}M^{3/4}N^{3/4})·L` for `L ≥ 0`. -/
lemma conj1_arith (M N Pz L : ℝ) (hM : 0 < M) (hN : 0 < N) (_hL : 0 ≤ L) :
    (M * N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt M / (Pz * Real.sqrt N)) * N * L
      ≤ (M ^ ((1 : ℝ) / 4) * N ^ ((5 : ℝ) / 4)
          + Pz⁻¹ * M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) * L := by
  have h1 := conj1_rpow_nat M N hM.le hN
  have h2 := conj1_rpow_inv M N Pz hM hN
  calc (M * N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt M / (Pz * Real.sqrt N)) * N * L
      = ((M * N) ^ ((1 : ℝ) / 4) * N
          + (M * N) ^ ((1 : ℝ) / 4) * N * (Real.sqrt M / (Pz * Real.sqrt N))) * L := by ring
    _ ≤ (M ^ ((1 : ℝ) / 4) * N ^ ((5 : ℝ) / 4)
          + Pz⁻¹ * M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) * L := le_of_eq (by rw [h2, h1])


/-! ## 4. The divisor/`ω` sum: `Σ_z [β_z ≠ 0] ‖β_z‖ ω(|z|²) ≤ C N (log N)³`

This is the quantitative heart of (5.10).  `‖β_z‖ ≤ τ(|z|²)` (`norm_beta_le_divisors_card`) and
`ω(|z|²) ≤ log₂(2·radN²)` (`Helpers.card_primeFactors_le_log_of_le`, `conj1_gnorm_le_boxN`), while
`sum_tau_gnorm` bounds `Σ_{z ∈ boxN} τ(|z|²)` by `C₀ (radN²+1)(log(radN+2))²`; the elementary
comparisons `radN ≤ 4√N`, `log(radN+2) ≤ 6N`, `log(6N) ≤ 21 log N`, `log(32N)/log 2 ≤ 250 log N`
(for `N > 4/3`; the constants are crude but absolute) then give `C N (log N)³`. -/

/-- `exp(1/4) ≤ 4/3`. -/
lemma conj1_exp_quarter_le : Real.exp (1/4 : ℝ) ≤ 4/3 := by
  have h4 : Real.exp (1/4 : ℝ) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have hlt : Real.exp (1/4 : ℝ) ^ 4 ≤ (4/3 : ℝ) ^ 4 := by
    rw [h4]
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h2 : (3:ℝ) ≤ (4/3 : ℝ) ^ 4 := by norm_num
    linarith
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (4:ℕ) ≠ 0)).mp hlt

/-- `exp(1/2) ≤ 2`. -/
lemma conj1_exp_half_le : Real.exp (1/2 : ℝ) ≤ 2 := by
  have h4 : Real.exp (1/2 : ℝ) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have hlt : Real.exp (1/2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    rw [h4]
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    norm_num
    linarith
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (2:ℕ) ≠ 0)).mp hlt

/-- `log 2 ≥ 1/2`. -/
lemma conj1_log_two_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]; exact conj1_exp_half_le

/-- `1/4 ≤ log N` for `N > 4/3` (so that every `log (cN)` is comparable with `log N` with an
*explicit* constant). -/
lemma conj1_log_ge_quarter {N : ℝ} (hN : 4/3 < N) : (1/4 : ℝ) ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact le_trans conj1_exp_quarter_le (le_of_lt hN)

/-- `log (cN) ≤ (4(c-1)+1) log N` for `c ≥ 1`, `N > 4/3`. -/
lemma conj1_log_mul_le {c N : ℝ} (hc : 1 ≤ c) (hN : 4/3 < N) :
    Real.log (c * N) ≤ (4 * (c - 1) + 1) * Real.log N := by
  have hN0 : 0 < N := by linarith
  have hc0 : 0 < c := by linarith
  have hlogN : (1/4 : ℝ) ≤ Real.log N := conj1_log_ge_quarter hN
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  rw [Real.log_mul hc0.ne' hN0.ne']
  have h1 : (0:ℝ) ≤ c - 1 := by linarith
  have h2 : (c - 1) * (1/4) ≤ (c - 1) * Real.log N := mul_le_mul_of_nonneg_left hlogN h1
  linarith

/-- **The box bound on the norm**: `z ∈ boxN Pa` has `|z|² ≤ 2·⌈√(4N)⌉₊²` (a point of the box
`[-R,R]² ⊆ ℂ` has `|z|² = r² + s² ≤ 2R²`). -/
lemma conj1_gnorm_le_boxN {Pa : Work.FITop.Params} {z : GaussianInt}
    (hz : z ∈ Work.FITop.boxN Pa) :
    (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ)) ^ 2 := by
  have hz' : z ∈ Work.FIPlan.gBox (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℤ)) := hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz'
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hc, hd⟩ := Finset.mem_Icc.mp hp2
  have ha' : -(((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast ha
  have hb' : (p.1 : ℝ) ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) := by exact_mod_cast hb
  have hc' : -(((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hc
  have hd' : (p.2 : ℝ) ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) := by exact_mod_cast hd
  have h1 : (p.1 : ℝ) ^ 2 ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ)) ^ 2 := by
    have habs : |(p.1 : ℝ)| ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) := abs_le.mpr ⟨ha', hb'⟩
    have := pow_le_pow_left₀ (abs_nonneg (p.1:ℝ)) habs 2
    rwa [sq_abs] at this
  have h2 : (p.2 : ℝ) ^ 2 ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ)) ^ 2 := by
    have habs : |(p.2 : ℝ)| ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) := abs_le.mpr ⟨hc', hd'⟩
    have := pow_le_pow_left₀ (abs_nonneg (p.2:ℝ)) habs 2
    rwa [sq_abs] at this
  have hgi : (Work.FIPlan.gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ)
      = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    have h := gnorm_int (⟨p.1, p.2⟩ : GaussianInt)
    have h' : (Work.FIPlan.gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℤ) = p.1 ^ 2 + p.2 ^ 2 := by simpa using h
    exact_mod_cast h'
  rw [hgi]; linarith

/-- `⌈√(4N)⌉₊ ≤ 4√N` for `N ≥ 1`. -/
lemma conj1_radN_le (Pa : Work.FITop.Params) :
    ((((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ)) ≤ 4 * Real.sqrt Pa.N := by
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hsqrt : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4:ℝ) * Pa.N = (2 * Real.sqrt Pa.N)^2 by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; ring]
    exact Real.sqrt_sq (by positivity)
  have h : (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) < Real.sqrt (4 * Pa.N) + 1 := by
    have := Nat.ceil_lt_add_one (a := Real.sqrt (4 * Pa.N)) (by positivity)
    simpa using this
  have h2 : (1:ℝ) ≤ Real.sqrt Pa.N := by
    have : Real.sqrt 1 ≤ Real.sqrt Pa.N := Real.sqrt_le_sqrt hN1
    simpa using this
  linarith

/-- **The divisor/`ω` sum of *FI* (5.10)**: for every coefficient `β` of (4.13)+(5.13) and every
`N > 4/3`, `Σ_{z ∈ boxN} [β z ≠ 0] ‖β z‖ ω(|z|²) ≤ C N (log N)³`, `C` absolute. -/
lemma conj1_sum_bound_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      (4 / 3 : ℝ) < Pa.N → Work.FITop3.IsBetaCoeff Pa φ β →
      (∑ z ∈ Work.FITop.boxN Pa,
          (if β z ≠ 0 then
            ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
        ≤ C * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := conj1_divisor_sum
  refine ⟨2000000 * C₀, by positivity, ?_⟩
  intro Pa φ β hN hβ
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := by linarith
  have hlogN : (1/4 : ℝ) ≤ Real.log Pa.N := conj1_log_ge_quarter hN
  have hlogN0 : (0:ℝ) ≤ Real.log Pa.N := by linarith
  rw [Work.FITop.boxN, Work.FITop.radN]
  set R : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hRdef
  have hRle : ((R:ℝ)) ≤ 4 * Real.sqrt Pa.N := by
    have h := conj1_radN_le Pa
    simpa [hRdef] using h
  have hτ := hC₀ (R : ℤ) (Int.natCast_nonneg R)
  have hτR : (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2) := by
    have := hτ
    simpa [Int.natAbs_natCast] using this
  have hgnorm : ∀ z ∈ Work.FIPlan.gBox (R : ℤ), Work.FIPlan.gnorm z ≤ 2 * R ^ 2 := by
    intro z hz
    have hcast : ((2 * R ^ 2 : ℕ) : ℝ) = 2 * (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ^ 2 := by
      rw [hRdef]; push_cast; ring
    have hle : (Work.FIPlan.gnorm z : ℝ) ≤ ((2 * R ^ 2 : ℕ) : ℝ) := by
      rw [hcast]
      exact conj1_gnorm_le_boxN hz
    exact_mod_cast hle
  have hpt : ∀ z ∈ Work.FIPlan.gBox (R : ℤ),
      (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0)
        ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    intro z hz
    by_cases hz0 : β z = 0
    · simp only [hz0, ne_eq, not_true_eq_false, reduceIte]
      positivity
    · rw [if_pos hz0]
      have hnorm := norm_beta_le_divisors_card hβ z
      have homega : (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) := by
        obtain ⟨-, hbox, -⟩ := beta_ne_zero_structure hβ hz0
        have h1 : 1 ≤ Work.FIPlan.gnorm z := by
          have h2 : (1:ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by
            have h3 := hbox.2.1
            linarith
          exact_mod_cast h2
        exact_mod_cast card_primeFactors_le_log_of_le h1 (hgnorm z hz)
      calc ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hnorm (by positivity)
        _ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left homega (by positivity)
        _ = ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
  have hL0 : (0:ℝ) ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) := by positivity
  have hmain : (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
      ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
          * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) := by
    calc _ ≤ ∑ z ∈ Work.FIPlan.gBox (R : ℤ),
            ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Finset.sum_le_sum hpt
      _ = ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * ∑ z ∈ Work.FIPlan.gBox (R : ℤ),
                (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hτR hL0
  have hsqN : (Real.sqrt Pa.N)^2 = Pa.N := Real.sq_sqrt (by linarith)
  have hA2 : ((R:ℝ)) ^ 2 ≤ 16 * Pa.N := by
    nlinarith [hRle, hsqN, Real.sqrt_nonneg Pa.N]
  have hR17 : ((R:ℝ) ^ 2 + 1) ≤ 17 * Pa.N := by nlinarith [hA2, hN1]
  have hlogR : Real.log ((R:ℝ) + 2) ≤ 21 * Real.log Pa.N := by
    have hsle : Real.sqrt Pa.N ≤ Pa.N := by
      have h1 : Pa.N ≤ Pa.N * Pa.N := by nlinarith [hN1]
      calc Real.sqrt Pa.N ≤ Real.sqrt (Pa.N * Pa.N) := Real.sqrt_le_sqrt h1
        _ = Pa.N := Real.sqrt_mul_self (by linarith)
    have h6N : (R:ℝ) + 2 ≤ 6 * Pa.N := by nlinarith [hRle, hsle]
    have h0 : 0 < (R:ℝ) + 2 := by positivity
    refine (Real.log_le_log h0 h6N).trans ?_
    have h6 := conj1_log_mul_le (c := 6) (N := Pa.N) (by norm_num) hN
    rwa [show (4 * ((6:ℝ) - 1) + 1) = 21 by norm_num] at h6
  have hL' : ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) ≤ 250 * Real.log Pa.N := by
    have hm : 1 ≤ 2 * R ^ 2 := by
      have : 1 ≤ R := by
        have h1 : (2:ℝ) ≤ ((R:ℕ) : ℝ) := by
          have h2 : (2:ℝ) ≤ Real.sqrt (4 * Pa.N) := by
            rw [show (4:ℝ) * Pa.N = (2 * Real.sqrt Pa.N)^2 by
              rw [mul_pow, Real.sq_sqrt (by linarith)]; ring, Real.sqrt_sq (by positivity)]
            have h3 := Real.sqrt_le_sqrt hN1
            simp only [Real.sqrt_one] at h3
            linarith
          exact le_trans h2 (Nat.le_ceil _)
        have h1' : (1:ℝ) ≤ ((R:ℕ) : ℝ) := by linarith
        exact_mod_cast h1'
      nlinarith
    have h2 := cast_log_le_log_div (2 * R ^ 2) hm
    have h3 : Real.log (((2 * R ^ 2 : ℕ)) : ℝ) ≤ Real.log (32 * Pa.N) := by
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith [hRle, hsqN, Real.sqrt_nonneg Pa.N]
    have h4 : Real.log (32 * Pa.N) ≤ 125 * Real.log Pa.N := by
      have h32 := conj1_log_mul_le (c := 32) (N := Pa.N) (by norm_num) hN
      rwa [show (4 * ((32:ℝ) - 1) + 1) = 125 by norm_num] at h32
    have h5 : Real.log (32 * Pa.N) / Real.log 2 ≤ 250 * Real.log Pa.N := by
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := conj1_log_two_ge_half
      rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
      have hstep : Real.log Pa.N ≤ 2 * Real.log 2 * Real.log Pa.N := by
        nlinarith [mul_le_mul_of_nonneg_right hlog2 hlogN0]
      linarith [h4, hstep]
    have h3' : Real.log (((2 * R ^ 2 : ℕ)) : ℝ) / Real.log 2
        ≤ Real.log (32 * Pa.N) / Real.log 2 :=
      div_le_div_of_nonneg_right h3 (by linarith [conj1_log_two_ge_half])
    linarith [h2, h3', h5]
  have hY2 : (Real.log ((R:ℝ) + 2)) ^ 2 ≤ 441 * (Real.log Pa.N) ^ 2 := by
    have hY0 : 0 ≤ Real.log ((R:ℝ) + 2) := by
      apply Real.log_nonneg
      have h : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
      linarith
    have hsq := pow_le_pow_left₀ hY0 hlogR 2
    have h21 : ((21:ℝ) * Real.log Pa.N)^2 = 441 * (Real.log Pa.N)^2 := by ring
    rwa [h21] at hsq
  have hstep1 : ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
        * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2))
      ≤ (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2))) := by
    apply mul_le_mul hL' _ (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀pos.le
    exact mul_le_mul hR17 hY2 (by positivity) (by positivity)
  have hstep2 : (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2)))
      = 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := by ring
  have hstep3 : 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3
      ≤ 2000000 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := by
    have h1 : 0 ≤ C₀ * Pa.N * (Real.log Pa.N) ^ 3 :=
      mul_nonneg (mul_nonneg hC₀pos.le (by linarith)) (pow_nonneg hlogN0 3)
    nlinarith
  calc (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
      ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
          * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) := hmain
    _ ≤ (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2))) := hstep1
    _ = 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := hstep2
    _ ≤ 2000000 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := hstep3

/-! ## 5. The first conjunct of *FI* (5.10) -/

end

end Work.FIArea1
