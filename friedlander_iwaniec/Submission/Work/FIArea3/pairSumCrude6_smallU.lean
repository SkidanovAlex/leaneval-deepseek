import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.box_card_le
import Submission.Work.FIArea3.tau_le_log_pz_rough
import Submission.Work.FIArea3.loglog_x_gt_eighteen
import Submission.Work.FIArea3.tau_card_le_half_loglog
import Submission.Work.FIArea3.smallU_w_ge
import Submission.Work.FIArea3.smallU_budget
import Submission.Work.FIArea3.smallU_final_arith
import Submission.Work.FIArea3.div_log_mono
import Submission.Work.FIArea4.absDelta_le_sector

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary lemmas for the small-`u` pair-sum bound -/

/-- `|Δ(z₁,z₂)| = |Im(z̄₁z₂)| ≤ |z₁|·|z₂| = √|z₁|²·√|z₂|²`. -/
lemma absDelta_cast_le_sqrt_mul (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := by
  have hkey : ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)
      = (((starRingEnd ℂ) (z1 : ℂ)) * (z2 : ℂ)).im := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
      GaussianInt.toComplex_star]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
        rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
    _ = |(((starRingEnd ℂ) (z1 : ℂ)) * (z2 : ℂ)).im| := by rw [hkey]
    _ ≤ ‖((starRingEnd ℂ) (z1 : ℂ)) * (z2 : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by rw [norm_mul, Complex.norm_conj]
    _ = Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := by
        rw [Work.FIArea4.sqrt_gnorm z1, Work.FIArea4.sqrt_gnorm z2]

/-- For `z` in the polar box and free of primes `≤ Pz`: `τ(|z|²) ≤ exp((log N + 1)/467)`.
(All prime factors of `|z|²` exceed `Pz ≥ exp((loglog x)²)`, `loglog x > 18`, and
`|z|² ≤ (1+θ)N ≤ 2N`.) -/
lemma tau_gnorm_le_exp (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : Work.FITop3.InPolarBox Pa φ z) (hnsp : Work.FITop3.NoSmallPrimes Pa z)
    (hu : (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N) :
    ((Work.FIPlan.gnorm z).divisors.card : ℝ)
      ≤ Real.exp ((Real.log (Pa.N : ℝ) + 1) / 467) := by
  set n := Work.FIPlan.gnorm z with hn
  have hn1 : 1 ≤ n := by
    have h : (Pa.N : ℝ) < (n : ℝ) := hz.2.1
    have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
    have : (1 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hτ := tau_le_log_pz_rough hn1 Pa.hP2 hnsp
  have hlogx1 : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) (by exact_mod_cast Pa.hx))
  have hL18 : (18 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) := loglog_x_gt_eighteen Pa hu
  have hLsq : (324 : ℝ) ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := by
    have : (18 : ℝ) ^ 2 ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hL18.le 2
    linarith
  have hlogPz : (324 : ℝ) ≤ Real.log (Pa.Pz : ℝ) := le_trans hLsq Pa.hPlo
  have hθ1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    exact le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hlogx1 (by linarith [Pa.hA, Pa.hA']))
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith [Pa.hN1]
  have hn2N : (n : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    have h := hz.2.2.1; nlinarith
  have hlogn : Real.log (n : ℝ) ≤ Real.log (Pa.N : ℝ) + 1 := by
    have h1 : Real.log (n : ℝ) ≤ Real.log (2 * (Pa.N : ℝ)) :=
      Real.log_le_log (by positivity) hn2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h1
    linarith [Real.log_two_lt_d9]
  have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have hw1 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) + 1 := by
    have : 0 ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg (by linarith [Pa.hN1])
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : Real.log 2 * Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ)
      ≤ (Real.log (Pa.N : ℝ) + 1) / 467 := by
    have h1 : Real.log 2 * Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ)
        ≤ Real.log 2 * (Real.log (Pa.N : ℝ) + 1) / 324 := by
      have ha : Real.log 2 * Real.log (n : ℝ) ≤ Real.log 2 * (Real.log (Pa.N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogn hlog2pos.le
      have hb : Real.log 2 * Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ)
          ≤ Real.log 2 * Real.log (n : ℝ) / 324 :=
        div_le_div_of_nonneg_left (mul_nonneg hlog2pos.le hlogn0) (by norm_num) hlogPz
      have hc : Real.log 2 * Real.log (n : ℝ) / 324
          ≤ Real.log 2 * (Real.log (Pa.N : ℝ) + 1) / 324 :=
        div_le_div_of_nonneg_right ha (by norm_num)
      linarith
    have hlog2le : Real.log 2 ≤ 324 / 467 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 467)]
      nlinarith [Real.log_two_lt_d9]
    have h2 : Real.log 2 * (Real.log (Pa.N : ℝ) + 1) / 324
        ≤ (Real.log (Pa.N : ℝ) + 1) / 467 := by
      calc Real.log 2 * (Real.log (Pa.N : ℝ) + 1) / 324
          ≤ (324 / 467) * (Real.log (Pa.N : ℝ) + 1) / 324 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlog2le hw1) (by norm_num)
        _ = (Real.log (Pa.N : ℝ) + 1) / 467 := by field_simp
    linarith
  have hnpos : (0 : ℝ) < ((n.divisors.card : ℕ) : ℝ) := by
    have : 0 < n.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast this
  exact (Real.log_le_iff_le_exp hnpos).mp (hτ.trans hstep)

/-- For `z₁,z₂` in the polar box: `1 + τ(|Δ(z₁,z₂)|) ≤ exp((3/2)(log N + 1)/log(log N + 1) + 10⁵)`.
(`|Δ| ≤ (1+θ)N ≤ 2N`, and `τ(m) ≤ exp(3/2·log m/loglog m + 10⁴)`, with
`log m/loglog m ≤ (log N + 1)/log(log N + 1)`.) -/
lemma one_add_tau_absDelta_le_exp (Pa : Work.FITop.Params) (φ : ℝ) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hw : (37000000 : ℝ) ≤ Real.log (Pa.N : ℝ)) :
    1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)
      ≤ Real.exp (3 / 2 * (Real.log (Pa.N : ℝ) + 1)
          / Real.log (Real.log (Pa.N : ℝ) + 1) + 10 ^ 5) := by
  set w := Real.log (Pa.N : ℝ) with hwdef
  set m := Work.FIPlan.absDelta z1 z2 with hmdef
  have hw1 : (1 : ℝ) < w + 1 := by rw [hwdef]; linarith
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith [Pa.hN1]
  have hlogx1 : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) (by exact_mod_cast Pa.hx))
  have hθ1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    exact le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hlogx1 (by linarith [Pa.hA, Pa.hA']))
  have hsq : (m : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    have hb := absDelta_cast_le_sqrt_mul z1 z2
    have hg1 : Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
      Real.sqrt_le_sqrt h1.2.2.1
    have hg2 : Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
      Real.sqrt_le_sqrt h2.2.2.1
    have hθN : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
      have := Pa.hθ0; have := hNpos; nlinarith
    have hsq2 : Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N)
        = (1 + Pa.θ) * Pa.N := by
      rw [← sq]; exact Real.sq_sqrt hθN
    rw [hmdef]
    calc (Work.FIPlan.absDelta z1 z2 : ℝ)
        ≤ Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := hb
      _ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
          mul_le_mul hg1 hg2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (1 + Pa.θ) * Pa.N := hsq2
      _ ≤ 2 * Pa.N := by nlinarith
  have hmexp : (m : ℝ) ≤ Real.exp (w + 1) := by
    have h2N : 2 * (Pa.N : ℝ) ≤ Real.exp (w + 1) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos), hwdef]
      linarith [Real.log_two_lt_d9]
    linarith
  by_cases hm2 : m ≤ 2
  · have hcard : (m.divisors.card : ℝ) ≤ 2 := by
      have h1' : (m.divisors.card : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.card_divisors_le_self m
      have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
      linarith
    have hexp3 : (3 : ℝ) ≤ Real.exp (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5) := by
      have h23 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have h2105 : (2 : ℝ) ≤ (10 : ℝ) ^ 5 := by norm_num
      have hexp : Real.exp 2 ≤ Real.exp ((10 : ℝ) ^ 5) := Real.exp_le_exp.mpr h2105
      have hle : Real.exp ((10 : ℝ) ^ 5) ≤
          Real.exp (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5) := by
        apply Real.exp_le_exp.mpr
        have h1 : 0 < Real.log (w + 1) := Real.log_pos hw1
        have hnn : (0 : ℝ) ≤ 3 / 2 * (w + 1) / Real.log (w + 1) := by positivity
        linarith
      exact le_trans h23 (le_trans hexp hle)
    linarith
  · have hm3 : 3 ≤ m := by omega
    have hτ := tau_card_le_half_loglog m hm3
    have hlogm : Real.log (m : ℝ) ≤ w + 1 := by
      have h := Real.log_le_log (by positivity) hmexp
      rwa [Real.log_exp] at h
    have hlog3m : Real.log 3 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm3)
    have hmono := div_log_mono (Real.log (m : ℝ)) w hlog3m hlogm hw
    have hcardpos : (0 : ℝ) < ((m.divisors.card : ℕ) : ℝ) := by
      have : 0 < m.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    have hlogτ : Real.log ((m.divisors.card : ℕ) : ℝ)
        ≤ 3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 4 := by
      have h := Real.log_le_log hcardpos hτ
      rw [Real.log_exp] at h
      have h2 : 3 / 2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))
          ≤ 3 / 2 * (w + 1) / Real.log (w + 1) := by
        have hmul := mul_le_mul_of_nonneg_left hmono (show (0 : ℝ) ≤ 3 / 2 by norm_num)
        calc 3 / 2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))
            = 3 / 2 * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) := by ring
          _ ≤ 3 / 2 * ((w + 1) / Real.log (w + 1)) := hmul
          _ = 3 / 2 * (w + 1) / Real.log (w + 1) := by ring
      linarith
    have hfinal : Real.log (1 + ((m.divisors.card : ℕ) : ℝ))
        ≤ 3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5 := by
      have hcard1 : (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by
        have : 1 ≤ m.divisors.card := by
          rw [Nat.one_le_iff_ne_zero]
          exact Finset.card_ne_zero_of_mem (Nat.one_mem_divisors.mpr (by omega))
        exact_mod_cast this
      have hlogineq : Real.log (1 + ((m.divisors.card : ℕ) : ℝ))
          ≤ Real.log (2 * ((m.divisors.card : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      rw [Real.log_mul (by norm_num) (by positivity)] at hlogineq
      linarith [Real.log_two_lt_d9, hlogτ]
    exact (Real.log_le_iff_le_exp (by positivity)).mp hfinal

/-- **The target pair-sum bound in the regime `θ√N ≤ N^{1/4}`.**

Here `u := θ√N` is so small that the polar box has at most `C(u²+u+1)` points
(`JointCount.box_card_le`), hence `≪ u⁴` ordered pairs, and the crude pointwise bound

  `S ≤ (#B)² · (max_{z∈B} τ(|z|²))² · (1 + max τ(|Δ(z₁,z₂)|))`

suffices.  The three maxima are controlled by

* `τ(|z|²) ≤ 2^{(w+0.7)/ℓ²}` where `w = log N`, `ℓ = log log x` (all prime factors of `|z|²`
  exceed `Pz ≥ exp(ℓ²)`, so `Pz^{Ω(|z|²)} ≤ |z|² ≤ 2N`; or `JointCount.tau_max_le`);
* `τ(Δ) ≤ exp(3 log|Δ|/log log|Δ|)` with `|Δ| ≤ 2πθ(1+θ)N ≤ 2π u√N`, i.e.
  `log|Δ| ≤ w - σ + 2` where `σ = A'ℓ ≥ w/4` is `-log θ`;
* the factor `(τ⁻¹+θ)/θ = 1 + 1/(θτ)` of the right-hand side is *large* here: `τ ≤ x^{η/3` (`hτ2`)
  gives `1/(θτ) ≥ e^{σ-ηz/3} ≥ e^{w/12}` (using `σ ≥ w/4`, `η < 1/4`, `w > (1/4+η)z`), which
  absorbs `(max τ(|z|²))²` because `ℓ ≥ 18` in this regime; `τ(Δ)` is absorbed by
  `(log N)^{2^20-1}`. -/
theorem pairSumCrude6_smallU :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((1 : ℝ) / 4) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  refine ⟨1, one_pos, ?_⟩
  intro Pa φ β hβ hu10 hu38 hu14
  simp only [one_mul]
  set w : ℝ := Real.log (Pa.N : ℝ) with hw
  have hw_gt : (37000000 : ℝ) < w := by rw [hw]; exact smallU_w_ge Pa hu10
  have hw_ge : (37000000 : ℝ) ≤ w := le_of_lt hw_gt
  have hwpos : 0 < w := by linarith
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  have hu_g : (1 / 10 : ℝ) ≤ u := by rw [hu]; exact hu10
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith [Pa.hN1]
  have hu_pos : 0 < u := by rw [hu]; positivity
  have hθpos : 0 < Pa.θ := Pa.hθ0
  have hlogx1 : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) (by exact_mod_cast Pa.hx))
  have hτpos : 0 < Pa.τ := by
    have h := Pa.hτ1
    have hpos : 0 < (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  set τg : GaussianInt → ℝ := fun z => (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) with hτg
  set δ : GaussianInt → GaussianInt → ℝ :=
    fun z1 z2 => ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) with hδ
  set EM : ℝ := Real.exp ((w + 1) / 467) with hEM
  set EJ : ℝ := Real.exp (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5) with hEJ
  set B : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hBdef
  have hEMpos : 0 < EM := by rw [hEM]; positivity
  have hEJpos : 0 < EJ := by rw [hEJ]; positivity
  have hCpos : 0 < EM * (EM * EJ) := mul_pos hEMpos (mul_pos hEMpos hEJpos)
  have hu4 : u ^ 4 = Pa.θ ^ 4 * Pa.N ^ 2 := by
    rw [hu, mul_pow]
    have hsq : Real.sqrt (Pa.N : ℝ) ^ 2 = Pa.N := Real.sq_sqrt (le_of_lt hNpos)
    have h4 : Real.sqrt (Pa.N : ℝ) ^ 4 = Pa.N ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
    rw [h4]
  have hBsub : B ⊆ polarBoxFinset Pa φ := by
    intro z hz
    rw [hBdef, Finset.mem_filter] at hz
    exact mem_polarBoxFinset.mpr ⟨hz.1, (hβ.2 z hz.2).1⟩
  have hstep : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then τg z1 * (τg z2 * (1 + δ z1 z2)) else 0))
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 then (∑ z2 ∈ Work.FITop.boxN Pa,
            (if β z2 ≠ 0 then EM * (EM * EJ) else 0)) else 0) := by
    apply Finset.sum_le_sum; intro z1 _
    by_cases h1 : β z1 ≠ 0
    · rw [if_pos h1]
      apply Finset.sum_le_sum; intro z2 _
      by_cases h2 : β z2 ≠ 0
      · rw [if_pos h2]
        have hIP1 : Work.FITop3.InPolarBox Pa φ z1 := (hβ.2 z1 h1).1
        have hIP2 : Work.FITop3.InPolarBox Pa φ z2 := (hβ.2 z2 h2).1
        have hτg1 : τg z1 ≤ EM := by
          rw [hτg, hEM]; exact tau_gnorm_le_exp Pa φ hIP1 (hβ.2 z1 h1).2 hu10
        have hτg2 : τg z2 ≤ EM := by
          rw [hτg, hEM]; exact tau_gnorm_le_exp Pa φ hIP2 (hβ.2 z2 h2).2 hu10
        have hδ2 : 1 + δ z1 z2 ≤ EJ := by
          rw [hδ, hEJ]; exact one_add_tau_absDelta_le_exp Pa φ hIP1 hIP2 hw_ge
        by_cases h3 : z1 = z2
        · rw [if_neg (fun h => h.2.2 h3)]
          exact hCpos.le
        · rw [if_pos ⟨h1, h2, h3⟩]
          have h2b : τg z2 * (1 + δ z1 z2) ≤ EM * EJ :=
            mul_le_mul hτg2 hδ2 (by positivity) hEMpos.le
          exact mul_le_mul hτg1 h2b (by positivity) hEMpos.le
      · rw [if_neg h2]
        rw [if_neg (fun h => h2 h.2.1)]
    · rw [if_neg h1]
      apply Finset.sum_nonpos; intro z2 _
      rw [if_neg (fun h => h1 h.1)]
  have hstep2 : (∑ z1 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 then (∑ z2 ∈ Work.FITop.boxN Pa,
            (if β z2 ≠ 0 then EM * (EM * EJ) else 0)) else 0))
      = (B.card : ℝ) * ((B.card : ℝ) * (EM * (EM * EJ))) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← hBdef]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hcardB : (B.card : ℝ) ≤ 2300 * u ^ 2 := by
    have h1 : B.card ≤ (polarBoxFinset Pa φ).card := Finset.card_le_card hBsub
    have h1' : (B.card : ℝ) ≤ ((polarBoxFinset Pa φ).card : ℝ) := by exact_mod_cast h1
    have h2 : ((polarBoxFinset Pa φ).card : ℝ)
        ≤ Real.pi / 8 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + 20 :=
      JointCount.box_card_le Pa φ
    rw [← hu] at h2
    have hu2 : (1 / 100 : ℝ) ≤ u ^ 2 := by nlinarith
    have h3 : Real.pi / 8 * u ^ 2 + 20 * u + 20 ≤ 2300 * u ^ 2 := by
      have hpi : Real.pi < 4 := Real.pi_lt_four
      nlinarith [hu_g, hu2, hpi, hu_pos.le]
    linarith
  have hcardB2 : (B.card : ℝ) ^ 2 ≤ (2300 : ℝ) ^ 2 * u ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (B.card : ℝ)) hcardB 2
    nlinarith [h]
  have h2300 : (2300 : ℝ) ^ 2 ≤ Real.exp 20 := by
    have he : Real.exp 20 = (Real.exp 1) ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7182818283 : ℝ) ^ 20 ≤ Real.exp 20 := by
      rw [he]
      exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 20
    have h4 : (2300 : ℝ) ^ 2 ≤ (2.7182818283 : ℝ) ^ 20 := by norm_num
    linarith
  have hEMform : EM * (EM * EJ) =
      Real.exp (2 * ((w + 1) / 467) + (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5)) := by
    rw [hEM, hEJ, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp_le : (2300 : ℝ) ^ 2 * (EM * (EM * EJ)) ≤ Real.exp (w / 12) * w ^ (1048575 : ℕ) := by
    rw [hEMform]
    have hsplit : 2 * ((w + 1) / 467) ≤ (w + 1) / 233 := by linarith
    calc (2300 : ℝ) ^ 2 * Real.exp (2 * ((w + 1) / 467) + (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5))
        ≤ Real.exp 20 * Real.exp (2 * ((w + 1) / 467) + (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5)) :=
          mul_le_mul_of_nonneg_right h2300 (by positivity)
      _ = Real.exp (20 + (2 * ((w + 1) / 467) + (3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5))) := by
          simp only [← Real.exp_add]
      _ ≤ Real.exp (w / 12 + 1048575 * Real.log w) := by
          apply Real.exp_le_exp.mpr
          have h := smallU_final_arith w hw_ge
          linarith
      _ = Real.exp (w / 12) * Real.exp (1048575 * Real.log w) := by rw [Real.exp_add]
      _ = Real.exp (w / 12) * w ^ (1048575 : ℕ) := by
          congr 1
          have h1 : Real.exp (((1048575 : ℕ) : ℝ) * Real.log w) = w ^ (1048575 : ℕ) := by
            rw [Real.exp_nat_mul, Real.exp_log hwpos]
          simpa using h1
  have hCnn : (0 : ℝ) ≤ EM * (EM * EJ) := hCpos.le
  have hfinal_le : (B.card : ℝ) ^ 2 * (EM * (EM * EJ)) ≤
      (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ 3 * Pa.N ^ 2 * w ^ (1048575 : ℕ) := by
    calc (B.card : ℝ) ^ 2 * (EM * (EM * EJ))
        ≤ ((2300 : ℝ) ^ 2 * u ^ 4) * (EM * (EM * EJ)) :=
          mul_le_mul_of_nonneg_right hcardB2 hCnn
      _ = u ^ 4 * ((2300 : ℝ) ^ 2 * (EM * (EM * EJ))) := by ring
      _ ≤ u ^ 4 * (Real.exp (w / 12) * w ^ (1048575 : ℕ)) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ ≤ u ^ 4 * ((1 + (Pa.θ * Pa.τ)⁻¹) * w ^ (1048575 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right (smallU_budget Pa hu10 hu14) (by positivity)
      _ = (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ 3 * Pa.N ^ 2 * w ^ (1048575 : ℕ) := by
          rw [hu4]
          have hθ0 : Pa.θ ≠ 0 := ne_of_gt hθpos
          have hτ0 : Pa.τ ≠ 0 := ne_of_gt hτpos
          have hN0 : (Pa.N : ℝ) ≠ 0 := ne_of_gt hNpos
          have hw0 : w ^ (1048575 : ℕ) ≠ 0 := pow_ne_zero _ (ne_of_gt hwpos)
          field_simp
          ring
  have hexp_eq : ((2 : ℕ) ^ (20 : ℕ)) - 1 = 1048575 := by norm_num
  calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
      ≤ (B.card : ℝ) * ((B.card : ℝ) * (EM * (EM * EJ))) :=
        le_trans hstep (le_of_eq hstep2)
    _ = (B.card : ℝ) ^ 2 * (EM * (EM * EJ)) := by ring
    _ ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ 3 * Pa.N ^ 2 * w ^ (1048575 : ℕ) := hfinal_le
    _ = (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ 3 * Pa.N ^ 2 * w ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
        rw [hexp_eq]

end

end Work.FIArea3
