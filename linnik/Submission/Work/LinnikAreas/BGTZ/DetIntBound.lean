/-
# The contour-integrand bound of the BGTZ detector

`detInt χ₁ χ R θw N ρ s = L(χ, ρ+s) L(χχ₁, ρ+s) G(ρ+s,χ) N^s/(s(s+1))` is the integrand of the
detector contour integral.  This file proves that it decays like `(1+|t|)^{-4/3}` on the three
contours used by the contour shift: the critical line `Re s = 1/2 - Re ρ`, the line `Re s = 2`
(where the two `L`-factors are bounded by `2` since their argument has real part `> 5/2`), and the
rectangle `1/2 - Re ρ ≤ Re s ≤ 2` at height `|T| ≥ 1 + |Im ρ|` (both `L`-arguments have imaginary
part `≥ 1` there).  The analytic inputs are

* the classical convexity bound for `ζ` on the critical strip (`ZetaConvexityHalfAlt`),
* the boundedness of `ζ` on the segment `Re s = 1/2`, `|Im s| ≤ 1` (`ZetaHalfSmallT`),
* the `log`-bound for non-principal `L`-functions on `1 ≤ Re s ≤ 3` (`LFunctionSigmaGeOne`),
* the `(1+|t|)^{1/4}` convexity bound for non-principal `L`-functions on the half-strip
  `1/2 ≤ Re s ≤ 1` (`LFunction_half_strip`, proved below from the shared-library convexity
  estimate `prim_LFunction_quarter_convex` and the imprimitive reduction
  `LFunction_nonprimitive_le`),
* the exact evaluation of the principal `L`-function as
  `L(s, χ₀) = ∏_{p | q}(1 - p^{-s}) ζ(s)` (Mathlib's `LFunctionTrivChar_eq_mul_riemannZeta`).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs
import Submission.Work.LinnikAreas.BGTZ.ZetaConvexityHalfAlt
import Submission.Work.LinnikAreas.BGTZ.ZetaHalfSmallT
import Submission.Work.LinnikAreas.BGTZ.LFunctionSigmaGeOne
import Submission.Work.LinnikAreas.prim_LFunction_quarter_convex
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_two_of_two_le_re
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.LinnikAreas.BGTZ
lemma sieveLocal_norm_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) {u : ℂ}
    (hu : (1 : ℝ) / 2 ≤ u.re) (p : ℕ) : ‖sieveLocal χ₁ χ u p‖ ≤ 3 := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  have hsieve : sieveLocal χ₁ χ u p
      = (((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-u)
        - (((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * u)) := by
    simp only [sieveLocal]
    push_cast
    ring
  have hre_le : (χ₁ p).re ≤ 1 := by
    have h := Complex.abs_re_le_norm (χ₁ p)
    have h2 := DirichletCharacter.norm_le_one χ₁ p
    exact (abs_le.mp (le_trans h h2)).2
  have hre_ge : -1 ≤ (χ₁ p).re := by
    have h := Complex.abs_re_le_norm (χ₁ p)
    have h2 := DirichletCharacter.norm_le_one χ₁ p
    exact (abs_le.mp (le_trans h h2)).1
  have hpow1 : ‖(p : ℂ) ^ (-u)‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0
      rw [show (((0 : ℕ)) : ℂ) = 0 by norm_num, Complex.zero_cpow (neg_ne_zero.mpr hu0),
        norm_zero]
      norm_num
    · rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp0)]
      have hre : (-u).re = -u.re := Complex.neg_re u
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp0) (by linarith)
  have hpow2 : ‖(p : ℂ) ^ (-(2 * u))‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0
      have h2u : (2 : ℂ) * u ≠ 0 := mul_ne_zero two_ne_zero hu0
      rw [show (((0 : ℕ)) : ℂ) = 0 by norm_num, Complex.zero_cpow (neg_ne_zero.mpr h2u),
        norm_zero]
      norm_num
    · rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp0)]
      have hre : (-(2 * u)).re = -(2 * u.re) := by
        rw [Complex.neg_re, Complex.mul_re]
        simp
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp0) (by linarith)
  have hχ : ‖χ p‖ ≤ 1 := DirichletCharacter.norm_le_one χ p
  have hA : ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-u)‖ ≤ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    have hprod1 : ‖χ p‖ * ‖(p : ℂ) ^ (-u)‖ ≤ 1 := by
      exact mul_le_one₀ hχ (norm_nonneg _) hpow1
    calc (1 + (χ₁ p).re) * ‖χ p‖ * ‖(p : ℂ) ^ (-u)‖
        = (1 + (χ₁ p).re) * (‖χ p‖ * ‖(p : ℂ) ^ (-u)‖) := by ring
      _ ≤ (1 + (χ₁ p).re) * 1 := mul_le_mul_of_nonneg_left hprod1 (by linarith)
      _ ≤ 2 := by linarith
  have hB : ‖(((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * u))‖ ≤ 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    have habs : |(χ₁ p).re| ≤ 1 := abs_le.mpr ⟨hre_ge, hre_le⟩
    have hχ2 : ‖χ p‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hχ
    have hprod2 : ‖χ p‖ ^ 2 * ‖(p : ℂ) ^ (-(2 * u))‖ ≤ 1 := by
      exact mul_le_one₀ hχ2 (norm_nonneg _) hpow2
    calc |(χ₁ p).re| * ‖χ p‖ ^ 2 * ‖(p : ℂ) ^ (-(2 * u))‖
        = |(χ₁ p).re| * (‖χ p‖ ^ 2 * ‖(p : ℂ) ^ (-(2 * u))‖) := by ring
      _ ≤ 1 * 1 := mul_le_mul habs hprod2 (by positivity) (by norm_num)
      _ = 1 := by ring
  calc ‖sieveLocal χ₁ χ u p‖
      = ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-u)
          - (((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * u))‖ := by rw [hsieve]
    _ ≤ ‖(((1 + (χ₁ p).re : ℝ)) : ℂ) * (χ p) * (p : ℂ) ^ (-u)‖
          + ‖(((χ₁ p).re : ℝ) : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * u))‖ := norm_sub_le _ _
    _ ≤ 2 + 1 := add_le_add hA hB
    _ = 3 := by norm_num

lemma sieveG_norm_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℂ, (1 : ℝ) / 2 ≤ u.re → ‖sieveG χ₁ R θw u χ‖ ≤ K := by
  refine ⟨1 + ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      |θw d| * |θw e| * (3 : ℝ) ^ (R * R + 1), by positivity, ?_⟩
  intro u hu
  have hstep : ‖sieveG χ₁ R θw u χ‖ ≤
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        ‖(θw d : ℂ) * (θw e : ℂ)
          * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖ := by
    rw [sieveG]
    calc ‖∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖
        ≤ ∑ d ∈ Finset.Icc 1 R, ‖∑ e ∈ Finset.Icc 1 R,
            (θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖ :=
          norm_sum_le (Finset.Icc 1 R) _
      _ ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            ‖(θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖ := by
          apply Finset.sum_le_sum
          intro d hd
          exact norm_sum_le (Finset.Icc 1 R) _
  refine le_trans hstep ?_
  have hgoal : ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        ‖(θw d : ℂ) * (θw e : ℂ)
          * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖
      ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          |θw d| * |θw e| * (3 : ℝ) ^ (R * R + 1) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro e he
    have hdR : d ≤ R := (Finset.mem_Icc.mp hd).2
    have heR : e ≤ R := (Finset.mem_Icc.mp he).2
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hcard : ((Nat.lcm d e).primeFactors).card ≤ R * R + 1 := by
      have h1 : ((Nat.lcm d e).primeFactors).card ≤ (Nat.lcm d e).divisors.card := by
        apply Finset.card_le_card
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        rw [Nat.mem_divisors]
        exact ⟨hp.2.1, hp.2.2⟩
      have h2 : (Nat.lcm d e).divisors.card ≤ Nat.lcm d e := Nat.card_divisors_le_self _
      have h3 : Nat.lcm d e ≤ R * R := by
        have h4 : Nat.lcm d e ≤ d * e := Nat.lcm_le_mul (by omega) (by omega)
        have h5 : d * e ≤ R * R := Nat.mul_le_mul hdR heR
        omega
      omega
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hprod : ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖ ≤ (3 : ℝ) ^ (R * R + 1) := by
      calc ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖
          ≤ ∏ p ∈ (Nat.lcm d e).primeFactors, ‖sieveLocal χ₁ χ u p‖ :=
            Finset.norm_prod_le _ _
        _ ≤ ∏ p ∈ (Nat.lcm d e).primeFactors, (3 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro p hp; positivity
            · intro p hp; exact sieveLocal_norm_le χ₁ χ hu p
        _ = (3 : ℝ) ^ ((Nat.lcm d e).primeFactors).card := Finset.prod_const 3
        _ ≤ (3 : ℝ) ^ (R * R + 1) := pow_le_pow_right₀ (by norm_num) hcard
    calc |θw d| * |θw e| * ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ u p‖
        ≤ |θw d| * |θw e| * (3 : ℝ) ^ (R * R + 1) := by
          apply mul_le_mul_of_nonneg_left hprod
          positivity
      _ = |θw d| * |θw e| * (3 : ℝ) ^ (R * R + 1) := rfl
  exact le_trans hgoal (le_add_of_nonneg_left (by positivity))


/-- Absorption: `(1+x)^{1/4}(log(2+x)+2) ≤ C(1+x)^{1/3}` for `x ≥ 0`. -/
lemma absorb_quarter_third :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      (1 + x) ^ ((1 : ℝ) / 4) * (Real.log (2 + x) + 2) ≤ C * (1 + x) ^ ((1 : ℝ) / 3) := by
  refine ⟨12 * (2 : ℝ) ^ ((1 : ℝ) / 12) + 2, by positivity, ?_⟩
  intro x hx
  have h1x : (1 : ℝ) ≤ 1 + x := by linarith
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h2x : (0 : ℝ) < 2 + x := by linarith
  have h1x12 : (1 : ℝ) ≤ (1 + x) ^ ((1 : ℝ) / 12) := Real.one_le_rpow h1x (by norm_num)
  have hlog : Real.log (2 + x) ≤ 12 * (2 + x) ^ ((1 : ℝ) / 12) := by
    have h := Real.log_le_rpow_div (le_of_lt h2x) (by norm_num : (0 : ℝ) < (1 : ℝ) / 12)
    have he : (2 + x) ^ ((1 : ℝ) / 12) / ((1 : ℝ) / 12) = 12 * (2 + x) ^ ((1 : ℝ) / 12) := by
      rw [div_eq_mul_inv, show (((1 : ℝ) / 12)⁻¹) = 12 by norm_num, mul_comm]
    rw [he] at h; exact h
  have hmono : (2 + x) ^ ((1 : ℝ) / 12) ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) * (1 + x) ^ ((1 : ℝ) / 12) := by
    have h2 : 2 + x ≤ 2 * (1 + x) := by linarith
    calc (2 + x) ^ ((1 : ℝ) / 12) ≤ (2 * (1 + x)) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow (le_of_lt h2x) h2 (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 12) * (1 + x) ^ ((1 : ℝ) / 12) :=
          Real.mul_rpow (by norm_num) (le_of_lt hpos)
  have h2p : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos (by norm_num) _
  have hstep : Real.log (2 + x) + 2 ≤
      (12 * (2 : ℝ) ^ ((1 : ℝ) / 12) + 2) * (1 + x) ^ ((1 : ℝ) / 12) := by
    have h1 : 12 * (2 + x) ^ ((1 : ℝ) / 12) ≤
        12 * ((2 : ℝ) ^ ((1 : ℝ) / 12) * (1 + x) ^ ((1 : ℝ) / 12)) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    nlinarith only [hlog, h1, h1x12, h2p]
  have hx14 : 0 ≤ (1 + x) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hpos) _
  calc (1 + x) ^ ((1 : ℝ) / 4) * (Real.log (2 + x) + 2)
      ≤ (1 + x) ^ ((1 : ℝ) / 4)
          * ((12 * (2 : ℝ) ^ ((1 : ℝ) / 12) + 2) * (1 + x) ^ ((1 : ℝ) / 12)) :=
        mul_le_mul_of_nonneg_left hstep hx14
    _ = (12 * (2 : ℝ) ^ ((1 : ℝ) / 12) + 2)
          * ((1 + x) ^ ((1 : ℝ) / 4) * (1 + x) ^ ((1 : ℝ) / 12)) := by ring
    _ = (12 * (2 : ℝ) ^ ((1 : ℝ) / 12) + 2) * (1 + x) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_add hpos]; norm_num

/-- Absorption: `log(2+x) ≤ C(1+x)^{1/3}` for `x ≥ 0`. -/
lemma log_le_third :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → Real.log (2 + x) ≤ C * (1 + x) ^ ((1 : ℝ) / 3) := by
  refine ⟨3 * (2 : ℝ) ^ ((1 : ℝ) / 3) + 1, by positivity, ?_⟩
  intro x hx
  have h1x : (1 : ℝ) ≤ 1 + x := by linarith
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h2x : (0 : ℝ) < 2 + x := by linarith
  have h1x13 : (1 : ℝ) ≤ (1 + x) ^ ((1 : ℝ) / 3) := Real.one_le_rpow h1x (by norm_num)
  have hlog : Real.log (2 + x) ≤ 3 * (2 + x) ^ ((1 : ℝ) / 3) := by
    have h := Real.log_le_rpow_div (le_of_lt h2x) (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)
    have he : (2 + x) ^ ((1 : ℝ) / 3) / ((1 : ℝ) / 3) = 3 * (2 + x) ^ ((1 : ℝ) / 3) := by
      rw [div_eq_mul_inv, show (((1 : ℝ) / 3)⁻¹) = 3 by norm_num, mul_comm]
    rw [he] at h; exact h
  have hmono : (2 + x) ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) * (1 + x) ^ ((1 : ℝ) / 3) := by
    have h2 : 2 + x ≤ 2 * (1 + x) := by linarith
    calc (2 + x) ^ ((1 : ℝ) / 3) ≤ (2 * (1 + x)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (le_of_lt h2x) h2 (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 3) * (1 + x) ^ ((1 : ℝ) / 3) :=
          Real.mul_rpow (by norm_num) (le_of_lt hpos)
  have h2p : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith only [hlog, hmono, h1x13, h2p]

lemma LFunction_one_bound (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂ), (1 : ℝ) / 2 ≤ u.re → u.re ≤ 3 →
      (1 ≤ |u.im| ∨ u.re = 1 / 2) →
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) u‖
        ≤ C * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
  obtain ⟨C1, hC1pos, hC1⟩ := ZetaConvexityHalfAlt
  obtain ⟨C2, hC2pos, hC2⟩ := ZetaHalfSmallT
  obtain ⟨Ca, hCapos, hCa⟩ := absorb_quarter_third
  obtain ⟨Cb, hCbpos, hCb⟩ := log_le_third
  have hn1 : (0 : ℝ) ≤ C1 * Ca := mul_nonneg hC1pos.le hCapos.le
  set Q : ℝ := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  refine ⟨Q * (C1 * Ca + C2 + 5 * Cb) + 1, by positivity, ?_⟩
  intro u hu1 hu3 hdisj
  have h0 : (0 : ℝ) ≤ (1 + |u.im|) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hu_ne_one : u ≠ 1 := by
    intro hc
    rcases hdisj with h | h
    · rw [hc] at h; norm_num at h
    · rw [hc] at h; norm_num at h
  have hEP := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) (s := u) hu_ne_one
  simp only [DirichletCharacter.LFunctionTrivChar] at hEP
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-u))‖ ≤ Q := by
    rw [hQ, norm_prod]
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.one_le
      have hnorm : ‖(p : ℂ) ^ (-u)‖ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        rw [Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      calc ‖(1 : ℂ) - (p : ℂ) ^ (-u)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-u)‖ := norm_sub_le _ _
        _ ≤ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [norm_one]; linarith
  have hζ : ‖riemannZeta u‖ ≤ (C1 * Ca + C2 + 5 * Cb) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
    by_cases him : 1 ≤ |u.im|
    · by_cases hσ : u.re ≤ 1
      · have h := hC1 u.re u.im hu1 hσ him
        rw [Complex.re_add_im u] at h
        refine le_trans h ?_
        calc C1 * (1 + |u.im|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |u.im|) + 2)
            = C1 * ((1 + |u.im|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |u.im|) + 2)) := by ring
          _ ≤ C1 * (Ca * (1 + |u.im|) ^ ((1 : ℝ) / 3)) :=
              mul_le_mul_of_nonneg_left (hCa |u.im| (abs_nonneg u.im)) hC1pos.le
          _ ≤ (C1 * Ca + C2 + 5 * Cb) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
              rw [← mul_assoc]
              apply mul_le_mul_of_nonneg_right _ h0
              linarith [hn1, hC2pos, hCbpos]
      · push_neg at hσ
        have h := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log (σ := u.re) (t := u.im)
          (le_of_lt hσ) him
        rw [Complex.re_add_im u] at h
        refine le_trans h ?_
        calc 5 * Real.log (|u.im| + 2) = 5 * Real.log (2 + |u.im|) := by rw [add_comm]
          _ ≤ 5 * (Cb * (1 + |u.im|) ^ ((1 : ℝ) / 3)) :=
              mul_le_mul_of_nonneg_left (hCb |u.im| (abs_nonneg u.im)) (by norm_num)
          _ ≤ (C1 * Ca + C2 + 5 * Cb) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
              rw [← mul_assoc]
              apply mul_le_mul_of_nonneg_right _ h0
              linarith [hn1, hC2pos]
    · push_neg at him
      rcases hdisj with h | h
      · exact absurd h (not_le.mpr him)
      · have h2 := hC2 u.im (le_of_lt him)
        have hu_eq : ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * Complex.I = u := by
          rw [← h, Complex.re_add_im u]
        rw [hu_eq] at h2
        refine le_trans h2 ?_
        have hX1 : (1 : ℝ) ≤ (1 + |u.im|) ^ ((1 : ℝ) / 3) :=
          Real.one_le_rpow (by have := abs_nonneg u.im; linarith) (by norm_num)
        nlinarith only [hn1, hC2pos, hCbpos, hX1]
  calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) u‖
      = ‖(∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-u))) * riemannZeta u‖ := by rw [hEP]
    _ = ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-u))‖ * ‖riemannZeta u‖ := norm_mul _ _
    _ ≤ Q * ((C1 * Ca + C2 + 5 * Cb) * (1 + |u.im|) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul hprod hζ (norm_nonneg _) hQpos.le
    _ = (Q * (C1 * Ca + C2 + 5 * Cb)) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by ring
    _ ≤ (Q * (C1 * Ca + C2 + 5 * Cb) + 1) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
        apply mul_le_mul_of_nonneg_right _ h0
        linarith

/-- The convexity bound `‖L(χ, σ+it)‖ ≤ C (1+|t|)^{1/4} (log(2+|t|)+2)` for a non-principal
`χ` mod `q` on the half-strip `1/2 ≤ Re s ≤ 1` (imprimitive characters included). -/
lemma LFunction_half_strip (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |t|) + 2) := by
  obtain ⟨Cp, hCppos, hCp⟩ := Work.LinnikAreas.prim_LFunction_quarter_convex
  obtain ⟨Cpd, hCpdpos, hCpd⟩ :=
    Commons.NumberTheory.DirichletCharacter.prod_primeFactors_one_add_rpow_le'
      (σ := (1 : ℝ) / 2) (δ := (1 : ℝ) / 12) (by norm_num) (by norm_num)
  refine ⟨Cp * Cpd * (q : ℝ) ^ ((1 : ℝ) / 12) * ((q : ℝ) ^ ((1 : ℝ) / 4))
      * (Real.log (q : ℝ) + 3), by positivity, ?_⟩
  intro χ hχ σ t hσ1 hσ2
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hq1
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprimne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le χ hχ hσ1 (t := t)
  have hpb := hCp χ.conductor χ.primitiveCharacter hprimne
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) σ t hσ1 hσ2
  have hd_le : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) χ.conductor_dvd_level
  have hprod' : (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))) ≤ Cpd * (q : ℝ) ^ ((1 : ℝ) / 12) := by
    refine le_trans (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_) (hCpd q (NeZero.ne q))
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.one_le
    have := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1 / 2 : ℝ) by linarith)
    linarith
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hlogt : (0 : ℝ) ≤ Real.log (2 + |t|) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hlogstep : Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2
      ≤ (Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2) := by
    have hdpos : (0 : ℝ) < (χ.conductor : ℝ) := by
      have : (0:ℕ) < χ.conductor := NeZero.pos χ.conductor
      exact_mod_cast this
    have h2pos : (0 : ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
    rw [Real.log_mul (ne_of_gt hdpos) (ne_of_gt h2pos)]
    have hlogd : Real.log (χ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log hdpos hd_le
    nlinarith only [hlogq, hlogt, hlogd, mul_nonneg hlogq hlogt]
  have hkey : (χ.conductor : ℝ) ^ ((1 : ℝ) / 4) * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2)
      ≤ (q : ℝ) ^ ((1 : ℝ) / 4) * ((Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2)) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow (by positivity) hd_le (by norm_num)
    · exact hlogstep
    · have harg1 : (1 : ℝ) ≤ (χ.conductor : ℝ) * (2 + |t|) := by
        have hd1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
          have : (1 : ℕ) ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor)
          exact_mod_cast this
        have h2 : (1 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
        exact one_le_mul_of_one_le_of_one_le hd1 h2
      have := Real.log_nonneg harg1
      linarith
    · exact Real.rpow_nonneg hqpos.le _
  have hstep : ‖DirichletCharacter.LFunction χ.primitiveCharacter
        (((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ Cp * (q : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
          * ((Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2)) := by
    refine le_trans hpb ?_
    have hCpnn : (0 : ℝ) ≤ Cp := le_of_lt hCppos
    have hx14 : (0 : ℝ) ≤ (1 + |t|) ^ ((1 : ℝ) / 4) :=
      Real.rpow_nonneg (by positivity) _
    calc Cp * (χ.conductor : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
            * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2)
        = Cp * (1 + |t|) ^ ((1 : ℝ) / 4)
            * ((χ.conductor : ℝ) ^ ((1 : ℝ) / 4)
              * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2)) := by ring
      _ ≤ Cp * (1 + |t|) ^ ((1 : ℝ) / 4)
            * ((q : ℝ) ^ ((1 : ℝ) / 4) * ((Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2))) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = Cp * (q : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
            * ((Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2)) := by ring
  have hnorm : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Cpd * (q : ℝ) ^ ((1 : ℝ) / 12))
          * (Cp * (q : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
              * ((Real.log (q : ℝ) + 3) * (Real.log (2 + |t|) + 2))) :=
    le_trans hred (mul_le_mul hprod' hstep (norm_nonneg _) (by positivity))
  refine le_trans hnorm (le_of_eq ?_)
  ring

lemma LFunction_uniform (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
      (1 : ℝ) / 2 ≤ u.re → u.re ≤ 3 → (1 ≤ |u.im| ∨ u.re = 1 / 2) →
      ‖DirichletCharacter.LFunction χ u‖ ≤ B * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := LFunction_one_bound q
  obtain ⟨C3, hC3pos, hC3⟩ := LFunctionSigmaGeOne q hq
  obtain ⟨C4, hC4pos, hC4⟩ := LFunction_half_strip q hq
  obtain ⟨Ca, hCapos, hCa⟩ := absorb_quarter_third
  obtain ⟨Cb, hCbpos, hCb⟩ := log_le_third
  have hn3 : (0 : ℝ) ≤ C3 * Cb := mul_nonneg hC3pos.le hCbpos.le
  have hn4 : (0 : ℝ) ≤ C4 * Ca := mul_nonneg hC4pos.le hCapos.le
  refine ⟨C₀ + C3 * Cb + C4 * Ca + 1, by positivity, ?_⟩
  intro χ u hu1 hu3 hdisj
  have h0 : (0 : ℝ) ≤ (1 + |u.im|) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  by_cases hχ : χ = 1
  · subst hχ
    have h := hC₀ u hu1 hu3 hdisj
    refine le_trans h ?_
    apply mul_le_mul_of_nonneg_right _ h0
    linarith [hn3, hn4]
  · by_cases hσ : u.re ≤ 1
    · have h := hC4 χ hχ u.re u.im hu1 hσ
      rw [Complex.re_add_im u] at h
      refine le_trans h ?_
      calc C4 * (1 + |u.im|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |u.im|) + 2)
          = C4 * ((1 + |u.im|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |u.im|) + 2)) := by ring
        _ ≤ C4 * (Ca * (1 + |u.im|) ^ ((1 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left (hCa |u.im| (abs_nonneg u.im)) hC4pos.le
        _ ≤ (C₀ + C3 * Cb + C4 * Ca + 1) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
            rw [← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ h0
            linarith [hC₀pos, hn3, hn4]
    · push_neg at hσ
      have him : 1 ≤ |u.im| := hdisj.elim id (fun h => absurd h (by linarith))
      have h := hC3 χ hχ u.re u.im (le_of_lt hσ) hu3 him
      rw [Complex.re_add_im u] at h
      refine le_trans h ?_
      calc C3 * Real.log (2 + |u.im|) ≤ C3 * (Cb * (1 + |u.im|) ^ ((1 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left (hCb |u.im| (abs_nonneg u.im)) hC3pos.le
        _ ≤ (C₀ + C3 * Cb + C4 * Ca + 1) * (1 + |u.im|) ^ ((1 : ℝ) / 3) := by
            rw [← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ h0
            linarith [hC₀pos, hn3, hn4]


/-- Arithmetic helper: `Y^{2/3}/(c Y²) = c⁻¹ Y^{-4/3}` for `Y > 0`. -/
lemma rpow_div_arith {Y c : ℝ} (hY : 0 < Y) :
    Y ^ ((2 : ℝ) / 3) / (c * Y ^ 2) = c⁻¹ * Y ^ (-(4 / 3 : ℝ)) := by
  have h1 : Y ^ ((2 : ℝ) / 3) * Y ^ (-(2 : ℝ)) = Y ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hY]; norm_num
  have h2 : (c * Y ^ 2)⁻¹ = c⁻¹ * Y ^ (-(2 : ℝ)) := by
    have hY2 : (Y ^ 2 : ℝ) = Y ^ (2 : ℝ) := by norm_num
    rw [hY2, mul_inv, ← Real.rpow_neg hY.le]
  have h3 : Y ^ ((2 : ℝ) / 3) / (c * Y ^ 2) = Y ^ ((2 : ℝ) / 3) * (c * Y ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [h3, h2]
  calc Y ^ ((2 : ℝ) / 3) * (c⁻¹ * Y ^ (-(2 : ℝ)))
      = c⁻¹ * (Y ^ ((2 : ℝ) / 3) * Y ^ (-(2 : ℝ))) := by ring
    _ = c⁻¹ * Y ^ (-(4 / 3 : ℝ)) := by rw [h1]

/-- `max 2 |t| ≥ (1+|t|)/2`. -/
lemma half_le_max_two_abs (t : ℝ) : (1 + |t|) / 2 ≤ max 2 |t| := by
  by_cases h : |t| ≤ 2
  · rw [max_eq_left h]; linarith [abs_nonneg t]
  · push_neg at h
    rw [max_eq_right h.le]; linarith

lemma re_im_le_norm (w : ℂ) : max |w.re| |w.im| ≤ ‖w‖ := by
  rw [max_le_iff]
  exact ⟨Complex.abs_re_le_norm w, Complex.abs_im_le_norm w⟩

/-- `(Y²/4)⁻¹ = 4 Y^{-2}`. -/
lemma inv_quarter_sq {Y : ℝ} (hY : 0 < Y) : (Y ^ 2 / 4)⁻¹ = 4 * Y ^ (-(2 : ℝ)) := by
  have hY2 : (Y ^ 2 : ℝ) = Y ^ (2 : ℝ) := by norm_num
  have h1 : Y ^ (-(2 : ℝ)) = (Y ^ 2)⁻¹ := by
    rw [hY2, ← Real.rpow_neg hY.le]
  rw [div_eq_mul_inv, mul_inv, inv_inv, ← h1]
  ring

/-- `Y^{2/3} · Y^{-2} = Y^{-4/3}`. -/
lemma rpow_combine {Y : ℝ} (hY : 0 < Y) :
    Y ^ ((2 : ℝ) / 3) * Y ^ (-(2 : ℝ)) = Y ^ (-(4 / 3 : ℝ)) := by
  rw [← Real.rpow_add hY]; norm_num

theorem DetIntBound {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ₁ χ : DirichletCharacter ℂ q)
    (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (ρ : ℂ)
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) :
    ∃ C A : ℝ, 0 < C ∧ A < -1 ∧
      (∀ t : ℝ, ‖Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ
          (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ A) ∧
      (∀ t : ℝ, ‖Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ
          ((2 : ℝ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ A) ∧
      (∀ x : ℝ, (1 / 2 - ρ.re) ≤ x → x ≤ 2 → ∀ T : ℝ, 1 + |ρ.im| ≤ |T| →
          ‖Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)‖
            ≤ C * (1 + |T|) ^ A) := by
  obtain ⟨B, hBpos, hB⟩ := LFunction_uniform q hq
  obtain ⟨K, hKpos, hK⟩ := sieveG_norm_le χ₁ χ R θw
  set M : ℝ := 1 + |ρ.im| with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg ρ.im; linarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  set cs : ℝ := min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) with hcs
  have hcs_pos : 0 < cs := by
    rw [hcs]
    refine lt_min ?_ (by norm_num)
    exact mul_pos (by linarith only [h1]) (by linarith only [h2])
  set c : ℝ := cs / 8 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set NK : ℝ := (N : ℝ) ^ 2 with hNK
  have hNKpos : 0 < NK := by rw [hNK]; positivity
  have hNK1 : 1 ≤ NK := by
    rw [hNK]
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact one_le_pow₀ this
  refine ⟨B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ + 16 * K * NK
      + 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK + 1, -(4 / 3), by positivity,
    by norm_num, ?_, ?_, ?_⟩
  · -- ================ region 1 ================
    intro t
    set s : ℂ := (((1 / 2 : ℝ) - ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
    set u : ℂ := ρ + s with hu
    have hsre : s.re = 1 / 2 - ρ.re := by rw [hs]; simp
    have hu_eq : u = ((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * Complex.I := by
      rw [hu, hs]
      apply Complex.ext <;> simp <;> ring
    have hure : u.re = 1 / 2 := by rw [hu_eq]; simp
    have huim : u.im = ρ.im + t := by rw [hu_eq]; simp
    set X : ℝ := 1 + |t| with hX
    have hXpos : 0 < X := by rw [hX]; positivity
    have hX1 : 1 ≤ X := by rw [hX]; have := abs_nonneg t; linarith
    have hMXu : 1 + |u.im| ≤ M * X := by
      rw [huim, hM, hX]
      have h : |ρ.im + t| ≤ |ρ.im| + |t| := abs_add_le _ _
      nlinarith only [h, abs_nonneg ρ.im, abs_nonneg t, mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    have hL1 : ‖LFunction χ u‖ ≤ B * (1 + |u.im|) ^ ((1 : ℝ) / 3) :=
      hB χ u (le_of_eq hure.symm) (by rw [hure]; norm_num) (Or.inr hure)
    have hL2 : ‖LFunction (χ * χ₁) u‖ ≤ B * (1 + |u.im|) ^ ((1 : ℝ) / 3) :=
      hB (χ * χ₁) u (le_of_eq hure.symm) (by rw [hure]; norm_num) (Or.inr hure)
    have hG : ‖sieveG χ₁ R θw u χ‖ ≤ K := hK u (le_of_eq hure.symm)
    have hNs : ‖(N : ℂ) ^ s‖ ≤ 1 := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hsneg : s.re ≤ 0 := by rw [hsre]; linarith
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 hsneg
    have hp : (1 + |u.im|) ^ ((1 : ℝ) / 3) ≤ (M * X) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hMXu (by norm_num)
    have e1 : ‖LFunction χ u‖ ≤ B * (M * X) ^ ((1 : ℝ) / 3) :=
      le_trans hL1 (mul_le_mul_of_nonneg_left hp hBpos.le)
    have e2 : ‖LFunction (χ * χ₁) u‖ ≤ B * (M * X) ^ ((1 : ℝ) / 3) :=
      le_trans hL2 (mul_le_mul_of_nonneg_left hp hBpos.le)
    have hnum : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
        * ‖(N : ℂ) ^ s‖ ≤ B * B * K * (M * X) ^ ((2 : ℝ) / 3) := by
      have h1' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖
          ≤ (B * (M * X) ^ ((1 : ℝ) / 3)) * (B * (M * X) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      have h2' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
          ≤ ((B * (M * X) ^ ((1 : ℝ) / 3)) * (B * (M * X) ^ ((1 : ℝ) / 3))) * K :=
        mul_le_mul h1' hG (norm_nonneg _) (by positivity)
      have h3' := mul_le_mul h2' hNs (norm_nonneg _) (by positivity)
      refine le_trans h3' (le_of_eq ?_)
      calc B * (M * X) ^ ((1 : ℝ) / 3) * (B * (M * X) ^ ((1 : ℝ) / 3)) * K * 1
          = B * B * K * ((M * X) ^ ((1 : ℝ) / 3) * (M * X) ^ ((1 : ℝ) / 3)) := by ring
        _ = B * B * K * (M * X) ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add (by positivity)]; norm_num
    have hss : c * X ^ 2 ≤ ‖s * (s + 1)‖ := by
      rw [norm_mul]
      have hs1re : (s + 1).re = 3 / 2 - ρ.re := by
        rw [Complex.add_re, Complex.one_re, hsre]; ring
      have hsim : s.im = t := by rw [hs]; simp
      have hs1im : (s + 1).im = t := by rw [hs]; simp
      have hc₀ : (ρ.re - 1 / 2) * (3 / 2 - ρ.re) ≤ ‖s‖ * ‖s + 1‖ := by
        have ha₁ : ρ.re - 1 / 2 ≤ ‖s‖ := by
          have h := Complex.abs_re_le_norm s
          rw [hsre, abs_of_neg (by linarith only [h1])] at h
          linarith only [h]
        have ha₂ : 3 / 2 - ρ.re ≤ ‖s + 1‖ := by
          have h := Complex.abs_re_le_norm (s + 1)
          rw [hs1re, abs_of_pos (by linarith only [h2])] at h
          linarith only [h]
        exact mul_le_mul ha₁ ha₂ (by linarith only [h2]) (norm_nonneg s)
      have ht2 : t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
        have hb₁ : |t| ≤ ‖s‖ := by
          have h := Complex.abs_im_le_norm s; rwa [hsim] at h
        have hb₂ : |t| ≤ ‖s + 1‖ := by
          have h := Complex.abs_im_le_norm (s + 1); rwa [hs1im] at h
        nlinarith only [mul_le_mul hb₁ hb₂ (abs_nonneg t) (norm_nonneg s), sq_abs t]
      have hkey : c * X ^ 2 ≤ max ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (t ^ 2) := by
        rw [hc, hX, hcs]
        have hsnn : (0 : ℝ) ≤ min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) := le_of_lt hcs_pos
        have h4 : (1 + |t|) ^ 2 ≤ 4 * (1 + t ^ 2) := by nlinarith only [sq_nonneg (|t| - 1), sq_abs t]
        by_cases ht : (1 : ℝ) ≤ t ^ 2
        · have h8 : (1 + t ^ 2) ≤ 2 * t ^ 2 := by linarith
          have hcs_t : min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) / 8
              * (1 + |t|) ^ 2 ≤ min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) * t ^ 2 := by
            nlinarith only [mul_le_mul_of_nonneg_left h4 hsnn, mul_le_mul_of_nonneg_left h8 hsnn]
          have hle : min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) * t ^ 2
              ≤ max ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (t ^ 2) := by
            calc min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) * t ^ 2
                ≤ 1 * t ^ 2 := by
                  apply mul_le_mul_of_nonneg_right
                  · exact le_trans (min_le_right _ _) (by norm_num)
                  · exact sq_nonneg t
              _ = t ^ 2 := by ring
              _ ≤ max ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (t ^ 2) := le_max_right _ _
          linarith [hcs_t, hle]
        · push_neg at ht
          have h8 : (1 + t ^ 2) ≤ 2 := by linarith
          have hcs_t : min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) / 8 * (1 + |t|) ^ 2
              ≤ min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4) := by
            nlinarith only [mul_le_mul_of_nonneg_left h4 hsnn, mul_le_mul_of_nonneg_left h8 hsnn]
          have hle : min ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (1 / 4)
              ≤ max ((ρ.re - 1 / 2) * (3 / 2 - ρ.re)) (t ^ 2) :=
            le_trans (min_le_left _ _) (le_max_left _ _)
          linarith [hcs_t, hle]
      exact le_trans hkey (max_le hc₀ ht2)
    have hrepr : detInt χ₁ χ R θw N ρ s
        = LFunction χ u * LFunction (χ * χ₁) u * sieveG χ₁ R θw u χ
            * (N : ℂ) ^ s / (s * (s + 1)) := by
      rw [detInt, ← hu]
    have hnorm : ‖detInt χ₁ χ R θw N ρ s‖
        = ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
            * ‖(N : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
      rw [hrepr, norm_div, norm_mul, norm_mul, norm_mul]
    have hdenpos : (0 : ℝ) < c * X ^ 2 := by positivity
    have hmain : ‖detInt χ₁ χ R θw N ρ s‖
        ≤ (B * B * K * M ^ ((2 : ℝ) / 3) * c⁻¹) * X ^ (-(4 / 3 : ℝ)) := by
      rw [hnorm]
      refine le_trans (div_le_div_of_nonneg_left (by positivity) hdenpos hss) ?_
      refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)) ?_
      have hinv : (c * X ^ 2)⁻¹ = c⁻¹ * X ^ (-(2 : ℝ)) := by
        have hX2 : (X ^ 2 : ℝ) = X ^ (2 : ℝ) := by norm_num
        rw [mul_inv, hX2, ← Real.rpow_neg hXpos.le]
      exact le_of_eq (by
        calc B * B * K * (M * X) ^ ((2 : ℝ) / 3) / (c * X ^ 2)
            = B * B * K * (M * X) ^ ((2 : ℝ) / 3) * (c * X ^ 2)⁻¹ := by rw [div_eq_mul_inv]
          _ = B * B * K * (M * X) ^ ((2 : ℝ) / 3) * (c⁻¹ * X ^ (-(2 : ℝ))) := by rw [hinv]
          _ = (B * B * K * M ^ ((2 : ℝ) / 3)) * (X ^ ((2 : ℝ) / 3) * X ^ (-(2 : ℝ))) * c⁻¹ := by
                rw [Real.mul_rpow hMpos.le hXpos.le]; ring
          _ = (B * B * K * M ^ ((2 : ℝ) / 3)) * X ^ (-(4 / 3 : ℝ)) * c⁻¹ := by
                rw [rpow_combine hXpos]
          _ = (B * B * K * M ^ ((2 : ℝ) / 3) * c⁻¹) * X ^ (-(4 / 3 : ℝ)) := by ring)
    have hconst : B * B * K * M ^ ((2 : ℝ) / 3) * c⁻¹
        ≤ B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ + 16 * K * NK
          + 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK + 1 := by
      have hA : (0 : ℝ) ≤ B * B * K * M ^ ((2 : ℝ) / 3) := by
        have hMnn := Real.rpow_nonneg hMpos.le ((2 : ℝ) / 3); positivity
      have hle : B * B * K * M ^ ((2 : ℝ) / 3) ≤ B * B * K * M ^ ((2 : ℝ) / 3) * NK := by
        exact le_mul_of_one_le_right hA hNK1
      have hfin : B * B * K * M ^ ((2 : ℝ) / 3) * c⁻¹
          ≤ B * B * K * M ^ ((2 : ℝ) / 3) * NK * c⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hcpos.le)
      have h16 : (0 : ℝ) ≤ 16 * K * NK := by positivity
      have h4' : (0 : ℝ) ≤ 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK := by positivity
      linarith [hfin, h16, h4']
    exact le_trans hmain (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by positivity) _))
  · -- ================ region 2 ================
    intro t
    set s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
    set u : ℂ := ρ + s with hu
    have hure : 2 ≤ u.re := by rw [hu, hs]; simp; linarith [h1]
    set X : ℝ := 1 + |t| with hX
    have hXpos : 0 < X := by rw [hX]; positivity
    have hX1 : 1 ≤ X := by rw [hX]; have := abs_nonneg t; linarith
    have hL1 : ‖LFunction χ u‖ ≤ 2 :=
      Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_two_of_two_le_re χ u hure
    have hL2 : ‖LFunction (χ * χ₁) u‖ ≤ 2 :=
      Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_two_of_two_le_re (χ * χ₁) u hure
    have hG : ‖sieveG χ₁ R θw u χ‖ ≤ K := hK u (by linarith)
    have hNs : ‖(N : ℂ) ^ s‖ ≤ NK := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      have hsre : s.re = 2 := by rw [hs]; simp
      rw [hsre, hNK]
      simp
    have hss : X ^ 2 / 4 ≤ ‖s * (s + 1)‖ := by
      rw [norm_mul, hX]
      have hsre : s.re = 2 := by rw [hs]; simp
      have hsim : s.im = t := by rw [hs]; simp
      have hs1re : (s + 1).re = 3 := by
        rw [Complex.add_re, Complex.one_re, hsre]; norm_num
      have hs1im : (s + 1).im = t := by rw [hs]; simp
      have h1' : (1 + |t|) / 2 ≤ ‖s‖ := by
        have h := re_im_le_norm s
        rw [hsre, hsim, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
        linarith [h, half_le_max_two_abs t]
      have h2' : (1 + |t|) / 2 ≤ ‖s + 1‖ := by
        have h := re_im_le_norm (s + 1)
        rw [hs1re, hs1im, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
        have hmax : max 2 |t| ≤ max 3 |t| := max_le_max (by norm_num) le_rfl
        linarith [h, half_le_max_two_abs t, hmax]
      nlinarith only [mul_le_mul h1' h2' (by positivity) (norm_nonneg s)]
    have hrepr : detInt χ₁ χ R θw N ρ s
        = LFunction χ u * LFunction (χ * χ₁) u * sieveG χ₁ R θw u χ
            * (N : ℂ) ^ s / (s * (s + 1)) := by
      rw [detInt, ← hu]
    have hnorm : ‖detInt χ₁ χ R θw N ρ s‖
        = ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
            * ‖(N : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
      rw [hrepr, norm_div, norm_mul, norm_mul, norm_mul]
    have hnum : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
        * ‖(N : ℂ) ^ s‖ ≤ 2 * 2 * K * NK := by
      have h1' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ ≤ 2 * 2 :=
        mul_le_mul hL1 hL2 (norm_nonneg _) (by norm_num)
      have h2' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
          ≤ 2 * 2 * K := mul_le_mul h1' hG (norm_nonneg _) (by norm_num)
      exact mul_le_mul h2' hNs (norm_nonneg _) (by positivity)
    have hdenpos : (0 : ℝ) < X ^ 2 / 4 := by positivity
    have hmain : ‖detInt χ₁ χ R θw N ρ s‖ ≤ (16 * K * NK) * X ^ (-(4 / 3 : ℝ)) := by
      rw [hnorm]
      refine le_trans (div_le_div_of_nonneg_left (by positivity) hdenpos hss) ?_
      refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)) ?_
      calc 2 * 2 * K * NK / (X ^ 2 / 4)
          = 2 * 2 * K * NK * (X ^ 2 / 4)⁻¹ := by rw [div_eq_mul_inv]
        _ = 2 * 2 * K * NK * (4 * X ^ (-(2 : ℝ))) := by rw [inv_quarter_sq hXpos]
        _ = 16 * K * NK * X ^ (-(2 : ℝ)) := by ring
        _ ≤ 16 * K * NK * X ^ (-(4 / 3 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have hconst : 16 * K * NK ≤ B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ + 16 * K * NK
        + 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK + 1 := by
      have h1n : (0 : ℝ) ≤ B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ := by
        have hMnn := Real.rpow_nonneg hMpos.le ((2 : ℝ) / 3); positivity
      have h3n : (0 : ℝ) ≤ 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK := by positivity
      linarith
    exact le_trans hmain (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by positivity) _))
  · -- ================ region 3 ================
    intro x hx1 hx2 T hT
    set s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I with hs
    set u : ℂ := ρ + s with hu
    have hure : 1 / 2 ≤ u.re := by rw [hu, hs]; simp; linarith [hx1]
    have hure3 : u.re ≤ 3 := by rw [hu, hs]; simp; linarith [hx2, h2]
    have huim : u.im = ρ.im + T := by rw [hu, hs]; simp
    have hT1 : 1 ≤ |T| := by linarith [hT, abs_nonneg ρ.im]
    have him1 : 1 ≤ |u.im| := by
      rw [huim]
      have h : |T| ≤ |ρ.im + T| + |ρ.im| := by
        calc |T| = |(ρ.im + T) - ρ.im| := by ring_nf
          _ ≤ |ρ.im + T| + |ρ.im| := abs_sub _ _
      linarith
    have him2 : 1 + |u.im| ≤ 3 * (1 + |T|) := by
      rw [huim]
      have h : |ρ.im + T| ≤ |ρ.im| + |T| := abs_add_le _ _
      linarith only [abs_nonneg T, h, hT]
    have hL1 : ‖LFunction χ u‖ ≤ B * (1 + |u.im|) ^ ((1 : ℝ) / 3) :=
      hB χ u hure hure3 (Or.inl him1)
    have hL2 : ‖LFunction (χ * χ₁) u‖ ≤ B * (1 + |u.im|) ^ ((1 : ℝ) / 3) :=
      hB (χ * χ₁) u hure hure3 (Or.inl him1)
    have hG : ‖sieveG χ₁ R θw u χ‖ ≤ K := hK u hure
    set X : ℝ := 1 + |T| with hX
    have hXpos : 0 < X := by rw [hX]; positivity
    have hX1 : 1 ≤ X := by rw [hX]; have := abs_nonneg T; linarith
    have hNs : ‖(N : ℂ) ^ s‖ ≤ NK := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      have hsre : s.re = x := by rw [hs]; simp
      rw [hsre, hNK]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      calc (N : ℝ) ^ x ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx2
        _ = (N : ℝ) ^ 2 := by norm_num
    have hss : X ^ 2 / 4 ≤ ‖s * (s + 1)‖ := by
      rw [norm_mul, hX]
      have hsim : s.im = T := by rw [hs]; simp
      have hs1im : (s + 1).im = T := by rw [hs]; simp
      have h1' : |T| ≤ ‖s‖ := by
        have h := Complex.abs_im_le_norm s; rwa [hsim] at h
      have h2' : |T| ≤ ‖s + 1‖ := by
        have h := Complex.abs_im_le_norm (s + 1); rwa [hs1im] at h
      nlinarith only [mul_le_mul h1' h2' (abs_nonneg T) (norm_nonneg s), hT1, abs_nonneg T]
    have hrepr : detInt χ₁ χ R θw N ρ s
        = LFunction χ u * LFunction (χ * χ₁) u * sieveG χ₁ R θw u χ
            * (N : ℂ) ^ s / (s * (s + 1)) := by
      rw [detInt, ← hu]
    have hnorm : ‖detInt χ₁ χ R θw N ρ s‖
        = ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
            * ‖(N : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
      rw [hrepr, norm_div, norm_mul, norm_mul, norm_mul]
    have hp : (1 + |u.im|) ^ ((1 : ℝ) / 3) ≤ (3 * X) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [hX]; linarith [him2]
    have e1 : ‖LFunction χ u‖ ≤ B * (3 * X) ^ ((1 : ℝ) / 3) :=
      le_trans hL1 (mul_le_mul_of_nonneg_left hp hBpos.le)
    have e2 : ‖LFunction (χ * χ₁) u‖ ≤ B * (3 * X) ^ ((1 : ℝ) / 3) :=
      le_trans hL2 (mul_le_mul_of_nonneg_left hp hBpos.le)
    have hnum : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
        * ‖(N : ℂ) ^ s‖ ≤ B * B * (3 * X) ^ ((2 : ℝ) / 3) * K * NK := by
      have h1' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖
          ≤ (B * (3 * X) ^ ((1 : ℝ) / 3)) * (B * (3 * X) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      have h2' : ‖LFunction χ u‖ * ‖LFunction (χ * χ₁) u‖ * ‖sieveG χ₁ R θw u χ‖
          ≤ ((B * (3 * X) ^ ((1 : ℝ) / 3)) * (B * (3 * X) ^ ((1 : ℝ) / 3))) * K :=
        mul_le_mul h1' hG (norm_nonneg _) (by positivity)
      have h3' := mul_le_mul h2' hNs (norm_nonneg _) (by positivity)
      refine le_trans h3' (le_of_eq ?_)
      calc B * (3 * X) ^ ((1 : ℝ) / 3) * (B * (3 * X) ^ ((1 : ℝ) / 3)) * K * NK
          = B * B * K * ((3 * X) ^ ((1 : ℝ) / 3) * (3 * X) ^ ((1 : ℝ) / 3)) * NK := by ring
        _ = B * B * K * (3 * X) ^ ((2 : ℝ) / 3) * NK := by
            rw [← Real.rpow_add (by positivity)]; norm_num
        _ = B * B * (3 * X) ^ ((2 : ℝ) / 3) * K * NK := by ring
    have hdenpos : (0 : ℝ) < X ^ 2 / 4 := by positivity
    have hmain : ‖detInt χ₁ χ R θw N ρ s‖
        ≤ (4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK) * X ^ (-(4 / 3 : ℝ)) := by
      rw [hnorm]
      refine le_trans (div_le_div_of_nonneg_left (by positivity) hdenpos hss) ?_
      refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)) ?_
      exact le_of_eq (by
        calc B * B * (3 * X) ^ ((2 : ℝ) / 3) * K * NK / (X ^ 2 / 4)
            = B * B * (3 * X) ^ ((2 : ℝ) / 3) * K * NK * (X ^ 2 / 4)⁻¹ := by rw [div_eq_mul_inv]
          _ = B * B * (3 * X) ^ ((2 : ℝ) / 3) * K * NK * (4 * X ^ (-(2 : ℝ))) := by
                rw [inv_quarter_sq hXpos]
          _ = (4 * B * B * K * NK) * ((3 * X) ^ ((2 : ℝ) / 3) * X ^ (-(2 : ℝ))) := by ring
          _ = (4 * B * B * K * NK)
                * (3 ^ ((2 : ℝ) / 3) * (X ^ ((2 : ℝ) / 3) * X ^ (-(2 : ℝ)))) := by
                rw [Real.mul_rpow (by norm_num) hXpos.le]; ring
          _ = (4 * B * B * K * NK) * (3 ^ ((2 : ℝ) / 3) * X ^ (-(4 / 3 : ℝ))) := by
                rw [rpow_combine hXpos]
          _ = 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK * X ^ (-(4 / 3 : ℝ)) := by ring)
    have hconst : 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK
        ≤ B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ + 16 * K * NK
          + 4 * (3 : ℝ) ^ ((2 : ℝ) / 3) * B * B * K * NK + 1 := by
      have h1n : (0 : ℝ) ≤ B * B * K * (M ^ ((2 : ℝ) / 3)) * NK * c⁻¹ := by
        have hMnn := Real.rpow_nonneg hMpos.le ((2 : ℝ) / 3); positivity
      have h2n : (0 : ℝ) ≤ 16 * K * NK := by positivity
      linarith
    exact le_trans hmain (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by positivity) _))

end Work.LinnikAreas.BGTZ
