import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_real_growth
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.norm_completedLFunction_vertical
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_real_growth
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re
import Submission.Commons.NumberTheory.KroneckerSums.sum_product_cons_zero

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Linnik

lemma nat_cast_ge_one {N : ℕ} [NeZero N] : (1 : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))

lemma log_ge_one_of_one_le_add_two {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (x + 2) := by
  have hpos : 0 < x + 2 := by linarith
  have hle3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hle : Real.exp 1 ≤ x + 2 := le_trans hle3 (by linarith)
  have := Real.log_le_log (Real.exp_pos 1) hle
  rwa [Real.log_exp] at this

lemma log_x_add_two_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.log (x + 2) := by
  have hL : 1 ≤ Real.log (x + 2) := log_ge_one_of_one_le_add_two hx
  linarith

lemma log_x_add_three_le_two_log_x_add_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 3) ≤ 2 * Real.log (x + 2) := by
  have hpos1 : 0 < x + 3 := by linarith
  have hpos2 : 0 < x + 2 := by linarith
  have hsq : x + 3 ≤ (x + 2) ^ 2 := by
    nlinarith [sq_nonneg (x + 2)]
  have h := Real.log_le_log hpos1 hsq
  rw [Real.log_pow (x + 2) 2] at h
  norm_num at h
  linarith



-- ============ stubs (delegated) ============
-- ============ inline helpers ============
theorem completedLFunction_eq_mul_gammaFactor_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    simp at hs
  have h := LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  rcases χ.even_or_odd with hE | hO
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Even.gammaFactor_def hE]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hs
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Odd.gammaFactor_def hO]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by
        rw [Complex.add_re, Complex.one_re]
        linarith)
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]

lemma gammaFactor_norm_le_re_of_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : ‖gammaFactor χ s‖ ≤ ‖gammaFactor χ (s.re : ℂ)‖ := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE, Even.gammaFactor_def hE]
    exact Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re s hs
  · rw [Odd.gammaFactor_def hO, Odd.gammaFactor_def hO]
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re (s + 1) (by
      rw [Complex.add_re, Complex.one_re]
      linarith)
    simpa [Complex.add_re] using h

lemma exp_mono {a b : ℝ} (h : a ≤ b) : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr h

/-- growth of the gamma factor at real points, uniform in parity. -/
lemma gammaFactor_norm_real_le {N : ℕ} (χ : DirichletCharacter ℂ N)
    (cg : ℝ) (hcg : 0 ≤ cg)
    (hg : ∀ x : ℝ, 1 / 2 ≤ x → ‖Complex.Gammaℝ (x : ℂ)‖ ≤
       Real.exp (cg * (x + 1) * (Real.log (x + 2) + 1)))
    {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) :
    ‖gammaFactor χ (σ : ℂ)‖ ≤ Real.exp (cg * (σ + 2) * (Real.log (σ + 3) + 1)) := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    have hgσ := hg σ hσ
    have hle : cg * (σ + 1) * (Real.log (σ + 2) + 1) ≤ cg * (σ + 2) * (Real.log (σ + 3) + 1) := by
      have hA0 : 0 ≤ Real.log (σ + 2) + 1 := by
        have hlog : 0 ≤ Real.log (σ + 2) := by
          refine Real.log_nonneg ?_
          linarith
        linarith
      have hA : Real.log (σ + 2) + 1 ≤ Real.log (σ + 3) + 1 := by
        have hpos2 : 0 < σ + 2 := by linarith
        have hxy0 : σ + 2 ≤ σ + 3 := by linarith
        have hlogle := Real.log_le_log hpos2 hxy0
        linarith
      have h1 : (σ + 1) * (Real.log (σ + 2) + 1) ≤ (σ + 2) * (Real.log (σ + 3) + 1) := by
        calc
          (σ + 1) * (Real.log (σ + 2) + 1) ≤ (σ + 2) * (Real.log (σ + 2) + 1) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hA0
          _ ≤ (σ + 2) * (Real.log (σ + 3) + 1) := by
            exact mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ σ + 2)
      have hh := mul_le_mul_of_nonneg_left h1 hcg
      ring_nf at hh ⊢
      exact hh
    exact le_trans hgσ (exp_mono hle)
  · rw [Odd.gammaFactor_def hO]
    have hσ1 : (1 / 2 : ℝ) ≤ σ + 1 := by linarith
    have hg' := hg (σ + 1) hσ1
    have hL2 : ((σ + 1) + 1 : ℝ) = σ + 2 := by ring
    have hL3 : ((σ + 1) + 2 : ℝ) = σ + 3 := by ring
    rw [hL2, hL3] at hg'
    have hArg : (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) := by simp [Complex.ofReal_add]
    rw [hArg]
    exact hg'

lemma one_div_two_le_sigma_inv_le {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (hσ0 : 0 < σ) :
    (2 / σ : ℝ) ≤ 4 := by
  have h1 : (1 / σ : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hσ0]
    linarith
  calc
    (2 / σ : ℝ) = 2 * (1 / σ) := by ring_nf
    _ ≤ 2 * 2 := by exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 4 := by norm_num

lemma norm_le_re_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) : s.re ≤ ‖s‖ := by
  have h := Complex.abs_re_le_norm s
  rwa [abs_of_nonneg hs] at h

/-- log-free: |L(χ,s)| ≤ 4·N·‖s‖ for Re s ≥ 1/2. -/
lemma LFunction_norm_le_four_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) : ‖LFunction χ s‖ ≤ 4 * (N : ℝ) * ‖s‖ := by
  have hσ0 : 0 < s.re := by linarith
  have hL := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane χ hχ hσ0
  have hd : (2 / s.re : ℝ) ≤ 4 := one_div_two_le_sigma_inv_le hs hσ0
  have hNn : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  calc
    ‖LFunction χ s‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := hL
    _ = (2 / s.re) * ((N : ℝ) * ‖s‖) := by ring_nf
    _ ≤ 4 * ((N : ℝ) * ‖s‖) := by
      exact mul_le_mul_of_nonneg_right hd (mul_nonneg hNn (norm_nonneg s))
    _ = 4 * (N : ℝ) * ‖s‖ := by ring

lemma mul_four_N_x_le_exp {Nn x : ℝ} (hNn : 1 ≤ Nn) (hx : 1 ≤ x) :
    4 * Nn * x ≤ Real.exp (x * Real.log Nn + 2 * x) := by
  have hx0 : 0 < x := by linarith
  have h4x0 : 0 < 4 * x := by positivity
  have hlogx : Real.log x ≤ x - 1 := by
    exact Real.log_le_sub_one_of_pos hx0
  have hprod : Real.log (4 * x) ≤ 2 * x := by
    calc
      Real.log (4 * x) = Real.log 4 + Real.log x := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hx0)]
      _ ≤ 2 + (x - 1) := by
        have hlog4 : Real.log 4 ≤ 2 := by
          have h1 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num : (0 : ℝ) < 2)
            linarith
          calc Real.log 4 = Real.log (2 * 2) := by norm_num
            _ = Real.log 2 + Real.log 2 := by
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
            _ ≤ 1 + 1 := add_le_add h1 h1
            _ = 2 := by norm_num
        linarith
      _ ≤ 2 * x := by linarith
  have hlogN : Real.log Nn ≤ x * Real.log Nn := by
    have hlog : 0 ≤ Real.log Nn := Real.log_nonneg hNn
    nlinarith
  have hlogtot : Real.log (4 * Nn * x) ≤ x * Real.log Nn + 2 * x := by
    have hpos4x : 0 < 4 * x := by positivity
    calc
      Real.log (4 * Nn * x) = Real.log (4 * x) + Real.log Nn := by
        rw [show 4 * Nn * x = (4 * x) * Nn by ring]
        rw [Real.log_mul (ne_of_gt hpos4x) (ne_of_gt (by linarith : 0 < Nn))]
      _ ≤ 2 * x + x * Real.log Nn := add_le_add hprod hlogN
      _ = x * Real.log Nn + 2 * x := by ring
  have hpos : 0 < 4 * Nn * x := by positivity
  rw [← Real.exp_log hpos]
  exact exp_mono hlogtot

/-- The main right-half-plane growth bound, with the Gammaℝ-growth constant made explicit. -/
theorem completedL_right_half_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (cg : ℝ) (hcg : 0 ≤ cg)
    (hg : ∀ x : ℝ, 1 / 2 ≤ x → ‖Complex.Gammaℝ (x : ℂ)‖ ≤
       Real.exp (cg * (x + 1) * (Real.log (x + 2) + 1)))
    (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) (hsbig : 1 ≤ ‖s‖) :
    ‖completedLFunction χ s‖ ≤
      Real.exp ((1 + 6 * cg) * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)) := by
  let Nn : ℝ := (N : ℝ)
  let x : ℝ := ‖s‖
  let L : ℝ := Real.log (x + 2)
  have hx : 1 ≤ x := by dsimp [x]; exact hsbig
  have hx0 : 0 ≤ x := by linarith
  have hx0' : 0 < x := by linarith
  have hNn : 1 ≤ Nn := by dsimp [Nn]; exact nat_cast_ge_one
  have hNn0 : 0 ≤ Nn := by linarith
  have hL0 : 0 ≤ L := by dsimp [L]; exact log_x_add_two_nonneg hx
  have hL1 : 1 ≤ L := by dsimp [L]; exact log_ge_one_of_one_le_add_two hx
  have hσ : s.re ≤ x := by
    have hnon : 0 ≤ s.re := by linarith
    dsimp [x]
    exact norm_le_re_of_re_nonneg hnon
  have hσ0 : 0 < s.re := by linarith
  -- completedL = L · gammaFactor, gammaFactor split off vertically, then on the real axis
  have hG : ‖gammaFactor χ s‖ ≤ Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1)) := by
    have hγvert : ‖gammaFactor χ s‖ ≤ ‖gammaFactor χ (s.re : ℂ)‖ := gammaFactor_norm_le_re_of_pos χ hσ0
    have hγ : ‖gammaFactor χ (s.re : ℂ)‖ ≤ Real.exp (cg * (s.re + 2) * (Real.log (s.re + 3) + 1)) :=
      gammaFactor_norm_real_le χ cg hcg hg hs
    have hσ2 : s.re + 2 ≤ x + 2 := by linarith
    have hσ3 : s.re + 3 ≤ x + 3 := by linarith
    have hpos2 : 0 ≤ x + 2 := by linarith
    have hpos3 : 0 ≤ x + 3 := by linarith
    have hlog3le : Real.log (s.re + 3) + 1 ≤ Real.log (x + 3) + 1 := by
      have hp : 0 < s.re + 3 := by linarith
      have hxy1 : s.re + 3 ≤ x + 3 := by linarith
      have hl := Real.log_le_log hp hxy1
      linarith
    have hprod : (s.re + 2) * (Real.log (s.re + 3) + 1) ≤ (x + 2) * (Real.log (x + 3) + 1) := by
      have hA0 : 0 ≤ Real.log (s.re + 3) + 1 := by
        have hlogp : 0 ≤ Real.log (s.re + 3) := by
          refine Real.log_nonneg ?_
          linarith
        linarith
      calc
        (s.re + 2) * (Real.log (s.re + 3) + 1) ≤ (x + 2) * (Real.log (s.re + 3) + 1) := by
          exact mul_le_mul_of_nonneg_right hσ2 hA0
        _ ≤ (x + 2) * (Real.log (x + 3) + 1) := by
          exact mul_le_mul_of_nonneg_left hlog3le hpos2
    have hcgprod : cg * (s.re + 2) * (Real.log (s.re + 3) + 1) ≤ cg * (x + 2) * (Real.log (x + 3) + 1) := by
      have hh := mul_le_mul_of_nonneg_left hprod hcg
      ring_nf at hh ⊢
      exact hh
    exact le_trans (le_trans hγvert hγ) (exp_mono hcgprod)
  have hLfun : ‖LFunction χ s‖ ≤ 4 * Nn * x := by
    dsimp [Nn, x]
    exact LFunction_norm_le_four_mul χ hχ s hs
  have hfac : completedLFunction χ s = LFunction χ s * gammaFactor χ s :=
    completedLFunction_eq_mul_gammaFactor_re_pos χ hσ0
  have hmid : ‖completedLFunction χ s‖ ≤ (4 * Nn * x) * Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1)) := by
    calc
      ‖completedLFunction χ s‖ = ‖LFunction χ s‖ * ‖gammaFactor χ s‖ := by
        rw [hfac, norm_mul]
      _ ≤ (4 * Nn * x) * ‖gammaFactor χ s‖ := by
        exact mul_le_mul_of_nonneg_right hLfun (norm_nonneg _)
      _ ≤ (4 * Nn * x) * Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1)) := by
        exact mul_le_mul_of_nonneg_left hG (by positivity)
  have hBig : 4 * Nn * x ≤ Real.exp (x * Real.log Nn + 2 * x) := by
    dsimp [x]
    exact mul_four_N_x_le_exp hNn hsbig
  have hExp : (4 * Nn * x) * Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1))
      ≤ Real.exp (x * Real.log Nn + 2 * x + cg * (x + 2) * (Real.log (x + 3) + 1)) := by
    have h1 := mul_le_mul hBig (le_rfl : Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1)) ≤ Real.exp (cg * (x + 2) * (Real.log (x + 3) + 1)))
      (Real.exp_nonneg _) (Real.exp_nonneg _)
    rwa [← Real.exp_add] at h1
  -- exponent algebra: x·log N + 2x + cg(x+2)(log(x+3)+1) ≤ (1+6cg)·x·(L + log N + 2)
  have hGbound : cg * (x + 2) * (Real.log (x + 3) + 1) ≤ 6 * cg * x * L + 3 * cg * x := by
    have h32 : x + 2 ≤ 3 * x := by nlinarith
    have hLg : Real.log (x + 3) + 1 ≤ 2 * L + 1 := by
      have hll := log_x_add_three_le_two_log_x_add_two hx
      dsimp [L]
      linarith
    have hA0 : 0 ≤ Real.log (x + 3) + 1 := by
      have h : 0 ≤ Real.log (x + 3) := by
        refine Real.log_nonneg ?_
        linarith
      linarith
    have hA : (x + 2) * (Real.log (x + 3) + 1) ≤ (3 * x) * (Real.log (x + 3) + 1) := by
      exact mul_le_mul_of_nonneg_right h32 hA0
    have hA2 : (3 * x) * (Real.log (x + 3) + 1) ≤ (3 * x) * (2 * L + 1) := by
      exact mul_le_mul_of_nonneg_left hLg (by linarith : 0 ≤ 3 * x)
    have hA3 : (x + 2) * (Real.log (x + 3) + 1) ≤ (3 * x) * (2 * L + 1) := le_trans hA hA2
    have hh := mul_le_mul_of_nonneg_left hA3 hcg
    ring_nf at hh ⊢
    exact hh
  have hxL0 : 0 ≤ x * L := mul_nonneg hx0 hL0
  have hxlogN0 : 0 ≤ x * Real.log Nn := mul_nonneg hx0 (Real.log_nonneg hNn)
  have h1 : x * Real.log Nn ≤ (1 + 6 * cg) * x * Real.log Nn := by
    have hz : 0 ≤ (6 * cg) * x * Real.log Nn := by
      exact mul_nonneg (mul_nonneg (by nlinarith) hx0) (Real.log_nonneg hNn)
    nlinarith
  have h2 : 2 * x + 6 * cg * x * L + 3 * cg * x ≤ (1 + 6 * cg) * x * L + 2 * (1 + 6 * cg) * x := by
    nlinarith [hxL0, hcg]
  have hexp : x * Real.log Nn + 2 * x + cg * (x + 2) * (Real.log (x + 3) + 1)
      ≤ (1 + 6 * cg) * x * (L + Real.log Nn + 2) := by
    calc
      x * Real.log Nn + 2 * x + cg * (x + 2) * (Real.log (x + 3) + 1)
          ≤ x * Real.log Nn + 2 * x + (6 * cg * x * L + 3 * cg * x) := by
              exact add_le_add (le_refl (x * Real.log Nn + 2 * x)) hGbound
      _ = x * Real.log Nn + (2 * x + 6 * cg * x * L + 3 * cg * x) := by ring
      _ ≤ (1 + 6 * cg) * x * Real.log Nn + ((1 + 6 * cg) * x * L + 2 * (1 + 6 * cg) * x) := by
              exact add_le_add h1 h2
      _ = (1 + 6 * cg) * x * (L + Real.log Nn + 2) := by ring
  have hexpEq : (1 + 6 * cg) * x * (L + Real.log Nn + 2)
      = (1 + 6 * cg) * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2) := by
    dsimp [x, L, Nn]
  calc
    ‖completedLFunction χ s‖
        ≤ Real.exp (x * Real.log Nn + 2 * x + cg * (x + 2) * (Real.log (x + 3) + 1)) :=
          le_trans hmid hExp
    _ ≤ Real.exp ((1 + 6 * cg) * x * (L + Real.log Nn + 2)) := exp_mono hexp
    _ = Real.exp ((1 + 6 * cg) * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)) := by
          rw [hexpEq]


theorem completedL_right_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → 1 ≤ ‖s‖ →
      ‖completedLFunction χ s‖ ≤
        Real.exp (c * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)) := by
  rcases Commons.Analysis.SpecialFunctions.Gamma.gammaR_real_growth with ⟨cg, hcg, hg⟩
  refine ⟨1 + 6 * cg, by positivity, ?_⟩
  intro s hs hsbig
  exact completedL_right_half_aux χ hχ cg hcg hg s hs hsbig

-- ============ circle assembly ============
lemma inv_ne_one_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
  simpa using hh

lemma isPrimitive_inv' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact hχ

/-- Norm of the completed L-function via the functional equation
(N is at least 1, root number has norm one). -/
lemma completedLFunction_norm_fe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    ‖completedLFunction χ s‖ =
      (N : ℝ) ^ (1 / 2 - s.re) * ‖completedLFunction χ⁻¹ (1 - s)‖ := by
  have heq := Commons.NumberTheory.DirichletCharacter.completedLFunction_eq χ hχ s
  rw [heq]
  rw [norm_mul, norm_mul]
  have hroot : ‖χ.rootNumber‖ = 1 := Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one χ hχ
  rw [hroot]
  rw [mul_one]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hpow : ‖(N : ℂ) ^ (1 / 2 - s)‖ = (N : ℝ) ^ (1 / 2 - s.re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos (x := (N : ℝ)) hpos (1 / 2 - s))
  rw [hpow]

lemma log_R_add_three_le_two_log_R_add_two {R : ℝ} (hR : 2 ≤ R) :
    Real.log (R + 3) ≤ 2 * Real.log (R + 2) := by
  have hpos1 : 0 < R + 3 := by linarith
  have hpos2 : 0 < R + 2 := by linarith
  have hsq : R + 3 ≤ (R + 2) ^ 2 := by
    nlinarith [sq_nonneg (R + 2)]
  have h := Real.log_le_log hpos1 hsq
  rw [Real.log_pow (R + 2) 2] at h
  norm_num at h
  linarith

/-- exp is non-decreasing and nonnegative linear in a nonnegative multiplier. -/
lemma exp_mul_le_exp_mul {c C x : ℝ} (hC : c ≤ C) (hx : 0 ≤ x) :
    Real.exp (c * x) ≤ Real.exp (C * x) := exp_mono (mul_le_mul_of_nonneg_right hC hx)

lemma norm_one_sub_ge {s : ℂ} (h : 2 ≤ ‖s‖) : 1 ≤ ‖1 - s‖ := by
  -- ‖s‖ ≤ ‖1‖ + ‖1 - s‖ (triangle), so ‖1 - s‖ ≥ ‖s‖ - 1 ≥ 1.
  have htri : ‖s‖ ≤ ‖(1 : ℂ)‖ + ‖1 - s‖ := by
    calc
      ‖s‖ = ‖(1 : ℂ) - (1 - s)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ)‖ + ‖1 - s‖ := by simpa using (norm_sub_le (1 : ℂ) (1 - s))
  have h1 : ‖(1 : ℂ)‖ = 1 := by simp
  rw [h1] at htri
  linarith

/-- The circle growth theorem, with the right-half constants made explicit. -/
theorem completedL_growth_circle_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (c0 c1 : ℝ) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (h0 : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → 1 ≤ ‖s‖ →
       ‖completedLFunction χ s‖ ≤
         Real.exp (c0 * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)))
    (h1 : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → 1 ≤ ‖s‖ →
       ‖completedLFunction χ⁻¹ s‖ ≤
         Real.exp (c1 * ‖s‖ * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2))) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ = R →
      ‖completedLFunction χ s‖ ≤
        Real.exp (c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
  let C : ℝ := c0 + c1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc0C : c0 ≤ C := by dsimp [C]; linarith
  have hc1C : c1 ≤ C := by dsimp [C]; linarith
  let c : ℝ := 4 * C + 8
  refine ⟨c, ?_⟩
  intro R hR s hsnorm
  let Nn : ℝ := (N : ℝ)
  let T : ℝ := Real.log (R + 2) + Real.log Nn + 2
  have hNn : 1 ≤ Nn := by dsimp [Nn]; exact nat_cast_ge_one
  have hNn0 : 0 ≤ Nn := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hT0 : 0 ≤ T := by
    dsimp [T]
    have h1 : 1 ≤ Real.log (R + 2) := log_ge_one_of_one_le_add_two (by linarith)
    have h2 : 0 ≤ Real.log Nn := Real.log_nonneg hNn
    nlinarith
  have hlog : Real.log (R + 3) ≤ 2 * Real.log (R + 2) := log_R_add_three_le_two_log_R_add_two hR
  have hlogN : 0 ≤ Real.log Nn := Real.log_nonneg hNn
  have hRlog : 0 ≤ R * Real.log (R + 2) := mul_nonneg hR0 (by
    exact le_trans (by linarith : (0 : ℝ) ≤ 1) (log_ge_one_of_one_le_add_two (by linarith)))
  have hc : C ≤ c := by dsimp [c]; nlinarith
  by_cases hσ : (1 / 2 : ℝ) ≤ s.re
  · -- right half plane: use the bound for χ at s
    have hsbig : 1 ≤ ‖s‖ := by rw [hsnorm]; linarith
    have hb := h0 s hσ hsbig
    -- ‖Λ χ s‖ ≤ exp(c0·‖s‖·T') with T' = log(‖s‖+2)+logN+2 ; rewrite ‖s‖ = R
    rw [hsnorm] at hb
    have hmono : Real.exp (c0 * R * (Real.log (R + 2) + Real.log Nn + 2))
        ≤ Real.exp (c * R * (Real.log (R + 2) + Real.log Nn + 2)) := by
      have h1 : c0 * R * (Real.log (R + 2) + Real.log Nn + 2) ≤ c * R * (Real.log (R + 2) + Real.log Nn + 2) := by
        have hc0c : c0 ≤ c := by dsimp [c, C]; nlinarith
        have hz : 0 ≤ R * (Real.log (R + 2) + Real.log Nn + 2) := by positivity
        calc
          c0 * R * (Real.log (R + 2) + Real.log Nn + 2) = c0 * (R * (Real.log (R + 2) + Real.log Nn + 2)) := by ring
          _ ≤ c * (R * (Real.log (R + 2) + Real.log Nn + 2)) := mul_le_mul_of_nonneg_right hc0c hz
          _ = c * R * (Real.log (R + 2) + Real.log Nn + 2) := by ring
      exact exp_mono h1
    -- match Nn = (N:ℝ)
    have hb2 : ‖completedLFunction χ s‖ ≤ Real.exp (c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
      convert le_trans hb hmono using 1
    exact hb2
  · -- left: s.re < 1/2, use the functional equation
    let w : ℂ := 1 - s
    have hsbig : 1 ≤ ‖s‖ := by rw [hsnorm]; linarith
    have hwbig : 1 ≤ ‖w‖ := by
      dsimp [w]
      apply norm_one_sub_ge
      rw [hsnorm]
      linarith
    have hwre : (1 / 2 : ℝ) ≤ w.re := by
      have hslt : s.re < 1 / 2 := lt_of_not_ge hσ
      dsimp [w]
      linarith
    have hb := h1 w hwre hwbig
    -- ‖Λ χ⁻¹ w‖ ≤ exp(c1·‖w‖·(log(‖w‖+2)+logN+2))
    have hwub : ‖w‖ ≤ R + 1 := by
      dsimp [w]
      calc
        ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := by simpa using (norm_sub_le (1 : ℂ) s)
        _ = R + 1 := by rw [hsnorm]; simp; ring
    -- FE: ‖Λ χ s‖ = Nn^(1/2 - s.re) * ‖Λ χ⁻¹ w‖
    have hfe := completedLFunction_norm_fe χ hχprim s
    have hσlb : -R ≤ s.re := by
      have h := Complex.abs_re_le_norm s
      have h2 : -‖s‖ ≤ s.re := (abs_le.mp h).1
      rw [hsnorm] at h2
      exact h2
    have hpowle : (1 / 2 - s.re) ≤ R + 1 / 2 := by linarith
    have hpown : (N : ℝ) ^ (1 / 2 - s.re) ≤ (N : ℝ) ^ (R + 1 / 2) := by
      exact Real.rpow_le_rpow_of_exponent_le hNn hpowle
    -- combine:
    have hb2 : ‖completedLFunction χ⁻¹ w‖ ≤
        Real.exp (c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)) := by
      have hw1 : c1 * ‖w‖ * (Real.log (‖w‖ + 2) + Real.log Nn + 2)
          ≤ c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2) := by
        have hlogw : Real.log (‖w‖ + 2) ≤ Real.log (R + 3) := by
          have hpos : 0 < ‖w‖ + 2 := by linarith
          have hle : ‖w‖ + 2 ≤ R + 3 := by linarith
          exact Real.log_le_log hpos hle
        have h1 : ‖w‖ * (Real.log (‖w‖ + 2) + Real.log Nn + 2) ≤ (R + 1) * (Real.log (R + 3) + Real.log Nn + 2) := by
          have hA : Real.log (‖w‖ + 2) + Real.log Nn + 2 ≤ Real.log (R + 3) + Real.log Nn + 2 := by linarith
          have hnn : 0 ≤ Real.log (‖w‖ + 2) + Real.log Nn + 2 := by
            have h1l : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith [hwbig])
            have h2l : 0 ≤ Real.log Nn := Real.log_nonneg hNn
            nlinarith
          calc
            ‖w‖ * (Real.log (‖w‖ + 2) + Real.log Nn + 2) ≤ (R + 1) * (Real.log (‖w‖ + 2) + Real.log Nn + 2) := by
              exact mul_le_mul_of_nonneg_right hwub hnn
            _ ≤ (R + 1) * (Real.log (R + 3) + Real.log Nn + 2) := by
              exact mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ R + 1)
        have hh := mul_le_mul_of_nonneg_left h1 hc1
        ring_nf at hh ⊢
        exact hh
      exact le_trans hb (exp_mono hw1)
    -- now wrap into a single exponent and bound by c·R·T
    have hbig1 : (N : ℝ) ^ (R + 1 / 2) ≤ Real.exp ((R + 1) * Real.log (N : ℝ)) := by
      have hpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
      rw [Real.rpow_def_of_pos hpos (R + 1 / 2)]
      have hlogle : Real.log (N : ℝ) * (R + 1 / 2) ≤ (R + 1) * Real.log (N : ℝ) := by
        nlinarith [Real.log_nonneg hNn]
      exact exp_mono hlogle
    have hb3 : ‖completedLFunction χ s‖ ≤
        Real.exp ((R + 1) * Real.log Nn + c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)) := by
      calc
        ‖completedLFunction χ s‖ = (N : ℝ) ^ (1 / 2 - s.re) * ‖completedLFunction χ⁻¹ w‖ := by
          dsimp [w]
          exact hfe
        _ ≤ (N : ℝ) ^ (R + 1 / 2) * ‖completedLFunction χ⁻¹ w‖ := by
          exact mul_le_mul_of_nonneg_right hpown (norm_nonneg _)
        _ ≤ (N : ℝ) ^ (R + 1 / 2) * Real.exp (c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)) := by
          exact mul_le_mul_of_nonneg_left hb2 (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ)) _)
        _ ≤ Real.exp ((R + 1) * Real.log (N : ℝ)) * Real.exp (c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)) := by
          exact mul_le_mul_of_nonneg_right hbig1 (Real.exp_nonneg _)
        _ = Real.exp ((R + 1) * Real.log (N : ℝ) + c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)) := by
          rw [Real.exp_add]
    -- exponent ≤ c*R*T
    have hlogR2 : 0 ≤ Real.log (R + 2) := by
      exact le_trans (by linarith : (0 : ℝ) ≤ 1) (log_ge_one_of_one_le_add_two (x := R) (by linarith))
    have hsum12 : Real.log (R + 3) + Real.log Nn + 2 ≤ 2 * Real.log (R + 2) + Real.log Nn + 2 := by linarith
    have hB : c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)
        ≤ c1 * (R + 1) * (2 * Real.log (R + 2) + Real.log Nn + 2) := by
      have h1 : (R + 1) * (Real.log (R + 3) + Real.log Nn + 2) ≤ (R + 1) * (2 * Real.log (R + 2) + Real.log Nn + 2) := by
        exact mul_le_mul_of_nonneg_left hsum12 (by linarith : 0 ≤ R + 1)
      have hh := mul_le_mul_of_nonneg_left h1 hc1
      ring_nf at hh ⊢
      exact hh
    have hR2b : R + 1 ≤ 2 * R := by nlinarith
    have hc1l : 4 * c1 ≤ c := by dsimp [c, C]; nlinarith
    have hc2l : 2 * (c1 + 1) ≤ c := by dsimp [c, C]; nlinarith
    have hc3l : 2 * c1 ≤ c := by dsimp [c, C]; nlinarith
    have hcc1 : c0 ≤ c := by dsimp [c, C]; nlinarith
    have hcc2 : 4 * C ≤ c := by dsimp [c, C]; nlinarith
    -- m1: (c1+1)(R+1)·logN ≤ c·R·logN
    have hm1 : (c1 + 1) * (R + 1) ≤ c * R := by
      have hstep1 : (c1 + 1) * (R + 1) ≤ (c1 + 1) * (2 * R) := by
        exact mul_le_mul_of_nonneg_left hR2b (by linarith : 0 ≤ c1 + 1)
      have hstep2 : (c1 + 1) * (2 * R) ≤ c * R := by
        calc
          (c1 + 1) * (2 * R) = (2 * (c1 + 1)) * R := by ring
          _ ≤ c * R := by exact mul_le_mul_of_nonneg_right hc2l (by linarith : 0 ≤ R)
      exact le_trans hstep1 hstep2
    -- m2: 2·c1·(R+1) ≤ c·R
    have hm2 : 2 * c1 * (R + 1) ≤ c * R := by
      calc
        2 * c1 * (R + 1) ≤ 4 * c1 * R := by
          calc
            2 * c1 * (R + 1) ≤ 2 * c1 * (2 * R) := by
              exact mul_le_mul_of_nonneg_left hR2b (by positivity : 0 ≤ 2 * c1)
            _ = 4 * c1 * R := by ring
        _ ≤ c * R := by exact mul_le_mul_of_nonneg_right hc1l (by linarith : 0 ≤ R)
    -- m3: 2·c1·(R+1) ≤ 2·c·R
    have hm3 : 2 * c1 * (R + 1) ≤ 2 * c * R := by
      calc
        2 * c1 * (R + 1) ≤ 4 * c1 * R := by
          calc
            2 * c1 * (R + 1) ≤ 2 * c1 * (2 * R) := by
              exact mul_le_mul_of_nonneg_left hR2b (by positivity : 0 ≤ 2 * c1)
            _ = 4 * c1 * R := by ring
        _ ≤ 2 * c * R := by
          have hcpos : 0 ≤ c := by dsimp [c]; positivity
          exact mul_le_mul_of_nonneg_right (by nlinarith [hc1l, hcpos] : 4 * c1 ≤ 2 * c) (by linarith : 0 ≤ R)
    have hM1 : (c1 + 1) * (R + 1) * Real.log Nn ≤ c * R * Real.log Nn := by
      exact mul_le_mul_of_nonneg_right hm1 hlogN
    have hM2 : 2 * c1 * (R + 1) * Real.log (R + 2) ≤ c * R * Real.log (R + 2) := by
      exact mul_le_mul_of_nonneg_right hm2 hlogR2
    have hM3 : 2 * c1 * (R + 1) ≤ 2 * c * R := hm3
    have hsum : (c1 + 1) * (R + 1) * Real.log Nn + 2 * c1 * (R + 1) * Real.log (R + 2) + 2 * c1 * (R + 1)
        ≤ c * R * Real.log Nn + c * R * Real.log (R + 2) + 2 * c * R := by
      calc
        (c1 + 1) * (R + 1) * Real.log Nn + 2 * c1 * (R + 1) * Real.log (R + 2) + 2 * c1 * (R + 1)
            ≤ c * R * Real.log Nn + 2 * c1 * (R + 1) * Real.log (R + 2) + 2 * c1 * (R + 1) := by
                exact add_le_add (add_le_add hM1 le_rfl) le_rfl
        _ ≤ c * R * Real.log Nn + c * R * Real.log (R + 2) + 2 * c1 * (R + 1) := by
                exact add_le_add (add_le_add le_rfl hM2) le_rfl
        _ ≤ c * R * Real.log Nn + c * R * Real.log (R + 2) + 2 * c * R := by
                exact add_le_add (add_le_add le_rfl le_rfl) hM3
    have hexp : (R + 1) * Real.log Nn + c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)
        ≤ c * R * T := by
      calc
        (R + 1) * Real.log Nn + c1 * (R + 1) * (Real.log (R + 3) + Real.log Nn + 2)
            ≤ (R + 1) * Real.log Nn + c1 * (R + 1) * (2 * Real.log (R + 2) + Real.log Nn + 2) := by
                exact add_le_add (le_refl ((R + 1) * Real.log Nn)) hB
        _ = (c1 + 1) * (R + 1) * Real.log Nn + 2 * c1 * (R + 1) * Real.log (R + 2) + 2 * c1 * (R + 1) := by ring
        _ ≤ c * R * Real.log Nn + c * R * Real.log (R + 2) + 2 * c * R := hsum
        _ = c * R * (Real.log (R + 2) + Real.log Nn + 2) := by ring
        _ = c * R * T := by dsimp [T]
    have hb4 : ‖completedLFunction χ s‖ ≤ Real.exp (c * R * T) := by
      exact le_trans hb3 (exp_mono hexp)
    have hb5 : ‖completedLFunction χ s‖ ≤ Real.exp (c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
      convert hb4 using 1 <;> dsimp [T, Nn]
    exact hb5


/-- **Growth of the completed Dirichlet L-function on circles.**  For a primitive
non-trivial character `χ mod N` there is an absolute constant `c` such that for every
`R ≥ 2` and every `s` with `‖s‖ = R`,
`‖Λ(χ,s)‖ ≤ exp (c·R·(log(R+2) + log N + 2))`.  Split the circle at `Re s = 1/2`:
on the right half-plane `Λ = L·gammaFactor` with `|L(χ,s)| ≤ 2·N·‖s‖/Re s` (Abel
summation, `LFunction_norm_half_plane`) and `|gammaFactor| ≤ Γℝ(Re s)` bounded by the
real Gamma growth (`gammaR_real_growth`); on the left half-plane use the functional
equation `Λ(χ,s) = N^(1/2-s)·ε(χ)·Λ(χ⁻¹,1-s)` to reflect to the right half-plane. -/
theorem completedL_growth_circle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ = R →
      ‖DirichletCharacter.completedLFunction χ s‖ ≤
        Real.exp (c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
  rcases completedL_right_half χ hχ with ⟨c0, hc0, h0⟩
  rcases completedL_right_half (χ⁻¹) (inv_ne_one_of_ne_one χ hχ) with ⟨c1, hc1, h1⟩
  rcases completedL_growth_circle_aux χ hχ hχprim c0 c1 hc0 hc1 h0 h1 with ⟨c, hc⟩
  exact ⟨c, hc⟩
end Commons.NumberTheory.Linnik
