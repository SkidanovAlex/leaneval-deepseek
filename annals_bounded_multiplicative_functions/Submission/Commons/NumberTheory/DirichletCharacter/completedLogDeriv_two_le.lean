import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_lim_log_sub_sum_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Filter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### Helper lemmas for the proof of `completedLogDeriv_two_le` -/

lemma re_div_two (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring_nf

lemma im_div_two (s : ℂ) : (s / 2).im = s.im / 2 := by
  rw [Complex.div_im]
  norm_num
  ring_nf

lemma neq_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  have hre := congrArg Complex.re h
  rw [re_div_two] at hre
  have hneg : (-(m : ℂ)).re ≤ 0 := by simp
  linarith

lemma differentiableAt_Gamma_half (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma (s / 2) := by
  exact Complex.differentiableAt_Gamma (s / 2) (neq_neg_nat_of_re_pos hs)

lemma Gamma_half_ne_zero (s : ℂ) (hs : 0 < s.re) : Complex.Gamma (s / 2) ≠ 0 := by
  exact Complex.Gamma_ne_zero (neq_neg_nat_of_re_pos hs)

lemma cpow_pow_ne_zero (s : ℂ) : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
  exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))

lemma logDeriv_Gammaℝ_formula (s : ℂ) (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
  let f : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let g : ℂ → ℂ := fun z => Gamma (z / 2)
  have hc : (Real.pi : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    exact Real.pi_pos
  have hldf : logDeriv f s = -(Complex.log (Real.pi : ℂ)) / 2 := by
    dsimp [f]
    have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
    have hld := logDeriv_comp (f := fun w : ℂ => (Real.pi : ℂ) ^ w)
      (g := fun z : ℂ => -z / 2) (x := s)
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ w) (-s / 2)) hinner
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_const_cpow hc] at hld
    have hder : deriv (fun z : ℂ => -z / 2) s = -((2 : ℂ)⁻¹) := by
      simp
      norm_num
    rw [hder] at hld
    rw [Function.comp_def] at hld
    calc
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
          = Complex.log (Real.pi : ℂ) * (-((2 : ℂ)⁻¹)) := by
              simpa using hld
      _ = -(Complex.log (Real.pi : ℂ)) / 2 := by
            rw [div_eq_mul_inv]
            ring
  have hldg : logDeriv g s = Complex.digamma (s / 2) / 2 := by
    dsimp [g]
    have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
    have hld := logDeriv_comp (f := Gamma) (g := fun z : ℂ => z / 2) (x := s)
      (differentiableAt_Gamma_half s hs) hdiv
    have hder : deriv (fun z : ℂ => z / 2) s = (2 : ℂ)⁻¹ := by simp
    rw [hder] at hld
    rw [Function.comp_def] at hld
    rw [← Complex.digamma_def] at hld
    calc
      logDeriv (fun z : ℂ => Gamma (z / 2)) s = Complex.digamma (s / 2) * ((2 : ℂ)⁻¹) := by
        simpa using hld
      _ = Complex.digamma (s / 2) / 2 := by
        simp [div_eq_mul_inv]
  have hfun : Complex.Gammaℝ = (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) := by
    funext z
    rw [Complex.Gammaℝ_def]
  have hldG : logDeriv Complex.Gammaℝ s =
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s := by
    exact congrArg (fun F : ℂ → ℂ => logDeriv F s) hfun
  have hmul := logDeriv_mul (x := s) (f := f) (g := g) (cpow_pow_ne_zero s)
    (Gamma_half_ne_zero s hs) (by
      have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
      exact hinner.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))) (by
      have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
      exact (Complex.differentiableAt_Gamma (s / 2) (neq_neg_nat_of_re_pos hs)).comp s hdiv)
  calc
    logDeriv Complex.Gammaℝ s
        = logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s := hldG
    _ = logDeriv (fun z : ℂ => f z * g z) s := by
          dsimp [f, g]
    _ = logDeriv f s + logDeriv g s := hmul
    _ = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
          rw [hldf]
          rw [hldg]

lemma differentiableAt_Gammaℝ (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hfun : Complex.Gammaℝ = (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) := by
    funext z
    rw [Complex.Gammaℝ_def]
  rw [hfun]
  refine (DifferentiableAt.mul ?_ ?_)
  · have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
    exact hinner.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  · have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
    exact (Complex.differentiableAt_Gamma (s / 2) (neq_neg_nat_of_re_pos hs)).comp s hdiv

lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hO.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [Complex.add_re]
    simp
    linarith

lemma differentiableAt_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 0 < s.re) : DifferentiableAt ℂ (gammaFactor χ) s := by
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact hE.gammaFactor_def z
    rw [hfun]
    exact differentiableAt_Gammaℝ s hs
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      exact hO.gammaFactor_def z
    rw [hfun]
    have hs1 : 0 < (s + 1).re := by
      rw [Complex.add_re]
      simp
      linarith
    have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ (s + 1) hs1
    have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
    simpa [Function.comp_def] using (hf.comp s hg)

lemma half_expand (x y : ℝ) :
    (((x : ℂ) + Complex.I * (y : ℂ)) / 2) =
      ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

lemma norm_logDeriv_Gammaℝ_le (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 16) :
    ‖logDeriv Complex.Gammaℝ ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |y|) + 8) := by
  let s : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hs : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have hx1' : (1 : ℝ) / 4 ≤ x / 2 := by linarith
  have hx2' : x / 2 ≤ 8 := by linarith
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (x / 2) (y / 2) hx1' hx2'
  have hdg' : ‖Complex.digamma (s / 2)‖ ≤ Real.log (2 + |y / 2|) + 8 := by
    rw [half_expand x y]
    exact hdg
  have hdg'' : ‖Complex.digamma (s / 2)‖ / 2 ≤ (Real.log (2 + |y|) + 8) / 2 := by
    have hlogmono : Real.log (2 + |y / 2|) ≤ Real.log (2 + |y|) := by
      apply Real.log_le_log
      · positivity
      · have hy0 : 0 ≤ |y| := abs_nonneg y
        have : |y / 2| ≤ |y| := by
          rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          exact div_le_self hy0 (by norm_num)
        linarith
    have h1 : ‖Complex.digamma (s / 2)‖ / 2 ≤ (Real.log (2 + |y / 2|) + 8) / 2 :=
      div_le_div_of_nonneg_right hdg' (by norm_num)
    exact le_trans h1 (div_le_div_of_nonneg_right (by linarith) (by norm_num))
  have hformula := logDeriv_Gammaℝ_formula s hs
  rw [hformula]
  have hnorm1 : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ ≤ Real.log Real.pi / 2 := by
    have hlogpi_nonneg : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlogR : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      simpa using (Complex.ofReal_log (x := Real.pi) (by positivity : 0 ≤ Real.pi)).symm
    rw [hlogR]
    rw [norm_div]
    rw [norm_neg]
    rw [Complex.norm_of_nonneg hlogpi_nonneg]
    norm_num
  have hnorm2 : ‖(Complex.digamma (s / 2) / 2 : ℂ)‖ ≤ (Real.log (2 + |y|) + 8) / 2 := by
    rw [norm_div]
    have : ‖Complex.digamma (s / 2)‖ / ‖(2 : ℂ)‖ ≤ (Real.log (2 + |y|) + 8) / 2 := by
      norm_num
      exact hdg''
    simpa using this
  calc
    ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 : ℂ)‖
        ≤ ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ + ‖(Complex.digamma (s / 2) / 2 : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |y|) + 8) / 2 := add_le_add hnorm1 hnorm2
    _ = Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |y|) + 8) := by ring

lemma norm_logDeriv_gammaFactor_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖logDeriv (gammaFactor χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8) := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact hE.gammaFactor_def z
    have hb : ‖logDeriv Complex.Gammaℝ s‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8) := by
      have := norm_logDeriv_Gammaℝ_le 2 T (by norm_num) (by norm_num)
      simpa [s] using this
    simpa [hfun] using hb
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      exact hO.gammaFactor_def z
    have hsr : s.re = 2 := by
      dsimp [s]
      simp
    have hs1b : 0 < (s + 1).re := by
      have hre : (s + 1).re = s.re + 1 := by simp [Complex.add_re]
      rw [hre, hsr]
      norm_num
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ (s + 1) hs1b
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
      have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    have hb : ‖logDeriv Complex.Gammaℝ (s + 1)‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8) := by
      have hS : s + 1 = (3 : ℂ) + Complex.I * (T : ℂ) := by
        dsimp [s]
        ring
      rw [hS]
      exact norm_logDeriv_Gammaℝ_le 3 T (by norm_num) (by norm_num)
    calc
      ‖logDeriv (gammaFactor χ) s‖ = ‖logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s‖ := by
        rw [hfun]
      _ = ‖logDeriv Complex.Gammaℝ (s + 1)‖ := by rw [hldcomp]
      _ ≤ Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8) := hb

/-- The logarithmic derivative of the completed L-function decomposes as the sum of the
logarithmic derivatives of the `L`-function and the gamma factor, on the right half-plane. -/
lemma logDeriv_completedLFunction_eq_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    (hLs : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  let P : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ z * gammaFactor χ z
  have hzre : ∀ z : ℂ, 0 < z.re → DirichletCharacter.completedLFunction χ z =
      DirichletCharacter.LFunction χ z * gammaFactor χ z := by
    intro z hzre
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hzre
      simpa using hzre
    have hL := LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
    have hg : gammaFactor χ z ≠ 0 := gammaFactor_ne_zero_of_re_pos χ z hzre
    symm
    calc
      DirichletCharacter.LFunction χ z * gammaFactor χ z
          = (DirichletCharacter.completedLFunction χ z / gammaFactor χ z) * gammaFactor χ z := by
            rw [hL]
      _ = DirichletCharacter.completedLFunction χ z := by
            field_simp [hg]
  have hP_eq : (fun z : ℂ => DirichletCharacter.completedLFunction χ z) =ᶠ[𝓝 s]
      (fun z : ℂ => DirichletCharacter.LFunction χ z * gammaFactor χ z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact hzre z hz
  have hder_eq : deriv (DirichletCharacter.completedLFunction χ) s = deriv P s := by
    have h := hP_eq.deriv_eq
    simpa [P] using h
  have hP_s : DirichletCharacter.completedLFunction χ s = P s := hzre s hs
  have hg0 : gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ s hs
  have hdL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    differentiableAt_LFunction χ s (Or.inr hχ)
  have hdG : DifferentiableAt ℂ (gammaFactor χ) s := differentiableAt_gammaFactor χ s hs
  have hmul := logDeriv_mul (x := s) (f := DirichletCharacter.LFunction χ) (g := gammaFactor χ)
    hLs hg0 hdL hdG
  calc
    logDeriv (DirichletCharacter.completedLFunction χ) s
        = deriv P s / P s := by
            rw [logDeriv_apply]
            rw [hder_eq]
            rw [hP_s]
    _ = logDeriv P s := by
            rw [logDeriv_apply]
    _ = logDeriv (DirichletCharacter.LFunction χ) s + logDeriv (gammaFactor χ) s := by
            simpa [P, Pi.mul_def] using hmul

/-- Pointwise bound for the logarithmic derivative of the completed Dirichlet L-function on the
vertical line `Re s = 2`:

`‖logDeriv (completedLFunction χ) (2 + iT)‖ ≤ log (2 + |T|) + 20` for all real `T`,
uniformly over nontrivial characters `χ` (any modulus `N`).  The constant `20` is loose.

Method: `completedLFunction χ = gammaFactor χ · LFunction χ` away from the poles of the gamma
factor, in the sense of `LFunction_eq_completed_div_gammaFactor` (valid here since
`Re (2+iT) = 2 > 0`); `gammaFactor χ (2+iT) ≠ 0`.  Take the logarithmic derivative:
`logDeriv Λ = logDeriv (gammaFactor χ) + logDeriv (LFunction χ)` at `2+iT` (use a
`logDeriv_mul`-type lemma).  Then:
- `logDeriv (LFunction χ) (2+iT)` is bounded by 8:
  `Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le`.
- `logDeriv (gammaFactor χ) (2+iT)` = `logDeriv (Gammaℝ) (2+iT)` if `χ.Even`, and
  `logDeriv (Gammaℝ) (2+iT + 1)` if `χ.Odd` (`Even.gammaFactor_def` / `Odd.gammaFactor_def`).
  Since `Gammaℝ s = π ^ (-s/2) * Gamma (s/2)` (`Complex.Gammaℝ_def`), its logarithmic
  derivative is `-log π / 2 + (1/2) · digamma (s/2)` (cpow log-derivative `-log π/2` plus the
  chain rule `(1/2)·digamma(s/2)` through `Gamma ∘ (s/2)`), so its norm is at most
  `(log π)/2 + (1/2) · (log (2 + |T|/2) + 8)` by
  `Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound` applied at
  `x = Re((2+iT+ε)/2) ∈ {1, 3/2} ⊆ [1/4, 8]` and `y = T/2` (for ε = 0 or 1 the even/odd shift),
  using `log (2 + |T|/2) ≤ log (2 + |T|)`.
  Everything together is well below `log (2+|T|) + 20`; any constant ≤ 20 is fine. -/
theorem completedLogDeriv_two_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      Real.log (2 + |T|) + 20 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : 0 < s.re := by
    dsimp [s]
    simp
  have hLs0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hnorm : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
      simpa [s] using L_lower_re_two_explicit χ hχ T
    have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hpos)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs0
  have hnormL : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 8 := by
    rw [logDeriv_apply]
    dsimp [s]
    exact logDeriv_L_two_le χ hχ T
  have hnormG : ‖logDeriv (gammaFactor χ) s‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8) := by
    simpa [s] using norm_logDeriv_gammaFactor_le χ T
  have hnorm : ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      8 + (Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8)) := by
    rw [hdec]
    exact le_trans (norm_add_le _ _) (add_le_add hnormL hnormG)
  have hX0 : 0 ≤ Real.log (2 + |T|) := by
    apply Real.log_nonneg
    linarith [abs_nonneg T]
  have hpi : Real.log Real.pi ≤ 4 := by
    have h1 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hfin : 8 + (Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 8)) ≤
      Real.log (2 + |T|) + 20 := by
    nlinarith
  simpa [s] using le_trans hnorm hfin

end Commons.NumberTheory.DirichletCharacter