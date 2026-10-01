import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_small
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_small
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight
import Submission.Commons.NumberTheory.DirichletCharacter.re_logDeriv_completedLFunction_three_halves
import Submission.Commons.NumberTheory.DirichletCharacter.re_logDeriv_completedLFunction_three_halves_sharp
import Submission.Commons.Analysis.Complex.divisor_sum_le_circleAverage
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.pfPole_pointwise
import Submission.Commons.NumberTheory.DirichletCharacter.poleXIntegral_le
import Submission.Commons.NumberTheory.DirichletCharacter.circleIntegralX_integrable
import Submission.Commons.NumberTheory.DirichletCharacter.rectPoleArea_perimeter_le
import Submission.Commons.NumberTheory.DirichletCharacter.verticalLogDeriv_integral_le
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.Analysis.Complex.rectZeroCount_boundary_le
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_sharp_upper
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_norm_le_one
import Submission.Commons.Analysis.Integral.boxKernel_le_rebased
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le

open Complex DirichletCharacter Filter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! Continuity infrastructure. -/

/-- `logDeriv` of the completed Dirichlet L-function is continuous away from its zeros
(it is the quotient `Λ'/Λ` of two entire functions, `Λ ≠ 0` there). -/
lemma contOn_logDeriv_completedLFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
      {z | DirichletCharacter.completedLFunction χ z ≠ 0} := by
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hdF : Differentiable ℂ F := by simpa [F] using (differentiable_completedLFunction (χ := χ) hχ)
  have hder_cont : ContinuousOn (deriv F) {z | F z ≠ 0} := hdF.deriv.continuous.continuousOn
  have hF_cont : ContinuousOn F {z | F z ≠ 0} := hdF.continuous.continuousOn
  have hq : ContinuousOn (fun z : ℂ => deriv F z / F z) {z | F z ≠ 0} := by
    exact ContinuousOn.div hder_cont hF_cont (by intro z hz; exact hz)
  apply ContinuousOn.congr hq
  intro z hz
  rfl

/-- The vertical line `Re = 2` contains no zero of the completed L-function of a primitive
non-trivial character. -/
lemma completedLFunction_ne_zero_re_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
  intro hz
  have hstrip := zerosInStrip χ hχ hχprim ((2 : ℂ) + Complex.I * (T : ℂ)) hz
  have hre : (((2 : ℂ) + Complex.I * (T : ℂ)).re) = 2 := by simp
  have hlt : ((2 : ℂ) + Complex.I * (T : ℂ)).re < 1 := by simpa [hre] using hstrip.2
  norm_num at hlt

/-- The vertical line `Re = -1` contains no zero of the completed L-function of a primitive
non-trivial character. -/
lemma completedLFunction_ne_zero_re_neg_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    DirichletCharacter.completedLFunction χ ((-1 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
  intro hz
  have hstrip := zerosInStrip χ hχ hχprim ((-1 : ℂ) + Complex.I * (T : ℂ)) hz
  have hre : (((-1 : ℂ) + Complex.I * (T : ℂ)).re) = -1 := by simp
  have hgt : (0 : ℝ) < ((-1 : ℂ) + Complex.I * (T : ℂ)).re := by simpa [hre] using hstrip.1
  norm_num at hgt

/-- `T ↦ ‖logDeriv Λ(2+iT)‖` is continuous on ℝ. -/
lemma cont_two_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    Continuous (fun T : ℝ =>
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
  have hcont : ContinuousOn (fun z : ℂ =>
      logDeriv (DirichletCharacter.completedLFunction χ) z) {z | DirichletCharacter.completedLFunction χ z ≠ 0} :=
    contOn_logDeriv_completedLFunction χ hχ
  have hcur : Continuous (fun T : ℝ => (2 : ℂ) + Complex.I * (T : ℂ)) := by fun_prop
  have hmaps : ∀ T : ℝ, (2 : ℂ) + Complex.I * (T : ℂ) ∈
      {z | DirichletCharacter.completedLFunction χ z ≠ 0} := by
    intro T
    exact completedLFunction_ne_zero_re_two χ hχ hχprim T
  have hcomp : ContinuousOn (fun T : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))) Set.univ := by
    exact hcont.comp hcur.continuousOn (by intro T hT; exact hmaps T)
  have hcomp' : Continuous (fun T : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))) := continuousOn_univ.mp hcomp
  exact hcomp'.norm

/-- `T ↦ ‖logDeriv Λ(-1+iT)‖` is continuous on ℝ. -/
lemma cont_neg_one_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    Continuous (fun T : ℝ =>
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))‖) := by
  have hcont : ContinuousOn (fun z : ℂ =>
      logDeriv (DirichletCharacter.completedLFunction χ) z) {z | DirichletCharacter.completedLFunction χ z ≠ 0} :=
    contOn_logDeriv_completedLFunction χ hχ
  have hcur : Continuous (fun T : ℝ => (-1 : ℂ) + Complex.I * (T : ℂ)) := by fun_prop
  have hmaps : ∀ T : ℝ, (-1 : ℂ) + Complex.I * (T : ℂ) ∈
      {z | DirichletCharacter.completedLFunction χ z ≠ 0} := by
    intro T
    exact completedLFunction_ne_zero_re_neg_one χ hχ hχprim T
  have hcomp : ContinuousOn (fun T : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (T : ℂ))) Set.univ := by
    exact hcont.comp hcur.continuousOn (by intro T hT; exact hmaps T)
  have hcomp' : Continuous (fun T : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (T : ℂ))) := continuousOn_univ.mp hcomp
  exact hcomp'.norm

/-! Elementary monotonicity / nonnegativity facts. -/

/-- `c ≥ 1/2` implies `0 ≤ c`. -/
lemma hc_nonneg {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) : 0 ≤ c := by linarith

/-- `log N ≥ 0`. -/
lemma logN_nonneg {N : ℕ} [NeZero N] : 0 ≤ Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1nat : 1 ≤ N := by omega
    exact_mod_cast hN1nat
  exact Real.log_nonneg hN1

/-- For `c ≥ 1/2` the log-argument `2 + c + 3` is `≥ 1` (so its log is nonnegative). -/
lemma log_arg_ge_one {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) : (1 : ℝ) ≤ 2 + c + 3 := by nlinarith

/-- For `T ∈ [c, c+1]`, `c ≥ 1/2`: `2 + |T| ≤ 2 + c + 3`. -/
lemma T_bound_arg {c T : ℝ} (hc : (1 : ℝ) / 2 ≤ c) (hT1 : c ≤ T) (hT2 : T ≤ c + 1) :
    2 + |T| ≤ 2 + c + 3 := by
  have hT0 : 0 ≤ T := le_trans (hc_nonneg hc) hT1
  rw [abs_of_nonneg hT0]
  linarith

/-! Unit-window vertical integrals from the pointwise bounds. -/

/-- Integrate the pointwise bound on `Re = 2` over `T ∈ [c, c+1]`:
`∫_c^{c+1} ‖logDeriv Λ(2+iT)‖ dT ≤ (1/2)·log (2 + c + 3) + 5`. -/
lemma twoUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) :
    (∫ T : ℝ in c..c + 1,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖) ≤
      (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5 := by
  let f : ℝ → ℝ := fun T => ‖logDeriv (DirichletCharacter.completedLFunction χ)
    ((2 : ℂ) + Complex.I * (T : ℂ))‖
  let g : ℝ → ℝ := fun _ : ℝ => (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5
  have hcf : Continuous f := by simpa [f] using cont_two_line χ hχ hχprim
  have hf : IntervalIntegrable f MeasureTheory.volume c (c + 1) := hcf.intervalIntegrable c (c + 1)
  have hg : IntervalIntegrable g MeasureTheory.volume c (c + 1) := continuous_const.intervalIntegrable c (c + 1)
  have hcc1 : c ≤ c + 1 := by linarith
  have hpt : ∀ T ∈ Set.Icc c (c + 1), f T ≤ g T := by
    intro T hT
    have hb := completedLogDeriv_two_small χ hχ T
    have hmono : Real.log (2 + |T|) ≤ Real.log (2 + c + 3) := by
      apply Real.log_le_log
      · positivity
      · exact T_bound_arg hc hT.1 hT.2
    have hmul : (1 / 2 : ℝ) * Real.log (2 + |T|) ≤ (1 / 2 : ℝ) * Real.log (2 + c + 3) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    dsimp [f, g]
    linarith
  have hmono := intervalIntegral.integral_mono_on hcc1 hf hg hpt
  have hconst : (∫ T : ℝ in c..c + 1, g T) = (1 : ℝ) * ((1 / 2 : ℝ) * Real.log (2 + c + 3) + 5) := by
    dsimp [g]
    rw [intervalIntegral.integral_const]
    simp
  calc
    (∫ T : ℝ in c..c + 1,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        = ∫ T : ℝ in c..c + 1, f T := by simp [f]
    _ ≤ ∫ T : ℝ in c..c + 1, g T := hmono
    _ = (1 : ℝ) * ((1 / 2 : ℝ) * Real.log (2 + c + 3) + 5) := hconst
    _ = (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5 := by ring

/-- Integrate the pointwise bound on `Re = -1` over `T ∈ [c, c+1]`:
`∫_c^{c+1} ‖logDeriv Λ(-1+iT)‖ dT ≤ log N + (1/2)·log (2 + c + 3) + 5`. -/
lemma negOneUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) :
    (∫ T : ℝ in c..c + 1,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))‖) ≤
      Real.log (N : ℝ) + (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5 := by
  let f : ℝ → ℝ := fun T => ‖logDeriv (DirichletCharacter.completedLFunction χ)
    ((-1 : ℂ) + Complex.I * (T : ℂ))‖
  let g : ℝ → ℝ := fun _ : ℝ => Real.log (N : ℝ) + (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5
  have hcf : Continuous f := by simpa [f] using cont_neg_one_line χ hχ hχprim
  have hf : IntervalIntegrable f MeasureTheory.volume c (c + 1) := hcf.intervalIntegrable c (c + 1)
  have hg : IntervalIntegrable g MeasureTheory.volume c (c + 1) := continuous_const.intervalIntegrable c (c + 1)
  have hcc1 : c ≤ c + 1 := by linarith
  have hpt : ∀ T ∈ Set.Icc c (c + 1), f T ≤ g T := by
    intro T hT
    have hb := completedLogDeriv_neg_one_small χ hχ hχprim T
    have hmono : Real.log (2 + |T|) ≤ Real.log (2 + c + 3) := by
      apply Real.log_le_log
      · positivity
      · exact T_bound_arg hc hT.1 hT.2
    have hmul : (1 / 2 : ℝ) * Real.log (2 + |T|) ≤ (1 / 2 : ℝ) * Real.log (2 + c + 3) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    dsimp [f, g]
    linarith
  have hmono := intervalIntegral.integral_mono_on hcc1 hf hg hpt
  have hconst : (∫ T : ℝ in c..c + 1, g T) = (1 : ℝ) * (Real.log (N : ℝ) + (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5) := by
    dsimp [g]
    rw [intervalIntegral.integral_const]
    simp
  calc
    (∫ T : ℝ in c..c + 1,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))‖)
        = ∫ T : ℝ in c..c + 1, f T := by simp [f]
    _ ≤ ∫ T : ℝ in c..c + 1, g T := hmono
    _ = (1 : ℝ) * (Real.log (N : ℝ) + (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5) := hconst
    _ = Real.log (N : ℝ) + (1 / 2 : ℝ) * Real.log (2 + c + 3) + 5 := by ring

/-- The horizontal integrand `x ↦ ‖logDeriv Λ(x+iT)‖` is continuous on ℝ whenever the
height `T` is not the imaginary part of a zero of `Λ` (so the horizontal line carries no
pole of the log-derivative). -/
lemma cont_horizontal_at {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {T : ℝ}
    (hT : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T) :
    Continuous (fun x : ℝ =>
        ‖logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) + Complex.I * (T : ℂ))‖) := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hdΛ : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction (χ := χ) hχ)
  have hΛnz_at : ∀ x : ℝ, Λ ((x : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
    intro x hz
    have : ((x : ℂ) + Complex.I * (T : ℂ)).im = T := by simp
    exact hT ((x : ℂ) + Complex.I * (T : ℂ)) (by simpa [Λ] using hz) this
  have hc_at_z : ∀ z : ℂ, Λ z ≠ 0 → ContinuousAt (fun w : ℂ => ‖logDeriv Λ w‖) z := by
    intro z hz
    have hder : ContinuousAt (deriv Λ) z := (hdΛ.deriv.continuous).continuousAt
    have hΛc : ContinuousAt Λ z := hdΛ.continuous.continuousAt
    have hdiv : ContinuousAt (fun w : ℂ => deriv Λ w / Λ w) z := hder.div hΛc hz
    have heq : (fun w : ℂ => logDeriv Λ w) = fun w : ℂ => deriv Λ w / Λ w := by
      funext w
      rfl
    have hld : ContinuousAt (fun w : ℂ => logDeriv Λ w) z := by
      simpa [heq] using hdiv
    exact hld.norm
  apply continuous_iff_continuousAt.mpr
  intro x
  have h1 : ContinuousAt (fun w : ℂ => ‖logDeriv Λ w‖) ((x : ℂ) + Complex.I * (T : ℂ)) :=
    hc_at_z ((x : ℂ) + Complex.I * (T : ℂ)) (hΛnz_at x)
  have hγ : ContinuousAt (fun x' : ℝ => (x' : ℂ) + Complex.I * (T : ℂ)) x := by
    exact (by fun_prop : Continuous (fun x' : ℝ => (x' : ℂ) + Complex.I * (T : ℂ))).continuousAt
  have hcomp : ContinuousAt (fun x' : ℝ =>
      ‖logDeriv Λ ((x' : ℂ) + Complex.I * (T : ℂ))‖) x := by
    exact ContinuousAt.comp (f := fun x' : ℝ => (x' : ℂ) + Complex.I * (T : ℂ))
      (g := fun w : ℂ => ‖logDeriv Λ w‖) h1 hγ
  simpa [Λ] using hcomp

/-! Finiteness of zero heights in a unit window (needed for any "generic height" /
Markov / a.e. argument over `T`). -/

/-- At most finitely many heights `T ∈ [c,c+1]` support a zero of the completed
L-function of a primitive non-trivial character (for `c ≥ 1/2` the zeros at such
heights lie in the disk `closedBall 0 (c+3)`, whose divisor support is finite). -/
lemma finite_zeroHeights_window_closed {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) :
    Set.Finite {T : ℝ | c ≤ T ∧ T ≤ c + 1 ∧
      ∃ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 ∧ u.im = T} := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have h_eq : {T : ℝ | c ≤ T ∧ T ≤ c + 1 ∧ ∃ u : ℂ,
        DirichletCharacter.completedLFunction χ u = 0 ∧ u.im = T} =
      {T : ℝ | c ≤ T ∧ T ≤ c + 1 ∧ ∃ u : ℂ, Λ u = 0 ∧ u.im = T} := by
    simp [Λ]
  rw [h_eq]
  have hdΛ : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction (χ := χ) hχ)
  have hΛ_ne0 : Λ ≠ 0 := by
    intro hz
    have hpt := congrFun hz ((2 : ℂ) + Complex.I * (0 : ℂ))
    have htwo : Λ ((2 : ℂ) + Complex.I * (0 : ℂ)) ≠ 0 := by
      simpa [Λ] using completedLFunction_ne_zero_re_two χ hχ hχprim (0 : ℝ)
    exact htwo hpt
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall (0 : ℂ) (c + 3)) := by
    intro z hz
    exact hdΛ.analyticAt z
  have hsupp : (Function.support (MeromorphicOn.divisor Λ
      (Metric.closedBall (0 : ℂ) (c + 3)))).Finite :=
    Commons.Analysis.Complex.divisor_support_finite_closedBall (f := Λ) (a := (0 : ℂ))
      (ρ := c + 3) hAn
  let Z : Set ℂ := {u | Λ u = 0 ∧ ‖u‖ ≤ c + 3}
  have hZ_sub : Z ⊆ Function.support (MeromorphicOn.divisor Λ
      (Metric.closedBall (0 : ℂ) (c + 3))) := by
    intro u hu
    have hu0 : Λ u = 0 := hu.1
    have huB : u ∈ Metric.closedBall (0 : ℂ) (c + 3) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu.2
    exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hdΛ hΛ_ne0 huB hu0
  have hZ_fin : Z.Finite := hsupp.subset hZ_sub
  have hTsub : {T : ℝ | c ≤ T ∧ T ≤ c + 1 ∧ ∃ u : ℂ, Λ u = 0 ∧ u.im = T} ⊆
      (fun u : ℂ => u.im) '' Z := by
    intro T hT
    rcases hT with ⟨h1, h2, u, hu0, huT⟩
    refine ⟨u, ?_, huT⟩
    constructor
    · exact hu0
    · -- show ‖u‖ ≤ c + 3 from Im u = T ∈ [c, c+1] and 0 < Re u < 1
      have hstrip := zerosInStrip χ hχ hχprim u (by simpa [Λ] using hu0)
      have hre0 : 0 ≤ u.re := le_of_lt hstrip.1
      have hre1 : u.re ≤ 1 := le_of_lt hstrip.2
      have hT0 : 0 ≤ T := le_trans (hc_nonneg hc) h1
      have hns : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
        calc
          ‖u‖ ^ 2 = Complex.normSq u := by rw [← Complex.normSq_eq_norm_sq]
          _ = u.re ^ 2 + u.im ^ 2 := by rw [Complex.normSq_apply]; ring
      have hre_sq : u.re ^ 2 ≤ 1 ^ 2 := by
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hre0] using hre1)
      have him_sq : u.im ^ 2 ≤ (c + 1) ^ 2 := by
        have huT0 : 0 ≤ u.im := by simpa [huT] using hT0
        have hub : |u.im| ≤ c + 1 := by
          rw [abs_of_nonneg huT0]
          linarith
        have hub' : |u.im| ≤ |c + 1| := by
          simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c + 1)] using hub
        exact sq_le_sq.mpr hub'
      have hsq : ‖u‖ ^ 2 ≤ (c + 3) ^ 2 := by
        nlinarith [hns, hre_sq, him_sq]
      have hc3 : 0 ≤ c + 3 := by linarith
      have habs : |‖u‖| ≤ |c + 3| := (sq_le_sq.mp hsq)
      rwa [abs_of_nonneg (norm_nonneg u), abs_of_nonneg hc3] at habs
  exact (hZ_fin.image (fun u : ℂ => u.im)).subset hTsub

/-! ### SESSION-8 helper lemmas: Poisson/Herglotz machinery for `carleman_logDeriv`

The three lemmas below are the translation layer of Mathlib's Poisson-integral machinery
(`Mathlib/Analysis/Complex/Harmonic/Poisson.lean`) to an arbitrary centre `c`, together
with the elementary algebraic identity that turns the boundary values `log‖ζ-u‖` into the
harmonic extension `log‖R² - conj(u-c)(w-c)‖ - log R`.  They are the building blocks of
the Carleman–Heilbronn formula `carleman_logDeriv` described in the SESSION-8 note below
(requested from the commons as `Analysis/Complex/carleman_logDeriv`). -/

/-- `circleMap 0 R θ + c = circleMap c R θ`. -/
lemma circleMap_zero_add (c : ℂ) (R θ : ℝ) :
    _root_.circleMap (0 : ℂ) R θ + c = _root_.circleMap c R θ := by
  simp [_root_.circleMap, add_comm]

open MeasureTheory in
/-- A point of the open ball is off the bounding sphere (port helper). -/
private lemma not_mem_sphere_abs_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball c R) :
    w ∉ Metric.sphere c |R| := by
  intro h
  rw [Metric.mem_sphere] at h
  rw [Metric.mem_ball] at hw
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg hw
  rw [abs_of_pos hR] at h
  linarith

/-- **General-centre derivative of the Herglotz–Riesz kernel average** (translation of
Mathlib's `hasDerivAt_circleAverage_herglotzRieszKernel_smul`).  For a circle-integrable
`g : ℂ → ℂ` and `w` inside the circle of centre `c` and radius `R`,

    ∂_w circleAverage (herglotzRieszKernel c w · g) c R
      = circleAverage (2(ζ-c)/((ζ-c)-(w-c))² · g ζ) c R.

At `w = c` the right-hand side is `circleAverage (fun ζ => (2/(ζ-c)) * g ζ) c R`, i.e. the
Poisson-derivative of the boundary data, which is the term appearing in the Carleman
formula. -/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul' {g : ℂ → ℂ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hg : CircleIntegrable g c R) (hw : w ∈ Metric.ball c R) :
    HasDerivAt (fun u => Real.circleAverage (fun ζ => herglotzRieszKernel c u ζ * g ζ) c R)
      (Real.circleAverage (fun ζ => (2 * (ζ - c) / ((ζ - c) - (w - c)) ^ 2) * g ζ) c R) w := by
  have hG : CircleIntegrable (fun z => g (z + c)) 0 R := by
    rw [circleIntegrable_def] at hg ⊢
    refine hg.congr ?_
    intro θ _
    exact congrArg g (circleMap_zero_add c R θ).symm
  have hw' : w - c ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball]
    simpa [dist_eq_norm] using hw
  have hmain := hasDerivAt_circleAverage_herglotzRieszKernel_smul (f := fun z => g (z + c)) hG
    (not_mem_sphere_abs_of_mem_ball hw')
  have hfun : (fun u => Real.circleAverage (fun ζ => herglotzRieszKernel c u ζ * g ζ) c R)
      = (fun u => Real.circleAverage (fun z => herglotzRieszKernel 0 u z * g (z + c)) 0 R) ∘
        (fun w => w - c) := by
    funext u
    rw [Function.comp_apply]
    rw [← Real.circleAverage_map_add_const (f := fun ζ => herglotzRieszKernel c u ζ * g ζ)
      (c := c)]
    congr 1
    funext z
    rw [herglotzRieszKernel_add_const]
  have hder : Real.circleAverage (fun ζ => (2 * (ζ - c) / ((ζ - c) - (w - c)) ^ 2) * g ζ) c R
      = Real.circleAverage (fun z => (2 * z / (z - (w - c)) ^ 2) * g (z + c)) 0 R := by
    rw [← Real.circleAverage_map_add_const
      (f := fun ζ => (2 * (ζ - c) / ((ζ - c) - (w - c)) ^ 2) * g ζ) (c := c)]
    congr 1
    funext z
    simp only [add_sub_cancel_right]
  rw [hfun, hder]
  exact hmain.comp_sub_const w c

/-! The **Poisson extension of `log‖·-u‖`** (the step that converts the boundary integral of
`carleman_logDeriv` into the per-zero polar term `1/(c-u) - conj(c-u)/R²`) is proved below as
`circleAverage_poissonExtension_logNorm_sub`, on top of `norm_sq_sub_conj_mul`. -/

/-- **Algebraic identity behind the Poisson extension of `log‖·-u‖`.**  For `‖ξ‖ = R`,

    ‖R² - conj(a)·ξ‖ = R·‖ξ - a‖.

Taking `a = u - c`, `ξ = ζ - c` with `‖ζ - c‖ = R` this says
`log‖R² - conj(u-c)(ζ-c)‖ - log R = log‖ζ - u‖`, i.e. the harmonic function
`w ↦ log‖R² - conj(u-c)(w-c)‖ - log R` (harmonic because `|conj(u-c)(w-c)| < R²` on the
ball when `‖u-c‖ < R`) has the boundary values `log‖·-u‖`; by the Poisson integral formula
it is therefore the harmonic extension of `log‖·-u‖`, and

    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • (log‖·-u‖)) c R
      = log‖R² - conj(u-c)(w-c)‖ - log R      (‖u-c‖ < R, w ∈ ball c R).

(That Poisson-extension identity is the step which produces the per-zero polar term
`1/(c-u) - conj(c-u)/R²` of the Carleman formula.) -/
lemma norm_sq_sub_conj_mul {R : ℝ} {a ξ : ℂ} (hξ : ‖ξ‖ = R) :
    ‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) a * ξ‖ = R * ‖ξ - a‖ := by
  have hξn : ξ.re * ξ.re + ξ.im * ξ.im = R^2 := by
    have h := Complex.normSq_eq_norm_sq ξ
    rw [Complex.normSq_apply] at h
    rw [h, hξ]
  have hN : Complex.normSq (((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) a * ξ)
      = R^2 * Complex.normSq (ξ - a) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [← hξn]
    ring
  have hX := Complex.normSq_eq_norm_sq (((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) a * ξ)
  have hY := Complex.normSq_eq_norm_sq (ξ - a)
  rw [hX, hY] at hN
  have h1 : (0:ℝ) ≤ ‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) a * ξ‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ R * ‖ξ - a‖ := by
    have h3 := norm_nonneg (ξ - a)
    nlinarith [hξ, norm_nonneg ξ]
  nlinarith [hN, h1, h2, sq_nonneg (‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) a * ξ‖ - R * ‖ξ - a‖)]

/-! **WARNING — the naive "right half = box[1,2] + log N" decomposition is FALSE.**

The left-half analogue (`logDeriv_leftHalf_avg`) is proved as
`∫_{-1}^0 = ∫_1^2 ‖logDeriv Λ‖ + log N` using the FE transfer
`logDeriv Λ(χ)(s) = -log N - logDeriv Λ(χ⁻¹)(1-s)` (pointwise, `Re s ≤ 0`).
It is tempting to split the right half the same way,
`∫_0^2 = ∫_0^1 + ∫_1^2` with `∫_1^2 ≤ 20+3·log N+4·log(2+c+3)` and `∫_0^1 ≤ log N`.
**The bound `∫_0^1 ‖logDeriv Λ(χ)(x+iT)‖ dx ≤ log N` is false** (independently of the
T-window): for χ mod 3, direct numerical evaluation of
`logDeriv Λ(s) = -(log π)/2 + digamma((s+1)/2)/2 + L'/L(s,χ)` (verified against a finite
difference of `Λ(s) = Complex.Gammaℝ (s+1) · L(s,χ)`) gives
`∫_0^1 ‖logDeriv Λ(x+iT)‖ dx ≈ 2.223` at `T = 20`, `≈ 2.933` at `T = 50`,
`≈ 4.620` at `T = 500`, all `> log 3 = 1.0986`.

Reason: the FE reflection is an *involution*, `A(x) + conj(A(1-x)) = -log N` where
`A(x) = logDeriv Λ(x+iT)`; on `[0,1]` it maps `[0,1]` to itself (and `1-x ∈ [-1,0]` for
`x ∈ [1,2]`). Hence `∫_0^1‖A(x)‖dx = ∫_0^1‖log N + A(u)‖du ≤ log N + ∫_0^1‖A‖` is a
tautology, and any "folding" of `[0,2]` onto itself via the reflection is likewise a
tautology. Consequently `∫_0^1` must be controlled analytically.

The correct target box constant `20+4·(log N+log(2+c+3))` is *not* tight for these
regimes: for χ mod 3 the true double integral
`∫_c^{c+1}∫_0^2 ‖logDeriv Λ‖` is ≈ 2.8 at `c = 10`, ≈ 4.1 at `c = 15.5`, ≈ 4.7 at
`c = 50`, all far below `20+4(log N+log(2+c+3))`. What makes the proof hard is only the
crude per-zero loss, not the constant.

Reduction in this file: `horizontalGoodLine_bound` bounds the x-integral pointwise in T
by the smooth `Re = 2` line plus the pole sum `Σ_u m_u·2/|T-u.im|` plus the circle
remainder; integrating in T over a unit window hits the (log-divergent) near-zero weights,
so the usable reduction must be the **two-dimensional** pole area
`Σ_u m_u·∫_{c}^{c+1}∫_0^2 (2-x)/(‖s-u‖·‖2+iT-u‖)`, whose per-zero weight is O(1)
(`poleArea_box_le`, `rectPoleArea_perimeter_le`). The remaining crux is a
Riemann–von-Mangoldt-quality *local* window zero count with logarithmic constant
`≈ 1/π` (the `windowCount_unit`/`windowZeroCount65` bottleneck), which is not derivable
from the Jensen-based counts in the commons (`completedL_zeroCount`, cw ≈ 20–60) and is
mutually dependent with a horizontal-log-derivative bound. -/

/-- **Poisson extension of `log‖·-u‖`.**  For `‖u-c‖ < R` and `w` inside the circle of
centre `c` and radius `R`, the Poisson integral of the boundary function `log‖·-u‖` equals
`log‖R² - conj(u-c)(w-c)‖ - log R`.

This is the identity that turns the harmonic extension of `log‖·-u‖` into the per-zero polar
term `1/(c-u) - conj(c-u)/R²` of the Carleman–Heilbronn formula `carleman_logDeriv`
(Heath-Brown 1992, Lemma 3.2): the harmonic function
`h w = log‖R² - conj(u-c)(w-c)‖ - log R` has the boundary values `log‖ζ-u‖` on `sphere c R`
(by `norm_sq_sub_conj_mul`), and the general-centre Poisson formula
`HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul` identifies it with the Poisson
integral. -/
theorem circleAverage_poissonExtension_logNorm_sub {u c w : ℂ} {R : ℝ}
    (hu : ‖u - c‖ < R) (hw : w ∈ Metric.ball c R) :
    Real.circleAverage (fun ζ => (Complex.re ∘ herglotzRieszKernel c w) ζ * Real.log ‖ζ - u‖) c R
      = Real.log ‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (w - c)‖ - Real.log R := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hu
  let A : ℂ := (starRingEnd ℂ) (u - c)
  let P : ℂ → ℂ := fun z => ((R^2 : ℝ) : ℂ) - A * (z - c)
  have hPne : ∀ z ∈ Metric.closedBall c R, P z ≠ 0 := by
    intro z hz
    have hzR : ‖z - c‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have hlt : ‖A * (z - c)‖ < R^2 := by
      have hAn : A = (starRingEnd ℂ) (u - c) := rfl
      rw [hAn, norm_mul, Complex.norm_conj]
      calc ‖u - c‖ * ‖z - c‖ ≤ ‖u - c‖ * R := by gcongr
        _ < R * R := by nlinarith
        _ = R^2 := by ring
    have hre : 0 < (P z).re := by
      have hre' : (P z).re = R^2 - (A * (z - c)).re := by
        simp only [P, Complex.sub_re, Complex.ofReal_re]
      rw [hre']
      have := Complex.re_le_norm (A * (z - c))
      linarith
    intro h0
    rw [h0] at hre
    simp at hre
  have hharm0 : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖P z‖)
      (Metric.closedBall c R) :=
    fun z hz => (by fun_prop : AnalyticAt ℂ P z).harmonicAt_log_norm (hPne z hz)
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖P z‖ - Real.log R)
      (Metric.closedBall c R) :=
    hharm0.sub (InnerProductSpace.harmonicOnNhd_const (Real.log R))
  have hpois := hharm.circleAverage_re_herglotzRieszKernel_smul
    (f := fun z => Real.log ‖P z‖ - Real.log R) hw
  have hsphere : ∀ ζ ∈ Metric.sphere c R, Real.log ‖ζ - u‖ = Real.log ‖P ζ‖ - Real.log R := by
    intro ζ hζ
    have hζR : ‖ζ - c‖ = R := by
      rw [Metric.mem_sphere, dist_eq_norm] at hζ; exact hζ
    have hpos : 0 < ‖ζ - u‖ := by
      have h := abs_norm_sub_norm_le (ζ - c) (u - c)
      have hsub : (ζ - c) - (u - c) = ζ - u := by ring
      rw [hsub, hζR, abs_of_pos (by linarith : (0:ℝ) < R - ‖u - c‖)] at h
      linarith
    have hmul := norm_sq_sub_conj_mul (R := R) (a := u - c) (ξ := ζ - c) hζR
    have hsub : ζ - c - (u - c) = ζ - u := by ring
    rw [hsub] at hmul
    have hPeq : P ζ = ((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (ζ - c) := by
      simp only [P, A]
    have hlog : Real.log ‖P ζ‖ = Real.log R + Real.log ‖ζ - u‖ := by
      rw [hPeq, hmul, Real.log_mul hR.ne' hpos.ne']
    linarith
  change Real.circleAverage
      (fun ζ => (Complex.re ∘ herglotzRieszKernel c w) ζ * Real.log ‖ζ - u‖) c R
      = Real.log ‖P w‖ - Real.log R
  rw [← hpois]
  refine Real.circleAverage_congr_sphere (fun ζ hζ => ?_)
  simp only [Function.comp_apply]
  rw [hsphere ζ (by simpa [abs_of_pos hR] using hζ)]
  simp [smul_eq_mul]

/-- **General-centre analyticity of the Herglotz–Riesz kernel average** (translation of
Mathlib's `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`, which is stated at centre
`0`): for circle-integrable `g`, the function
`w ↦ circleAverage (herglotzRieszKernel c w · g) c R` is analytic on `ball c R`. -/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul' {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : CircleIntegrable g c R) :
    AnalyticOnNhd ℂ (fun w => Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * g ζ) c R)
      (Metric.ball c R) := by
  have hG : CircleIntegrable (fun z => g (z + c)) 0 R := by
    rw [circleIntegrable_def] at hg ⊢
    refine hg.congr ?_
    intro θ _
    exact congrArg g (circleMap_zero_add c R θ).symm
  have hmain := analyticOnNhd_circleAverage_herglotzRieszKernel_smul (f := fun z => g (z + c)) hG
  have hfun : (fun w => Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * g ζ) c R)
      = (fun u => Real.circleAverage (fun z => herglotzRieszKernel 0 u z * g (z + c)) 0 R) ∘
        (fun w => w - c) := by
    funext u
    rw [Function.comp_apply]
    rw [← Real.circleAverage_map_add_const (f := fun ζ => herglotzRieszKernel c u ζ * g ζ) (c := c)]
    congr 1
    funext z
    rw [herglotzRieszKernel_add_const]
  rw [hfun]
  refine hmain.comp ?_ ?_
  · exact analyticOnNhd_id.sub analyticOnNhd_const
  · intro w hw
    refine Set.mem_compl (not_mem_sphere_abs_of_mem_ball (c := 0) ?_)
    show w - c ∈ Metric.ball (0 : ℂ) R
    rw [Metric.mem_ball] at hw ⊢
    simpa [dist_eq_norm] using hw

/-- **Carleman–Heilbronn formula, zero-free case.**  If `f` is analytic and non-vanishing on
the closed disc `closedBall c R` (`R > 0`), then the logarithmic derivative of `f` at `c` is
the Poisson–Herglotz derivative of `log‖f‖`:

    f'(c)/f(c) = circleAverage (fun ζ => (2/(ζ-c)) * (log‖f ζ‖ : ℂ)) c R.

This is the cancellation-aware form of the identity `f'/f = 2·∂_w log‖f‖`: it turns
`Σ_ρ (1/(s-ρ) + 1/ρ)` into a *signed* circle integral of `log‖f‖` (plus, in the general case,
a polar sum over the zeros inside the circle).  Proof: `H := f · exp(-V)`, where `V` is the
complex Poisson integral of `log‖f‖`, has constant modulus `1`, so by the maximum modulus
principle it is constant, whence `f'/f = V'`, and `V'` is computed by
`hasDerivAt_circleAverage_herglotzRieszKernel_smul'`. -/
theorem logDeriv_eq_circleAverage_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hne : ∀ z ∈ Metric.closedBall c R, f z ≠ 0) :
    deriv f c / f c
      = Real.circleAverage (fun ζ => (2 / (ζ - c)) * (Real.log ‖f ζ‖ : ℂ)) c R := by
  have hc_ball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hne_sphere : ∀ z ∈ Metric.sphere c R, f z ≠ 0 :=
    fun z hz => hne z (Metric.sphere_subset_closedBall hz)
  let u : ℂ → ℝ := fun ζ => Real.log ‖f ζ‖
  let G : ℂ → ℂ := fun ζ => ((u ζ : ℝ) : ℂ)
  have hu_cont : ContinuousOn u (Metric.sphere c R) := by
    have h1 : ContinuousOn (fun ζ => ‖f ζ‖) (Metric.sphere c R) :=
      continuous_norm.comp_continuousOn
        ((hf.differentiableOn.continuousOn).mono Metric.sphere_subset_closedBall)
    exact h1.log (fun ζ hζ => norm_ne_zero_iff.mpr (hne_sphere ζ hζ))
  have hG_cont : ContinuousOn G (Metric.sphere c R) :=
    Complex.continuous_ofReal.comp_continuousOn hu_cont
  have hGint : CircleIntegrable G c R := hG_cont.circleIntegrable (le_of_lt hR)
  let V : ℂ → ℂ := fun w => Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R
  have hV_an : AnalyticOnNhd ℂ V (Metric.ball c R) :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul' hGint
  have hV_diff : DifferentiableOn ℂ V (Metric.ball c R) := hV_an.differentiableOn
  have hharm : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c R) :=
    fun z hz => (hf z hz).harmonicAt_log_norm (hne z hz)
  have hReV : ∀ w ∈ Metric.ball c R, (V w).re = u w := by
    intro w hw
    have hint_w : CircleIntegrable (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R := by
      have h0 := hGint.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere (not_mem_sphere_abs_of_mem_ball hw))
      rw [show (herglotzRieszKernel c w • G) = fun ζ => herglotzRieszKernel c w ζ * G ζ by
        funext ζ
        show herglotzRieszKernel c w ζ • G ζ = herglotzRieszKernel c w ζ * G ζ
        exact smul_eq_mul _ _] at h0
      exact h0
    have h1 : (Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R).re
        = Real.circleAverage (fun ζ => (herglotzRieszKernel c w ζ * G ζ).re) c R :=
      (Complex.reCLM.circleAverage_comp_comm
        (f := fun ζ => herglotzRieszKernel c w ζ * G ζ) hint_w).symm
    show (Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R).re = u w
    rw [h1]
    have h2 : Real.circleAverage (fun ζ => (herglotzRieszKernel c w ζ * G ζ).re) c R
        = Real.circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • u) c R := by
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp only [Function.comp_apply, Pi.smul_apply, G]
      rw [Complex.mul_re]
      simp
    rw [h2]
    exact hharm.circleAverage_re_herglotzRieszKernel_smul hw
  let H : ℂ → ℂ := fun w => f w * Complex.exp (-(V w))
  have hHnorm : ∀ w ∈ Metric.ball c R, ‖H w‖ = 1 := by
    intro w hw
    have hfw : f w ≠ 0 := hne w (Metric.ball_subset_closedBall hw)
    show ‖f w * Complex.exp (-(V w))‖ = 1
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hReV w hw]
    simp only [u, neg_re]
    rw [Real.exp_neg, Real.exp_log (norm_pos_iff.mpr hfw)]
    field_simp
  have hf_diff : DifferentiableOn ℂ f (Metric.ball c R) :=
    (hf.mono Metric.ball_subset_closedBall).differentiableOn
  have hexp_diff : DifferentiableOn ℂ (fun w => Complex.exp (-(V w))) (Metric.ball c R) :=
    Complex.differentiable_exp.comp_differentiableOn hV_diff.neg
  have hH_diff : DifferentiableOn ℂ H (Metric.ball c R) := hf_diff.mul hexp_diff
  have hle : ∀ z ∈ Metric.ball c R, ‖H z‖ ≤ ‖H c‖ := by
    intro z hz
    rw [hHnorm z hz, hHnorm c hc_ball]
  have hmax : IsMaxOn (norm ∘ H) (Metric.ball c R) c := by
    intro z hz
    simpa [Function.comp_apply] using hle z hz
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball c R).isPreconnected Metric.isOpen_ball hH_diff hc_ball hmax
  have hevent : H =ᶠ[𝓝 c] fun _ => H c := by
    filter_upwards [Metric.ball_mem_nhds c hR] with z hz
    exact hconst hz
  have hH0 : HasDerivAt H 0 c :=
    (hasDerivAt_const (c := H c) (x := c)).congr_of_eventuallyEq hevent
  have hHderiv : HasDerivAt H
      (deriv f c * Complex.exp (-(V c)) + f c * (Complex.exp (-(V c)) * (-(deriv V c)))) c := by
    have hf' : HasDerivAt f (deriv f c) c :=
      (hf_diff.differentiableAt (Metric.ball_mem_nhds c hR)).hasDerivAt
    have hV' : HasDerivAt V (deriv V c) c :=
      (hV_diff.differentiableAt (Metric.ball_mem_nhds c hR)).hasDerivAt
    have hexp : HasDerivAt (fun w => Complex.exp (-(V w)))
        (Complex.exp (-(V c)) * (-(deriv V c))) c := hV'.neg.cexp
    exact hf'.mul hexp
  have hzero : deriv f c * Complex.exp (-(V c))
      + f c * (Complex.exp (-(V c)) * (-(deriv V c))) = 0 := hHderiv.unique hH0
  have hmain : deriv f c = f c * deriv V c := by
    have hexpne : Complex.exp (-(V c)) ≠ 0 := Complex.exp_ne_zero _
    have h1 : (deriv f c - f c * deriv V c) * Complex.exp (-(V c)) = 0 := by
      linear_combination hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hexpne)
  have hfc : f c ≠ 0 := hne c (Metric.mem_closedBall_self (le_of_lt hR))
  rw [hmain, mul_div_cancel_left₀ _ hfc]
  have hVd := hasDerivAt_circleAverage_herglotzRieszKernel_smul' (g := G) hGint hc_ball
  rw [hVd.deriv]
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hζc : ζ - c ≠ 0 := by
    intro h0
    have hR' : ‖ζ - c‖ = R := by
      rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] at hζ; exact hζ
    rw [h0, norm_zero] at hR'
    linarith
  simp only [G, u, sub_self, sub_zero]
  field_simp

/-- **Carleman polar term (dipole identity).**  The Poisson–Herglotz derivative of the
single boundary logarithm `log‖·-u‖` is `-conj(u-c)/R²`:

    Real.circleAverage (fun ζ => (2/(ζ-c)) * (log‖ζ-u‖ : ℂ)) c R = -conj(u-c)/R².

This is the per-zero polar term of the Carleman–Heilbronn formula.  Proof: the complex
Poisson integral `V` of `log‖·-u‖` and `L w := log(R² - conj(u-c)(w-c))` are both analytic on
`ball c R`, their real parts differ by the constant `-log R` (the Poisson-extension identity
`circleAverage_poissonExtension_logNorm_sub`), so `V - L` is constant and `V' = L'`; `L'` is
computed by the chain rule for `Complex.log` (`P c = R²`). -/
theorem circleAverage_dipole_logNorm_sub {u c : ℂ} {R : ℝ} (hu : ‖u - c‖ < R) :
    Real.circleAverage (fun ζ => (2 / (ζ - c)) * (Real.log ‖ζ - u‖ : ℂ)) c R
      = - (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2 := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hu
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  let G : ℂ → ℂ := fun ζ => ((Real.log ‖ζ - u‖ : ℝ) : ℂ)
  have hGcont : ContinuousOn G (Metric.sphere c R) := by
    have h1 : ContinuousOn (fun ζ => ‖ζ - u‖) (Metric.sphere c R) :=
      continuous_norm.comp_continuousOn
        ((continuous_id.sub continuous_const).continuousOn)
    have hne : ∀ ζ ∈ Metric.sphere c R, ‖ζ - u‖ ≠ 0 := by
      intro ζ hζ
      have hζR : ‖ζ - c‖ = R := by
        rw [Metric.mem_sphere, dist_eq_norm] at hζ; exact hζ
      have h := abs_norm_sub_norm_le (ζ - c) (u - c)
      have hsub : (ζ - c) - (u - c) = ζ - u := by ring
      rw [hsub, hζR, abs_of_pos (by linarith : (0:ℝ) < R - ‖u - c‖)] at h
      exact ne_of_gt (by linarith : (0:ℝ) < ‖ζ - u‖)
    exact Complex.continuous_ofReal.comp_continuousOn (h1.log hne)
  have hGint : CircleIntegrable G c R := hGcont.circleIntegrable (le_of_lt hR)
  let V : ℂ → ℂ := fun w => Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R
  have hV_an : AnalyticOnNhd ℂ V (Metric.ball c R) :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul' hGint
  have hReV : ∀ w ∈ Metric.ball c R, (V w).re
      = Real.log ‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (w - c)‖ - Real.log R := by
    intro w hw
    have hint_w : CircleIntegrable (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R := by
      have h0 := hGint.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere (not_mem_sphere_abs_of_mem_ball hw))
      rw [show (herglotzRieszKernel c w • G) = fun ζ => herglotzRieszKernel c w ζ * G ζ by
        funext ζ
        show herglotzRieszKernel c w ζ • G ζ = herglotzRieszKernel c w ζ * G ζ
        exact smul_eq_mul _ _] at h0
      exact h0
    have h1 : (Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R).re
        = Real.circleAverage (fun ζ => (herglotzRieszKernel c w ζ * G ζ).re) c R :=
      (Complex.reCLM.circleAverage_comp_comm
        (f := fun ζ => herglotzRieszKernel c w ζ * G ζ) hint_w).symm
    show (Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * G ζ) c R).re
      = Real.log ‖((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (w - c)‖ - Real.log R
    rw [h1]
    have h2 : Real.circleAverage (fun ζ => (herglotzRieszKernel c w ζ * G ζ).re) c R
        = Real.circleAverage
            ((Complex.re ∘ herglotzRieszKernel c w) • (fun ζ => Real.log ‖ζ - u‖)) c R := by
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp only [Function.comp_apply, Pi.smul_apply, G]
      rw [Complex.mul_re]
      simp
    rw [h2]
    exact circleAverage_poissonExtension_logNorm_sub hu hw
  let P : ℂ → ℂ := fun w => ((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (w - c)
  have hP_mem : ∀ w ∈ Metric.ball c R, P w ∈ Complex.slitPlane := by
    intro w hw
    rw [Complex.mem_slitPlane_iff]
    left
    have hwR : ‖w - c‖ < R := by
      rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
    have hlt : ((starRingEnd ℂ) (u - c) * (w - c)).re ≤ ‖(starRingEnd ℂ) (u - c) * (w - c)‖ :=
      Complex.re_le_norm _
    have hnorm : ‖(starRingEnd ℂ) (u - c) * (w - c)‖ < R^2 := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖u - c‖ * ‖w - c‖ ≤ ‖u - c‖ * R := by gcongr
        _ < R * R := by nlinarith
        _ = R^2 := by ring
    have hre : (P w).re = R^2 - ((starRingEnd ℂ) (u - c) * (w - c)).re := by
      simp only [P, Complex.sub_re, Complex.ofReal_re]
    rw [hre]; linarith
  let L : ℂ → ℂ := fun w => Complex.log (P w)
  have hL_an : AnalyticOnNhd ℂ L (Metric.ball c R) := by
    have hP_diff : DifferentiableOn ℂ P (Metric.ball c R) := by fun_prop
    have hL_diff : DifferentiableOn ℂ L (Metric.ball c R) := by
      intro w hw
      exact ((Complex.differentiableAt_log (hP_mem w hw)).comp w
        (hP_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hw))).differentiableWithinAt
    exact hL_diff.analyticOnNhd Metric.isOpen_ball
  have hRe : ∀ w ∈ Metric.ball c R, ((V - L) w).re = -Real.log R := by
    intro w hw
    have h1 : (V w).re = Real.log ‖P w‖ - Real.log R := by
      simpa only [P] using hReV w hw
    have h2 : (L w).re = Real.log ‖P w‖ := by
      simp only [L, Complex.log_re]
    simp only [Pi.sub_apply, Complex.sub_re, h1, h2]
    ring
  obtain ⟨k, hk⟩ := AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const (hV_an.sub hL_an) hRe
    Metric.isOpen_ball ((convex_ball c R).isConnected ⟨c, hc⟩)
  have hPderiv : HasDerivAt P (-(starRingEnd ℂ) (u - c)) c := by
    have h1 : HasDerivAt (fun y : ℂ => (starRingEnd ℂ) (u - c) * (y - c))
        ((starRingEnd ℂ) (u - c) * 1) c :=
      ((hasDerivAt_id c).sub_const c).const_mul ((starRingEnd ℂ) (u - c))
    have h2 : HasDerivAt (fun y : ℂ => ((R^2 : ℝ) : ℂ) - (starRingEnd ℂ) (u - c) * (y - c))
        (0 - (starRingEnd ℂ) (u - c) * 1) c :=
      (hasDerivAt_const c (((R^2 : ℝ) : ℂ))).sub h1
    simpa only [zero_sub, mul_one, P] using h2
  have hLderiv : HasDerivAt L (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2) c := by
    have hPc : P c = ((R^2 : ℝ) : ℂ) := by
      simp only [P]; ring
    have hlog : HasDerivAt (Complex.log ∘ P)
        (((R^2 : ℝ) : ℂ)⁻¹ * (-(starRingEnd ℂ) (u - c))) c := by
      have h := (Complex.hasDerivAt_log (hP_mem c hc)).comp c hPderiv
      simpa only [hPc] using h
    have hval : (((R^2 : ℝ) : ℂ)⁻¹ * (-(starRingEnd ℂ) (u - c)))
        = - (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2 := by
      rw [show (((R^2 : ℝ) : ℂ)) = (R : ℂ)^2 by push_cast; ring]
      field_simp
    rw [hval] at hlog
    exact hlog
  have hVderiv : HasDerivAt V (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2) c := by
    have hev : L =ᶠ[𝓝 c] fun w => V w - ((V c) - (L c)) := by
      filter_upwards [Metric.ball_mem_nhds c hR] with w hw
      have h1 : V w - L w = V c - L c := by
        show (V - L) w = (V - L) c
        rw [hk w hw, hk c hc]
      linear_combination -h1
    have h1 : HasDerivAt (fun w => V w - ((V c) - (L c)))
        (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2) c :=
      hLderiv.congr_of_eventuallyEq hev.symm
    have h2 := h1.add_const ((V c) - (L c))
    simpa [sub_eq_add_neg, add_assoc] using h2
  have hd := hasDerivAt_circleAverage_herglotzRieszKernel_smul' (g := G) hGint hc
  have hval : Real.circleAverage
      (fun ζ => (2 * (ζ - c) / ((ζ - c) - (c - c)) ^ 2) * G ζ) c R
      = - (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2 := hd.unique hVderiv
  rw [← hval]
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hζc : ζ - c ≠ 0 := by
    intro h0
    have hR' : ‖ζ - c‖ = R := by
      rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] at hζ; exact hζ
    rw [h0, norm_zero] at hR'
    linarith
  simp only [G, sub_self, sub_zero]
  field_simp

/-! ### Step 1 of the Carleman assembly: the divisor identity -/

/-- Multiplying a circle-integrable function by the Herglotz–Riesz kernel keeps it
circle-integrable (the kernel is continuous on the sphere). -/
lemma circleIntegrable_kernel_mul {h : ℂ → ℂ} {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball c R)
    (hh : CircleIntegrable h c R) :
    CircleIntegrable (fun ζ => herglotzRieszKernel c w ζ * h ζ) c R := by
  have hint := hh.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere (not_mem_sphere_abs_of_mem_ball hw))
  rwa [show (herglotzRieszKernel c w • h) = fun ζ => herglotzRieszKernel c w ζ * h ζ by
    funext ζ
    exact smul_eq_mul (herglotzRieszKernel c w ζ) (h ζ)] at hint

/-- **Divisor identity for the Poisson–Herglotz boundary integral** (step 1 of the Carleman
assembly).  If, off a set that is codiscrete on the sphere, the logarithms satisfy

    log‖f‖ = ∑ᶠ u, D u · log‖·-u‖ + log‖g‖,

then the boundary integrals (`V_·` = the Herglotz–Riesz Poisson integral with kernel
`herglotzRieszKernel c w`) satisfy the same linear identity:

    V_f = ∑ᶠ u, (D u) · V_u + V_g.

This is the function-level identity `V_f = ∑ᶠ u D u · V_u + V_g`, obtained by splicing the
a.e. logarithmic identity (`MeromorphicOn.extract_zeros_poles_log`) with
`Real.circleAverage_congr_codiscreteWithin` and the linearity of the circle average
(`Real.circleAverage_add`, `Real.circleAverage_sum`, `Real.circleAverage_fun_smul`). -/
theorem circleAverage_logNorm_divisor {f g : ℂ → ℂ} {D : ℂ → ℤ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hw : w ∈ Metric.ball c R)
    (hlog : (fun ζ => Real.log ‖f ζ‖) =ᶠ[Filter.codiscreteWithin (Metric.sphere c |R|)]
      fun ζ => (∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖) + Real.log ‖g ζ‖)
    (hDfin : D.support.Finite)
    (hint_g : CircleIntegrable (fun ζ => ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R)
    (hint_u : ∀ u, D u ≠ 0 → CircleIntegrable (fun ζ => ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R) :
    Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R
      = ∑ᶠ u, ((D u : ℤ) : ℂ) * Real.circleAverage
            (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R
        + Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R := by
  classical
  have hRne : R ≠ 0 := ne_of_gt hR
  have hcongr : (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖f ζ‖ : ℝ) : ℂ))
      =ᶠ[Filter.codiscreteWithin (Metric.sphere c |R|)]
      fun ζ => herglotzRieszKernel c w ζ *
        ((((∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖) + Real.log ‖g ζ‖ : ℝ)) : ℂ) := by
    filter_upwards [hlog] with ζ hζ
    rw [hζ]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hRne]
  let S : Finset ℂ := hDfin.toFinset
  have hS : ∀ u, D u ≠ 0 → u ∈ S := fun u hu => hDfin.mem_toFinset.mpr hu
  have hintu' : ∀ u ∈ S, CircleIntegrable
      (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R :=
    fun u hu => circleIntegrable_kernel_mul hw
      (hint_u u (by simpa only [S, hDfin.mem_toFinset, Function.mem_support] using hu))
  have hg_int : CircleIntegrable
      (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R :=
    circleIntegrable_kernel_mul hw hint_g
  have hfun : (fun ζ => herglotzRieszKernel c w ζ *
        ((((∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖) + Real.log ‖g ζ‖ : ℝ)) : ℂ))
      = (∑ u ∈ S, fun ζ => ((D u : ℤ) : ℂ) *
            (herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)))
        + fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖g ζ‖ : ℝ) : ℂ) := by
    funext ζ
    have h1 : (∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖)
        = ∑ u ∈ S, (D u : ℝ) * Real.log ‖ζ - u‖ := by
      apply finsum_eq_sum_of_support_subset
      intro u hu
      rw [Function.mem_support] at hu
      exact hS u (fun h0 => hu (by simp [h0]))
    have h2 : ((((∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖) : ℝ)
          + Real.log ‖g ζ‖ : ℝ) : ℂ)
        = ((∑ u ∈ S, ((D u : ℤ) : ℂ) * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) : ℂ)
          + ((Real.log ‖g ζ‖ : ℝ) : ℂ) := by
      rw [h1]
      push_cast
      rfl
    rw [h2, Pi.add_apply, Finset.sum_apply, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hfun]
  have hintu'' : ∀ u ∈ S, CircleIntegrable
      (fun ζ => ((D u : ℤ) : ℂ) *
        (herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ))) c R := by
    intro u hu
    have h := (hintu' u hu).const_smul (a := ((D u : ℤ) : ℂ))
    rwa [show (((D u : ℤ) : ℂ) • (fun ζ => herglotzRieszKernel c w ζ *
          ((Real.log ‖ζ - u‖ : ℝ) : ℂ)))
        = fun ζ => ((D u : ℤ) : ℂ) *
          (herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) by
      funext ζ
      exact smul_eq_mul _ _] at h
  rw [Real.circleAverage_add (CircleIntegrable.sum S hintu'') hg_int,
    Real.circleAverage_sum hintu'']
  have hscal : ∀ u ∈ S, Real.circleAverage
        (fun ζ => ((D u : ℤ) : ℂ) *
          (herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ))) c R
      = ((D u : ℤ) : ℂ) * Real.circleAverage
        (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R := by
    intro u hu
    have h := Real.circleAverage_fun_smul (a := ((D u : ℤ) : ℂ))
      (f := fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) (c := c) (R := R)
    simpa only [smul_eq_mul] using h
  rw [Finset.sum_congr rfl hscal]
  have hfin : (∑ᶠ u, ((D u : ℤ) : ℂ) * Real.circleAverage
        (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R)
      = ∑ u ∈ S, ((D u : ℤ) : ℂ) * Real.circleAverage
        (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hD : D u ≠ 0 := by
      intro h0
      exact hu (by simp [h0])
    exact hS u hD
  rw [hfin]

/-! ### Step 2 of the Carleman assembly: differentiating the divisor identity -/

/-- Simplification of the derivative value of the Herglotz integral at the centre. -/
lemma circleAverage_kernel_value_simp {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) :
    Real.circleAverage (fun ζ => (2 * (ζ - c) / ((ζ - c) - (c - c)) ^ 2) * F ζ) c R
      = Real.circleAverage (fun ζ => (2 / (ζ - c)) * F ζ) c R := by
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hζc : ζ - c ≠ 0 := by
    intro h0
    have hR' : ‖ζ - c‖ = R := by
      rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hR] at hζ; exact hζ
    rw [h0, norm_zero] at hR'
    linarith
  simp only [sub_self, sub_zero]
  field_simp

/-- **Step 2: differentiate the divisor identity.** -/
theorem circleAverage_deriv_divisor {f g : ℂ → ℂ} {D : ℂ → ℤ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hlog : (fun ζ => Real.log ‖f ζ‖) =ᶠ[Filter.codiscreteWithin (Metric.sphere c |R|)]
      fun ζ => (∑ᶠ u, (D u : ℝ) * Real.log ‖ζ - u‖) + Real.log ‖g ζ‖)
    (hDfin : D.support.Finite)
    (hult : ∀ u ∈ D.support, ‖u - c‖ < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hg_ne : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (hint_f : CircleIntegrable (fun ζ => ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R)
    (hint_g : CircleIntegrable (fun ζ => ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R)
    (hint_u : ∀ u ∈ D.support, CircleIntegrable (fun ζ => ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R) :
    Real.circleAverage (fun ζ => (2 / (ζ - c)) * ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R
      = ((∑ᶠ u, ((D u : ℤ) : ℂ) * (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2)) : ℂ)
        + deriv g c / g c := by
  classical
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hle_R : ‖c - c‖ < R := by simpa using hR
  -- the function identity, at every inner point
  have hdiv : ∀ w ∈ Metric.ball c R,
      Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R
        = ∑ᶠ u, ((D u : ℤ) : ℂ) * Real.circleAverage
              (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R
          + Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R :=
    fun w hw => circleAverage_logNorm_divisor hR hw hlog hDfin hint_g
      (fun u hu => hint_u u (by simpa only [Function.mem_support] using hu))
  -- the three families of functions
  set Ff : ℂ → ℂ := fun w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R with hFf
  set Fu : ℂ → ℂ → ℂ := fun u w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) c R with hFu
  set Fg : ℂ → ℂ := fun w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel c w ζ * ((Real.log ‖g ζ‖ : ℝ) : ℂ)) c R with hFg
  -- derivatives of the pieces
  have hFf' : HasDerivAt Ff
      (Real.circleAverage (fun ζ => (2 / (ζ - c)) * ((Real.log ‖f ζ‖ : ℝ) : ℂ)) c R) c := by
    have h := hasDerivAt_circleAverage_herglotzRieszKernel_smul'
      (g := fun ζ => ((Real.log ‖f ζ‖ : ℝ) : ℂ)) hint_f hc
    rw [circleAverage_kernel_value_simp (F := fun ζ => ((Real.log ‖f ζ‖ : ℝ) : ℂ)) hR] at h
    exact h
  have hFu' : ∀ u, D u ≠ 0 → HasDerivAt (Fu u)
      (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2) c := by
    intro u hu
    have h := hasDerivAt_circleAverage_herglotzRieszKernel_smul'
      (g := fun ζ => ((Real.log ‖ζ - u‖ : ℝ) : ℂ))
      (hint_u u (by simpa only [Function.mem_support] using hu)) hc
    rw [circleAverage_kernel_value_simp (F := fun ζ => ((Real.log ‖ζ - u‖ : ℝ) : ℂ)) hR,
      circleAverage_dipole_logNorm_sub (hult u (by simpa only [Function.mem_support] using hu))] at h
    exact h
  have hFg' : HasDerivAt Fg (deriv g c / g c) c := by
    have h := hasDerivAt_circleAverage_herglotzRieszKernel_smul'
      (g := fun ζ => ((Real.log ‖g ζ‖ : ℝ) : ℂ)) hint_g hc
    rw [circleAverage_kernel_value_simp (F := fun ζ => ((Real.log ‖g ζ‖ : ℝ) : ℂ)) hR] at h
    rw [← logDeriv_eq_circleAverage_of_ne_zero hR hg hg_ne] at h
    exact h
  -- the identity as an eventual equality
  let S : Finset ℂ := hDfin.toFinset
  have hS : ∀ u, D u ≠ 0 → u ∈ S := fun u hu => hDfin.mem_toFinset.mpr hu
  have hev : Ff =ᶠ[𝓝 c] fun w => Finset.sum S (fun u => ((D u : ℤ) : ℂ) * Fu u w) + Fg w := by
    filter_upwards [Metric.ball_mem_nhds c hR] with w hw
    have h1 := hdiv w hw
    simp only [hFf, hFu, hFg]
    rw [h1]
    congr 1
    exact finsum_eq_sum_of_support_subset _ (fun u hu => by
      rw [Function.mem_support] at hu
      exact hS u (fun h0 => hu (by simp [h0])))
  set Vd : ℂ := Finset.sum S (fun u => ((D u : ℤ) : ℂ) *
    (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2)) with hVd
  have hRHS' : HasDerivAt (fun w => Finset.sum S (fun u => ((D u : ℤ) : ℂ) * Fu u w) + Fg w)
      (Vd + deriv g c / g c) c := by
    have hsum : HasDerivAt (fun w => Finset.sum S (fun u => ((D u : ℤ) : ℂ) * Fu u w)) Vd c := by
      have h0 : HasDerivAt (Finset.sum S (fun u => fun w => ((D u : ℤ) : ℂ) * Fu u w))
          (Finset.sum S (fun u => ((D u : ℤ) : ℂ) * (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2))) c := by
        apply HasDerivAt.sum
        intro u hu
        have hu' : D u ≠ 0 := by
          intro h0
          exact (hDfin.mem_toFinset.mp hu) (by simp [h0])
        exact (hFu' u hu').const_mul _
      rw [hVd]
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards with w
      simp only [Finset.sum_apply]
    exact hsum.add hFg'
  have hmain : HasDerivAt Ff (Vd + deriv g c / g c) c :=
    hRHS'.congr_of_eventuallyEq hev
  have huniq := hFf'.unique hmain
  rw [hVd] at huniq
  have hgoal : (∑ᶠ u, ((D u : ℤ) : ℂ) * (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2))
      = ∑ u ∈ S, ((D u : ℤ) : ℂ) * (- (starRingEnd ℂ) (u - c) / (R : ℂ) ^ 2) :=
    finsum_eq_sum_of_support_subset _ (fun u hu => by
      rw [Function.mem_support] at hu
      exact hS u (fun h0 => hu (by simp [h0])))
  rw [hgoal]
  exact huniq


/-! ### SESSION-8/9: the Carleman–Heilbronn layer, now proven in this file

The following are **proved** above (no `sorry`), and together they are the analytic heart of
the missing ingredient identified in the SESSION-8 note below:

* `circleMap_zero_add`, `norm_sq_sub_conj_mul` — elementary translation/algebra lemmas;
* `hasDerivAt_circleAverage_herglotzRieszKernel_smul'` — the general-centre `∂_w` of the
  Herglotz–Riesz Poisson integral (the **boundary term** of Carleman);
* `analyticOnNhd_circleAverage_herglotzRieszKernel_smul'` — the same integral is analytic in
  the pole parameter (general centre);
* `circleAverage_poissonExtension_logNorm_sub` — the Poisson extension of `log‖·-u‖`;
* `logDeriv_eq_circleAverage_of_ne_zero` — **Carleman, zero-free case**:
  `f'/f(c) = circleAverage (fun ζ => (2/(ζ-c)) * (log‖f ζ‖ : ℂ)) c R`;
* `circleAverage_dipole_logNorm_sub` — the **per-zero polar term**:
  `circleAverage (fun ζ => (2/(ζ-c)) * (log‖ζ-u‖ : ℂ)) c R = -conj(u-c)/R²`.

**Steps 1 and 2 are done**:
`circleAverage_logNorm_divisor` proves the function identity `V_f = ∑ᶠ u D u · V_u + V_g` from
the a.e. logarithmic factorization (spliced with `Real.circleAverage_congr_codiscreteWithin`
and the linearity lemmas), and `circleAverage_deriv_divisor` differentiates it at `c` using
`hasDerivAt_circleAverage_herglotzRieszKernel_smul'` for the three families, the zero-free
Carleman identity for `g`, the dipole identity for each zero `u`, and `HasDerivAt.sum` /
`const_mul` / `congr_of_eventuallyEq` for the bookkeeping.

**What remains for the full `carleman_logDeriv`** (statement: for `f` analytic on
`closedBall c R`, `f c ≠ 0`, `f ≠ 0` on `sphere c R`, with `D = divisor f (closedBall c R)`,
one has `f'(c)/f(c) = circleAverage ((2/(ζ-c)) · (log‖f ζ‖ : ℂ)) c R
+ ∑ᶠ u, D u · (1/(c-u) - conj(c-u)/R²)`) is *assembly only*, in four steps:

1. `MeromorphicOn.extract_zeros_poles` gives `g` analytic and zero-free on `closedBall c R`
   with `f =ᶠ[codiscreteWithin _] (∏ᶠ u, (· - u) ^ D u) • g`; the corresponding log
   decomposition `extract_zeros_poles_log` gives, on the sphere,
   `log‖f·‖ = ∑ᶠ u D u log‖·-u‖ + log‖g·‖` (a.e.), whence by linearity of the circle average
   and `Real.circleAverage_congr_codiscreteWithin`
   `V_f = ∑ᶠ u D u · V_u + V_g` as **functions** (`V_·` = the Poisson integral).
2. All `V_·` are analytic (the lemma above), so the identity survives `deriv` at `c`; use
   `logDeriv_eq_circleAverage_of_ne_zero` for `g` and `circleAverage_dipole_logNorm_sub` for
   each `u` (valid since `f ≠ 0` on the sphere forces `‖u-c‖ < R` for `D u ≠ 0`), and
   `hasDerivAt_circleAverage_herglotzRieszKernel_smul'` for `f`.
3. Product rule near `c`: the a.e. factorization plus continuity gives `f = φ · g` pointwise
   on a neighbourhood of `c`, hence `f'/f(c) = φ'/φ(c) + g'/g(c)` where
   `φ = ∏ᶠ u, (· - u) ^ D u`; `logDeriv_prod` + `logDeriv_zpow` give `φ'/φ(c) = ∑ᶠ u D u/(c-u)`.
4. Algebra: `conj(u-c) = -conj(c-u)` turns `∑ D (1/(c-u) + conj(u-c)/R²)` into
   `∑ D (1/(c-u) - conj(c-u)/R²)`, which is exactly the polar sum of the statement.

The lemma is also requested from the commons as `Analysis/Complex/carleman_logDeriv`; both
`depends_on` ingredients named in that request are now available:

  `NumberTheory.DirichletCharacter.logDeriv_eq_circleAverage_of_ne_zero`  (zero-free case)
  `NumberTheory.DirichletCharacter.circleAverage_dipole_logNorm_sub`      (polar term) -/

/-! ### SESSION-8 UPDATE — the Carleman–Heilbronn formula is the missing cancellation-aware tool

**1. The exact tool** (Heath-Brown 1992, Lemma 3.2; Titchmarsh §3.71; Carleman/Jensen).
For `f` holomorphic on `closedBall c R` (`R > 0`), `f c ≠ 0`, `f ≠ 0` on `sphere c R`,
with `D := MeromorphicOn.divisor f (closedBall c R)` (nonnegative, finitely supported,
supported in the open ball), the following identity holds **exactly**:

    f'(c)/f(c) = Real.circleAverage (fun ζ ↦ (2/(ζ-c)) * (log‖f ζ‖ : ℂ)) c R
                 + ∑ᶠ u, D(u) * (1/(c-u) - conj(c-u)/R²).

Equivalently, in the real-part form quoted in the paper:
`Re(f'/f)(c) = (1/(πR))∫₀^{2π} cos θ · log‖f(c+Re^{iθ})‖ dθ - Σ_ρ D(ρ) (r_ρ⁻¹ - r_ρ/R²) cos θ_ρ`.
[The formula was checked by hand against `f(z) = z - a`, `c = 0`, `R = 1`: both sides give
`-1/a`.  Derivation: (i) `log‖f·‖ = ∑ᶠ D(u) log‖·-u‖ + log‖g·‖` a.e. on the sphere
(`MeromorphicOn.extract_zeros_poles_log`) with `g` analytic zero-free;
(ii) `Real.circleAverage ((re ∘ herglotzRieszKernel c w) • log‖·-u‖) c R
= log|R² - conj(u-c)(w-c)| - log R` (harmonic Poisson formula + the boundary identity
`|R²-āξ| = R|ξ-a|` for `|ξ| = R`); (iii) `w ↦ Real.circleAverage (herglotzRieszKernel c w •
(log‖f·‖:ℂ)) c R` is analytic, its `∂_w(Re ·)` is `(1/2)×` its derivative, and
`f'/f = 2∂_w log‖f·‖`; (iv) `deriv` of the Poisson integral at `w = c` is
`Real.circleAverage (fun ζ ↦ (2/(ζ-c)) • (log‖f ζ‖:ℂ)) c R`
(Mathlib `hasDerivAt_circleAverage_herglotzRieszKernel_smul`, translated in the centre);
(v) `Real.circleAverage (fun ζ ↦ (2/(ζ-c)) * (log‖ζ-u‖:ℂ)) c R = -conj(u-c)/R²`
(computed, no harmonicity needed).]

**2. Why this is the tool that is missing from the file.**  Every reduction already in
this file bounds `‖Λ'/Λ‖` by `Σ_ρ` of *absolute values* of the partial-fraction kernel
`|1/(s-ρ) + 1/ρ|`.  That loses the cancellation that makes the true size `~ log N`
instead of `~ (log N)(log c)`: the low-height zeros `γ_ρ ≪ c` contribute `Σ 1/|γ_ρ|`
with no partner to cancel against.  The Carleman formula replaces the far zeros by a
*signed boundary integral* of `log‖Λ‖` on a circle, and keeps only the zeros inside the
circle in the polar sum.

**3. New count-free corollary (the `Re c = 1` sign trick).**  All nontrivial zeros satisfy
`0 < β_ρ < 1`.  Hence for the centre `c = 1 + iT` (`Re c = 1`) and *every* radius `R`,
every polar term in the real-part formula has `cos θ_ρ = (1 - β_ρ)/r_ρ > 0` and
`r_ρ < R`, so `(r_ρ⁻¹ - r_ρ/R²) cos θ_ρ > 0` and the polar sum enters with a **negative**
sign.  Therefore, with **no zero count at all**,

    Re(logDeriv Λ(χ)(1 + iT)) ≤ (1/(πR)) ∫₀^{2π} cos θ · log‖Λ(1 + iT + R e^{iθ})‖ dθ,

and the right-hand side is bounded *pointwise* by `(2/(πR))·sup_{cos θ>0} log‖Λ‖`, which is
explicit from the certified pointwise bounds on `Re = 1,2` and the functional equation
(the `(N/π)^{(z+a)/2}Γ((z+a)/2)` prefactor and the gamma factor cancel exactly in the
circle average, and `log‖L‖` is controlled by `LFunction_norm_half_plane`
`‖L‖ ≤ 2N‖s‖/Re s` on `Re > 0` and by `norm_LFunction_le_re_ge_one` on `Re ≥ 1`).

**4. Remaining gap, precisely.**
 (a) The imaginary part: `Im(Λ'/Λ) = -∂_T log‖Λ‖`; its Carleman polar weights
     `sin θ_ρ` change sign with the height of `ρ` relative to `T`, so no count-free sign
     trick is available.  A local zero count (below) is needed.
 (b) The range `Re ∈ [0,1)`: for `Re c = x < 1` the zeros with `β_ρ > x` give polar terms
     of the *wrong* sign, again requiring a count.
 (c) Therefore the target needs the explicit local zero count; and the count is provable
     *explicitly* from the certified pieces, as follows.

**5. Explicit Jensen local count (plan, with explicit constants).**  Centre `s₀ = 2 + iT`,
radius `R ∈ [3,6]`, inner radius `r = 2.062` (the box `[0,2]×[c,c+1]` lies in
`B(2+i(c+1/2), r)`).  Jensen (`AnalyticOnNhd.circleAverage_log_norm`) gives

    #{ρ : |ρ - s₀| ≤ r} · log(R/r) ≤ circleAvg(log‖Λ‖, s₀, R) - log‖Λ(s₀)‖.

The *linear* part `((z+a)/2)log(N/π)` and the *gamma* part `log‖Γ((z+a)/2)‖` of
`log‖Λ‖` are harmonic on the disc, so their circle averages equal their centre values and
**cancel exactly**; `log‖Λ(s₀)‖ ≥ log(1/4)` (`L_lower_re_two` plus the explicit gamma
value).  The `L`-part contributes, with the certified explicit bounds,

    coeff(σ) = 1 for 0 < σ < 1   (`LFunction_norm_half_plane`), 
    coeff(σ) = 1/2 - σ for σ ≤ 0 (functional equation + `norm_LFunction_le_re_ge_one`),
    coeff(σ) = 0 for σ ≥ 1       (`norm_LFunction_le_re_ge_one`),

so `circleAvg(log‖L‖) ≤ (1/2π)∫ coeff(2+R cos θ) dθ · log N + O(log(2+|T|+R))`.  Numerically
`(1/2π)∫coeff = 0.624` at `R = 4` (the exact convexity coefficient `(1-σ)/2` would give
`0.624`; the certified coefficient `1` on `(0,1)` gives `0.689`), giving

    #{zeros in B(2+iT, 2.062)} ≤ 1.04·(log N + log(2+|T|)) + O(1)

(factor `1/log(R/r) = 1/0.663`).  The true count is `≈ 0.36(log N + log|T|)`: a factor-3
slack.  With the pole-area `∫∫_box ‖1/(s-ρ) - conj(s-ρ)/R'²‖ ds ≲ 2.4` per zero
(`poleArea_box_le`) the polar contribution to the box integral is `≈ 0.4 (log N + log c)`,
far inside the budget `4(log N + log(2+c+3))`.

**6. Consequence for the assembly.**  Combining § 5 (count) with § 1 (Carleman) and the
pointwise description `Λ'/Λ = ½log(N/π) + ½ψ((s+a)/2) + L'/L` (the `½log(N/π)` term
contributes exactly `log N` over the area-2 box, the `ψ` term `O(log c)`), the budget is
`≈ log N + log c + (2.4 × 1.04)(log N + log c) ≈ 3.5 (log N + log c)`, inside
`4(log N + log(2+c+3)) + 20`.  The two concrete formalisation targets are therefore
(a) `carleman_logDeriv` (the identity of § 1; requested from the commons as
`Analysis/Complex/carleman_logDeriv`) and (b) the explicit Jensen count of § 5. -/

/-! ### Rebased partial fraction: the two-point difference identity

`Commons.NumberTheory.Linnik.partialFraction_eq` gives, for every `s` with `Λ s ≠ 0`,

    Λ'(s)/Λ(s) - Λ'(0)/Λ(0) = lim_R ∑ᶠ_{|u| ≤ R} d_u · (1/(s-u) + 1/u)   (d_u = divisor coefficient).

Subtracting the identities for two points `s`, `s₁` kills the `1/u` (i.e. the constant
`Λ'(0)/Λ(0)`), leaving the rebased form

    Λ'(s)/Λ(s) - Λ'(s₁)/Λ(s₁) = lim_R ∑ᶠ_{|ρ| ≤ R} d_ρ · (1/(s-ρ) - 1/(s₁-ρ)).

This is the starting point of the `Re s₁ = 2` route to the target: with `s₁ = 2 + iT` the
fixed part `Λ'/Λ(s₁)` is `log N`-free (`completedLogDeriv_two_small`), so all of the
`log N`-dependence of `Λ'/Λ(s)` passes into the zero sum, whose weights
`|s - s₁|/(|s-ρ||s₁-ρ|)` are `O(1/dist(ρ, box)²)` and hence summable. -/
/-! ### SESSION-10 UPDATE — the exact quantitative scheme for the target, and its margin

**Chosen route** (the only one whose constants can fit; supersedes the pole-area route):

1. `partialFraction_diff` (proved above): for `Λ = completedLFunction χ` and `Λ s ≠ 0 ≠ Λ s₁`,
   `Λ'/Λ(s) - Λ'/Λ(s₁) = lim_R ∑ᶠ_{|ρ| ≤ R} d_ρ (1/(s-ρ) - 1/(s₁-ρ))`.
2. Take `s₁ = 2 + iT` (`T = s.im`).  Then `‖Λ'/Λ(s₁)‖ ≤ (1/2)·log(2+|T|) + 5`
   (`completedLogDeriv_two_small`) — **no `log N`**, because `Λ = L·γ` carries no conductor.
   So `‖Λ'/Λ(s)‖ ≤ ‖Λ'/Λ(2+iT)‖ + ∑ᶠ_ρ d_ρ |s-s₁| / (|s-ρ|·|s₁-ρ|)`.
3. Integrate over the box `[0,2]×[c,c+1]`.  Since `|s₁-ρ| ≥ 2 - β_ρ > 1` and
   `|s-s₁| = |x-2| ≤ 2`, the weight of a zero at distance `D` from the box is `O(1/D²)`
   (numercially 1.8–2.8 for zeros in/near the box, 0.32 at distance 2, 0.025 at distance 10).
4. So the estimate needed is
   `∑ᶠ_ρ d_ρ W_ρ ≤ 4·log N + 3·log(2+c+3) + 10`,
   where `W_ρ = ∫∫_box |x-2| / (|s-ρ|·|s₁-ρ|)`, because the base term contributes
   `2·[(1/2)log(2+c+1)+5] = log(c+3) + 10`.

**Budget.**  With the local count `N(B(2+iT, 2.062)) ≤ C·(log N + log(2+T) + 2)` (a Jensen
count with centre `2+iT`, inner radius `2.062` = the covering radius of the box about
`2 + i(c+1/2)`, outer radius `4`) and an average near-zero weight `W̄ ≈ 2.4`:
near part `≈ 2.4·C·(log N + log)`; far part `≈ 0.5·(log N + log)`.  Hence
`2.4·C + 0.5 ≤ 3` (the log-coefficient budget) forces **`C ≤ 1.04`**, and `2.4·C ≤ 4`
(the `log N` budget) is then automatic.  This is *exactly on the edge*.

**Best available Jensen constant.**  Jensen at centre `2+iT` (`R = 4`, `r = 2.062`,
`log(R/r) = 0.663`) gives `C = κ̄/0.663` where `κ̄ = (1/2π)∫₀^{2π} κ(2 + 4cos θ) dθ` and
`κ(σ)` is the exponent in `‖L(σ+it)‖ ≤ C·(N(1+|t|))^{κ(σ)}` on the circle:
* `κ(σ) = 0` for `σ ≥ 3/2` (Euler product: `‖L(σ+it)‖ ≤ ζ(σ) ≤ ζ(3/2)`);
* `κ(σ) = 1` for `σ ∈ [1,3/2]` (`norm_LFunction_le_re_ge_one`: `log N + log(2+|t|) + 6`);
* `κ(σ) = 1` for `σ ∈ (0,1)` (`LFunction_norm_half_plane`: `‖L‖ ≤ 2N‖s‖/Re s`;
  the `1/σ` gives an integrable `log` singularity at `σ = 0`);
* `κ(σ) = 1/2 - σ` for `σ ≤ 0` (functional equation `+` `norm_LFunction_le_re_ge_one`,
  the `log N` of the reflected factor entering only through `log(log)`).
Numerically `κ̄ ≈ 0.69` (the `σ ≤ 0` arc contributes `0.60`, the other two `0.09`),
giving `C ≈ 1.04` — **just at the boundary**.  Any loss (e.g. using
`LFunction_band_poly`'s exponent `k ≥ 5/2`, or the `∃C`-form growth lemmas) pushes
`C` to `1.2–4`, which **breaks** the log-coefficient budget.

**Consequence.**  The target is provable iff one can formalise the four `κ(σ)` bounds
above with *those* constants (in particular a genuine convexity bound
`‖L(σ+it)‖ ≪ (N(1+|t|))^{(1-σ)/2+ε}` would improve `κ̄` to `≈0.62`, i.e. `C ≈ 0.94`,
inside the budget).  The numerical truth is `C ≈ 0.7–0.8`, so the statement is not tight
mathematically — it is tight only for the crude tools certified in the commons today. -/

theorem partialFraction_diff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s s₁ : ℂ)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hs₁ : DirichletCharacter.completedLFunction χ s₁ ≠ 0) :
    Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))
      atTop (nhds (logDeriv (DirichletCharacter.completedLFunction χ) s
        - logDeriv (DirichletCharacter.completedLFunction χ) s₁)) := by
  have h1 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
  have h2 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s₁ hs₁
  have hsub := h1.sub h2
  change Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))
    atTop (nhds (deriv (DirichletCharacter.completedLFunction χ) s /
      DirichletCharacter.completedLFunction χ s -
      deriv (DirichletCharacter.completedLFunction χ) s₁ /
      DirichletCharacter.completedLFunction χ s₁))
  have hgoal : (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0) -
      (deriv (DirichletCharacter.completedLFunction χ) s₁ /
        DirichletCharacter.completedLFunction χ s₁ -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0) =
      deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) s₁ /
        DirichletCharacter.completedLFunction χ s₁ := by ring
  rw [← hgoal]
  refine hsub.congr' ?_
  filter_upwards with R
  have hfs : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  have hfs₁ : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s₁ - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  rw [← finsum_sub_distrib hfs hfs₁]
  exact finsum_congr fun u => by ring

/-! ### Weighted zero count via the rebased partial fraction

The real part of the rebased partial-fraction identity at the pair of points
`s₁ = 2 + iT` and `s₀ = -1 + iT` (both on zero-free vertical lines) shows that

`Σ_{|u| ≤ R} ord_Λ(u) · (Re 1/(s₁-u) - Re 1/(s₀-u))`

increases with `R` towards `Re(Λ'/Λ(s₁) - Λ'/Λ(s₀))`, and every summand is nonnegative
(every zero of `Λ` lies in `0 < Re < 1`, so `2 - Re u > 0` and `1 + Re u > 0`).  Bounding
the limit by the norms of the two logarithmic derivatives gives a conductor-uniform
*weighted zero count*: for every `R`, the sum is at most `log N + log(2+|T|) + 10`.
This is the quantitative form of the classical fact that the partial fractions of `L'/L`
on a fixed vertical line are controlled by `log(N(|T|+2))`. -/

/-- `Re (1/((x : ℂ) + i T - u)) = (x - Re u)/((x - Re u)² + (T - Im u)²)`. -/
private lemma re_inv_shift (x T : ℝ) (u : ℂ) :
    (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)).re
      = (x - u.re) / ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hz : (((x : ℂ) + Complex.I * (T : ℂ)) - u).re = x - u.re := by simp
  have hi : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hz, hi]
  ring

/-- The divisor of `Λ = completedLFunction χ` on a ball has finite support (as a plain
function `ℂ → ℤ`). -/
private lemma divisor_support_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) :
    (Function.support ⇑(MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R))).Finite :=
  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R))

private lemma rebased_kernel_nonneg {u : ℂ} (h1 : 0 < u.re) (h2 : u.re < 1) (T : ℝ) :
    0 ≤ (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) := by
  have ha : (0:ℝ) < 2 - u.re := by linarith
  have hb : (0:ℝ) < 1 + u.re := by linarith
  have hd1 : 0 < (2 - u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos ha ha]
  have hd2 : 0 < (1 + u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos hb hb]
  exact add_nonneg (div_nonneg ha.le hd1.le) (div_nonneg hb.le hd2.le)

/-- Positivity of the rebased kernel for a general line `Re = σ₁ ≥ 1`. -/
private lemma rebased_kernel_nonneg' {u : ℂ} (h1 : 0 < u.re) (h2 : u.re < 1) (T σ₁ : ℝ)
    (hσ₁ : 1 ≤ σ₁) :
    0 ≤ (σ₁ - u.re) / ((σ₁ - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) := by
  have ha : (0:ℝ) < σ₁ - u.re := by linarith
  have hb : (0:ℝ) < 1 + u.re := by linarith
  have hd1 : 0 < (σ₁ - u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos ha ha]
  have hd2 : 0 < (1 + u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos hb hb]
  exact add_nonneg (div_nonneg ha.le hd1.le) (div_nonneg hb.le hd2.le)


/-- **Weighted zero count.**  For a primitive non-trivial character `χ` mod `N`, every real
`T` and every `R`, the divisor-weighted sum of the rebased partial-fraction kernel is at
most `log N + log(2 + |T|) + 10`. -/
theorem finsum_divisor_re_sub_inv_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))
      ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by
  classical
  set K : ℂ → ℝ := fun u => (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) with hK
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛdiff _
  have hz1 : DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 :=
    completedLFunction_ne_zero_re_two χ hχ hχprim T
  have hz2 : DirichletCharacter.completedLFunction χ ((-1 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 :=
    completedLFunction_ne_zero_re_neg_one χ hχ hχprim T
  have hpf := partialFraction_diff χ hχ hχprim ((2 : ℂ) + Complex.I * (T : ℂ))
    ((-1 : ℂ) + Complex.I * (T : ℂ)) hz1 hz2
  set L : ℝ := (logDeriv (DirichletCharacter.completedLFunction χ)
      ((2 : ℂ) + Complex.I * (T : ℂ))
    - logDeriv (DirichletCharacter.completedLFunction χ)
      ((-1 : ℂ) + Complex.I * (T : ℂ))).re with hL
  have hre : Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))).re)
      atTop (𝓝 L) := by
    rw [hL]
    exact (Complex.continuous_re.tendsto _).comp hpf
  -- identify the real part of the sum with the target finsum
  have hident : ∀ R : ℝ, (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))).re
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u := by
    intro R
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))) := by
      refine (divisor_support_finite χ R).subset (fun u hu => ?_)
      have hu' : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)) ≠ 0 := hu
      exact fun h => hu' (by rw [h, Int.cast_zero, zero_mul])
    rw [← Complex.reCLM_apply, map_finsum Complex.reCLM hfs]
    refine finsum_congr fun u => ?_
    rw [Complex.reCLM_apply]
    rw [Complex.mul_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
        show (-1 : ℂ) = ((-1 : ℝ) : ℂ) from by norm_num]
    rw [Complex.sub_re, re_inv_shift (2:ℝ) T u, re_inv_shift (-1:ℝ) T u, hK]
    ring
  have hre' : Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u) atTop (𝓝 L) := by
    refine hre.congr' ?_
    filter_upwards with R
    exact hident R
  -- monotonicity in R
  have hmono : ∀ R R' : ℝ, R ≤ R' → (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u)
      ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u) := by
    intro R R' hRR'
    refine finsum_le_finsum'
      (f := fun u => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u)
      (g := fun u => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u) ?_ ?_ ?_
    · refine (divisor_support_finite χ R).subset (fun u hu => ?_)
      have hu' : ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ)) * K u ≠ 0 := hu
      exact fun h => hu' (by rw [h, Int.cast_zero, zero_mul])
    · refine (divisor_support_finite χ R').subset (fun u hu => ?_)
      have hu' : ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ)) * K u ≠ 0 := hu
      intro h
      exact hu' (by rw [h, Int.cast_zero, zero_mul])
    · intro u
      show (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u
        ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u
      by_cases hu : u ∈ Metric.closedBall (0:ℂ) R
      · have hu' : u ∈ Metric.closedBall (0:ℂ) R' := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu ⊢
          exact le_trans hu hRR'
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R ∪ Metric.closedBall 0 R') := by
          intro z hz
          exact hΛdiff.analyticAt z
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (hf := hfU) hu hu'
        rw [heq]
      · have h0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u = 0 :=
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
        rw [h0, Int.cast_zero, zero_mul]
        by_cases hd : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R') u = 0
        · rw [hd, Int.cast_zero, zero_mul]
        · refine mul_nonneg (Int.cast_nonneg ?_) ?_
          · exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn R') u
          · have hfu : DirichletCharacter.completedLFunction χ u = 0 :=
              Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R') hd
            have hs := zerosInStrip χ hχ hχprim u hfu
            rw [hK]
            exact rebased_kernel_nonneg hs.1 hs.2 T
  have hfin : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u) ≤ L :=
    ge_of_tendsto hre' (Filter.eventually_atTop.2 ⟨R, fun c hc => hmono R c hc⟩)
  have hLb : L ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by
    rw [hL]
    have h2 : ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ (1 / 2) * Real.log (2 + |T|) + 5 :=
      completedLogDeriv_two_small χ hχ T
    have h1 : ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (T : ℂ))‖
        ≤ Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 5 :=
      completedLogDeriv_neg_one_small χ hχ hχprim T
    calc (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))
              - logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))).re
          ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))
              - logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))‖ := Complex.re_le_norm _
      _ ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖
            + ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))‖ := norm_sub_le _ _
      _ ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by linarith
  calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u := by
        rw [hK]
    _ ≤ L := hfin
    _ ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := hLb

/-- **Weighted zero count at the line `Re = 3/2`.**  Combining the general rebased zero count
`finsum_divisor_re_inv_sub_le` with the published one-sided estimate
`re_logDeriv_completedLFunction_three_halves` gives, for every `R`,

`Σ_{‖u‖≤R} ord_Λ(u)·[(3/2-Re u)/((3/2-Re u)²+(T-Im u)²) + (1+Re u)/((1+Re u)²+(T-Im u)²)]`
`≤ log N + log(2+|T|) + 11/2`.

This is the weighted count used by the `σ₁ = 3/2` route to the target: the comparison
constant against the box weight `W_ρ` is `≈ 2.45` numerically, against `3.27` for the `σ₁ = 2`
line. -/
theorem finsum_divisor_re_inv_sub_le_three_halves {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        (((3 / 2 : ℝ) - u.re) / (((3 / 2 : ℝ) - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))
      ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 11 / 2 := by
  have hσ : (1 : ℝ) ≤ 3 / 2 := by norm_num
  have h := finsum_divisor_re_inv_sub_le χ hχ hχprim T (3 / 2)
    ((1 / 2) * Real.log (2 + |T|) + 4) hσ
    (by simpa using
      Commons.NumberTheory.DirichletCharacter.re_logDeriv_completedLFunction_three_halves_sharp χ hχ T)
    R
  linarith

/-! ### SESSION-12 STATUS — a working route to the target

**Proved in this file this session (no `sorry`).**

1. `finsum_divisor_re_inv_sub_le` — **weighted zero count at a general rebasing line**.
   If `Re (Λ'/Λ)(σ₁+iT) ≤ B₁` for some `σ₁ ≥ 1`, then for every `R`
   `Σ_{‖u‖≤R} ord_Λ(u)·[(σ₁-Re u)/((σ₁-Re u)²+(T-Im u)²) + (1+Re u)/((1+Re u)²+(T-Im u)²)]`
   `≤ B₁ + log N + ½log(2+|T|) + 3/2`.
   (Real part of the rebased partial fraction `partialFraction_diff` at the pair `σ₁+iT`,
   `-1+iT`; both lines are zero-free by `zerosInStrip`, all summands are nonnegative since the
   zeros satisfy `0 < Re u < 1`, the sums increase in `R`, and
   `-Re(Λ'/Λ(-1+iT)) ≤ log N + ½log(2+|T|)+3/2` is the published
   `completedLogDeriv_neg_one_re_tight`.)  The `σ₁ = 2` instance is
   `finsum_divisor_re_sub_inv_le`, and `finsum_divisor_re_inv_sub_le_three_halves` is the
   `σ₁ = 3/2` instance.
2. `divisor_support_finite`, `re_inv_shift`, `rebased_kernel_nonneg(')` — supporting lemmas.

**Commons published by the fleet from requests of this session.**
* `Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le` (the general zero
  count of item 1, re-proved from the commons alone).
* `Commons.NumberTheory.DirichletCharacter.re_logDeriv_completedLFunction_three_halves`
  (`Re (Λ'/Λ(3/2+iT)) ≤ ½log(2+|T|) + 5`) and its sharpening `..._sharp` (`+ 4`).
* `Commons.Analysis.Integral.boxKernel_le_rebased`: for `β ∈ (0,1)`, all `c, γ`,
  `∫_c^{c+1}∫_0^2 (2-x)/(√((x-β)²+(T-γ)²)√((2-β)²+(T-γ)²)) ≤ (13/5)·∫_c^{c+1}q_β(T) dT`
  with `q_β(T) = (3/2-β)/((3/2-β)²+(T-γ)²) + (1+β)/((1+β)²+(T-γ)²)`.
  (The sharp constant is `2.5049…`; `5/2` is *false*, `2.6` is provable.)
* `Commons.Analysis.Complex.divisor_sum_le_circleAverage`: the Jensen counting bound
  `Σ_{‖c-u‖≤r} ord(u) ≤ (B - log‖f c‖)/log(R/r)`.

**THE ROUTE to the target (all ingredients now exist; verified numerically).**
Work with `Λ` throughout and use the *tight* base bound `completedLogDeriv_two_tight`
(`‖Λ'/Λ(2+iT)‖ ≤ ½log(2+|T|) + 3`, commons).  Re-basing the partial fraction at `s₁ = 2+iT`,

  `∫_c^{c+1}∫_0^2 ‖Λ'/Λ(x+iT)‖ ≤ 2∫_c^{c+1}‖Λ'/Λ(2+iT)‖dT + Σ_ρ d_ρ W_ρ`,

with `W_ρ = ∫_c^{c+1}∫_0^2 (2-x)/(‖x+iT-ρ‖·‖2+iT-ρ‖)`.  Then

* `2∫_c^{c+1}‖Λ'/Λ(2+iT)‖dT ≤ ∫_c^{c+1}[log(2+|T|)+6]dT ≤ log(c+3) + 6`;
* `W_ρ ≤ (13/5)∫_c^{c+1}q_ρ(T)dT` (`boxKernel_le_rebased`), and
  `Σ_{‖u‖≤R}d_u q_u(T) ≤ log N + log(2+|T|) + 11/2` for every `R`
  (`finsum_divisor_re_inv_sub_le_three_halves` + `..._three_halves_sharp`), so
  `Σ_ρ d_ρW_ρ ≤ (13/5)∫_c^{c+1}[log N + log(2+|T|) + 11/2]dT ≤ 2.6log N + 2.6log(c+3) + 14.3`.

Total: `2.6·log N + 3.6·log(c+3) + 20.3 ≤ 20 + 4log N + 4log(c+5)` for all `c ≥ 1/2`,
`N ≥ 2`: at the tightest corner `(c,N) = (1/2,2)` the sides are `26.6` vs `29.6` (margin
`1.11`); at `(50,2)`: `26.6` vs `40.3`; at `(10²⁰,2)`: `192.2` vs `223.6`.  Note that the
γ-factor is **not** separated out, so no `γ`-difference term arises (the alternative `L`-route
via `logDeriv_gammaFactor_box` needs `∫∫‖γ'/γ(x+iT)-γ'/γ(2+iT)‖`, whose crude digamma bound
(`digamma_sub_le_same_im`) is `≈ 2–3` at `c = 1/2`, eating the whole slack — do not use it).

**Remaining formalisation (the assembly; the analytic content is done).**
(a) the limit step: from `partialFraction_diff` at `(x+iT, 2+iT)` and the triangle inequality,
    `‖Λ'/Λ(x+iT) − Λ'/Λ(2+iT)‖ ≤ ⨆_R Σ_{‖u‖≤R} d_u·|2−x|/(‖x+iT−u‖·‖2+iT−u‖)`
    (`Tendsto.norm`, `Monotone`, `tendsto_atTop_ciSup`, `le_of_tendsto_of_tendsto`); at a zero
    `x+iT` the left side is `0` (Lean's `x/0 = 0`) so no exceptional set is needed;
(b) interchange `⨆_R` with `∫_0^2` (monotone convergence for the nonnegative partial sums,
    `MeasureTheory.integral_iSup_of_monotone`/`lintegral_iSup`) and with the finite divisor
    sums over `‖u‖ ≤ R` (`finsum` over a finite support) and then with `∫_c^{c+1}`;
(c) apply `boxKernel_le_rebased` (with `β = u.re`, `γ = u.im`) pointwise in `u`, then the
    zero count `finsum_divisor_re_inv_sub_le_three_halves` (for the ball of radius `R`) and
    `linarith`/`ring_nf` for the final arithmetic;
(d) the measurability/integrability side conditions of `intervalIntegral`.

**Dead ends (do not retry).**  The `σ₁ = 2` rebasing (kernel ratio `3.27 > 3`); the Jensen
route (`κ(1.5,4) = 2.84`, `M(4) ≈ 0.95(log N+log c)+3.4`, but the far zeros need either a Jensen
count on infinitely many disks or the identity and every combination lands at `3.15–4.2` on the
`log c` coefficient); the `min_T q_ρ(T)` variant (ratio `3.7`); `σ₁ = 0` / `z₂ = 0` (needs a
`Re`-bound at `Re = 0`, i.e. again a `Re`-bound at `Re = 1`); the `L`-box route via the gamma
box (the `γ`-difference term). -/

open MeasureTheory
open scoped ENNReal

theorem window_int_le {c β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ T in c..c+1, (Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
        - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ)))
      ≤ (13 / 5) * (∫ T in c..c + 1,
          ((3 / 2 - β) / ((3 / 2 - β) ^ 2 + (T - γ) ^ 2)
            + (1 + β) / ((1 + β) ^ 2 + (T - γ) ^ 2))) := by
  refine Commons.Analysis.Integral.window_reduction hβ0 hβ1 ?_ c γ
  refine Commons.Analysis.Integral.boxWindow_all_of ?_ ?_ ?_
  · intro s hs
    have h := Commons.Analysis.Integral.boxMaj_le_target_kernel_ge_sixth hβ0 hβ1 hs
    convert h using 1
    simp only [Commons.Analysis.Integral.winE, Commons.Analysis.Integral.boxH,
      Commons.Analysis.Integral.boxQlb, Commons.Analysis.Integral.boxMaj,
      Commons.Analysis.Integral.boxMajTerm,
      abs_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1/6) hs)]
    ring_nf
  · intro δ h1 h2
    have h := Commons.Analysis.Integral.boxWindow_middle hβ0 hβ1 δ h1 h2
    convert h using 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Commons.Analysis.Integral.winE, Commons.Analysis.Integral.boxH,
      Commons.Analysis.Integral.boxQlb, Commons.Analysis.Integral.boxMaj,
      Commons.Analysis.Integral.boxMajTerm]
    ring_nf
  · intro δ h1 h2
    have h := Commons.Analysis.Integral.boxWindow_left_half hβ0 hβ1 δ h1 h2
    convert h using 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Commons.Analysis.Integral.winE, Commons.Analysis.Integral.boxH,
      Commons.Analysis.Integral.boxQlb, Commons.Analysis.Integral.boxMaj,
      Commons.Analysis.Integral.boxMajTerm]
    ring_nf

theorem zeroKernel_lintegral_le {c β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - ((β : ℂ) + Complex.I * (γ : ℂ)))
        - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - ((β : ℂ) + Complex.I * (γ : ℂ)))‖
        ∂((volume.restrict (Set.Ioc c (c + 1))).prod (volume.restrict (Set.Ioc 0 2))))
      ≤ ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
          ((3 / 2 - β) / ((3 / 2 - β) ^ 2 + (T - γ) ^ 2)
            + (1 + β) / ((1 + β) ^ 2 + (T - γ) ^ 2)))) := by
  classical
  set ρ : Measure ℝ := volume.restrict (Set.Ioc c (c + 1)) with hρ
  set σ : Measure ℝ := volume.restrict (Set.Ioc 0 2) with hσ
  set u : ℂ := (β : ℂ) + Complex.I * (γ : ℂ) with hu
  have hβ2 : (0:ℝ) < 2 - β := by linarith
  have hβ21 : (1:ℝ) ≤ 2 - β := by linarith
  have hnormid : ∀ T x : ℝ, T ≠ γ →
      ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u) - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖
        = |2 - x| / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
            * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) := by
    intro T x hTγ
    have hz1 : (((x : ℂ) + Complex.I * (T : ℂ)) - u)
        = ((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I := by
      rw [hu]; push_cast; ring
    have hz2 : (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
        = ((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I := by
      rw [hu]; push_cast; ring
    have h1nz : ((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      exact hTγ (by linarith [this])
    have h2nz : ((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      exact hTγ (by linarith [this])
    have hBA : (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)
        - (((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I) = ((2 - x : ℝ) : ℂ) := by
      push_cast; ring
    have hkey : 1 / (((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)
        - 1 / (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)
        = ((2 - x : ℝ) : ℂ) / ((((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)
            * (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)) := by
      field_simp
      push_cast
      ring
    have hA : ‖(((x - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)‖
        = Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_add_mul_I]
    have hB : ‖(((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * Complex.I)‖
        = Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_add_mul_I]
    have h0 : ‖(((2 - x : ℝ) : ℂ))‖ = |2 - x| := by
      rw [Complex.norm_def, Complex.normSq_ofReal]
      simpa [sq] using Real.sqrt_sq_eq_abs (2 - x)
    rw [hz1, hz2, hkey, Complex.norm_div, Complex.norm_mul, hA, hB, h0]
  have hmeasInner : Measurable (fun p : ℝ × ℝ =>
      1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
        - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)) := by
    apply Measurable.sub
    · apply Measurable.div measurable_const
      fun_prop
    · apply Measurable.div measurable_const
      fun_prop
  have hae : AEMeasurable (Function.uncurry (fun T x : ℝ => ENNReal.ofReal
      ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
        - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖)) (ρ.prod σ) :=
    (ENNReal.continuous_ofReal.measurable.comp (continuous_norm.measurable.comp hmeasInner)).aemeasurable
  have hstep1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
        - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂(ρ.prod σ))
      = ∫⁻ T, (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ) ∂ρ := by
    have h := MeasureTheory.lintegral_lintegral (μ := ρ) (ν := σ)
      (f := fun T x : ℝ => ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖) hae
    rw [← h]

  have hTne : ∀ᵐ T ∂ρ, T ≠ γ := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not]
    have hset : ({a : ℝ | a = γ} : Set ℝ) = {γ} := by ext a; simp
    rw [hset, hρ, MeasureTheory.Measure.restrict_apply (measurableSet_singleton γ)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton γ)
  have hfinT : ∀ T : ℝ, T ≠ γ →
      (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ) ≠ ⊤ := by
    intro T hTγ
    have hle : (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ)
        ≤ ENNReal.ofReal (2 / |T - γ|) * 2 := by
      have hbound : ∀ x : ℝ, x ∈ Set.Ioc (0:ℝ) 2 →
          ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ≤ 2 / |T - γ| := by
        intro x hx
        rw [hnormid T x hTγ, abs_of_nonneg (by linarith [hx.2])]
        have hTp : 0 < |T - γ| := abs_pos.mpr (sub_ne_zero.mpr hTγ)
        have hbb : |T - γ| ≤ Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) := by
          have h3 : Real.sqrt ((T - γ) ^ 2) ≤ Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - β)])
          rwa [Real.sqrt_sq_eq_abs] at h3
        have hcc : 1 ≤ Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2) := by
          have h3 : Real.sqrt ((2 - β) ^ 2) ≤ Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (T - γ)])
          rw [Real.sqrt_sq_eq_abs] at h3
          have h4 : (1:ℝ) ≤ |2 - β| := by rw [abs_of_pos hβ2]; linarith
          linarith
        have hbc : |T - γ| ≤ Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
            * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2) := by
          have h1 := mul_le_mul hbb hcc (by norm_num) (Real.sqrt_nonneg _)
          rwa [mul_one] at h1
        have hnum : (2 - x) ≤ 2 := by linarith [hx.1]
        have hnum0 : (0:ℝ) ≤ 2 - x := by linarith [hx.2]
        calc (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
              * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2))
            ≤ 2 / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
              * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) := by
              apply div_le_div_of_nonneg_right hnum
              exact le_of_lt (mul_pos (lt_of_lt_of_le hTp hbb) (lt_of_lt_of_le zero_lt_one hcc))
          _ ≤ 2 / |T - γ| := by
              apply div_le_div_of_nonneg_left (by norm_num) hTp hbc
      calc (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ)
          ≤ ∫⁻ x, ENNReal.ofReal (2 / |T - γ|) ∂σ := by
            apply MeasureTheory.lintegral_mono_ae
            rw [hσ]
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
            exact ENNReal.ofReal_le_ofReal (hbound x hx)
        _ = ENNReal.ofReal (2 / |T - γ|) * σ Set.univ := MeasureTheory.lintegral_const _
        _ = ENNReal.ofReal (2 / |T - γ|) * 2 := by
            rw [hσ, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
            norm_num
    exact ne_of_lt (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num)))
  set Mf : ℝ → ℝ := fun T => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
      - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ) with hMf
  have hperT : ∀ T : ℝ, T ≠ γ →
      (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ) ≤ ENNReal.ofReal (Mf T) := by
    intro T hTγ
    have hmeasg : Measurable (fun x : ℝ => ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
        - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖) := by fun_prop
    have heq : (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ)
        = ENNReal.ofReal (∫ x, ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ) := by
      have h1 := integral_eq_lintegral_of_nonneg_ae (μ := σ)
        (f := fun x : ℝ => ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖)
        (by filter_upwards with x; exact norm_nonneg _) hmeasg.aestronglyMeasurable
      rw [h1, ENNReal.ofReal_toReal (hfinT T hTγ)]
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    have h2 : (∫ x, ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ)
        = ∫ x in (0:ℝ)..2, |2 - x| / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
            * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) := by
      rw [hσ, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2)]
      apply intervalIntegral.integral_congr
      intro x _
      exact hnormid T x hTγ
    rw [h2]
    have h3 : (∫ x in (0:ℝ)..2, |2 - x| / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
          * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)))
        = ∫ x in (0:ℝ)..2, (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
          * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hx
      change |2 - x| / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
          * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2))
        = (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
          * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2))
      rw [abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ 2 - x)]
    rw [h3]
    exact Commons.Analysis.Integral.inner_le_boxMaj hβ0 hβ1 (sub_ne_zero.mpr hTγ)

  have hmeasMf : Measurable Mf := by
    rw [hMf]
    have hterm : ∀ b δ : ℝ, Measurable (fun T : ℝ =>
        Commons.Analysis.Integral.boxMajTerm b δ |T - γ|) := by
      intro b δ
      unfold Commons.Analysis.Integral.boxMajTerm
      apply Measurable.ite
      · exact measurableSet_le (by fun_prop) measurable_const
      · fun_prop
      · fun_prop
    have hmaj : Measurable (fun T : ℝ => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)) := by
      have : (fun T : ℝ => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ))
          = fun T : ℝ => Commons.Analysis.Integral.boxMajTerm (2 - β) (2 - β) |T - γ|
              + Commons.Analysis.Integral.boxMajTerm (2 - β) β |T - γ| := rfl
      rw [this]
      exact (hterm (2 - β) (2 - β)).add (hterm (2 - β) β)
    have hqlb : Measurable (fun T : ℝ => Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ)) := by
      unfold Commons.Analysis.Integral.boxQlb
      fun_prop
    exact hmaj.sub hqlb
  have hMmeas : AEStronglyMeasurable Mf ρ := hmeasMf.aestronglyMeasurable
  have hMnn : 0 ≤ᵐ[ρ] Mf := by
    filter_upwards [hTne] with T hT
    rw [hMf]
    show (0:ℝ) ≤ Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
        - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ)
    have h := Commons.Analysis.Integral.inner_le_boxMaj hβ0 hβ1 (sub_ne_zero.mpr hT)
    have h2 : (0:ℝ) ≤ ∫ x in (0:ℝ)..2, (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2)
        * Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x hx => div_nonneg (by linarith [hx.2])
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    linarith
  have hMfin : (∫⁻ T, ENNReal.ofReal (Mf T) ∂ρ) ≠ ⊤ := by
    rw [hMf, hρ]
    have hint : IntervalIntegrable (fun T : ℝ => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
        - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ)) volume c (c + 1) := by
      have h1 : IntervalIntegrable (fun T : ℝ => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ))
          volume c (c + 1) := by
        have := (Commons.Analysis.Integral.intervalIntegrable_boxMaj β (2 - β) hβ0 hβ2 (c - γ) (c + 1 - γ)).comp_sub_right γ
        simpa using this
      have h2 : IntervalIntegrable (fun T : ℝ => Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ))
          volume c (c + 1) := by
        have := (Commons.Analysis.Integral.intervalIntegrable_boxQlb β (2 - β) hβ2 (c - γ) (c + 1 - γ)).comp_sub_right γ
        simpa using this
      exact h1.sub h2
    have hint2 : Integrable (fun T : ℝ => Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
        - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ)) ρ := by
      rw [hρ]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : c ≤ c + 1)).mp hint |>.integrable
    exact ne_of_lt (Integrable.lintegral_lt_top hint2)
  rw [hstep1]
  calc (∫⁻ T, (∫⁻ x, ENNReal.ofReal ‖1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)
          - 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)‖ ∂σ) ∂ρ)
      ≤ ∫⁻ T, ENNReal.ofReal (Mf T) ∂ρ := by
        apply MeasureTheory.lintegral_mono_ae
        filter_upwards [hTne] with T hT
        exact hperT T hT
    _ = ENNReal.ofReal (∫ T, Mf T ∂ρ) := by
        have h1 : (∫ T, Mf T ∂ρ) = (∫⁻ T, ENNReal.ofReal (Mf T) ∂ρ).toReal :=
          integral_eq_lintegral_of_nonneg_ae hMnn hMmeas
        rw [h1, ENNReal.ofReal_toReal hMfin]
    _ = ENNReal.ofReal (∫ T in c..c + 1, (Commons.Analysis.Integral.boxMaj β (2 - β) (T - γ)
          - Commons.Analysis.Integral.boxQlb β (2 - β) (T - γ))) := by
        rw [hMf, hρ, ← intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
    _ ≤ ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
          ((3 / 2 - β) / ((3 / 2 - β) ^ 2 + (T - γ) ^ 2)
            + (1 + β) / ((1 + β) ^ 2 + (T - γ) ^ 2)))) :=
        ENNReal.ofReal_le_ofReal (window_int_le hβ0 hβ1)


theorem finsum_divisor_three_halves_integral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        (∫ T in c..c + 1,
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))
      ≤ Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2 := by
  classical
  have hcpos : 0 < c := by linarith
  set S : Finset ℂ := (divisor_support_finite χ R).toFinset with hS
  have hSmem : ∀ u : ℂ, u ∈ S ↔ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) u ≠ 0 := by
    intro u; rw [hS]; exact Set.Finite.mem_toFinset _
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R) :=
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable
      (DirichletCharacter.differentiable_completedLFunction hχ) _
  have hterm_nonneg : ∀ u ∈ S, ∀ T : ℝ, 0 ≤ ((((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))) := by
    intro u hu T
    have hd : 0 ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) :=
      Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u)
    have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
      Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn ((hSmem u).mp hu)
    have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
    have ha : 0 < (3 / 2 : ℝ) - u.re := by linarith [hs.2]
    have hb : 0 < 1 + u.re := by linarith [hs.1]
    have hd1 : 0 < ((3 / 2 : ℝ) - u.re) ^ 2 + (T - u.im) ^ 2 := by
      nlinarith [sq_nonneg (T - u.im), mul_pos ha ha]
    have hd2 : 0 < (1 + u.re) ^ 2 + (T - u.im) ^ 2 := by
      nlinarith [sq_nonneg (T - u.im), mul_pos hb hb]
    exact mul_nonneg hd (add_nonneg (div_nonneg ha.le hd1.le) (div_nonneg hb.le hd2.le))
  set G : ℝ → ℝ := fun T => Real.log (N:ℝ) + Real.log (2 + |T|) + 11/2 with hG
  have hGcont : ContinuousOn G (Set.uIcc c (c+1)) := by
    rw [hG]
    have hlog : ContinuousOn (fun T : ℝ => Real.log (2 + |T|)) (Set.uIcc c (c+1)) := by
      apply ContinuousOn.log
      · fun_prop
      · intro T hT; positivity
    exact (continuousOn_const.add hlog).add continuousOn_const
  have hGint : IntervalIntegrable G volume c (c+1) := hGcont.intervalIntegrable
  have hmono_bound : ∀ T : ℝ, T ∈ Set.Icc c (c+1) → ∑ u ∈ S, ((((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))) ≤ G T := by
    intro T hT
    have hzf := finsum_divisor_re_inv_sub_le_three_halves χ hχ hχprim T R
    have hfsub : Function.support (fun u : ℂ => ((((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) ⊆ (S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, hSmem]
      intro h0; exact hu (by rw [h0, Int.cast_zero, zero_mul])
    rw [finsum_eq_sum_of_support_subset _ hfsub] at hzf
    rw [hG]
    have hlog : Real.log (2 + |T|) ≤ Real.log (c + 3) := by
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by linarith [hT.1, hcpos])]
      linarith [hT.2]
    linarith
  have hFint : IntervalIntegrable (fun T : ℝ => ∑ u ∈ S, ((((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) volume c (c+1) := by
    refine IntervalIntegrable.mono_fun (f := G) hGint ?_ ?_
    · apply Measurable.aestronglyMeasurable
      apply Finset.measurable_sum
      intro u hu
      exact (Measurable.mul measurable_const (Measurable.add
        (Measurable.div measurable_const (by fun_prop))
        (Measurable.div measurable_const (by fun_prop))))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with T hT
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun u hu => hterm_nonneg u hu T))]
      rw [hG, Real.norm_of_nonneg]
      · rw [Set.uIoc_of_le (by linarith : c ≤ c + 1)] at hT
        exact hmono_bound T (Set.Ioc_subset_Icc_self hT)
      · have h1 : 0 ≤ Real.log (N:ℝ) := Commons.NumberTheory.DirichletCharacter.logN_nonneg
        have h2 : 0 ≤ Real.log (2 + |T|) := Real.log_nonneg (by have := abs_nonneg T; linarith)
        linarith
  have hIntTerm : ∀ u ∈ S, IntervalIntegrable (fun T : ℝ => ((((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) volume c (c+1) := by
    intro u hu
    by_cases hd0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R) u = 0
    · have hz : (fun T : ℝ => ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
            ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
              + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))
          = fun _ : ℝ => (0:ℝ) := by
        rw [hd0]; funext T; simp
      rw [hz]
      exact intervalIntegrable_const
    · have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn hd0
      have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
      have ha : 0 < (3 / 2 : ℝ) - u.re := by linarith [hs.2]
      have hb : 0 < 1 + u.re := by linarith [hs.1]
      have hcont : Continuous (fun T : ℝ =>
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))) := by
        apply Continuous.add
        · apply Continuous.div continuous_const (by fun_prop)
          intro T
          exact ne_of_gt (by nlinarith [sq_nonneg (T - u.im), mul_pos ha ha])
        · apply Continuous.div continuous_const (by fun_prop)
          intro T
          exact ne_of_gt (by nlinarith [sq_nonneg (T - u.im), mul_pos hb hb])
      exact (hcont.const_mul _).intervalIntegrable c (c+1)
  have hsub : Function.support (fun u : ℂ =>
      ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        (∫ T in c..c + 1,
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, hSmem]
    intro h0
    exact hu (by rw [h0, Int.cast_zero, zero_mul])
  rw [finsum_eq_sum_of_support_subset _ hsub]
  have hstep1 : (∑ u ∈ S, ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        (∫ T in c..c + 1,
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))
      = ∑ u ∈ S, ∫ T in c..c + 1, ((((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [intervalIntegral.integral_const_mul]
  rw [hstep1, ← intervalIntegral.integral_finset_sum hIntTerm]
  have hfinal := intervalIntegral.integral_mono_on (by linarith : c ≤ c+1) hFint hGint hmono_bound
  have hGval : (∫ T in c..c+1, G T) ≤ Real.log (N:ℝ) + Real.log (c+3) + 11/2 := by
    have hlogcont : ContinuousOn (fun T : ℝ => Real.log (2 + |T|)) (Set.uIcc c (c+1)) := by
      apply ContinuousOn.log
      · fun_prop
      · intro T hT; positivity
    have hlogint : IntervalIntegrable (fun T : ℝ => Real.log (2 + |T|)) volume c (c+1) :=
      hlogcont.intervalIntegrable
    have hsplit : (∫ T in c..c+1, G T)
        = (Real.log (N:ℝ) + 11/2) + ∫ T in c..c+1, Real.log (2 + |T|) := by
      rw [hG]
      rw [show (fun T : ℝ => Real.log (N:ℝ) + Real.log (2 + |T|) + 11/2)
          = fun T : ℝ => (Real.log (N:ℝ) + 11/2) + Real.log (2 + |T|) from by funext T; ring]
      rw [intervalIntegral.integral_add intervalIntegrable_const hlogint,
        intervalIntegral.integral_const]
      simp
    rw [hsplit]
    have h2 : (∫ T in c..c+1, Real.log (2 + |T|)) ≤ ∫ T in c..c+1, Real.log (c+3) := by
      apply intervalIntegral.integral_mono_on (by linarith : c ≤ c+1) hlogint
        (continuous_const.intervalIntegrable c (c+1))
      intro T hT
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by linarith [hT.1, hcpos])]
      linarith [hT.2]
    have h3 : (∫ T in c..c+1, Real.log (c+3)) = Real.log (c+3) := by
      rw [intervalIntegral.integral_const]; simp
    linarith
  linarith

lemma zeroKernel_lintegral_le' {c : ℝ} {u : ℂ} (h1 : 0 < u.re) (h2 : u.re < 1) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
        - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖
        ∂((volume.restrict (Set.Ioc c (c + 1))).prod (volume.restrict (Set.Ioc 0 2))))
      ≤ ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
          ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
  have h := zeroKernel_lintegral_le (c := c) (β := u.re) (γ := u.im) h1 h2
  convert h using 2
  have hcu : ((↑u.re : ℂ) + Complex.I * (↑u.im : ℂ)) = u := by apply Complex.ext <;> simp
  simp only [hcu]


noncomputable def zeroWeight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z z₁ : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ∑ᶠ u : ℂ, ENNReal.ofReal
    ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖)


noncomputable def zeroIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) (u : ℂ)
    (z z₁ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖)

lemma zeroWeight_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z z₁ : ℂ) :
    zeroWeight χ z z₁ = ⨆ n : ℕ, ∑ᶠ u : ℂ, zeroIntegrand χ n u z z₁ := rfl

lemma measurable_zeroIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) (u : ℂ) :
    Measurable fun p : ℝ × ℝ => zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
      ((2 : ℂ) + Complex.I * (p.1 : ℂ)) := by
  unfold zeroIntegrand
  apply ENNReal.continuous_ofReal.measurable.comp
  apply Measurable.const_mul
  apply continuous_norm.measurable.comp
  apply Measurable.sub
  · apply Measurable.div measurable_const
    exact (by fun_prop : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u))
  · apply Measurable.div measurable_const
    exact (by fun_prop : Measurable (fun p : ℝ × ℝ => ((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u))

theorem ofReal_norm_logDeriv_le_base_add_zeroWeight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (z z₁ : ℂ) (hz₁ : DirichletCharacter.completedLFunction χ z₁ ≠ 0) :
    ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z‖ ≤
      ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z₁‖ + zeroWeight χ z z₁ := by
  classical
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable
      (DirichletCharacter.differentiable_completedLFunction hχ) _
  by_cases hz : DirichletCharacter.completedLFunction χ z = 0
  · have h0 : logDeriv (DirichletCharacter.completedLFunction χ) z = 0 := by
      rw [logDeriv_apply, hz]; simp
    rw [h0]; simp
  · have hpf := Commons.NumberTheory.DirichletCharacter.partialFraction_diff χ hχ hχprim z z₁ hz hz₁
    have hnorm : Tendsto (fun R : ℝ => ENNReal.ofReal ‖∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u))‖)
        atTop (𝓝 (ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z
          - logDeriv (DirichletCharacter.completedLFunction χ) z₁‖)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpf.norm
    have hbound : ∀ R : ℝ, ENNReal.ofReal ‖∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u))‖
        ≤ ⨆ n : ℕ, ∑ᶠ u : ℂ,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖) := by
      intro R
      set m : ℕ := Nat.ceil R with hm
      have hRm : R ≤ (m : ℝ) := Nat.le_ceil R
      set S : Finset ℂ := (divisor_support_finite χ (m:ℝ)).toFinset with hS
      have hSmem : ∀ u : ℂ, u ∈ S ↔ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (m:ℝ)) u ≠ 0 := by
        intro u
        rw [hS]
        exact Set.Finite.mem_toFinset _
      have hfs : Function.HasFiniteSupport (fun u : ℂ =>
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u))) :=
        (divisor_support_finite χ R).subset (fun u hu => by
          rw [Function.mem_support] at hu ⊢
          exact fun h => hu (by rw [h, Int.cast_zero, zero_mul]))
      have hsub : Function.support (fun u : ℂ =>
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u))) ⊆ (S : Set ℂ) := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.mem_coe, hSmem]
        have hdR : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u ≠ 0 := by
          intro h; exact hu (by rw [h, Int.cast_zero, zero_mul])
        have huR : u ∈ Metric.closedBall (0:ℂ) R := by
          by_contra hc
          exact hdR (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
        have hun : u ∈ Metric.closedBall (0:ℂ) (m:ℝ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at huR ⊢
          exact le_trans huR hRm
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0:ℂ) R ∪ Metric.closedBall (0:ℂ) (m:ℝ)) := by
          intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (hf := hfU) huR hun
        rw [← heq]; exact hdR
      have hstep1 : ENNReal.ofReal ‖∑ u ∈ S, ((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖
          ≤ ∑ u ∈ S, ENNReal.ofReal ‖((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖ := by
        calc ENNReal.ofReal ‖∑ u ∈ S, ((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖
            ≤ ENNReal.ofReal (∑ u ∈ S, ‖((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖) :=
              ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
          _ = ∑ u ∈ S, ENNReal.ofReal ‖((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖ :=
              ENNReal.ofReal_sum_of_nonneg (fun u _ => norm_nonneg _)
      have hstep2 : ∑ u ∈ S, ENNReal.ofReal ‖((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖
          ≤ ∑ᶠ u : ℂ, ENNReal.ofReal ((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (m : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖) := by
        have hsub2 : Function.support (fun u : ℂ => ENNReal.ofReal ((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (m : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖))
            ⊆ (S : Set ℂ) := by
          intro u hu
          rw [Function.mem_support] at hu
          rw [Finset.mem_coe, hSmem]
          intro h0
          exact hu (by rw [h0, Int.cast_zero, zero_mul, ENNReal.ofReal_zero])
        rw [finsum_eq_sum_of_support_subset _ hsub2]
        apply Finset.sum_le_sum
        intro u hu
        by_cases hd0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u = 0
        · rw [hd0, Int.cast_zero, zero_mul, norm_zero, ENNReal.ofReal_zero]
          exact bot_le
        · have huR : u ∈ Metric.closedBall (0:ℂ) R := by
            by_contra hc
            exact hd0 (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
          have hum : u ∈ Metric.closedBall (0:ℂ) (m:ℝ) := by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at huR ⊢
            exact le_trans huR hRm
          have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0:ℂ) R ∪ Metric.closedBall (0:ℂ) (m:ℝ)) := by
            intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
          have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
            (hf := hfU) huR hum
          have hdnn : 0 ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R) u :=
            MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn R) u
          rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg hdnn), heq]
      calc ENNReal.ofReal ‖∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u))‖
          = ENNReal.ofReal ‖∑ u ∈ S, ((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z₁ - u)))‖ := by
              rw [finsum_eq_sum_of_support_subset _ hsub]
        _ ≤ _ := hstep1
        _ ≤ _ := hstep2
        _ ≤ ⨆ k : ℕ, ∑ᶠ u : ℂ, ENNReal.ofReal ((((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (k : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖) :=
              le_iSup (fun k : ℕ => ∑ᶠ u : ℂ, ENNReal.ofReal ((((MeromorphicOn.divisor
                (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (k : ℝ))) u : ℤ) : ℝ) * ‖1 / (z - u) - 1 / (z₁ - u)‖)) m
    have hkey := le_of_tendsto hnorm (Filter.Eventually.of_forall hbound)
    have htri : ‖logDeriv (DirichletCharacter.completedLFunction χ) z‖
        ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) z₁‖
          + ‖logDeriv (DirichletCharacter.completedLFunction χ) z
              - logDeriv (DirichletCharacter.completedLFunction χ) z₁‖ := by
      have h1 := norm_add_le (logDeriv (DirichletCharacter.completedLFunction χ) z₁)
        (logDeriv (DirichletCharacter.completedLFunction χ) z
          - logDeriv (DirichletCharacter.completedLFunction χ) z₁)
      have h2 : logDeriv (DirichletCharacter.completedLFunction χ) z₁
          + (logDeriv (DirichletCharacter.completedLFunction χ) z
            - logDeriv (DirichletCharacter.completedLFunction χ) z₁)
          = logDeriv (DirichletCharacter.completedLFunction χ) z := by ring
      rwa [h2] at h1
    calc ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z‖
        ≤ ENNReal.ofReal (‖logDeriv (DirichletCharacter.completedLFunction χ) z₁‖
            + ‖logDeriv (DirichletCharacter.completedLFunction χ) z
              - logDeriv (DirichletCharacter.completedLFunction χ) z₁‖) :=
            ENNReal.ofReal_le_ofReal htri
      _ = ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z₁‖
          + ENNReal.ofReal ‖logDeriv (DirichletCharacter.completedLFunction χ) z
            - logDeriv (DirichletCharacter.completedLFunction χ) z₁‖ :=
            ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := add_le_add le_rfl hkey

theorem linnik_avg_arith {N : ℕ} [NeZero N] {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) :
    (13 / 5) * Real.log (N : ℝ) + (18 / 5) * Real.log (c + 3) + 203 / 10
      ≤ 20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3)) := by
  have hN : 0 ≤ Real.log (N : ℝ) := Commons.NumberTheory.DirichletCharacter.logN_nonneg
  have hc3 : 0 ≤ Real.log (c + 3) := Real.log_nonneg (by linarith)
  have hlog35 : 1 ≤ Real.log (3.5 : ℝ) := by
    have h1 : Real.exp 1 ≤ (3.5 : ℝ) := by
      have := Real.exp_one_lt_three; linarith
    have h2 : Real.log (Real.exp 1) ≤ Real.log (3.5 : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hc35 : (3.5 : ℝ) ≤ c + 3 := by linarith
  have hlogc : 1 ≤ Real.log (c + 3) :=
    le_trans hlog35 (Real.log_le_log (by norm_num) hc35)
  have hlogc5 : Real.log (c + 3) ≤ Real.log (c + 5) :=
    Real.log_le_log (by linarith) (by linarith)
  have harg : (2 : ℝ) + c + 3 = c + 5 := by ring
  rw [harg]
  linarith [hN, hlogc, hlogc5]

theorem MAIN {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) :
    (∫ T : ℝ in c..c + 1, ∫ x : ℝ in 0..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (T : ℂ))‖) ≤
      20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3)) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  change (∫ T : ℝ in c..c + 1, ∫ x : ℝ in 0..2,
      ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖) ≤
    20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3))
  have hcpos : 0 < c := by linarith [hc]
  set ρ : Measure ℝ := volume.restrict (Set.Ioc c (c + 1)) with hρ
  set σ : Measure ℝ := volume.restrict (Set.Ioc 0 2) with hσ
  set ν : Measure (ℝ × ℝ) := ρ.prod σ with hν
  have hdΛ : Differentiable ℂ Λ := fun w =>
    (DirichletCharacter.differentiable_completedLFunction hχ).differentiableAt
  have hmeasLD : Measurable (fun w : ℂ => logDeriv Λ w) := by
    have h1 : Measurable (deriv Λ) := hdΛ.deriv.continuous.measurable
    have h2 : Measurable Λ := hdΛ.continuous.measurable
    exact h1.div h2
  have hmeas_f : Measurable (fun p : ℝ × ℝ =>
      ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
    continuous_norm.measurable.comp (hmeasLD.comp
      ((by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)))).measurable))
  set Zw : ℝ × ℝ → ℝ≥0∞ := fun p =>
      zeroWeight χ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) with hZw
  have hpoint : ∀ p : ℝ × ℝ, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ≤
      ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ + Zw p := by
    intro p
    have hz₁ : Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ≠ 0 := by
      simpa [Λ] using completedLFunction_ne_zero_re_two χ hχ hχprim p.1
    simpa [hZw] using ofReal_norm_logDeriv_le_base_add_zeroWeight χ hχ hχprim _ _ hz₁
  have hI1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
      ≤ (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        + ∫⁻ p, Zw p ∂ν := by
    have hmeasB : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp
        (continuous_norm.measurable.comp (hmeasLD.comp
          ((by fun_prop : Continuous (fun p : ℝ × ℝ => ((2 : ℂ) + Complex.I * (p.1 : ℂ)))).measurable)))
    calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ ∫⁻ p, (ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ + Zw p) ∂ν :=
          MeasureTheory.lintegral_mono hpoint
      _ = _ := MeasureTheory.lintegral_add_left hmeasB _
  have hmeasB_T : Measurable (fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) :=
    continuous_norm.measurable.comp (hmeasLD.comp
      ((by fun_prop : Continuous (fun T : ℝ => ((2 : ℂ) + Complex.I * (T : ℂ)))).measurable))
  have hBpt : ∀ T : ℝ, T ∈ Set.Icc c (c + 1) →
      ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ (1 / 2) * Real.log (c + 3) + 3 := by
    intro T hT
    have h1 : ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖
        ≤ (1 / 2) * Real.log (2 + |T|) + 3 := by
      simpa [Λ] using
        Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight χ hχ T
    have hTabs : |T| ≤ c + 1 := by
      rw [abs_of_nonneg (by linarith [hT.1, hcpos])]
      exact hT.2
    have hlog : Real.log (2 + |T|) ≤ Real.log (c + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hBnn : 0 ≤ (1 / 2) * Real.log (c + 3) + 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ c + 3 by linarith)
    linarith
  have hBint : IntervalIntegrable (fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
      volume c (c + 1) := by
    refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := (1/2) * Real.log (c+3) + 3)) ?_ ?_
    · exact hmeasB_T.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with T hT
      rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hBnn]
      rw [Set.uIoc_of_le (by linarith : c ≤ c + 1)] at hT
      exact hBpt T (Set.Ioc_subset_Icc_self hT)
  have hIV : 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
      ≤ Real.log (c + 3) + 6 := by
    have hmono : (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        ≤ (1 / 2) * Real.log (c + 3) + 3 := by
      have h := intervalIntegral.integral_mono_on
        (f := fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        (g := fun _ : ℝ => (1 / 2) * Real.log (c + 3) + 3) (by linarith) hBint
        intervalIntegrable_const (fun x hx => hBpt x hx)
      simpa using h
    linarith
  have hI2 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
      = ENNReal.ofReal (2 * ∫ T in c..c + 1,
          ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
    have hmeasBB : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp
        (hmeasB_T.comp measurable_fst)
    have hae : AEMeasurable (Function.uncurry (fun T _x : ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)) (ρ.prod σ) :=
      hmeasBB.aemeasurable
    rw [show ν = ρ.prod σ from hν]
    rw [← MeasureTheory.lintegral_lintegral (f := fun T _x : ℝ =>
      ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) hae]
    have hinner : ∀ T : ℝ, (∫⁻ x, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂σ)
        = ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ * 2 := by
      intro T
      have hσ1 : σ Set.univ = 2 := by
        rw [hσ, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        norm_num
      rw [MeasureTheory.lintegral_const, hσ1]
    have hmeasBT' : Measurable (fun T : ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp hmeasB_T
    simp_rw [hinner]
    rw [MeasureTheory.lintegral_mul_const (2 : ℝ≥0∞) hmeasBT']
    have hfinB : (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ) ≠ ⊤ := by
      have h1 : (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
          ≤ ∫⁻ T, ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) ∂ρ := by
        apply MeasureTheory.lintegral_mono_ae
        rw [hρ]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with T hT
        exact ENNReal.ofReal_le_ofReal (hBpt T (Set.Ioc_subset_Icc_self hT))
      have h2 : (∫⁻ T, ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) ∂ρ)
          = ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Ioc]
        norm_num
      exact ne_of_lt (lt_of_le_of_lt (le_trans h1 (le_of_eq h2)) ENNReal.ofReal_lt_top)
    have hintBρ : (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (by filter_upwards with T; exact norm_nonneg _)
        hmeasB_T.aestronglyMeasurable
    have hofB : ENNReal.ofReal (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = ∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ := by
      rw [hintBρ, ENNReal.ofReal_toReal hfinB]
    have hρeq : (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = ∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
      rw [hρ, ← intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
    have hAnn : (0 : ℝ) ≤ ∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
    rw [← hofB, hρeq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_mul hAnn]
    congr 1
    ring
  have hI3 : (∫⁻ p, Zw p ∂ν)
      ≤ ENNReal.ofReal ((13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2)) := by
    have hAn' : ∀ r : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 r) := fun r =>
      Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable
        (DirichletCharacter.differentiable_completedLFunction hχ) _
    have hker : ∀ u : ℂ, 0 < u.re → u.re < 1 →
        (∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
            - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν)
          ≤ ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
      intro u h1 h2
      rw [hν, hρ, hσ]
      exact zeroKernel_lintegral_le' h1 h2
    set W : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
        ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
            ((2 : ℂ) + Complex.I * (p.1 : ℂ)) with hWdef
    have hZw' : ∀ p : ℝ × ℝ, Zw p = ⨆ n : ℕ, W n p := by
      intro p
      show zeroWeight χ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) = _
      rw [zeroWeight_eq]
      exact iSup_congr (fun n => by
        have hsupp : Function.support (fun u : ℂ => zeroIntegrand χ n u
              ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)))
            ⊆ ((divisor_support_finite χ (n:ℝ)).toFinset : Set ℂ) := by
          intro u hu
          rw [Function.mem_support] at hu
          rw [Finset.mem_coe, Set.Finite.mem_toFinset]
          change MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n:ℝ)) u ≠ 0
          intro h0
          refine hu ?_
          simp only [zeroIntegrand, h0, Int.cast_zero, zero_mul, ENNReal.ofReal_zero]
        rw [finsum_eq_sum_of_support_subset _ hsupp])
    have hZeq : Zw = fun p : ℝ × ℝ => ⨆ n : ℕ, W n p := funext hZw'
    have hmeasW : ∀ n : ℕ, AEMeasurable (W n) ν := by
      intro n
      apply Measurable.aemeasurable
      rw [hWdef]
      exact Finset.measurable_sum _ (fun u _ => measurable_zeroIntegrand χ n u)
    have hmonoW : ∀ᵐ p ∂ν, Monotone fun n => W n p := by
      filter_upwards with p
      intro a b hab
      rw [hWdef]
      simp only
      have hcongr : (∑ u ∈ (divisor_support_finite χ (a:ℝ)).toFinset,
            zeroIntegrand χ a u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)))
          = ∑ u ∈ (divisor_support_finite χ (a:ℝ)).toFinset,
            zeroIntegrand χ b u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Set.Finite.mem_toFinset] at hu
        rw [Function.mem_support] at hu
        have hua : u ∈ Metric.closedBall (0:ℂ) (a:ℝ) := by
          by_contra hc
          exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
        have hub : u ∈ Metric.closedBall (0:ℂ) (b:ℝ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hua ⊢
          exact le_trans hua (Nat.cast_le.mpr hab)
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0:ℂ) (a:ℝ) ∪ Metric.closedBall (0:ℂ) (b:ℝ)) := by
          intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (hf := hfU) hua hub
        simp only [zeroIntegrand, heq]
      rw [hcongr]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro u hu
        rw [Set.Finite.mem_toFinset] at hu ⊢
        rw [Function.mem_support] at hu ⊢
        have hua : u ∈ Metric.closedBall (0:ℂ) (a:ℝ) := by
          by_contra hc
          exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
        have hub : u ∈ Metric.closedBall (0:ℂ) (b:ℝ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hua ⊢
          exact le_trans hua (Nat.cast_le.mpr hab)
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0:ℂ) (a:ℝ) ∪ Metric.closedBall (0:ℂ) (b:ℝ)) := by
          intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (hf := hfU) hua hub
        rw [← heq]; exact hu
      · intro u hu _
        simp only [zeroIntegrand]
        exact bot_le
    rw [hZeq, MeasureTheory.lintegral_iSup' hmeasW hmonoW]
    apply iSup_le
    intro n
    have hSsub : ∀ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (n : ℝ)) u ≠ 0 := by
      intro u hu; rw [Set.Finite.mem_toFinset] at hu; exact hu
    have hlin : (∫⁻ p, W n p ∂ν)
        = ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            (∫⁻ p, zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
              ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ∂ν) := by
      rw [hWdef]
      exact MeasureTheory.lintegral_finsetSum _ (fun u _ => measurable_zeroIntegrand χ n u)
    have hstep : ∀ u : ℂ, (∫⁻ p, zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
            ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ∂ν)
        = ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
              - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν := by
      intro u
      simp only [zeroIntegrand]
      simp_rw [ENNReal.ofReal_mul (Int.cast_nonneg
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u))]
      rw [MeasureTheory.lintegral_const_mul]
      apply ENNReal.continuous_ofReal.measurable.comp
      exact continuous_norm.measurable.comp (Measurable.sub
        (Measurable.div measurable_const
          (by fun_prop : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)))
        (Measurable.div measurable_const
          (by fun_prop : Measurable (fun p : ℝ × ℝ => ((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u))))
    have hsum2 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
              - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν)
        ≤ ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn' (n:ℝ)) (hSsub u hu)
      have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
      exact mul_le_mul_of_nonneg_left (hker u hs.1 hs.2) bot_le
    have hsum3 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
        = ENNReal.ofReal (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
            * ((13 / 5) * (∫ T in c..c + 1,
                ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                  + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun u hu => by
        have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
          Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn' (n:ℝ)) (hSsub u hu)
        have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
        have ha : 0 < (3 / 2 : ℝ) - u.re := by linarith [hs.2]
        have hb : 0 < 1 + u.re := by linarith [hs.1]
        have hq : 0 ≤ ∫ T in c..c + 1,
            ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
              + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)) := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro T _
          apply add_nonneg
          · apply div_nonneg ha.le; positivity
          · apply div_nonneg hb.le; positivity
        exact mul_nonneg (Int.cast_nonneg
          (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u)) (mul_nonneg (by norm_num) hq))]
      apply Finset.sum_congr rfl
      intro u hu
      rw [ENNReal.ofReal_mul (Int.cast_nonneg
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u))]
    have hsum4 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
            * ((13 / 5) * (∫ T in c..c + 1,
                ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                  + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
        ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
      have h := finsum_divisor_three_halves_integral χ hχ hχprim hc (n : ℝ)
      have hfs : Function.support (fun u : ℂ => ((((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ) *
          (∫ T in c..c + 1,
            ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
              + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
          ⊆ ((divisor_support_finite χ (n : ℝ)).toFinset : Set ℂ) := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        intro h0; exact hu (by rw [h0, Int.cast_zero, zero_mul])
      rw [finsum_eq_sum_of_support_subset _ hfs] at h
      calc ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
              * ((13 / 5) * (∫ T in c..c + 1,
                  ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                    + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))
          = ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset, (13 / 5) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ)
              * (∫ T in c..c + 1,
                  ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                    + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
            apply Finset.sum_congr rfl; intro u _; ring
        _ ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left h (by norm_num)
    rw [hlin, Finset.sum_congr rfl (fun u _ => hstep u)]
    exact le_trans (le_trans hsum2 (le_of_eq hsum3)) (ENNReal.ofReal_le_ofReal hsum4)
  have hfin : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν) < ⊤ := by
    have hb1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν) < ⊤ := by
      rw [hI2]; exact ENNReal.ofReal_lt_top
    have hb2 : (∫⁻ p, Zw p ∂ν) < ⊤ := lt_of_le_of_lt hI3 ENNReal.ofReal_lt_top
    calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ _ := hI1
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hb1, hb2⟩
  have hV : (∫ T : ℝ in c..c + 1, ∫ x : ℝ in 0..2,
        ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖)
      = (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal := by
    have hAE : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) ν :=
      hmeas_f.aestronglyMeasurable
    have hint : Integrable
        (fun p : ℝ × ℝ => ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) ν :=
      ⟨hAE, (MeasureTheory.hasFiniteIntegral_iff_ofReal
        (by filter_upwards with p; exact norm_nonneg _)).mpr hfin⟩
    have h1 : (∫ p, ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        = (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal :=
      integral_eq_lintegral_of_nonneg_ae (by filter_upwards with p; exact norm_nonneg _) hAE
    have h2 : (∫ p, ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        = ∫ T in c..c + 1, ∫ x in 0..2, ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖ := by
      simp only [intervalIntegral.integral_of_le (by linarith : c ≤ c + 1),
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2)]
      rw [← hρ, ← hσ, hν]
      exact MeasureTheory.integral_prod _ hint
    rw [← h2, h1]
  rw [hV]
  have htot : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal
      ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
    have h1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ ENNReal.ofReal (2 * ∫ T in c..c + 1,
              ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
          + ENNReal.ofReal ((13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2)) := by
      calc _ ≤ (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
              + ∫⁻ p, Zw p ∂ν := hI1
        _ = _ := by rw [hI2]
        _ ≤ _ := add_le_add le_rfl hI3
    have h2 := ENNReal.toReal_mono (by
      rw [ne_eq, ENNReal.add_eq_top]
      push_neg
      exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) h1
    have h2nn : (0:ℝ) ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
      apply mul_nonneg (by norm_num)
      exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
    have h3nn : (0:ℝ) ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
      apply mul_nonneg (by norm_num)
      linarith [Commons.NumberTheory.DirichletCharacter.logN_nonneg (N := N),
        Real.log_nonneg (show (1:ℝ) ≤ c + 3 by linarith)]
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal h2nn,
      ENNReal.toReal_ofReal h3nn] at h2
  calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal
      ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := htot
    _ ≤ (Real.log (c + 3) + 6) + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
        linarith [hIV]
    _ ≤ 20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3)) := by
        have h := linnik_avg_arith (N := N) hc
        linarith [h]


theorem logDeriv_rightHalf_avg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) :
    (∫ T : ℝ in c..c + 1,
        ∫ x : ℝ in 0..2,
          ‖logDeriv (DirichletCharacter.completedLFunction χ)
            ((x : ℂ) + Complex.I * (T : ℂ))‖) ≤
      20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3)) := by

  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  change (∫ T : ℝ in c..c + 1, ∫ x : ℝ in 0..2,
      ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖) ≤
    20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3))
  have hcpos : 0 < c := by linarith [hc]
  set ρ : Measure ℝ := volume.restrict (Set.Ioc c (c + 1)) with hρ
  set σ : Measure ℝ := volume.restrict (Set.Ioc 0 2) with hσ
  set ν : Measure (ℝ × ℝ) := ρ.prod σ with hν
  have hdΛ : Differentiable ℂ Λ := fun w =>
    (DirichletCharacter.differentiable_completedLFunction hχ).differentiableAt
  have hmeasLD : Measurable (fun w : ℂ => logDeriv Λ w) := by
    have h1 : Measurable (deriv Λ) := hdΛ.deriv.continuous.measurable
    have h2 : Measurable Λ := hdΛ.continuous.measurable
    exact h1.div h2
  have hmeas_f : Measurable (fun p : ℝ × ℝ =>
      ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
    continuous_norm.measurable.comp (hmeasLD.comp
      ((by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)))).measurable))
  set Zw : ℝ × ℝ → ℝ≥0∞ := fun p =>
      zeroWeight χ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) with hZw
  have hpoint : ∀ p : ℝ × ℝ, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ≤
      ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ + Zw p := by
    intro p
    have hz₁ : Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ≠ 0 := by
      simpa [Λ] using completedLFunction_ne_zero_re_two χ hχ hχprim p.1
    simpa [hZw] using ofReal_norm_logDeriv_le_base_add_zeroWeight χ hχ hχprim _ _ hz₁
  have hI1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
      ≤ (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        + ∫⁻ p, Zw p ∂ν := by
    have hmeasB : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp
        (continuous_norm.measurable.comp (hmeasLD.comp
          ((by fun_prop : Continuous (fun p : ℝ × ℝ => ((2 : ℂ) + Complex.I * (p.1 : ℂ)))).measurable)))
    calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ ∫⁻ p, (ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ + Zw p) ∂ν :=
          MeasureTheory.lintegral_mono hpoint
      _ = _ := MeasureTheory.lintegral_add_left hmeasB _
  have hmeasB_T : Measurable (fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) :=
    continuous_norm.measurable.comp (hmeasLD.comp
      ((by fun_prop : Continuous (fun T : ℝ => ((2 : ℂ) + Complex.I * (T : ℂ)))).measurable))
  have hBpt : ∀ T : ℝ, T ∈ Set.Icc c (c + 1) →
      ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ (1 / 2) * Real.log (c + 3) + 3 := by
    intro T hT
    have h1 : ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖
        ≤ (1 / 2) * Real.log (2 + |T|) + 3 := by
      simpa [Λ] using
        Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight χ hχ T
    have hTabs : |T| ≤ c + 1 := by
      rw [abs_of_nonneg (by linarith [hT.1, hcpos])]
      exact hT.2
    have hlog : Real.log (2 + |T|) ≤ Real.log (c + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hBnn : 0 ≤ (1 / 2) * Real.log (c + 3) + 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ c + 3 by linarith)
    linarith
  have hBint : IntervalIntegrable (fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
      volume c (c + 1) := by
    refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := (1/2) * Real.log (c+3) + 3)) ?_ ?_
    · exact hmeasB_T.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with T hT
      rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hBnn]
      rw [Set.uIoc_of_le (by linarith : c ≤ c + 1)] at hT
      exact hBpt T (Set.Ioc_subset_Icc_self hT)
  have hIV : 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
      ≤ Real.log (c + 3) + 6 := by
    have hmono : (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        ≤ (1 / 2) * Real.log (c + 3) + 3 := by
      have h := intervalIntegral.integral_mono_on
        (f := fun T : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        (g := fun _ : ℝ => (1 / 2) * Real.log (c + 3) + 3) (by linarith) hBint
        intervalIntegrable_const (fun x hx => hBpt x hx)
      simpa using h
    linarith
  have hI2 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
      = ENNReal.ofReal (2 * ∫ T in c..c + 1,
          ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
    have hmeasBB : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp
        (hmeasB_T.comp measurable_fst)
    have hae : AEMeasurable (Function.uncurry (fun T _x : ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)) (ρ.prod σ) :=
      hmeasBB.aemeasurable
    rw [show ν = ρ.prod σ from hν]
    rw [← MeasureTheory.lintegral_lintegral (f := fun T _x : ℝ =>
      ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) hae]
    have hinner : ∀ T : ℝ, (∫⁻ x, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂σ)
        = ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ * 2 := by
      intro T
      have hσ1 : σ Set.univ = 2 := by
        rw [hσ, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        norm_num
      rw [MeasureTheory.lintegral_const, hσ1]
    have hmeasBT' : Measurable (fun T : ℝ =>
        ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) :=
      ENNReal.continuous_ofReal.measurable.comp hmeasB_T
    simp_rw [hinner]
    rw [MeasureTheory.lintegral_mul_const (2 : ℝ≥0∞) hmeasBT']
    have hfinB : (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ) ≠ ⊤ := by
      have h1 : (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
          ≤ ∫⁻ T, ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) ∂ρ := by
        apply MeasureTheory.lintegral_mono_ae
        rw [hρ]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with T hT
        exact ENNReal.ofReal_le_ofReal (hBpt T (Set.Ioc_subset_Icc_self hT))
      have h2 : (∫⁻ T, ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) ∂ρ)
          = ENNReal.ofReal ((1 / 2) * Real.log (c + 3) + 3) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Ioc]
        norm_num
      exact ne_of_lt (lt_of_le_of_lt (le_trans h1 (le_of_eq h2)) ENNReal.ofReal_lt_top)
    have hintBρ : (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = (∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (by filter_upwards with T; exact norm_nonneg _)
        hmeasB_T.aestronglyMeasurable
    have hofB : ENNReal.ofReal (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = ∫⁻ T, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ := by
      rw [hintBρ, ENNReal.ofReal_toReal hfinB]
    have hρeq : (∫ T, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ∂ρ)
        = ∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
      rw [hρ, ← intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
    have hAnn : (0 : ℝ) ≤ ∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
    rw [← hofB, hρeq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_mul hAnn]
    congr 1
    ring
  have hI3 : (∫⁻ p, Zw p ∂ν)
      ≤ ENNReal.ofReal ((13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2)) := by
    have hAn' : ∀ r : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 r) := fun r =>
      Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable
        (DirichletCharacter.differentiable_completedLFunction hχ) _
    have hker : ∀ u : ℂ, 0 < u.re → u.re < 1 →
        (∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
            - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν)
          ≤ ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
      intro u h1 h2
      rw [hν, hρ, hσ]
      exact zeroKernel_lintegral_le' h1 h2
    set W : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
        ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
            ((2 : ℂ) + Complex.I * (p.1 : ℂ)) with hWdef
    have hZw' : ∀ p : ℝ × ℝ, Zw p = ⨆ n : ℕ, W n p := by
      intro p
      show zeroWeight χ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) = _
      rw [zeroWeight_eq]
      exact iSup_congr (fun n => by
        have hsupp : Function.support (fun u : ℂ => zeroIntegrand χ n u
              ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)))
            ⊆ ((divisor_support_finite χ (n:ℝ)).toFinset : Set ℂ) := by
          intro u hu
          rw [Function.mem_support] at hu
          rw [Finset.mem_coe, Set.Finite.mem_toFinset]
          change MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n:ℝ)) u ≠ 0
          intro h0
          refine hu ?_
          simp only [zeroIntegrand, h0, Int.cast_zero, zero_mul, ENNReal.ofReal_zero]
        rw [finsum_eq_sum_of_support_subset _ hsupp])
    have hZeq : Zw = fun p : ℝ × ℝ => ⨆ n : ℕ, W n p := funext hZw'
    have hmeasW : ∀ n : ℕ, AEMeasurable (W n) ν := by
      intro n
      apply Measurable.aemeasurable
      rw [hWdef]
      exact Finset.measurable_sum _ (fun u _ => measurable_zeroIntegrand χ n u)
    have hmonoW : ∀ᵐ p ∂ν, Monotone fun n => W n p := by
      filter_upwards with p
      intro a b hab
      rw [hWdef]
      simp only
      have hcongr : (∑ u ∈ (divisor_support_finite χ (a:ℝ)).toFinset,
            zeroIntegrand χ a u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)))
          = ∑ u ∈ (divisor_support_finite χ (a:ℝ)).toFinset,
            zeroIntegrand χ b u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) ((2 : ℂ) + Complex.I * (p.1 : ℂ)) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Set.Finite.mem_toFinset] at hu
        rw [Function.mem_support] at hu
        have hua : u ∈ Metric.closedBall (0:ℂ) (a:ℝ) := by
          by_contra hc
          exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
        have hub : u ∈ Metric.closedBall (0:ℂ) (b:ℝ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hua ⊢
          exact le_trans hua (Nat.cast_le.mpr hab)
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0:ℂ) (a:ℝ) ∪ Metric.closedBall (0:ℂ) (b:ℝ)) := by
          intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (hf := hfU) hua hub
        simp only [zeroIntegrand, heq]
      rw [hcongr]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro u hu
        rw [Set.Finite.mem_toFinset] at hu ⊢
        rw [Function.mem_support] at hu ⊢
        have hua : u ∈ Metric.closedBall (0:ℂ) (a:ℝ) := by
          by_contra hc
          exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
        have hub : u ∈ Metric.closedBall (0:ℂ) (b:ℝ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hua ⊢
          exact le_trans hua (Nat.cast_le.mpr hab)
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0:ℂ) (a:ℝ) ∪ Metric.closedBall (0:ℂ) (b:ℝ)) := by
          intro w _; exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt w
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (hf := hfU) hua hub
        rw [← heq]; exact hu
      · intro u hu _
        simp only [zeroIntegrand]
        exact bot_le
    rw [hZeq, MeasureTheory.lintegral_iSup' hmeasW hmonoW]
    apply iSup_le
    intro n
    have hSsub : ∀ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (n : ℝ)) u ≠ 0 := by
      intro u hu; rw [Set.Finite.mem_toFinset] at hu; exact hu
    have hlin : (∫⁻ p, W n p ∂ν)
        = ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            (∫⁻ p, zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
              ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ∂ν) := by
      rw [hWdef]
      exact MeasureTheory.lintegral_finsetSum _ (fun u _ => measurable_zeroIntegrand χ n u)
    have hstep : ∀ u : ℂ, (∫⁻ p, zeroIntegrand χ n u ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))
            ((2 : ℂ) + Complex.I * (p.1 : ℂ)) ∂ν)
        = ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
              - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν := by
      intro u
      simp only [zeroIntegrand]
      simp_rw [ENNReal.ofReal_mul (Int.cast_nonneg
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u))]
      rw [MeasureTheory.lintegral_const_mul]
      apply ENNReal.continuous_ofReal.measurable.comp
      exact continuous_norm.measurable.comp (Measurable.sub
        (Measurable.div measurable_const
          (by fun_prop : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)))
        (Measurable.div measurable_const
          (by fun_prop : Measurable (fun p : ℝ × ℝ => ((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u))))
    have hsum2 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ∫⁻ p, ENNReal.ofReal ‖1 / (((p.2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)
              - 1 / (((2 : ℂ) + Complex.I * (p.1 : ℂ)) - u)‖ ∂ν)
        ≤ ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn' (n:ℝ)) (hSsub u hu)
      have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
      exact mul_le_mul_of_nonneg_left (hker u hs.1 hs.2) bot_le
    have hsum3 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
          ENNReal.ofReal ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
          * ENNReal.ofReal ((13 / 5) * (∫ T in c..c + 1,
              ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
        = ENNReal.ofReal (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
            * ((13 / 5) * (∫ T in c..c + 1,
                ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                  + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun u hu => by
        have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
          Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn' (n:ℝ)) (hSsub u hu)
        have hs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
        have ha : 0 < (3 / 2 : ℝ) - u.re := by linarith [hs.2]
        have hb : 0 < 1 + u.re := by linarith [hs.1]
        have hq : 0 ≤ ∫ T in c..c + 1,
            ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
              + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)) := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro T _
          apply add_nonneg
          · apply div_nonneg ha.le; positivity
          · apply div_nonneg hb.le; positivity
        exact mul_nonneg (Int.cast_nonneg
          (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u)) (mul_nonneg (by norm_num) hq))]
      apply Finset.sum_congr rfl
      intro u hu
      rw [ENNReal.ofReal_mul (Int.cast_nonneg
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn' (n:ℝ)) u))]
    have hsum4 : (∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
            ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
            * ((13 / 5) * (∫ T in c..c + 1,
                ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                  + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
        ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
      have h := finsum_divisor_three_halves_integral χ hχ hχprim hc (n : ℝ)
      have hfs : Function.support (fun u : ℂ => ((((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ) *
          (∫ T in c..c + 1,
            ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
              + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))))
          ⊆ ((divisor_support_finite χ (n : ℝ)).toFinset : Set ℂ) := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        intro h0; exact hu (by rw [h0, Int.cast_zero, zero_mul])
      rw [finsum_eq_sum_of_support_subset _ hfs] at h
      calc ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset,
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ))
              * ((13 / 5) * (∫ T in c..c + 1,
                  ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                    + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2))))
          = ∑ u ∈ (divisor_support_finite χ (n : ℝ)).toFinset, (13 / 5) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (n : ℝ))) u : ℤ) : ℝ)
              * (∫ T in c..c + 1,
                  ((3 / 2 - u.re) / ((3 / 2 - u.re) ^ 2 + (T - u.im) ^ 2)
                    + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))) := by
            apply Finset.sum_congr rfl; intro u _; ring
        _ ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left h (by norm_num)
    rw [hlin, Finset.sum_congr rfl (fun u _ => hstep u)]
    exact le_trans (le_trans hsum2 (le_of_eq hsum3)) (ENNReal.ofReal_le_ofReal hsum4)
  have hfin : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν) < ⊤ := by
    have hb1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν) < ⊤ := by
      rw [hI2]; exact ENNReal.ofReal_lt_top
    have hb2 : (∫⁻ p, Zw p ∂ν) < ⊤ := lt_of_le_of_lt hI3 ENNReal.ofReal_lt_top
    calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ _ := hI1
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hb1, hb2⟩
  have hV : (∫ T : ℝ in c..c + 1, ∫ x : ℝ in 0..2,
        ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖)
      = (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal := by
    have hAE : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) ν :=
      hmeas_f.aestronglyMeasurable
    have hint : Integrable
        (fun p : ℝ × ℝ => ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖) ν :=
      ⟨hAE, (MeasureTheory.hasFiniteIntegral_iff_ofReal
        (by filter_upwards with p; exact norm_nonneg _)).mpr hfin⟩
    have h1 : (∫ p, ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        = (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal :=
      integral_eq_lintegral_of_nonneg_ae (by filter_upwards with p; exact norm_nonneg _) hAE
    have h2 : (∫ p, ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        = ∫ T in c..c + 1, ∫ x in 0..2, ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖ := by
      simp only [intervalIntegral.integral_of_le (by linarith : c ≤ c + 1),
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2)]
      rw [← hρ, ← hσ, hν]
      exact MeasureTheory.integral_prod _ hint
    rw [← h2, h1]
  rw [hV]
  have htot : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal
      ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
    have h1 : (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
        ≤ ENNReal.ofReal (2 * ∫ T in c..c + 1,
              ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
          + ENNReal.ofReal ((13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2)) := by
      calc _ ≤ (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν)
              + ∫⁻ p, Zw p ∂ν := hI1
        _ = _ := by rw [hI2]
        _ ≤ _ := add_le_add le_rfl hI3
    have h2 := ENNReal.toReal_mono (by
      rw [ne_eq, ENNReal.add_eq_top]
      push_neg
      exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) h1
    have h2nn : (0:ℝ) ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
      apply mul_nonneg (by norm_num)
      exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
    have h3nn : (0:ℝ) ≤ (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
      apply mul_nonneg (by norm_num)
      linarith [Commons.NumberTheory.DirichletCharacter.logN_nonneg (N := N),
        Real.log_nonneg (show (1:ℝ) ≤ c + 3 by linarith)]
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal h2nn,
      ENNReal.toReal_ofReal h3nn] at h2
  calc (∫⁻ p, ENNReal.ofReal ‖logDeriv Λ ((p.2 : ℂ) + Complex.I * (p.1 : ℂ))‖ ∂ν).toReal
      ≤ 2 * (∫ T in c..c + 1, ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := htot
    _ ≤ (Real.log (c + 3) + 6) + (13 / 5) * (Real.log (N : ℝ) + Real.log (c + 3) + 11 / 2) := by
        linarith [hIV]
    _ ≤ 20 + 4 * (Real.log (N : ℝ) + Real.log (2 + c + 3)) := by
        have h := linnik_avg_arith (N := N) hc
        linarith [h]


end Commons.NumberTheory.DirichletCharacter


/-! ### Partial-fraction identity (Davenport ch.12 (17), completed form) — reduction skeleton

The identity asserts: for some constant `B`, the *paired* partial sums over the zeros in
`closedBall 0 R`,

    pfSum Λ R s := ∑ᶠ_u divisor(Λ, closedBall 0 R) u · (1/(s-u) + 1/u)

converge as `R → ∞` to `Λ'(s)/Λ(s) − B` whenever `Λ(s) ≠ 0`.  Convergence of these
paired sums is `partialFraction_conv`/`partialFraction_tail` (Commons).  The remaining
content is the *identification* of the limit; the standard route is:

  * pick a base point `s₀ = 2` (Λ(2) ≠ 0);
  * from the circle-residue pair identity (`logDeriv_circle_residue_pair`) at any radius
    `R` whose circle is zero-free, and the vanishing of the circle term along good radii
    (`partialFraction_contour`-type input; needs the circle log-derivative bounds
    `logDeriv_estimate` + good-radius gap), obtain the *pair limit*
    `pfSum R s − pfSum R s₀ ⟶ Λ'(s)/Λ(s) − Λ'(s₀)/Λ(s₀)`;
  * conclude by the pure limit algebra below (`pf_identity_of_pair_limit`), which
    assembles the identity with `B = Λ'(2)/Λ(2) − lim_R pfSum R 2`
    (`logDeriv_pf_identity_of_pair`).
-/

/-- The partial-fraction partial sum over the divisor inside `closedBall 0 R`,
with the `1/u` pairing. -/
noncomputable abbrev pfSum (f : ℂ → ℂ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
    (1 / (s - u) + 1 / u)

/-- Limit algebra: convergence at one base point `s₀` plus the pair-difference limit for
every `s` yield the partial-fraction identity with `B = Λ'(s₀)/Λ(s₀) − lim_R pfSum s₀`. -/
theorem pf_identity_of_pair_limit {f : ℂ → ℂ} (s₀ : ℂ) (hf₀ : f s₀ ≠ 0)
    (hconv₀ : ∃ L₀ : ℂ, Tendsto (fun R : ℝ => pfSum f R s₀) atTop (𝓝 L₀))
    (hpair : ∀ s : ℂ, f s ≠ 0 →
      Tendsto (fun R : ℝ => pfSum f R s - pfSum f R s₀) atTop
        (𝓝 (deriv f s / f s - deriv f s₀ / f s₀))) :
    ∃ B : ℂ, ∀ s : ℂ, f s ≠ 0 →
      Tendsto (fun R : ℝ => pfSum f R s) atTop (𝓝 (deriv f s / f s - B)) := by
  classical
  rcases hconv₀ with ⟨L₀, hL₀⟩
  refine ⟨deriv f s₀ / f s₀ - L₀, ?_⟩
  intro s hs
  have hpair_s := hpair s hs
  have hadd : Tendsto (fun R : ℝ => (pfSum f R s - pfSum f R s₀) + pfSum f R s₀) atTop
      (𝓝 ((deriv f s / f s - deriv f s₀ / f s₀) + L₀)) := hpair_s.add hL₀
  have htarget : Tendsto (fun R : ℝ => pfSum f R s) atTop
      (𝓝 (deriv f s / f s - (deriv f s₀ / f s₀ - L₀))) := by
    convert hadd using 1
    · ext R
      ring
    · ring
  simpa [sub_eq_add_neg, add_assoc] using htarget

/-- The completed Dirichlet L-function partial-fraction identity, reduced to the single
analytic hypothesis that the *difference* of the paired partial sums at `s` and at the
base point `s₀ = 2` converges to the difference of the log-derivatives. -/
theorem logDeriv_pf_identity_of_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (hpair : ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 →
      Tendsto (fun R : ℝ =>
        pfSum (fun z : ℂ => DirichletCharacter.completedLFunction χ z) R s -
          pfSum (fun z : ℂ => DirichletCharacter.completedLFunction χ z) R (2 : ℂ)) atTop
        (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s /
              DirichletCharacter.completedLFunction χ s -
            deriv (DirichletCharacter.completedLFunction χ) (2 : ℂ) /
              DirichletCharacter.completedLFunction χ (2 : ℂ)))) :
    ∃ B : ℂ, ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 →
      Tendsto (fun R : ℝ =>
        pfSum (fun z : ℂ => DirichletCharacter.completedLFunction χ z) R s) atTop
        (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s - B)) := by
  classical
  let Λ : ℂ → ℂ := fun z => DirichletCharacter.completedLFunction χ z
  have hΛ2 : Λ (2 : ℂ) ≠ 0 := by
    simpa [Λ] using
      Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_re_two χ hχ hχprim (0 : ℝ)
  have hconv₀ : ∃ L₀ : ℂ, Tendsto (fun R : ℝ => pfSum Λ R (2 : ℂ)) atTop (𝓝 L₀) := by
    simpa [pfSum, Λ] using (Commons.NumberTheory.Linnik.partialFraction_conv χ hχ hχprim (2 : ℂ))
  have hpair' : ∀ s : ℂ, Λ s ≠ 0 →
      Tendsto (fun R : ℝ => pfSum Λ R s - pfSum Λ R (2 : ℂ)) atTop
        (𝓝 (deriv Λ s / Λ s - deriv Λ (2 : ℂ) / Λ (2 : ℂ))) := by
    intro s hs
    simpa [pfSum, Λ] using hpair s hs
  rcases pf_identity_of_pair_limit (f := Λ) (s₀ := (2 : ℂ)) hΛ2 hconv₀ hpair' with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  simpa [Λ] using hB s hs
/-! ### Rectangle zero count for the completed Dirichlet L-function

The argument-principle rectangle bound (`Commons.Analysis.Complex.rectZeroCount_boundary_le`),
instantiated for `Λ = completedLFunction χ` on the box `[−1,2] × [α,β]`: the number of zeros
(with multiplicity, `0 < Re < 1`) strictly inside the box is at most `(2π)⁻¹` times the sum
of the four side integrals of `‖logDeriv Λ‖` (horizontal at `Im = α, β`, vertical at
`Re = 2, −1`).  The vertical sides are automatically zero-free (`zerosInStrip`); the
horizontal sides are required to be zero-free heights (hypotheses `hzα`, `hzβ`), exactly the
output of a "good height" lemma. -/
theorem rectCount_box {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β)
    (hzα : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ α)
    (hzβ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ β) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (β + 4))) u : ℤ) : ℝ) *
        (if (-1 < u.re ∧ u.re < 2 ∧ α < u.im ∧ u.im < β) then 1 else 0)) ≤
      (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in (-1)..2,
            ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + Complex.I * (α : ℂ))‖) +
         (∫ x : ℝ in (-1)..2,
            ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + Complex.I * (β : ℂ))‖) +
         (∫ y : ℝ in α..β,
            ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + Complex.I * (y : ℂ))‖) +
         (∫ y : ℝ in α..β,
            ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((-1 : ℂ) + Complex.I * (y : ℂ))‖)) := by
  classical
  let f : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let z : ℂ := (-1 : ℂ) + Complex.I * (α : ℂ)
  let w : ℂ := (2 : ℂ) + Complex.I * (β : ℂ)
  have hfdiff : Differentiable ℂ f := by simpa [f] using (differentiable_completedLFunction (χ := χ) hχ)
  have hRpos : 0 < β + 4 := by linarith [hα0, hαβ]
  have hzre : z.re < w.re := by
    dsimp [z, w]
    norm_num
  have hzim : z.im < w.im := by
    dsimp [z, w]
    simpa using hαβ
  have hf0 : f 0 ≠ 0 := by
    simpa [f] using (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
  have hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ < β + 4 := by
    intro s hs1 hs2 hs3 hs4
    have hlow : (-1 : ℝ) ≤ s.re := by simpa [z] using hs1
    have hhigh : s.re ≤ (2 : ℝ) := by simpa [w] using hs2
    have hsre : |s.re| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hl0 : (0 : ℝ) ≤ s.im := by
      have hl : (α : ℝ) ≤ s.im := by simpa [z] using hs3
      linarith
    have hhi0 : s.im ≤ β := by simpa [w] using hs4
    have hsim0 : |s.im| ≤ β := by
      rw [abs_of_nonneg hl0]
      exact hhi0
    have hsre' : |s.re| ≤ |(2 : ℝ)| := by simpa using hsre
    have hre2 : s.re ^ 2 ≤ (2 : ℝ) ^ 2 := (sq_le_sq (a := s.re) (b := (2 : ℝ))).2 hsre'
    have hβ0 : 0 ≤ β := by linarith
    have hsim0' : |s.im| ≤ |β| := by simpa [abs_of_nonneg hβ0] using hsim0
    have him2 : s.im ^ 2 ≤ β ^ 2 := (sq_le_sq (a := s.im) (b := β)).2 hsim0'
    have hns0 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      calc
        ‖s‖ ^ 2 = Complex.normSq s := by rw [← Complex.normSq_eq_norm_sq]
        _ = s.re ^ 2 + s.im ^ 2 := by rw [Complex.normSq_apply]; ring
    have hns : ‖s‖ ^ 2 ≤ 4 + β ^ 2 := by nlinarith
    have hlt : 4 + β ^ 2 < (β + 4) ^ 2 := by nlinarith [sq_nonneg β]
    have hsq : ‖s‖ ^ 2 < (β + 4) ^ 2 := by linarith
    have hβ4 : 0 ≤ β + 4 := by linarith
    have habs : |‖s‖| < |β + 4| := (sq_lt_sq.mp hsq)
    rwa [abs_of_nonneg (norm_nonneg s), abs_of_nonneg hβ4] at habs
  have hfne : ∀ s : ℂ,
      (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0 := by
    intro s hsbd hs1 hs2 hs3 hs4 hz
    have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim s (by simpa [f] using hz)
    rcases hsbd with hsr | hsr | hsi | hsi
    · have hsr' : s.re = -1 := by simpa [z] using hsr
      have hgt : (0 : ℝ) < s.re := hstrip.1
      rw [hsr'] at hgt
      norm_num at hgt
    · have hsr' : s.re = 2 := by simpa [w] using hsr
      have hlt1 : s.re < 1 := hstrip.2
      rw [hsr'] at hlt1
      norm_num at hlt1
    · have hsi' : s.im = α := by simpa [z] using hsi
      exact hzα s (by simpa [f] using hz) (by rw [hsi'])
    · have hsi' : s.im = β := by simpa [w] using hsi
      exact hzβ s (by simpa [f] using hz) (by rw [hsi'])
  have hbound := Commons.Analysis.Complex.rectZeroCount_boundary_le (f := f) (z := z) (w := w)
    (R := β + 4) hfdiff hRpos hzre hzim hf0 hrect hfne
  simpa [f, z, w, mul_comm] using hbound


/-! ### First analytic brick of the box estimate: the smooth (Re = 2) part

The box integral of `‖logDeriv Λ‖` over `[0,2] × [c,c+1]` splits, via a partial-fraction
comparison with the same-height point `2 + iT`, into a *smooth part* (the `Re = 2` line,
bounded pointwise by `completedLogDeriv_two_small`) and a *pole part* (over the zeros of
`Λ` in the strip, to be controlled by clearance/window counts).  This lemma is the smooth
part: since the integrand is constant in `x`, the box integral of the `Re=2` values is
`2 ×` the unit-window vertical integral `twoUnit`, hence at most `log(2+c+3) + 10`. -/
lemma smoothPart_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) :
    (∫ T : ℝ in c..c + 1,
        ∫ x : ℝ in 0..2,
          ‖logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + Complex.I * (T : ℂ))‖) ≤
      Real.log (2 + c + 3) + 10 := by
  have hint : ∀ T : ℝ, (∫ x : ℝ in 0..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + Complex.I * (T : ℂ))‖) =
      (2 : ℝ) * ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
    intro T
    rw [intervalIntegral.integral_const]
    simp
  have h2b := Commons.NumberTheory.DirichletCharacter.twoUnit χ hχ hχprim hc
  calc
    (∫ T : ℝ in c..c + 1,
        ∫ x : ℝ in 0..2,
          ‖logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + Complex.I * (T : ℂ))‖)
        = ∫ T : ℝ in c..c + 1,
            (2 : ℝ) * ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
            apply intervalIntegral.integral_congr
            intro T hT
            exact hint T
    _ = (2 : ℝ) * (∫ T : ℝ in c..c + 1,
            ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + Complex.I * (T : ℂ))‖) := by
            rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 : ℝ) * ((1 / 2 : ℝ) * Real.log (2 + c + 3) + 5) := by
            exact mul_le_mul_of_nonneg_left h2b (by norm_num)
    _ = Real.log (2 + c + 3) + 10 := by ring
/-! ### Integral–finsum commutation layer

The horizontal-line assembly (`horizontalGoodLine_bound`) needs to integrate the pole sum
`∑ᶠ_u m_u · w_u(x)` over `x ∈ [0,2]` term by term.  This layer provides the interchange,
first for finite Finset sums with scalar coefficients, then for `∑ᶠ` over a finitely
supported coefficient family.  The second version is stated for an arbitrary coefficient
`m : ℂ → ℝ` with finite support and per-term integrability on the support — exactly the
situation of a divisor sum (divisor support in a closed ball is finite, and at a good
height the pole weights are continuous in `x`).
-/

/-- A scalar-multiple finite sum commutes with the interval integral. -/
lemma integral_finset_scalar_sum {a b : ℝ} (S : Finset ℂ) (m : ℂ → ℝ) (w : ℂ → ℝ → ℝ)
    (hw : ∀ u ∈ S, IntervalIntegrable (w u) MeasureTheory.volume a b) :
    (∫ x : ℝ in a..b, ∑ u ∈ S, m u * w u x) =
      ∑ u ∈ S, m u * (∫ x : ℝ in a..b, w u x) := by
  have hf : ∀ u : ℂ, u ∈ S → IntervalIntegrable (fun x : ℝ => m u * w u x)
      MeasureTheory.volume a b := by
    intro u hu
    exact (hw u hu).const_mul (m u)
  have h1 := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)
    (f := fun u : ℂ => fun x : ℝ => m u * w u x) (s := S) hf
  calc
    (∫ x : ℝ in a..b, ∑ u ∈ S, m u * w u x)
        = ∑ u ∈ S, (∫ x : ℝ in a..b, m u * w u x) := h1
    _ = ∑ u ∈ S, m u * (∫ x : ℝ in a..b, w u x) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [intervalIntegral.integral_const_mul]

/-- Interval integral commutes with `∑ᶠ` over a finitely supported coefficient family:
`∫ x, ∑ᶠ_u m u * w u x = ∑ᶠ_u m u * ∫ x, w u x`, provided each `w u` is interval-integrable
wherever `m u ≠ 0`. -/
lemma finsum_integral_interchange {a b : ℝ} {m : ℂ → ℝ} {w : ℂ → ℝ → ℝ}
    (hm : (Function.support m).Finite)
    (hw : ∀ u : ℂ, m u ≠ 0 → IntervalIntegrable (w u) MeasureTheory.volume a b) :
    (∫ x : ℝ in a..b, ∑ᶠ u : ℂ, m u * w u x) =
      ∑ᶠ u : ℂ, m u * (∫ x : ℝ in a..b, w u x) := by
  classical
  let S : Finset ℂ := hm.toFinset
  have hmemS : ∀ u : ℂ, m u ≠ 0 → u ∈ S := by
    intro u hu
    exact (hm.mem_toFinset).2 hu
  have hfun : (fun x : ℝ => ∑ᶠ u : ℂ, m u * w u x) =
      fun x : ℝ => ∑ u ∈ S, m u * w u x := by
    funext x
    apply finsum_eq_sum_of_support_subset (fun u : ℂ => m u * w u x) (s := S)
    intro u hu
    have hmz : m u ≠ 0 := by
      intro hm0
      have hz : m u * w u x = 0 := by simp [hm0]
      exact (Function.mem_support.mp hu) hz
    exact hmemS u hmz
  have hwS : ∀ u : ℂ, u ∈ S → IntervalIntegrable (w u) MeasureTheory.volume a b := by
    intro u hu
    have hu' : m u ≠ 0 := by
      have hs : u ∈ (Function.support m) := (hm.mem_toFinset).1 (by simpa [S] using hu)
      exact hs
    exact hw u hu'
  have h1 := integral_finset_scalar_sum (S := S) (m := m) (w := w) hwS
  have hfun2 : (∑ᶠ u : ℂ, m u * (∫ x : ℝ in a..b, w u x)) =
      ∑ u ∈ S, m u * (∫ x : ℝ in a..b, w u x) := by
    apply finsum_eq_sum_of_support_subset (fun u : ℂ => m u * (∫ x : ℝ in a..b, w u x)) (s := S)
    intro u hu
    have hmz : m u ≠ 0 := by
      intro hm0
      have hz : m u * (∫ x : ℝ in a..b, w u x) = 0 := by simp [hm0]
      exact (Function.mem_support.mp hu) hz
    exact hmemS u hmz
  calc
    (∫ x : ℝ in a..b, ∑ᶠ u : ℂ, m u * w u x)
        = (∫ x : ℝ in a..b, ∑ u ∈ S, m u * w u x) := by
            exact congrArg (fun F : ℝ → ℝ => ∫ x : ℝ in a..b, F x) hfun
    _ = ∑ u ∈ S, m u * (∫ x : ℝ in a..b, w u x) := h1
    _ = ∑ᶠ u : ℂ, m u * (∫ x : ℝ in a..b, w u x) := hfun2.symm


/-! ### Horizontal-line pole assembly (step A): pointwise and weight-integrability facts

`horizontalGoodLine_bound` is assembled from three certified pieces:
  (A) the pointwise pole bound at each `x ∈ [0,2]` (an instance of `pfPole_pointwise`),
  (B) termwise integration of the pole sum (`finsum_integral_interchange` +
      `poleXIntegral_le`, with integrability of each pole weight supplied below),
  (C) monotone integration against the (Re=2) smooth line, carrying the circle remainder
      through as its `x`-integral.
Step (A) and the weight-integrability fact are certified here; (B)+(C) assemble them.
-/

/-- At each `x ∈ [0,2]` on a zero-free height `T`, the horizontal log-derivative differs
from its `Re = 2` value by the pole sum plus the circle remainder (pointwise instance of
`pfPole_pointwise`). -/
lemma pfPole_pointwise_box {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T R : ℝ)
    (hR : 0 < R)
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hRbig : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖(x : ℂ) + Complex.I * (T : ℂ)‖ < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 2,
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (T : ℂ)) -
        logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
          ((2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖))) +
        ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
          circleIntegral (fun w : ℂ =>
            (deriv (DirichletCharacter.completedLFunction χ) w /
              DirichletCharacter.completedLFunction χ w) *
              (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w) -
               1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - w))) 0 R)‖ := by
  intro x hx
  exact Commons.NumberTheory.DirichletCharacter.pfPole_pointwise χ hχ hχprim T x R hR hgood
    hx.1 hx.2 (hRbig x hx) (hRbig 2 (by constructor <;> norm_num)) hcirc

/-- At a height `T` differing from `u.im`, the pole weight `x ↦ (2−x)/(‖x+iT−u‖·‖2+iT−u‖)`
is continuous (denominators bounded below by `|T − u.im| > 0`), hence interval-integrable
on `[0,2]`. -/
lemma poleWeight_integrable {T : ℝ} {u : ℂ} (hT : T ≠ u.im) :
    IntervalIntegrable (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖))
      MeasureTheory.volume 0 2 := by
  have hn1 : Continuous (fun x : ℝ => ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖) := by fun_prop
  have hn2 : Continuous (fun x : ℝ => ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) := continuous_const
  have hnum : Continuous (fun x : ℝ => (2 - x)) := by fun_prop
  have hden : Continuous (fun x : ℝ =>
      ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) := hn1.mul hn2
  have hpos : ∀ x : ℝ, (0 : ℝ) <
      ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
    intro x
    have hgt : 0 < |T - u.im| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hT)
    have hb1 : |T - u.im| ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
      have h := Complex.abs_im_le_norm (((x : ℂ) + Complex.I * (T : ℂ)) - u)
      have him : ((((x : ℂ) + Complex.I * (T : ℂ)) - u).im) = T - u.im := by simp
      simpa [him] using h
    have hb2 : |T - u.im| ≤ ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
      have h := Complex.abs_im_le_norm (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
      have him : ((((2 : ℂ) + Complex.I * (T : ℂ)) - u).im) = T - u.im := by simp
      simpa [him] using h
    have h1 : 0 < ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ := lt_of_lt_of_le hgt hb1
    have h2 : 0 < ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ := lt_of_lt_of_le hgt hb2
    exact mul_pos h1 h2
  have hden_nz : ∀ x : ℝ,
      ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ ≠ 0 := by
    intro x
    exact ne_of_gt (hpos x)
  have hcont : Continuous (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) := by
    exact hnum.div hden hden_nz
  exact hcont.intervalIntegrable 0 2


/-- Termwise integration of the pole sum: the `x`-integral of the divisor-weighted pole
sum over `[0,2]` is at most the divisor-weighted sum of the per-zero bounds
`2 / |T − u.im|`.  Uses `finsum_integral_interchange` (finite divisor support in the ball)
and `poleXIntegral_le` (each zero lies in `0 < Re < 1`, and its height differs from `T`). -/
lemma poleSum_horizontal_integral_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T R : ℝ)
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T) :
    (∫ x : ℝ in 0..2,
        (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
            ((2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ *
              ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)))) ≤
      ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R) u
  let m : ℂ → ℝ := fun u => ((d u : ℤ) : ℝ)
  let w : ℂ → ℝ → ℝ := fun u x =>
    (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    simpa [Λ] using (differentiable_completedLFunction (χ := χ) hχ).analyticAt z
  have hdFin : (Function.support d).Finite := by
    dsimp [d]
    exact Commons.Analysis.Complex.divisor_support_finite_closedBall (f := Λ) (a := (0 : ℂ)) (ρ := R) hAn
  have hmFin : (Function.support m).Finite := by
    refine hdFin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hd0
    apply hu
    simpa [m] using (congrArg (fun z : ℤ => (z : ℝ)) hd0)
  have hdz : ∀ u : ℂ, d u ≠ 0 → Λ u = 0 := by
    intro u hdu
    dsimp [d] at hdu
    exact Commons.Analysis.Complex.zero_of_divisor_ne_zero (f := Λ) (a := (0 : ℂ)) (ρ := R) hAn hdu
  have hwInt : ∀ u : ℂ, m u ≠ 0 → IntervalIntegrable (w u) MeasureTheory.volume 0 2 := by
    intro u hu
    have hd0 : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [m, hd0]
    have hΛu : Λ u = 0 := hdz u hd0
    have hTne : T ≠ u.im := by
      intro hT
      have h := hgood u (by simpa [Λ] using hΛu)
      exact h hT.symm
    have hu1 : u.re < 1 := by
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u (by simpa [Λ] using hΛu)
      exact hstrip.2
    simpa [w] using poleWeight_integrable hTne
  have hinter := finsum_integral_interchange (a := (0 : ℝ)) (b := (2 : ℝ)) (m := m) (w := w) hmFin hwInt
  have hterm : ∀ u : ℂ, m u ≠ 0 →
      m u * (∫ x : ℝ in 0..2, w u x) ≤ m u * (2 / |T - u.im|) := by
    intro u hu
    have hm0 : 0 ≤ m u := by
      have hnn : (0 : ℝ) ≤ (((d u : ℤ) : ℝ)) := by
        dsimp [d]
        exact Commons.Analysis.Complex.divisor_nonneg_on_closedBall (f := Λ) (a := (0 : ℂ)) (ρ := R) hAn u
      simpa [m] using hnn
    have hd0 : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [m, hd0]
    have hΛu : Λ u = 0 := hdz u hd0
    have hTne : T ≠ u.im := by
      intro hT
      have h := hgood u (by simpa [Λ] using hΛu)
      exact h hT.symm
    have hu1 : u.re < 1 := by
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u (by simpa [Λ] using hΛu)
      exact hstrip.2
    have hwle : (∫ x : ℝ in 0..2, w u x) ≤ 2 / |T - u.im| := by
      simpa [w] using (Commons.NumberTheory.DirichletCharacter.poleXIntegral_le (T := T) (u := u) hu1 hTne)
    exact mul_le_mul_of_nonneg_left hwle hm0
  -- assemble over the finite support
  let S : Finset ℂ := hmFin.toFinset
  have hS_mem : ∀ u : ℂ, m u ≠ 0 → u ∈ S := by
    intro u hu
    exact (hmFin.mem_toFinset).2 hu
  have hRHS : (∑ᶠ u : ℂ, m u * (2 / |T - u.im|)) = ∑ u ∈ S, m u * (2 / |T - u.im|) := by
    apply finsum_eq_sum_of_support_subset (fun u : ℂ => m u * (2 / |T - u.im|)) (s := S)
    intro u hu
    have hmz : m u ≠ 0 := by
      intro hm0
      have hz : m u * (2 / |T - u.im|) = 0 := by simp [hm0]
      exact (Function.mem_support.mp hu) hz
    exact hS_mem u hmz
  have hLHS : (∫ x : ℝ in 0..2, ∑ᶠ u : ℂ, m u * w u x) =
      ∑ u ∈ S, m u * (∫ x : ℝ in 0..2, w u x) := by
    -- rewrite via finsum_integral_interchange then convert RHS to S-sum
    have hconv : (∑ᶠ u : ℂ, m u * (∫ x : ℝ in 0..2, w u x)) =
        ∑ u ∈ S, m u * (∫ x : ℝ in 0..2, w u x) := by
      apply finsum_eq_sum_of_support_subset (fun u : ℂ => m u * (∫ x : ℝ in 0..2, w u x)) (s := S)
      intro u hu
      have hmz : m u ≠ 0 := by
        intro hm0
        have hz : m u * (∫ x : ℝ in 0..2, w u x) = 0 := by simp [hm0]
        exact (Function.mem_support.mp hu) hz
      exact hS_mem u hmz
    rw [hinter, hconv]
  have hsum : (∑ u ∈ S, m u * (∫ x : ℝ in 0..2, w u x)) ≤
      ∑ u ∈ S, m u * (2 / |T - u.im|) := by
    apply Finset.sum_le_sum
    intro u huS
    have hu' : m u ≠ 0 := by
      have hs : u ∈ (Function.support m) := (hmFin.mem_toFinset).1 (by simpa [S] using huS)
      exact hs
    exact hterm u hu'
  calc
    (∫ x : ℝ in 0..2, (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
          ((2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ *
            ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖))))
        = (∫ x : ℝ in 0..2, ∑ᶠ u : ℂ, m u * w u x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [m, w, d, Λ]
    _ = ∑ u ∈ S, m u * (∫ x : ℝ in 0..2, w u x) := hLHS
    _ ≤ ∑ u ∈ S, m u * (2 / |T - u.im|) := hsum
    _ = ∑ᶠ u : ℂ, m u * (2 / |T - u.im|) := by
        exact hRHS.symm
    _ = ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|) := by
        simp [m, d, Λ]


/-- The pole weight is continuous in `x` whenever its height differs from `u.im`. -/
lemma poleWeight_continuous {T : ℝ} {u : ℂ} (hT : T ≠ u.im) :
    Continuous (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) := by
  have hn1 : Continuous (fun x : ℝ => ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖) := by fun_prop
  have hn2 : Continuous (fun x : ℝ => ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) := continuous_const
  have hnum : Continuous (fun x : ℝ => (2 - x)) := by fun_prop
  have hden : Continuous (fun x : ℝ =>
      ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) := hn1.mul hn2
  have hgt : 0 < |T - u.im| := abs_pos.mpr (sub_ne_zero.mpr hT)
  have hden_nz : ∀ x : ℝ,
      ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ ≠ 0 := by
    intro x
    have hb1 : |T - u.im| ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
      have h := Complex.abs_im_le_norm (((x : ℂ) + Complex.I * (T : ℂ)) - u)
      have him : ((((x : ℂ) + Complex.I * (T : ℂ)) - u).im) = T - u.im := by simp
      simpa [him] using h
    have hb2 : |T - u.im| ≤ ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
      have h := Complex.abs_im_le_norm (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
      have him : ((((2 : ℂ) + Complex.I * (T : ℂ)) - u).im) = T - u.im := by simp
      simpa [him] using h
    have h1 : 0 < ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ := lt_of_lt_of_le hgt hb1
    have h2 : 0 < ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖ := lt_of_lt_of_le hgt hb2
    exact ne_of_gt (mul_pos h1 h2)
  exact hnum.div hden hden_nz

/-- The horizontal integral over `x ∈ [0,2]` at a zero-free height `T` is at most the
`Re = 2` smooth line plus the divisor-weighted per-zero pole bounds plus the `x`-integral
of the circle remainder (assembly of `pfPole_pointwise_box`, `poleSum_horizontal_integral_le`
and the parametric circle-integral integrability of the remainder). -/
theorem horizontalGoodLine_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T R : ℝ)
    (hR : 0 < R)
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hRbig : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖(x : ℂ) + Complex.I * (T : ℂ)‖ < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    (∫ x : ℝ in 0..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (T : ℂ))‖) ≤
      (∫ x : ℝ in 0..2,
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖) +
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|)) +
      (∫ x : ℝ in 0..2,
          ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
            circleIntegral (fun w : ℂ =>
              (deriv (DirichletCharacter.completedLFunction χ) w /
                DirichletCharacter.completedLFunction χ w) *
                (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w) -
                 1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - w))) 0 R)‖) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let c : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R) u
  let m : ℂ → ℝ := fun u => ((d u : ℤ) : ℝ)
  let w : ℂ → ℝ → ℝ := fun u x =>
    (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)
  let g : ℝ → ℝ := fun x => ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖
  let h : ℝ → ℝ := fun _ : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖
  let P : ℝ → ℝ := fun x => ∑ᶠ u : ℂ, m u * w u x
  let J : ℝ → ℝ := fun x =>
    ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
      circleIntegral (fun w0 : ℂ =>
        (deriv Λ w0 / Λ w0) *
          (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w0) - 1 / (c - w0))) 0 R)‖
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    simpa [Λ] using (differentiable_completedLFunction (χ := χ) hχ).analyticAt z
  have hdFin : (Function.support d).Finite := by
    dsimp [d]
    exact Commons.Analysis.Complex.divisor_support_finite_closedBall (f := Λ) (a := (0 : ℂ)) (ρ := R) hAn
  have hmFin : (Function.support m).Finite := by
    refine hdFin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hd0
    apply hu
    simpa [m] using (congrArg (fun z : ℤ => (z : ℝ)) hd0)
  have hdz : ∀ u : ℂ, d u ≠ 0 → Λ u = 0 := by
    intro u hdu
    dsimp [d] at hdu
    exact Commons.Analysis.Complex.zero_of_divisor_ne_zero (f := Λ) (a := (0 : ℂ)) (ρ := R) hAn hdu
  have hTne_of : ∀ u : ℂ, m u ≠ 0 → T ≠ u.im := by
    intro u hu
    have hd0 : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [m, hd0]
    have hΛu : Λ u = 0 := hdz u hd0
    intro hT
    have hh := hgood u (by simpa [Λ] using hΛu)
    exact hh hT.symm
  have hwInt : ∀ u : ℂ, m u ≠ 0 → IntervalIntegrable (w u) MeasureTheory.volume 0 2 := by
    intro u hu
    exact poleWeight_integrable (hTne_of u hu)
  -- integrability
  have hg : IntervalIntegrable g MeasureTheory.volume 0 2 := by
    have hcont : Continuous g := by
      dsimp [g]
      exact Commons.NumberTheory.DirichletCharacter.cont_horizontal_at χ hχ hgood
    exact hcont.intervalIntegrable 0 2
  have hh_int : IntervalIntegrable h MeasureTheory.volume 0 2 := by
    dsimp [h]
    exact (by fun_prop : Continuous (fun _ : ℝ => ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)).intervalIntegrable 0 2
  have hJ : IntervalIntegrable J MeasureTheory.volume 0 2 := by
    dsimp [J]
    simpa [Λ] using (Commons.NumberTheory.DirichletCharacter.circleIntegralX_integrable χ hχ hχprim T R hR hRbig hcirc)
  have hP : IntervalIntegrable P MeasureTheory.volume 0 2 := by
    let S : Finset ℂ := hmFin.toFinset
    have hmemS : ∀ u : ℂ, m u ≠ 0 → u ∈ S := by
      intro u hu
      exact (hmFin.mem_toFinset).2 hu
    have hfun : (fun x : ℝ => P x) = fun x : ℝ => ∑ u ∈ S, m u * w u x := by
      funext x
      dsimp [P]
      apply finsum_eq_sum_of_support_subset (fun u : ℂ => m u * w u x) (s := S)
      intro u hu
      have hmz : m u ≠ 0 := by
        intro hm0
        have hz : m u * w u x = 0 := by simp [hm0]
        exact (Function.mem_support.mp hu) hz
      exact hmemS u hmz
    have hwS_cont : ∀ u : ℂ, u ∈ S → Continuous (fun x : ℝ => m u * w u x) := by
      intro u huS
      have hu' : m u ≠ 0 := (hmFin.mem_toFinset).1 (by simpa [S] using huS)
      have hwc : Continuous (fun x : ℝ => w u x) := poleWeight_continuous (hTne_of u hu')
      exact hwc.const_mul (m u)
    have hcontS : Continuous (fun x : ℝ => ∑ u ∈ S, m u * w u x) := by
      apply continuous_finset_sum
      intro u huS
      exact hwS_cont u huS
    have hcontP : Continuous P := by
      have hPfun : P = (fun x : ℝ => ∑ u ∈ S, m u * w u x) := hfun
      rw [hPfun]
      exact hcontS
    exact hcontP.intervalIntegrable 0 2
  -- pointwise inequality g ≤ h + P + J on [0,2]
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 2, g x ≤ h x + P x + J x := by
    intro x hx
    have hpf := pfPole_pointwise_box χ hχ hχprim T R hR hgood hRbig hcirc x hx
    have htri : ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖ ≤
        ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ +
          ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ)) - logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
      -- |a| ≤ |b| + |a − b|
      have hsub : ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖ ≤
          ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ)) - logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ +
            ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
            simpa [add_comm] using (norm_add_le
              (logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ)) - logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ)))
              (logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))))
      linarith
    have htri' : ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖ ≤
        ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ +
          (∑ᶠ u : ℂ, m u * w u x) + J x := by
      dsimp [J]
      have hpf' : ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ)) - logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
          (∑ᶠ u : ℂ, m u * w u x) + ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
            circleIntegral (fun w0 : ℂ => (deriv Λ w0 / Λ w0) *
              (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w0) - 1 / (c - w0))) 0 R)‖ := by
            -- hpf is the same inequality in the statement form (with completedLFunction χ); convert
            simpa [Λ, c, m, w] using hpf
      calc
        ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ))‖
            ≤ ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ +
                ‖logDeriv Λ ((x : ℂ) + Complex.I * (T : ℂ)) - logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := htri
        _ ≤ ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ + ((∑ᶠ u : ℂ, m u * w u x) +
            ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
              circleIntegral (fun w0 : ℂ => (deriv Λ w0 / Λ w0) *
                (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w0) - 1 / (c - w0))) 0 R)‖) := by
              have hstep := add_le_add_right hpf' (‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖)
              simpa [add_comm, add_left_comm, add_assoc] using hstep
        _ = ‖logDeriv Λ ((2 : ℂ) + Complex.I * (T : ℂ))‖ + (∑ᶠ u : ℂ, m u * w u x) + J x := by
              dsimp [J]
              ring
    dsimp [g, h, P]
    simpa using htri'
  -- monotone integration
  have hle0 : (0 : ℝ) ≤ 2 := by norm_num
  have hsumInt2 : IntervalIntegrable (fun x : ℝ => h x + P x + J x) MeasureTheory.volume 0 2 := by
    have hpj : IntervalIntegrable (fun x : ℝ => h x + P x) MeasureTheory.volume 0 2 := hh_int.add hP
    exact hpj.add hJ
  have hmono := intervalIntegral.integral_mono_on hle0 hg hsumInt2 hpt
  have hsplit : (∫ x : ℝ in 0..2, h x + P x + J x) =
      (∫ x : ℝ in 0..2, h x) + (∫ x : ℝ in 0..2, P x) + (∫ x : ℝ in 0..2, J x) := by
    have h1 := intervalIntegral.integral_add hh_int (hP.add hJ)
    have h2 := intervalIntegral.integral_add hh_int hP
    have h3 := intervalIntegral.integral_add hP hJ
    -- (h + P) + J integrates as ∫(h+P) + ∫J; ∫(h+P) = ∫h + ∫P
    calc
      (∫ x in 0..2, h x + P x + J x) = (∫ x in 0..2, (h x + P x) + J x) := by
        apply intervalIntegral.integral_congr; intro x hx; ring
      _ = (∫ x in 0..2, h x + P x) + (∫ x in 0..2, J x) := intervalIntegral.integral_add (hh_int.add hP) hJ
      _ = ((∫ x in 0..2, h x) + (∫ x in 0..2, P x)) + (∫ x in 0..2, J x) := by
          rw [intervalIntegral.integral_add hh_int hP]
      _ = (∫ x in 0..2, h x) + (∫ x in 0..2, P x) + (∫ x in 0..2, J x) := by ring
  have hPSum := poleSum_horizontal_integral_le χ hχ hχprim T R hgood
  have hPSum' : (∫ x : ℝ in 0..2, P x) ≤ ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|) := by
    simpa [P, m, w] using hPSum
  -- ∫g ≤ ∫h + ∫P + ∫J
  have hmain : (∫ x : ℝ in 0..2, g x) ≤
      (∫ x : ℝ in 0..2, h x) + (∫ x : ℝ in 0..2, P x) + (∫ x : ℝ in 0..2, J x) := by
    calc
      (∫ x in 0..2, g x) ≤ ∫ x in 0..2, h x + P x + J x := hmono
      _ = (∫ x in 0..2, h x) + (∫ x in 0..2, P x) + (∫ x in 0..2, J x) := hsplit
  have hfinal : (∫ x in 0..2, g x) ≤
      (∫ x in 0..2, h x) + (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|)) +
        (∫ x in 0..2, J x) := by
    have hadd := add_le_add_right hPSum' ((∫ x : ℝ in 0..2, h x) + (∫ x : ℝ in 0..2, J x))
    -- hmain ≤ ∫h + ∫P + ∫J ; ∫P ≤ Σ: add ∫h + ∫J
    linarith
  -- rewrite to the statement's notation
  change (∫ x : ℝ in 0..2, g x) ≤
      (∫ x in 0..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))‖) +
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) * (2 / |T - u.im|)) +
      (∫ x in 0..2, J x)
  -- need: ∫h equals the smooth term, and J matches remainder
  · simpa [g, h, P, J, Λ, c, m, w] using hfinal


/-! ### Height-averaging layer: the T-average statement (next target)

The box bound of `logDeriv_rightHalf_avg` is the `T`-average of the horizontal integral
`F(T) = ∫_0^2 ‖logDeriv Λ(x+iT)‖ dx` over `T ∈ [c,c+1]` (`c ≥ 1/2`).  `horizontalGoodLine_bound`
bounds `F(T)` at each zero-free height by the smooth (`Re = 2`) line plus the pole sum
`Σ_u m_u · 2/|T − u.im|` (divisor over a ball containing the strip window) plus the `x`-integral
of the circle remainder.  The `T`-average of that bound is the next certified lemma:

```
theorem horizontalTAverage_bound {N} [NeZero N] (χ) (hχ) (hχprim) {c : ℝ} (hc : 1/2 ≤ c) :
    ∫_c^{c+1} ∫_0^2 ‖logDeriv Λ(x+iT)‖ ≤
      ∫_c^{c+1} ∫_0^2 ‖logDeriv Λ(2+iT)‖
        + ∫_c^{c+1} (pole sum bound at height T) dT
        + ∫_c^{c+1} (x-integral of the circle remainder) dT
```

**Handling of the pole-sum term** — the per-height pole sum does *not* integrate termwise over
the raw weight `2/|T−u.im|` (logarithmically divergent when `u.im ∈ [c,c+1]`); instead split by
zero position relative to the box `B := [0,2] × [c,c+1]`:

1. *Interior zeros* (`c < u.im < c+1`, `0 < u.re < 1`): the pole contributes, over the 2-D box,
   at most `perimeter(∂B) = 6` (polar-coordinate bound `∫_B dA/|z−u| ≤ ∮_∂B ds = 6`).  Their
   total is `6 ×` the unit-height zero count (with multiplicity) — the small-constant window
   count that the chain root must supply.
2. *Nearby zeros* (`u.im ∈ [c−1,c] ∪ [c+1,c+2]`): at vertical distance `d = |u.im − [c,c+1]| > 0`,
   `∫_c^{c+1} 2/|T − u.im| dT ≤ 2·ln(1+1/d)`, summable over the (finite) divisor support of a
   ball of radius `c+4` once the three-window count is available.
3. *Far zeros* (`u.im < c−1` or `> c+2`, still `|u| ≤ c+4`): the paired (two-point) decay of the
   partial-fraction kernel makes their total contribution `O(1)·(log N + log(c+3))`; this needs
   the global partial-fraction/tail input (logDeriv_pf_identity) or a shell-summed window count.

**Missing side conditions (flagged)**:
- (S1) `circleIntegralX_integrable` (parametric leaf; local placeholder in this file) — controls
  the `x`-integral of the circle remainder; its `T`-average additionally needs continuity/
  integrability in `(x,T)`, to be handled by the same parametric-integral machinery.
- (S2) per-zero `T`-average of `2/|T−u.im|` over a unit window (pure real analysis; closed form
  via `Real.log`), used in (2).
- (S3) per-zero 2-D pole area `∫∫_B 1/|z−u| ≤ perimeter(B) = 6` for `u` inside `B` (polar
  change of variables), used in (1).
- (S4) small-constant window zero counts (`c ≤ Im u ≤ c+1` and the neighbouring unit windows,
  with multiplicity) — the root content that the average/good-height chain must produce.
- (S5) far-zero control in (3): either `logDeriv_pf_identity`-type tail input or dyadic shell
  window counts.

With (S1)–(S5) in place, `horizontalTAverage_bound` is an assembly of: `horizontalGoodLine_bound`
+ `finsum_integral_interchange` (already certified, applied over `T ∈ [c,c+1]`) + (S2)–(S3)
per-zero bounds + (S4)/(S5) counts, followed by the box smooth-part bound (`smoothPart_le`,
already certified) and the real algebra against `20 + 4·(log N + log(2+c+3))`.
-/
/-! ### S2: per-zero T-average of the pole weight over a unit height window

For a zero at height `z` strictly below (`z < c`) or strictly above (`c + 1 < z`) the unit
window `[c, c+1]`, the weight `2/|T − z|` integrates to the closed form
`2·log((c+1−z)/(c−z))` (below) and `2·log((z−c)/(z−c−1))` (above).  These are the
per-zero coefficients of the height-averaged pole sum (item (S2) of the
`horizontalTAverage_bound` plan). -/

/-- The unscaled below-window integral: `∫_c^{c+1} (T−z)⁻¹ = log((c+1−z)/(c−z))`. -/
lemma int_inv_sub_below {c z : ℝ} (hz : z < c) :
    (∫ T : ℝ in c..c+1, (T - z)⁻¹) = Real.log ((c+1-z)/(c-z)) := by
  have h0 : 0 ∉ Set.uIcc (c - z) (c + 1 - z) := by
    intro hmem
    have hle : c - z ≤ c + 1 - z := by linarith
    have hz0 : (0 : ℝ) ∈ Set.Icc (c - z) (c + 1 - z) := by simpa [Set.uIcc_of_le hle] using hmem
    have : (0 : ℝ) < c - z := by linarith
    exact (not_le_of_gt this) hz0.1
  calc
    (∫ T : ℝ in c..c+1, (T - z)⁻¹) = ∫ y : ℝ in (c - z)..(c + 1 - z), y⁻¹ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (intervalIntegral.integral_comp_add_right (f := fun y : ℝ => y⁻¹) (d := -z) (a := c) (b := c + 1))
    _ = Real.log ((c + 1 - z) / (c - z)) := integral_inv h0

/-- Below the window: `∫_c^{c+1} 2/(T−z) dT = 2·log((c+1−z)/(c−z))` for `z < c`. -/
lemma TAveWeight_below {c z : ℝ} (hz : z < c) :
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (T - z)) = 2 * Real.log ((c + 1 - z) / (c - z)) := by
  have hmain := int_inv_sub_below hz
  calc
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (T - z))
        = ∫ T : ℝ in c..c + 1, (2 : ℝ) * (T - z)⁻¹ := by
          apply intervalIntegral.integral_congr; intro T hT; ring
    _ = (2 : ℝ) * (∫ T : ℝ in c..c + 1, (T - z)⁻¹) := by rw [intervalIntegral.integral_const_mul]
    _ = (2 : ℝ) * Real.log ((c + 1 - z) / (c - z)) := by rw [hmain]

/-- Above the window: `∫_c^{c+1} 2/(z−T) dT = 2·log((z−c)/(z−c−1))` for `c + 1 < z`. -/
lemma TAveWeight_above {c z : ℝ} (hz : c + 1 < z) :
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (z - T)) = 2 * Real.log ((z - c) / (z - c - 1)) := by
  have hA : (∫ T : ℝ in c..c+1, (T - z)⁻¹) = Real.log ((c + 1 - z) / (c - z)) := by
    have h0 : 0 ∉ Set.uIcc (c - z) (c + 1 - z) := by
      intro hmem
      have hle : c - z ≤ c + 1 - z := by linarith
      have hz0 : (0 : ℝ) ∈ Set.Icc (c - z) (c + 1 - z) := by simpa [Set.uIcc_of_le hle] using hmem
      have : c + 1 - z < 0 := by linarith
      exact (not_lt_of_ge hz0.2) this
    calc
      (∫ T : ℝ in c..c+1, (T - z)⁻¹) = ∫ y : ℝ in (c - z)..(c + 1 - z), y⁻¹ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (intervalIntegral.integral_comp_add_right (f := fun y : ℝ => y⁻¹) (d := -z) (a := c) (b := c + 1))
      _ = Real.log ((c + 1 - z) / (c - z)) := integral_inv h0
  have hneg : (∫ T : ℝ in c..c + 1, (z - T)⁻¹) = -Real.log ((c + 1 - z) / (c - z)) := by
    calc
      (∫ T : ℝ in c..c + 1, (z - T)⁻¹)
          = (∫ T : ℝ in c..c + 1, -((T - z)⁻¹)) := by
            apply intervalIntegral.integral_congr
            intro T hT
            change (z - T)⁻¹ = -((T - z)⁻¹)
            have hzt : z - T = -(T - z) := by ring
            rw [hzt]
            rw [inv_neg]
      _ = -(∫ T : ℝ in c..c + 1, (T - z)⁻¹) := by rw [intervalIntegral.integral_neg]
      _ = -Real.log ((c + 1 - z) / (c - z)) := by rw [hA]
  have hrat : -Real.log ((c + 1 - z) / (c - z)) = Real.log ((z - c) / (z - c - 1)) := by
    have hAinv : ((c + 1 - z) / (c - z))⁻¹ = (z - c) / (z - c - 1) := by
      rw [inv_div]
      have hrel : (c - z) / (c + 1 - z) = (z - c) / (z - c - 1) := by
        rw [show c - z = -(z - c) by ring, show c + 1 - z = -(z - c - 1) by ring]
        field_simp
      rw [hrel]
    calc
      -Real.log ((c + 1 - z) / (c - z))
          = Real.log (((c + 1 - z) / (c - z))⁻¹) := by
            exact (Real.log_inv ((c + 1 - z) / (c - z))).symm
      _ = Real.log ((z - c) / (z - c - 1)) := by rw [hAinv]
  have hmain : (∫ T : ℝ in c..c + 1, (z - T)⁻¹) = Real.log ((z - c) / (z - c - 1)) := by
    rw [hneg, hrat]
  calc
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (z - T))
        = ∫ T : ℝ in c..c + 1, (2 : ℝ) * (z - T)⁻¹ := by
          apply intervalIntegral.integral_congr; intro T hT; ring
    _ = (2 : ℝ) * (∫ T : ℝ in c..c + 1, (z - T)⁻¹) := by rw [intervalIntegral.integral_const_mul]
    _ = (2 : ℝ) * Real.log ((z - c) / (z - c - 1)) := by rw [hmain]


/-! ### S3: per-zero 2-D pole area over the box (next target)

For a zero `u = a + i·b` strictly inside the box `B = [0,2] × [c,c+1]` (zeros satisfy
`0 < a < 1`), the 2-D pole area is at most the perimeter of the box:

    ∫_c^{c+1} ∫_0^2 ‖((x+iT) − u)⁻¹‖ ≤ 2·(2 + 1) = 6.

Proof route (perimeter bound): in polar coordinates around `u`, `dA = r dr dθ` so the
integral is `∫_0^{2π} r(θ) dθ` with `r(θ)` the radial extent of `B` from `u`; parametrizing
`∂B` by arc length gives `ds ≥ r(θ) dθ`, hence the integral is at most `perimeter(∂B) = 6`.
(The coordinate statement type-checks; the polar/measure-theoretic proof is the next task,
delegated to the fleet as `Commons.NumberTheory.DirichletCharacter.poleArea_box_le`.) -/
theorem poleArea_box_le {c : ℝ} {u : ℂ}
    (ha1 : 0 < u.re) (ha2 : u.re < 1)
    (hb1 : c < u.im) (hb2 : u.im < c + 1) :
    (∫ T : ℝ in c..c+1, ∫ x : ℝ in 0..2, ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)⁻¹‖) ≤ 6 := by
  have hg := Commons.NumberTheory.DirichletCharacter.rectPoleArea_perimeter_le
      (x0 := (0 : ℝ)) (x1 := (2 : ℝ)) (y0 := c) (y1 := c + 1) (u := u)
      (hw := by norm_num) (hh := by norm_num)
      (hux := ha1) (hux2 := by linarith) (huy := hb1) (huy2 := hb2)
  have hc : (2 : ℝ) * ((2 : ℝ) - 0 + (c + 1 - c)) = 6 := by ring
  rwa [hc] at hg


/-! ### S4: small-constant window zero counts (next target)

The height-averaged pole sum needs, with small explicit constants, the count (with
multiplicity) of zeros in unit height windows: the box window `[c,c+1]` (interior poles,
each contributing ≤ 6 by `poleArea_box_le`) and the neighbouring unit windows (nearby
poles, each contributing ≤ `2·log(1+1/d)` by `TAveWeight_below`/`TAveWeight_above`).

```
theorem windowCount_unit {N} [NeZero N] (χ) (hχ) (hχprim) {c : ℝ} (hc : 1/2 ≤ c) :
    (∑ᶠ u, divisor(Λ, closedBall 0 (c+4)) u · 𝟙[c ≤ u.im ∧ u.im ≤ c+1]) ≤
      (1/2)·(log N + log(2+c+3)) + 2
```

Ingredients sitting above: `rectCount_box` bounds the window count by `(2π)⁻¹` times the
four side integrals; the vertical sides are bounded by the certified pointwise bounds
(`completedLogDeriv_two_small`/`neg_one_small`), and the horizontal sides by
`horizontalGoodLine_bound` at good heights.  This is the root bootstrap content: the tight
explicit constants require the good-height/average chain (the `∃`-form is certified; the
explicit-constant form is not yet dischargeable — cf. the fleet judgment on the identical
`unitWindow_zeroCount` statement). -/
-- (the legacy `windowCount_unit` statement, judged FALSE in an earlier session, has been removed)


/-! ### S5: far-zero tail of the height-averaged pole sum (next target)

Zeros of `Λ` with height outside `[c−1, c+2]` but still inside `closedBall 0 (c+4)`
contribute to the `T`-average of the pole sum only through their per-zero far weights:
below (`u.im ≤ c−1`) at most `2/(c − u.im)`, above (`u.im ≥ c+2`) at most
`2/(u.im − c − 1)` (verified locally below as `farWeight_le_below`/`farWeight_le_above`).
Summed over the neighbouring unit windows (using `windowCount_unit`-type counts, S4, with
the conjugate character for the negative heights), the total is `O(1)·(log N + log(2+c+3))`.

```
theorem farTail_le {N} [NeZero N] (χ) (hχ) (hχprim) {c : ℝ} (hc : 1/2 ≤ c) :
    ∑ᶠ u, divisor(Λ, closedBall 0 (c+4)) u
      · (if u.im ≤ c - 1 then 2/(c - u.im) else 0
         + if c + 2 ≤ u.im then 2/(u.im - c - 1) else 0)
      ≤ 6 · (log N + log(2+c+3)) + 12
```

Depends on S4 (window counts; its `∃`-form is certified, and the explicit-constant form is
in flight as `windowCount_unit`).  When S4 lands the window-sum over dyadic shells below/above
discharges the hypothesis and S5 becomes a theorem; the part independent of S4 — the
per-zero far weights — is verified below.
-/

/-- Far-below per-zero T-average bound: `∫_c^{c+1} 2/(T−z) ≤ 2/(c−z)` for `c−z ≥ 1`. -/
lemma farWeight_le_below {c z : ℝ} (h1 : (1 : ℝ) ≤ c - z) :
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (T - z)) ≤ 2 / (c - z) := by
  have hz : z < c := by linarith
  have hd : 0 < c - z := by linarith
  have heq := TAveWeight_below hz
  have hlog : Real.log ((c + 1 - z) / (c - z)) ≤ 1 / (c - z) := by
    have harg : (c + 1 - z) / (c - z) = 1 + 1 / (c - z) := by
      field_simp [hd.ne']
      ring
    rw [harg]
    have hle := Real.log_le_sub_one_of_pos (x := 1 + 1 / (c - z))
      (by have h1d : 0 < 1 / (c - z) := one_div_pos.mpr hd; nlinarith)
    exact hle.trans_eq (by ring)
  calc
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (T - z)) = 2 * Real.log ((c + 1 - z) / (c - z)) := heq
    _ ≤ 2 * (1 / (c - z)) := by
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = 2 / (c - z) := by ring

/-- Far-above per-zero T-average bound: `∫_c^{c+1} 2/(z−T) ≤ 2/(z−c−1)` for `z−c−1 ≥ 1`. -/
lemma farWeight_le_above {c z : ℝ} (h1 : (1 : ℝ) ≤ z - c - 1) :
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (z - T)) ≤ 2 / (z - c - 1) := by
  have hz : c + 1 < z := by linarith
  have hd : 0 < z - c - 1 := by linarith
  have heq := TAveWeight_above hz
  have hlog : Real.log ((z - c) / (z - c - 1)) ≤ 1 / (z - c - 1) := by
    have harg : (z - c) / (z - c - 1) = 1 + 1 / (z - c - 1) := by
      field_simp [hd.ne']
      ring
    rw [harg]
    have hle := Real.log_le_sub_one_of_pos (x := 1 + 1 / (z - c - 1))
      (by have h1d : 0 < 1 / (z - c - 1) := one_div_pos.mpr hd; nlinarith)
    exact hle.trans_eq (by ring)
  calc
    (∫ T : ℝ in c..c + 1, (2 : ℝ) / (z - T)) = 2 * Real.log ((z - c) / (z - c - 1)) := heq
    _ ≤ 2 * (1 / (z - c - 1)) := by
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = 2 / (z - c - 1) := by ring


/-! ### horizontalTAverage_bound — assembly statement (S4/S5 as hypotheses)

The final box bound is the `T`-average over `[c,c+1]` of the horizontal integral, whose
layered proof is now fully prepared.  To make the assembly concrete while S4 and S5 are in
flight, this theorem states the target with the two gap statements as explicit hypotheses:

* `hcount w` — unit-window zero count (`w ≤ Im u ≤ w+1`, divisor over `closedBall 0 (w+4)`),
* `hfar w` — far-zero tail bound for the height window `[w, w+1]`.

Downstream of these two hypotheses everything else is certified: `horizontalGoodLine_bound`
(pointwise pole bound + smooth line + circle remainder), `finsum_integral_interchange` over
`T`, `TAveWeight_below/above` and `farWeight_le_below/above` (per-zero weights),
`poleArea_box_le` (interior poles ≤ 6), `smoothPart_le` (smooth line), and the real algebra
against `20 + 4·(log N + log(2+c+3))`.  When L174 (S4) lands and S5 discharges, the proof
of this theorem is the remaining assembly; its statement is fixed below so both holes are
plugged in place. -/
-- (the legacy `horizontalTAverage_bound` statement has been removed; the target is proved directly above)


/-! ### Argument-principle window-count core (certified corollary of `rectCount_box`)

The number of zeros (with multiplicity) of `Λ` in the strip-window `(−1,2) × (α,β)` —
where `α, β` are zero-free heights — is at most `(2π)⁻¹·(V + 2B)`, with `B` a bound on the
horizontal side integrals at the two heights and `V` a bound on the two vertical side
integrals.  This is the counting core of the explicit-constant window counts (S4): its
vertical sides are bounded by the certified pointwise bounds, and its horizontal sides are
exactly the good-height horizontal bounds (to be supplied by the clearance partial-fraction
and functional-equation-growth estimates). -/
theorem windowCount_core {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {α β : ℝ}
    (hα0 : 0 ≤ α) (hαβ : α < β)
    (hzα : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ α)
    (hzβ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ β)
    (B V : ℝ)
    (hHα : (∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (α : ℂ))‖) ≤ B)
    (hHβ : (∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (β : ℂ))‖) ≤ B)
    (hV : (∫ y : ℝ in α..β,
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (y : ℂ))‖) +
        (∫ y : ℝ in α..β,
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (y : ℂ))‖) ≤ V) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (β + 4))) u : ℤ) : ℝ) *
        (if (-1 < u.re ∧ u.re < 2 ∧ α < u.im ∧ u.im < β) then 1 else 0)) ≤
      (1 / (2 * Real.pi)) * (V + 2 * B) := by
  have hR := rectCount_box χ hχ hχprim (α := α) (β := β) hα0 hαβ hzα hzβ
  have hsum : (((∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (α : ℂ))‖) +
      (∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (β : ℂ))‖)) +
      (∫ y : ℝ in α..β,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (y : ℂ))‖)) +
      (∫ y : ℝ in α..β,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (y : ℂ))‖) ≤
      V + 2 * B := by nlinarith
  have htwo : 0 ≤ (1 / (2 * Real.pi)) := by positivity
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (β + 4))) u : ℤ) : ℝ) *
        (if (-1 < u.re ∧ u.re < 2 ∧ α < u.im ∧ u.im < β) then 1 else 0))
        ≤ (1 / (2 * Real.pi)) *
            ((((∫ x : ℝ in (-1)..2,
                ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (α : ℂ))‖) +
              (∫ x : ℝ in (-1)..2,
                ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (β : ℂ))‖)) +
             (∫ y : ℝ in α..β,
                ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (y : ℂ))‖)) +
            (∫ y : ℝ in α..β,
                ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (y : ℂ))‖)) := hR
    _ ≤ (1 / (2 * Real.pi)) * (V + 2 * B) := by
        exact mul_le_mul_of_nonneg_left hsum htwo


/-! ### Clearance partial-fraction horizontal bound (next target)

The good-height horizontal side bound that `windowCount_core` consumes: at a height `T`
that keeps clearance `δ` from every zero height in the strip window, the horizontal
integral of `‖logDeriv Λ‖` over the segment `[−1,2]` is bounded explicitly in terms of the
`Re = 2`/`Re = −1` pointwise bounds, the clearance, and the per-zero pole weights:

```
theorem clearanceHorizontal_bound {N} [NeZero N] (χ) (hχ) (hχprim) {T : ℝ} (T ≥ 1/2)
    {δ : ℝ} (0 < δ)
    (hcl : ∀ u, Λ u = 0 → u.im ≠ T ∧ (u.im ∉ (T - 1, T + 1) → ...))  -- clearance form TBD
    :  (∫ x in -1..2, ‖logDeriv Λ (x+iT)‖) ≤ H(T, δ)
```

Derivation: decompose `logDeriv Λ` against the `Re = 2` line at the same height
(`pfPole_pointwise_box` + `poleXIntegral_le`, both certified): the horizontal integral is
the smooth line plus the pole sum with per-zero weights `2/|T−u.im|`.  Clearance `δ`
bounds the near-zero terms by `2/δ` each, the number of near zeros by a
`windowCount_core`-type count with vertical sides from the certified pointwise bounds, and
the far zeros by the paired decay / functional-equation growth.  The precise clearance
hypothesis and constants are to be pinned by the proof; the inequality is the one
`windowCount_core` and `horizontalTAverage_bound` fire. -/


/-- Counting core with the vertical side bound discharged by `verticalLogDeriv_integral_le`:
zeros in the strip-window `(−1,2) × (α,β)` (zero-free heights `α, β`, horizontal side
integrals ≤ `B`) number at most `(2π)⁻¹·(((β−α)·(log N + log(2+β) + 10)) + 2B)`. -/
theorem windowCount_core_vert {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {α β : ℝ}
    (hα0 : 0 ≤ α) (hαβ : α < β)
    (hzα : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ α)
    (hzβ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ β)
    (B : ℝ)
    (hHα : (∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (α : ℂ))‖) ≤ B)
    (hHβ : (∫ x : ℝ in (-1)..2,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (β : ℂ))‖) ≤ B) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (β + 4))) u : ℤ) : ℝ) *
        (if (-1 < u.re ∧ u.re < 2 ∧ α < u.im ∧ u.im < β) then 1 else 0)) ≤
      (1 / (2 * Real.pi)) *
        (((β - α) * (Real.log (N : ℝ) + Real.log (2 + β) + 10)) + 2 * B) := by
  let V : ℝ := (β - α) * (Real.log (N : ℝ) + Real.log (2 + β) + 10)
  have hV : (∫ y : ℝ in α..β,
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (y : ℂ))‖) +
        (∫ y : ℝ in α..β,
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (y : ℂ))‖) ≤ V := by
    have h := Commons.NumberTheory.DirichletCharacter.verticalLogDeriv_integral_le χ hχ hχprim
      (u := α) (v := β) hα0 (le_of_lt hαβ)
    simpa [V] using h
  exact windowCount_core χ hχ hχprim (α := α) (β := β) hα0 hαβ hzα hzβ B V hHα hHβ hV


/-! ### SESSION-11: the `L`-route to the target, layer by layer.

**Strategy** (constants checked numerically this session; see the block below):

1. `logDeriv (completedLFunction χ) = logDeriv (LFunction χ) + logDeriv (gammaFactor χ)`, and the
   gamma-side box integral is already certified in the commons
   (`logDeriv_gammaFactor_box`: `∫∫_{[0,2]} ‖logDeriv (gammaFactor χ)‖ ≤ log(2+c+3) + 4`).
   So it suffices to bound the `L`-side box `∫_c^{c+1}∫_0^2 ‖L'/L‖` by `16 + 4 log N + 3 log(2+c+3)`.
2. Rebase the partial fraction at `s₁ = 2 + iT`, where `‖L'/L(2+iT)‖ ≤ 1`
   (`logDeriv_L_two_norm_le_one`, no `log N`): for `s = x + iT` in the box,
   `‖L'/L(s)‖ ≤ 1 + Σᶠ_ρ d_ρ · |x-2| / (‖s-ρ‖ · ‖2+iT-ρ‖)`.
   The box integral of the kernel is the weight `W_ρ`; it is `≤ 4.04 · log(4/‖c₀-ρ‖)` for all zeros
   `ρ` with `‖c₀-ρ‖ ≤ 3.68` (`c₀ = 2 + i(c+1/2)`), and `O(1/dist²)` far away.
3. The logarithmic weight is exactly what the *weighted Jensen identity* produces:
   `Σᶠ_ρ d_ρ log(4/‖c₀-ρ‖) = circleAverage (log‖L·‖) c₀ 4 - log‖L c₀‖ ≤ J`, with `J ≲ 6`
   (the circle average of `log‖L‖` on `B(2+iT,4)` is bounded using the pointwise convexity
   bounds: `ζ(3/2)` on `Re ≥ 3/2`, `norm_LFunction_le_re_ge_one` on `[1,3/2]`,
   `LFunction_norm_half_plane` on `(0,1)`, and the functional-equation value transfer on
   `Re ≤ 0`).
4. Hence `Σ_ρ d_ρ W_ρ ≤ 4.04·J + (outside contribution) ≈ 23.5 + 3.3 = 26.8 ≤ 30.4`, and
   `∫∫_{[0,2]}‖L'/L‖ ≤ 2 + 26.8 = 28.8 ≤ 16 + 4 log N + 3 log(2+c+3) = 32.4`.  The margin is
   thin (≈ 10%), so every constant above has to be certified in this exact form. -/

namespace Commons.NumberTheory.DirichletCharacter

/-- **Weighted Jensen bound.**  If `f` is analytic on the closed ball of radius `R` around `c`,
`f c ≠ 0`, and the circle average of `log ‖f·‖` on that circle is at most `B`, then the
*weighted* divisor sum with the logarithmic weight `log (R / ‖c - u‖)` is at most
`B - log ‖f c‖`.  This is the weight-resolved form of Jensen's formula
(`AnalyticOnNhd.circleAverage_log_norm`); the crude sup-norm count
`AnalyticOnNhd.sum_divisor_le` loses a factor `≈ 5` on the constants needed here. -/
theorem finsum_divisor_mul_log_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hfc : f c ≠ 0)
    (havg : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) c R ≤ B) :
    (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ) *
      Real.log (R / ‖c - u‖)) ≤ B - Real.log ‖f c‖ := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by rwa [abs_of_pos hR]
  have h := AnalyticOnNhd.circleAverage_log_norm (f := f) (c := c) (R := R) hRne hf' hfc
  rw [abs_of_pos hR] at h
  have hsum : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ) *
      Real.log (R / ‖c - u‖)) =
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_congr fun u => rfl
  rw [hsum]
  linarith

end Commons.NumberTheory.DirichletCharacter


/-! ### SESSION-11: sharp-form archimedean (`Γ`-factor) estimates on vertical lines.

The following are proved from the certified sharp uniform bound
`Gamma_vertical_upper_uniform_sharp` (on `1/2 ≤ u ≤ 2`, from the *exact* value
`|Γ(1/2+iv)|² = π/cosh(π v)`) plus the recurrence `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)` and Mathlib's
reflection identity `Γ_ℝ(1-s)·Γ_ℝ(1+s) = (cos (π s/2))⁻¹`.

**Constant caveat.**  The constants obtained here are `C ≈ 142` (from the certified uniform
lemma), whereas the true constant in `|Γ_ℝ(a+it)| ≤ C(1+|t|)^{a/2-1/2}e^{-π|t|/4}` is
`√(2π) ≈ 2.5`.  The factor ≈ 50 comes from the slack `+2` in the certified increment lemma
`log_norm_Gamma_sub_le` (`Δ log‖Γ‖ ≤ Δu·(log(2+|v|)+2)`, whose true size is
`Δu·(log|v| + o(1))`).  Sharpening that increment bound is a prerequisite for the
zero-count budget of the target (see the SESSION-11 status note at the end of the file);
the *statements* below are already in the sharp shape, so only their constants need work. -/

namespace Commons.NumberTheory.DirichletCharacter

lemma GammaR_add_two (s : ℂ) (hs : s ≠ 0) :
    Complex.Gammaℝ (s + 2) = s / (2 * (Real.pi : ℂ)) * Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  have hexp : -(s + 2) / 2 = -s / 2 + (-1 : ℂ) := by ring
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, hexp,
    Complex.cpow_add (-s / 2) (-1) hpi, Complex.cpow_neg_one,
    show (s + 2) / 2 = s / 2 + 1 by ring, Complex.Gamma_add_one _ hs2]
  ring

lemma gammaR_sharp_upper_base :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℝ, 1 ≤ a → a ≤ 4 →
      ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
  obtain ⟨C0, hC0, hC0b⟩ := Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨C0, hC0, ?_⟩
  intro a t ha1 ha4
  have harg : ((a : ℂ) + (t : ℂ) * I) / 2 = ((a / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hnorm_pi : ‖(Real.pi : ℂ) ^ (-(((a : ℂ) + (t : ℂ) * I)) / 2)‖ =
      (Real.pi : ℝ) ^ (-(a / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hb := hC0b (a / 2) (t / 2) (by linarith) (by linarith)
  have hlog2 : (0 : ℝ) ≤ a / 2 - 1 / 2 := by linarith
  have habsdiv : |t / 2| = |t| / 2 := by rw [abs_div]; norm_num
  have h1 : (1 + |t / 2|) ^ (a / 2 - 1 / 2) ≤ (1 + |t|) ^ (a / 2 - 1 / 2) := by
    refine Real.rpow_le_rpow (by positivity) ?_ hlog2
    rw [habsdiv]
    have h2 : (0:ℝ) ≤ |t| := abs_nonneg t
    linarith
  have hexp : Real.exp (-(Real.pi / 2) * |t / 2|) ≤ Real.exp (-(Real.pi / 4) * |t|) := by
    apply Real.exp_le_exp.mpr
    rw [habsdiv]
    nlinarith [Real.pi_pos, abs_nonneg t]
  have hpi_le : (Real.pi : ℝ) ^ (-(a / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hcombined : ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤
      C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
    refine le_trans hb ?_
    calc C0 * (1 + |t / 2|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t / 2|)
        = C0 * ((1 + |t / 2|) ^ (a / 2 - 1 / 2) *
            Real.exp (-(Real.pi / 2) * |t / 2|)) := by ring
      _ ≤ C0 * ((1 + |t|) ^ (a / 2 - 1 / 2) *
            Real.exp (-(Real.pi / 4) * |t|)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC0)
          exact mul_le_mul h1 hexp (le_of_lt (Real.exp_pos _)) (by positivity)
      _ = C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by ring
  have hmain : ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖ ≤
      (Real.pi : ℝ) ^ (-(a / 2)) *
        (C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|)) := by
    rw [Complex.Gammaℝ_def, harg, norm_mul, hnorm_pi]
    exact mul_le_mul_of_nonneg_left hcombined (by positivity)
  calc ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖
      ≤ (Real.pi : ℝ) ^ (-(a / 2)) *
          (C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|)) := hmain
    _ ≤ 1 * (C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|)) := by
        apply mul_le_mul_of_nonneg_right hpi_le (by positivity)
    _ = C0 * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by ring

lemma gammaR_sharp_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℝ, 1 ≤ a → a ≤ 6 →
      ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
  obtain ⟨C0, hC0, hC0b⟩ := gammaR_sharp_upper_base
  refine ⟨C0, hC0, fun a t ha1 ha6 => ?_⟩
  by_cases h : a ≤ 4
  · exact hC0b a t ha1 h
  · push_neg at h
    set s : ℂ := ((a - 2 : ℝ) : ℂ) + (t : ℂ) * I with hsdef
    have hsne : s ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      simp [hsdef] at hre
      linarith
    have hrec := GammaR_add_two s hsne
    have harg : s + 2 = ((a : ℂ) + (t : ℂ) * I) := by
      rw [hsdef]; push_cast; ring
    rw [harg] at hrec
    have hsabs : ‖s‖ ≤ (1 + |a - 2|) * (1 + |t|) := by
      have hprod : (a - 2) ^ 2 + t ^ 2 ≤ ((1 + |a - 2|) * (1 + |t|)) ^ 2 := by
        nlinarith [sq_abs (a - 2), sq_abs t, abs_nonneg (a - 2), abs_nonneg t,
          sq_nonneg (1 + |a - 2|), sq_nonneg (1 + |t|)]
      calc ‖s‖ = Real.sqrt ((a - 2) ^ 2 + t ^ 2) := by
              rw [hsdef]; exact Complex.norm_add_mul_I _ _
        _ ≤ Real.sqrt (((1 + |a - 2|) * (1 + |t|)) ^ 2) := Real.sqrt_le_sqrt hprod
        _ = (1 + |a - 2|) * (1 + |t|) := Real.sqrt_sq (by positivity)
    have hb := hC0b (a - 2) t (by linarith) (by linarith)
    have hb' : ‖Complex.Gammaℝ s‖ ≤
        C0 * (1 + |t|) ^ ((a - 2) / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
      simpa [hsdef] using hb
    have hfac : ‖s‖ / (2 * Real.pi) ≤ (1 + |t|) := by
      have hden : (0:ℝ) < 2 * Real.pi := by positivity
      have h5 : (1 + |a - 2|) ≤ 5 := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - 2)]; linarith
      have hstep1 : ‖s‖ / (2 * Real.pi) ≤ ((1 + |a - 2|) * (1 + |t|)) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right hsabs hden.le
      have hstep2 : ((1 + |a - 2|) * (1 + |t|)) / (2 * Real.pi) ≤
          (5 * (1 + |t|)) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h5 (by positivity)) hden.le
      have hstep3 : (5 * (1 + |t|)) / (2 * Real.pi) ≤ (1 + |t|) := by
        rw [div_le_iff₀ hden]
        nlinarith [Real.pi_gt_three, abs_nonneg t]
      linarith
    have hnorm2 : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)]
    have hpow : (1 + |t|) ^ (a / 2 - 1 / 2) =
        (1 + |t|) * (1 + |t|) ^ ((a - 2) / 2 - 1 / 2) := by
      rw [show a / 2 - 1 / 2 = ((a - 2) / 2 - 1 / 2) + 1 by ring,
        Real.rpow_add (by positivity), Real.rpow_one, mul_comm]
    rw [hrec, norm_mul, norm_div, hnorm2]
    have hstep : ‖s‖ / (2 * Real.pi) * ‖Complex.Gammaℝ s‖ ≤
        (1 + |t|) * (C0 * (1 + |t|) ^ ((a - 2) / 2 - 1 / 2) *
          Real.exp (-(Real.pi / 4) * |t|)) :=
      mul_le_mul hfac hb' (norm_nonneg _) (by positivity)
    refine le_trans hstep ?_
    rw [hpow]
    linarith [le_refl ((1 + |t|) * (C0 * (1 + |t|) ^ ((a - 2) / 2 - 1 / 2) *
      Real.exp (-(Real.pi / 4) * |t|)))]

lemma GammaR_mul_GammaR_two_sub (s : ℂ) :
    Complex.Gammaℝ s * Complex.Gammaℝ (2 - s) = (Complex.sin (Real.pi * s / 2))⁻¹ := by
  have h := Complex.Gammaℝ_one_sub_mul_Gammaℝ_one_add (1 - s)
  rw [show (1:ℂ) - (1 - s) = s by ring, show (1:ℂ) + (1 - s) = 2 - s by ring] at h
  rw [h]
  congr 1
  have harg : Real.pi * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 := by ring
  rw [harg]
  simp [Complex.cos_pi_div_two_sub]


end Commons.NumberTheory.DirichletCharacter


namespace Commons.NumberTheory.DirichletCharacter

/-- **Lower bound for `|Γ_ℝ|` on `Re ≤ 1`** (via the reflection identity `Γ_ℝ s·Γ_ℝ(2-s) =
(sin (πs/2))⁻¹` and the certified sharp upper bound at `2-s`), in the sharp shape
`(2+|t|)^{a/2-1/2}e^{-π|t|/4}`.  The constant is `e^{-2}`; the reflection costs the factor
`2` in `|sin| ≤ 2 e^{π|t|/2}` and the slack `e²` of `gammaR_vertical_sharp_upper`, so this is
`≈ 25×` the truth (`√(2π)·2^{-a/2+1/2}`), and in the ratio `‖γ(1-s)‖/‖γ(s)‖` it combines with
the upper bound to the constant `e⁴ ≈ 55` (true value `π^{-1/2} ≈ 0.56`). -/
lemma gammaR_sharp_lower {a t : ℝ} (ha1 : -14 ≤ a) (ha : a ≤ 1)
    (hne : Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I) ≠ 0) :
    Real.exp (-2) * (2 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) ≤
      ‖Complex.Gammaℝ ((a : ℂ) + (t : ℂ) * I)‖ := by
  set s : ℂ := (a : ℂ) + (t : ℂ) * I with hsdef
  have hspos : (0:ℝ) < 2 + |t| := by positivity
  have h2s : (2 : ℂ) - s = ((2 - a : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by
    rw [hsdef]; push_cast; ring
  have hub : ‖Complex.Gammaℝ ((2:ℂ) - s)‖ ≤
      Real.exp (((1 - a) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|) := by
    have h :=
      Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_sharp_upper (2 - a) (-t)
        (by linarith) (by linarith)
    have hexp : (2 - a - 1) / 2 = (1 - a) / 2 := by ring
    rw [h2s]
    simpa [hexp] using h
  have href := GammaR_mul_GammaR_two_sub s
  have hprod : ‖Complex.Gammaℝ s‖ * ‖Complex.Gammaℝ (2 - s)‖ =
      1 / ‖Complex.sin (Real.pi * s / 2)‖ := by
    rw [← norm_mul, href, norm_inv, one_div]
  have hne2 : Complex.Gammaℝ ((2:ℂ) - s) ≠ 0 := by
    rw [h2s]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hsin_ne0 : ‖Complex.sin (Real.pi * s / 2)‖ ≠ 0 := by
    intro hz
    have hAB : ‖Complex.Gammaℝ s‖ * ‖Complex.Gammaℝ (2 - s)‖ ≠ 0 := by
      apply mul_ne_zero <;> rwa [norm_ne_zero_iff]
    rw [hprod, hz, div_zero] at hAB
    exact hAB rfl
  have hABS : ‖Complex.Gammaℝ s‖ * ‖Complex.Gammaℝ (2 - s)‖ *
      ‖Complex.sin (Real.pi * s / 2)‖ = 1 := by
    rw [hprod, one_div, inv_mul_cancel₀ hsin_ne0]
  have hsval : ‖Complex.Gammaℝ s‖ = 1 / (‖Complex.sin (Real.pi * s / 2)‖ *
      ‖Complex.Gammaℝ (2 - s)‖) := by
    rw [eq_div_iff (by positivity), mul_comm (‖Complex.sin (Real.pi * s / 2)‖), ← mul_assoc]
    exact hABS
  have hsin : ‖Complex.sin (Real.pi * s / 2)‖ ≤ Real.exp (Real.pi * |t| / 2) := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_sin_le_exp_abs_im (Real.pi * s / 2)
    have him : (Real.pi * s / 2).im = Real.pi * t / 2 := by
      rw [hsdef]
      rw [show (Real.pi : ℂ) * ((a : ℂ) + (t : ℂ) * I) / 2 =
          ((Real.pi * a / 2 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * I by
        apply Complex.ext <;> simp <;> ring]
      simp
    rw [him] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hD1 : Real.exp (Real.pi * |t| / 2) *
        Real.exp (((1 - a) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|) =
      Real.exp 2 * (2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hspos]
    rw [show Real.pi * |t| / 2 + (((1 - a) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|)
        = 2 + (((1 - a) / 2) * Real.log (2 + |t|) + (Real.pi / 4) * |t|) by ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  have hden_le : ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.Gammaℝ (2 - s)‖ ≤
      Real.exp 2 * (2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|) := by
    calc ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.Gammaℝ (2 - s)‖
        ≤ Real.exp (Real.pi * |t| / 2) *
            Real.exp (((1 - a) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|) :=
          mul_le_mul hsin hub (norm_nonneg _) (by positivity)
      _ = Real.exp 2 * (2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|) := hD1
  have hmain : (Real.exp 2 * (2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|))⁻¹ =
      Real.exp (-2) * (2 + |t|) ^ (a / 2 - 1 / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
    rw [show Real.exp 2 * (2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|)
        = Real.exp 2 * ((2 + |t|) ^ ((1 - a) / 2) * Real.exp ((Real.pi / 4) * |t|)) by ring]
    rw [mul_inv, mul_inv, ← Real.rpow_neg hspos.le, ← Real.exp_neg, ← Real.exp_neg]
    ring
  rw [hsval, ← hmain, one_div]
  simpa [one_div] using one_div_le_one_div_of_le (by positivity) hden_le



end Commons.NumberTheory.DirichletCharacter

/-! ### SESSION-11 STATUS — the `L`-box route to the target, with exact constants

**Route.**  `logDeriv Λ = logDeriv L + logDeriv γ`, and the gamma side is already certified in
the commons (`logDeriv_gammaFactor_box`: `∫∫_{[0,2]} ‖logDeriv (gammaFactor χ)‖ ≤ log(2+c+3)+4`).
Hence it suffices to prove the **`L`-box inequality**
`∫_c^{c+1}∫_0^2 ‖L'/L‖ ≤ 16 + 4 log N + 3 log(2+c+3)` (then `+ (log(2+c+3)+4)` is the target).

**Proof of the `L`-box (scheme, constants checked numerically this session).**
1. Rebase the partial fraction at `s₁ = 2+iT`, where `‖L'/L(2+iT)‖ ≤ 1`
   (`logDeriv_L_two_norm_le_one`): base contribution `2·1 = 2`.
2. For `s = x+iT` in the box, `‖L'/L(s)‖ ≤ 1 + Σᶠ_ρ d_ρ·|x-2|/(‖s-ρ‖·‖2+iT-ρ‖)`; the box
   integral of the kernel is the per-zero weight `W_ρ`.
3. With `c₀ = 2+i(c+1/2)`: for every zero with `‖c₀-ρ‖ ≤ 3.68` one has
   `W_ρ ≤ 4.04·log(4/‖c₀-ρ‖)` (verified numerically; the sup is attained at `ρ = (0.32,c+1/2)`,
   a bound with `≈ 1%` slack — this is a 2-D integral inequality, not yet formalised).
4. `Commons.Analysis.Complex.finsum_divisor_mul_log_le` (published this session) turns that
   into `Σ_{‖c₀-ρ‖≤4} d_ρ W_ρ ≤ 4.04·J` with `J = circleAverage (log‖L·‖) c₀ 4 - log‖L c₀‖`.
5. `J ≤ (circle average) + log 4`; the circle average of `log‖L‖` on `B(2+iT,4)` is bounded by
   the pointwise convexity bounds on the three arcs (`σ ≥ 3/2`: `ζ(3/2) ≈ 2.6`; `[1,3/2)`:
   `norm_LFunction_le_re_ge_one`; `(0,1)`: `LFunction_norm_half_plane` or the sharp convexity
   bound; `σ ≤ 0`: the functional-equation transfer = `(1/2-σ)(log N + log(2+|T|)) + log C`).
   Numerically (N = 3, c = 50): `≈ 0.9 + 0.3 + 4.7 = 5.9`, so `J ≈ 7.3` and
   `4.04·J ≈ 29`.
6. Zeros with `‖c₀-ρ‖ > 3.7` (two unit-height bands) contribute
   `≤ (per-window count)·(max W)`; the per-window count from Jensen with a ball of radius 0.71
   about `3/2 + iT` and outer radius 3 is `≈ 2` (true value `0.51`), giving `≈ 1.7`. Total
   `2 + 29 + 1.7 = 32.7` against the budget `16 + 4·1.1 + 3·4.01 = 32.4`: **inside, but by
   less than 1 %**, with every intermediate constant at its numerical optimum.

**The constant bottleneck.**  The `σ ≤ 0` arc contributes `log C` where `C` is the constant of
the functional-equation transfer `‖L(σ+iT)‖ ≤ C(N(2+|T|))^{1/2-σ}(log+2)`.  With the certified
`gammaR_vertical_sharp_upper` (`C_Γ = e² ≈ 7.4`, true value `√(2π) ≈ 2.5`) and the reflection
lower bound proved above (`e^{-2}`, true value `≈ 2.5`), one gets `C ≈ 3e⁴ ≈ 164`
(`log C ≈ 5.1`), which adds `≈ 0.33·(5.1+2) ≈ 2.4` to the circle average and pushes the total
to `≈ 36` — **outside** the budget.  Sharpening the lower bound for `Γ_ℝ` (whose true constant
is `2 sin(πσ/2)`-free: `√(2π)·2^{1/2-a/2}·π^{-a/2}`) to within a factor `≈ 2` is *necessary*
and is the first remaining task; the true ratio constant is `π^{-1/2} ≈ 0.56`.

**Remaining tasks, in dependency order.**
(i) sharp lower bound `‖Γ_ℝ(a+it)‖ ≥ c(1+|t|)^{a/2-1/2}e^{-π|t|/4}` for `a ≤ 1` (c ≈ 2–3);
(ii) the functional-equation transfer with that constant (the proof skeleton is laid out above:
`LFunction_eq_completed_div_gammaFactor` + `completedLFunction_eq` + `norm_LFunction_le_re_ge_one`);
(iii) the 2-D weight inequality `W_ρ ≤ 4.04 log(4/‖c₀-ρ‖)` (asinh antiderivatives);
(iv) the circle-average bounds (arc integrals with `arccos(1/4)`-type endpoints, or a
polynomial harmonic majorant — the latter loses `≈ 30 %` and is not enough);
(v) the per-window zero count (weighted Jensen again, on a small ball about `3/2+iT`);
(vi) the measure-theoretic assembly (`∫∫ ∑ = ∑ ∫∫` via
`Commons...finsum_divisor_mul_log_le`'s siblings and `MeasureTheory` Fubini).

Proved in this file this session (all used by the scheme): `finsum_divisor_mul_log_le`
(also published to the commons by the fleet), `GammaR_add_two`, `gammaR_sharp_upper_base`,
`gammaR_sharp_upper`, `GammaR_mul_GammaR_two_sub`, `gammaR_sharp_lower`. -/
