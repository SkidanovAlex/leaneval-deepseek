import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Lyap.lyap_eq_lim
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob
import Submission.Work.TMC7Core.Cocycle.log_frob_iterC_nonneg
import Submission.Work.TMC7Core.Solutions.iterC_qpow
import Submission.Work.TMC7Core.Solutions.max_norm_roots_eq_rhoSL
import Submission.Work.TMC7Core.Solutions.tendsto_intervalIntegral_of_bounded
import Submission.Work.TMC7Core.Solutions.tendsto_log_frob_pow_div

/-!
# The Lyapunov exponent at a rational frequency

For a rational frequency `α = p/q` the `q`-th transfer matrix `A_q(x)` is the period of the
cocycle, so the finite-scale averages along the arithmetic progression `n = q(k+1)` are
averages of `(1/(k+1)) log ‖A_q(x)^{k+1}‖_F`, whose pointwise limit is `log ρ(A_q(x))` with
`ρ` the spectral radius.  For real energy `A_q(x) ∈ SL(2,ℝ)` and `ρ(A_q(x))` is `rhoSL` of the
trace.  Dominated convergence over `x ∈ [0,1]` then gives
`lyap = (1/q) ∫₀¹ log (rhoSL (tr A_q(x))) dx`.
-/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.Frobenius
open LeanEval.Analysis.TenMartini
open Work.TMC7Core

noncomputable section

namespace Work.TMC7Core.Solutions

/-! ## The transfer matrices of a real energy are real -/

/-- The real transfer cocycle, defined so that `iterC` at real energy is its complexification. -/
def iterR (α lam E : ℝ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | n + 1, x => tmR lam E (x + (n : ℝ) * α) * iterR α lam E n x

theorem tmC_eq_map (lam E x : ℝ) :
    tmC lam (E : ℂ) x = (tmR lam E x).map Complex.ofRealHom := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, tmR]

theorem iterC_eq_map (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    iterC α lam (E : ℂ) n x = (iterR α lam E n x).map Complex.ofRealHom := by
  induction n with
  | zero =>
    show (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom
    rw [Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)]
  | succ n ih =>
    rw [iterC_succ, ih, tmC_eq_map]
    show (tmR lam E (x + (n : ℝ) * α)).map Complex.ofRealHom
        * (iterR α lam E n x).map Complex.ofRealHom
      = (tmR lam E (x + (n : ℝ) * α) * iterR α lam E n x).map Complex.ofRealHom
    rw [Matrix.map_mul]

theorem trace_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A.map Complex.ofRealHom).trace = (A.trace : ℂ) := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

theorem trace_iterC_im_zero (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    ((iterC α lam (E : ℂ) n x).trace).im = 0 := by
  rw [iterC_eq_map, trace_map_ofReal]
  exact Complex.ofReal_im _

theorem trace_eq_ofReal_re {A : Matrix (Fin 2) (Fin 2) ℂ} (h : (Matrix.trace A).im = 0) :
    Matrix.trace A = (((Matrix.trace A).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [h]

/-! ## A square root of the discriminant `τ² - 4` -/

/-- A square root in `ℂ` of `τ² - 4`, chosen by cases so that it is real when `τ² ≥ 4`. -/
noncomputable def sqrtDisc (τ : ℝ) : ℂ :=
  if 4 ≤ τ ^ 2 then (Real.sqrt (τ ^ 2 - 4) : ℂ) else Complex.I * (Real.sqrt (4 - τ ^ 2) : ℂ)

theorem sqrtDisc_sq (τ : ℝ) : (sqrtDisc τ) ^ 2 = (τ : ℂ) ^ 2 - 4 := by
  rw [sqrtDisc]
  split_ifs with h
  · have h4 : (0 : ℝ) ≤ τ ^ 2 - 4 := by linarith
    rw [← Complex.ofReal_pow, Real.sq_sqrt h4]
    push_cast
    ring
  · push_neg at h
    have h4 : (0 : ℝ) ≤ 4 - τ ^ 2 := by linarith
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h4]
    push_cast
    ring

/-! ## Two elementary Frobenius-norm estimates -/

theorem frob_pow_succ_le (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    frob (A ^ (k + 1)) ≤ frob A ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc frob (A ^ (k + 1) * A) ≤ frob (A ^ (k + 1)) * frob A := Cocycle.frob_mul_le _ _
      _ ≤ frob A ^ (k + 1) * frob A := mul_le_mul_of_nonneg_right ih (frob_nonneg A)

theorem log_frob_pow_succ_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hd : A.det = 1) (k : ℕ) :
    Real.log (frob (A ^ (k + 1))) ≤ ((k : ℝ) + 1) * Real.log (frob A) := by
  have hpos : 0 < frob (A ^ (k + 1)) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
      (Cocycle.frob_sqrt_two_le_of_det_one (by rw [Matrix.det_pow, hd]; simp))
  calc Real.log (frob (A ^ (k + 1))) ≤ Real.log (frob A ^ (k + 1)) :=
        Real.log_le_log hpos (frob_pow_succ_le A k)
    _ = ((k : ℝ) + 1) * Real.log (frob A) := by
        rw [Real.log_pow]; push_cast; ring

/-! ## The main theorem -/

theorem lyap_periodic (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (E : ℝ) : lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ) = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, Real.log (rhoSL ((Matrix.trace (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x)).re)) := by
  generalize hα : (p : ℝ) / (q : ℝ) = α
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  -- ## Step 1: pointwise convergence of the integrands
  have hpoint : ∀ x : ℝ,
      Tendsto (fun k : ℕ => Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x))
          / ((q : ℝ) * ((k : ℝ) + 1))) atTop
        (nhds ((1 / (q : ℝ)) * Real.log (rhoSL ((Matrix.trace (iterC α lam (E : ℂ) q x)).re)))) := by
    intro x
    set τx : ℝ := ((Matrix.trace (iterC α lam (E : ℂ) q x)).re) with hτx
    have hdet : (iterC α lam (E : ℂ) q x).det = 1 := det_iterC α lam (E : ℂ) q x
    have him : ((iterC α lam (E : ℂ) q x).trace).im = 0 := trace_iterC_im_zero α lam E q x
    have htrace : (iterC α lam (E : ℂ) q x).trace = ((τx : ℝ) : ℂ) :=
      trace_eq_ofReal_re him
    have hsum : ((τx : ℂ) + sqrtDisc τx) / 2 + ((τx : ℂ) - sqrtDisc τx) / 2
        = (iterC α lam (E : ℂ) q x).trace := by
      rw [htrace]; ring
    have hsum' : ((τx : ℂ) + sqrtDisc τx) / 2 + ((τx : ℂ) - sqrtDisc τx) / 2
        = (τx : ℂ) := by ring
    have hprod : (((τx : ℂ) + sqrtDisc τx) / 2) * (((τx : ℂ) - sqrtDisc τx) / 2) = 1 := by
      have hc := sqrtDisc_sq τx
      have key : (((τx : ℂ) + sqrtDisc τx) / 2) * (((τx : ℂ) - sqrtDisc τx) / 2)
          = ((τx : ℂ) ^ 2 - (sqrtDisc τx) ^ 2) / 4 := by ring
      rw [key, hc]
      ring
    have hmain := tendsto_log_frob_pow_div (iterC α lam (E : ℂ) q x) hdet
      (((τx : ℂ) + sqrtDisc τx) / 2) (((τx : ℂ) - sqrtDisc τx) / 2) hsum hprod
    have hmax := max_norm_roots_eq_rhoSL τx hsum' hprod
    rw [hmax] at hmain
    have hscaled := hmain.const_mul (1 / (q : ℝ))
    have hfun : (fun k : ℕ => Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x))
          / ((q : ℝ) * ((k : ℝ) + 1)))
        = fun k : ℕ => (1 / (q : ℝ))
            * (Real.log (frob ((iterC α lam (E : ℂ) q x) ^ (k + 1))) / ((k : ℝ) + 1)) := by
      funext k
      have hqk : iterC α lam (E : ℂ) (q * (k + 1)) x = (iterC α lam (E : ℂ) q x) ^ (k + 1) := by
        rw [← hα]
        exact iterC_qpow p q hq lam E (k + 1) x
      rw [hqk]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hfun]
    exact hscaled
  -- ## Step 2: the uniform bound
  have hcontq : Continuous (fun x : ℝ => Real.log (frob (iterC α lam (E : ℂ) q x))) :=
    Lyap.continuous_log_frob_iterC α lam (E : ℂ) q
  obtain ⟨x₀, hx₀, hx₀max⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn ⟨0, by norm_num⟩ hcontq.continuousOn
  rw [isMaxOn_iff] at hx₀max
  set C : ℝ := Real.log (frob (iterC α lam (E : ℂ) q x₀)) / (q : ℝ) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact div_nonneg (Cocycle.log_frob_iterC_nonneg α lam (E : ℂ) q x₀) (le_of_lt hqpos)
  have hFcont : ∀ k : ℕ, Continuous (fun x : ℝ =>
      Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)) / ((q : ℝ) * ((k : ℝ) + 1))) :=
    fun k => (Lyap.continuous_log_frob_iterC α lam (E : ℂ) (q * (k + 1))).div_const _
  have hbound : ∀ k x, x ∈ Set.Icc (0 : ℝ) 1 →
      |Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)) / ((q : ℝ) * ((k : ℝ) + 1))| ≤ C := by
    intro k x hx
    have hqk : (0 : ℝ) < (q : ℝ) * ((k : ℝ) + 1) := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hdetq : (iterC α lam (E : ℂ) q x).det = 1 := det_iterC α lam (E : ℂ) q x
    have hnum : 0 ≤ Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)) :=
      Cocycle.log_frob_iterC_nonneg α lam (E : ℂ) (q * (k + 1)) x
    rw [abs_of_nonneg (div_nonneg hnum (le_of_lt hqk))]
    have hpow : iterC α lam (E : ℂ) (q * (k + 1)) x = (iterC α lam (E : ℂ) q x) ^ (k + 1) := by
      rw [← hα]
      exact iterC_qpow p q hq lam E (k + 1) x
    rw [hpow]
    have hle := log_frob_pow_succ_le (iterC α lam (E : ℂ) q x) hdetq k
    have hfk : Real.log (frob (iterC α lam (E : ℂ) q x)) ≤
        Real.log (frob (iterC α lam (E : ℂ) q x₀)) := hx₀max x hx
    calc Real.log (frob ((iterC α lam (E : ℂ) q x) ^ (k + 1))) / ((q : ℝ) * ((k : ℝ) + 1))
        ≤ (((k : ℝ) + 1) * Real.log (frob (iterC α lam (E : ℂ) q x)))
            / ((q : ℝ) * ((k : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hle (le_of_lt hqk)
      _ = Real.log (frob (iterC α lam (E : ℂ) q x)) / (q : ℝ) := by
          field_simp
      _ ≤ Real.log (frob (iterC α lam (E : ℂ) q x₀)) / (q : ℝ) :=
          div_le_div_of_nonneg_right hfk (le_of_lt hqpos)
      _ = C := by rw [hC]
  -- ## Step 3: dominated convergence
  have hInt := tendsto_intervalIntegral_of_bounded
    (F := fun k x => Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x))
      / ((q : ℝ) * ((k : ℝ) + 1)))
    (G := fun x : ℝ => (1 / (q : ℝ))
      * Real.log (rhoSL ((Matrix.trace (iterC α lam (E : ℂ) q x)).re)))
    (C := C) hFcont hC0 hbound hpoint
  have hInt' : Tendsto (fun k : ℕ =>
      (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)))
        / ((q : ℝ) * ((k : ℝ) + 1))) atTop
      (nhds ((1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1,
        Real.log (rhoSL ((Matrix.trace (iterC α lam (E : ℂ) q x)).re)))) := by
    have h1 : ∀ k : ℕ, (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x))
          / ((q : ℝ) * ((k : ℝ) + 1)))
        = (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)))
          / ((q : ℝ) * ((k : ℝ) + 1)) := fun k => intervalIntegral.integral_div _ _
    have h2 : (∫ x in (0 : ℝ)..1, (1 / (q : ℝ))
          * Real.log (rhoSL ((Matrix.trace (iterC α lam (E : ℂ) q x)).re)))
        = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1,
          Real.log (rhoSL ((Matrix.trace (iterC α lam (E : ℂ) q x)).re)) :=
      intervalIntegral.integral_const_mul _ _
    simp only [h1, h2] at hInt
    exact hInt
  -- ## Step 4: the Lyapunov sequence along the subsequence `n + 1 = q(k+1)`
  have hφ : Tendsto (fun k : ℕ => q * (k + 1) - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun k hk => ?_⟩
    have h1 : k + 1 ≤ q * (k + 1) := by
      calc k + 1 = 1 * (k + 1) := (one_mul _).symm
        _ ≤ q * (k + 1) := Nat.mul_le_mul_right _ hq
    omega
  have hlyap := Lyap.lyap_eq_lim α lam (E : ℂ)
  have hseq : Tendsto (fun k : ℕ =>
      (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)))
        / ((q : ℝ) * ((k : ℝ) + 1))) atTop (nhds (lyap α lam (E : ℂ))) := by
    have hsub : Tendsto (fun k : ℕ =>
        (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) ((q * (k + 1) - 1) + 1) x)))
          / ((((q * (k + 1) - 1 : ℕ)) : ℝ) + 1)) atTop (nhds (lyap α lam (E : ℂ))) :=
      hlyap.comp hφ
    have hterm : ∀ k : ℕ,
        (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) ((q * (k + 1) - 1) + 1) x)))
            / ((((q * (k + 1) - 1 : ℕ)) : ℝ) + 1)
        = (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)))
            / ((q : ℝ) * ((k : ℝ) + 1)) := by
      intro k
      have hk1 : 1 ≤ q * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h1 : (q * (k + 1) - 1) + 1 = q * (k + 1) := Nat.sub_add_cancel hk1
      rw [h1]
      congr 1
      rw [Nat.cast_sub hk1, Nat.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [show (fun k : ℕ =>
          (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam (E : ℂ) ((q * (k + 1) - 1) + 1) x)))
            / ((((q * (k + 1) - 1 : ℕ)) : ℝ) + 1))
        = fun k : ℕ => (∫ x in (0 : ℝ)..1,
            Real.log (frob (iterC α lam (E : ℂ) (q * (k + 1)) x)))
            / ((q : ℝ) * ((k : ℝ) + 1)) from funext hterm] at hsub
    exact hsub
  exact tendsto_nhds_unique hseq hInt'

end Work.TMC7Core.Solutions
