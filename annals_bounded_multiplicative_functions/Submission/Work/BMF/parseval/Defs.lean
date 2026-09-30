import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.parseval_kernels
import Submission.Work.BMF.delta_bounds
import Submission.Work.BMF.cpow_theta_identity
import Submission.Work.BMF.stepKern_defs
import Submission.Work.BMF.stepKern_uniform_bound
import Submission.Work.BMF.dirPoly_perron_integral
import Submission.Work.BMF.perron_error_tendsto
import Submission.Work.BMF.fatou_interval
import Submission.Work.BMF.aemeasurable_window_avg
import Submission.Work.BMF.norm_window_avg_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions and elementary lemmas for the single-window Parseval bound

Self-contained copy of the vocabulary of the `mr_parseval_clean` node: the Dirichlet
polynomial `dirP` over `[X,3X]`, the logarithmic trapezoid weight `kappa`/`mwt`, the kernel
`Phi`, the truncated Perron integral `perronP` and the window average `winAvgS`, together with
the elementary estimates about them.

The file is deliberately independent of `Submission.Work.BMF.mr_parseval_direct` (which is
still a `sorry` node) so that consumers do not inherit `sorryAx`.
-/

namespace Work.BMF

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

/-- The Dirichlet polynomial over the window range `[X, 3X]`:
`A(1+it) = Σ_{X ≤ n ≤ 3X} a n · n^{-(1+it)}`. -/
def dirP (a : ℕ → ℂ) (X t : ℝ) : ℂ :=
  ∑ n ∈ natIcc X (3*X), a n * (n:ℂ)^(-(1 + Complex.I*(t:ℂ)))

/-- The trapezoid weight `κ` in the logarithmic variable: the convolution of the intervals
`[0,1]` and `[0,3]`, equal to `1` on `[1,3]` and vanishing outside `[0,4]`. -/
def kappa (w : ℝ) : ℝ :=
  if w ≤ 0 then 0 else if w ≤ 1 then w else if w ≤ 3 then 1 else if w ≤ 4 then 4 - w else 0

/-- The weight `mwt X x = κ(log (x/X) + 1)`, equal to `1` on `[X, e^2 X] ⊇ [X,3X]`. -/
def mwt (X x : ℝ) : ℝ := kappa (Real.log (x/X) + 1)

/-- `Φ(t,u) = ((1+u)^{1+it}-1)/(1+it) = u·Θ(u,t)`. -/
def Phi (t u : ℝ) : ℂ :=
  (((1+u:ℝ):ℂ)^(1 + Complex.I*(t:ℂ)) - 1)/(1 + Complex.I*(t:ℂ))

/-- The single-window truncated Perron integral
`(2π)⁻¹ ∫_{-T}^{T} A(1+it) x^{it} Θ(h/x, t) dt`. -/
def perronP (a : ℕ → ℂ) (X h T x : ℝ) : ℂ :=
  (1/(2*Real.pi)) * ∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(Complex.I*(t:ℂ))) * Theta (h/x) t

/-- The window average `h⁻¹ Σ_{x ≤ n ≤ x+h} a n`. -/
def winAvgS (a : ℕ → ℂ) (h x : ℝ) : ℂ := (1/h) * ∑ n ∈ natIcc x (x+h), a n

/-! ## Elementary properties of the weight and of `Φ` -/

lemma kappa_nonneg (w : ℝ) : 0 ≤ kappa w := by
  unfold kappa
  split_ifs with h1 h2 h3 h4 <;> linarith

lemma kappa_le_one (w : ℝ) : kappa w ≤ 1 := by
  unfold kappa
  split_ifs with h1 h2 h3 h4 <;> linarith

lemma kappa_eq_one {w : ℝ} (h1 : 1 ≤ w) (h3 : w ≤ 3) : kappa w = 1 := by
  unfold kappa
  rw [if_neg (by linarith : ¬ (w ≤ 0))]
  by_cases h : w ≤ 1
  · rw [if_pos h]; linarith
  · rw [if_neg h, if_pos h3]

lemma mwt_nonneg (X x : ℝ) : 0 ≤ mwt X x := kappa_nonneg _

lemma mwt_le_one (X x : ℝ) : mwt X x ≤ 1 := kappa_le_one _

lemma mwt_eq_one {X x : ℝ} (hX : 0 < X) (h1 : X ≤ x) (h3 : x ≤ 3*X) : mwt X x = 1 := by
  have hxX : 1 ≤ x/X := (one_le_div hX).mpr h1
  have hlog1 : 0 ≤ Real.log (x/X) := Real.log_nonneg hxX
  have hx3 : x/X ≤ 3 := by rw [div_le_iff₀ hX]; linarith
  have hlog3 : Real.log (x/X) ≤ 2 := by
    have h3' : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
    exact le_trans (Real.log_le_log (by positivity) hx3) h3'
  unfold mwt
  exact kappa_eq_one (by linarith) (by linarith)

lemma Phi_eq_mul_Theta (t u : ℝ) : Phi t u = (u:ℂ) * Theta u t := by
  unfold Phi Theta
  by_cases hu : (u:ℂ) = 0
  · simp [hu]
  · field_simp

lemma Phi_zero (t : ℝ) : Phi t 0 = 0 := by
  unfold Phi; norm_num

/-! ## Vanishing of the weight off its logarithmic support -/

lemma kappa_eq_zero_of_le {w : ℝ} (h : w ≤ 0) : kappa w = 0 := by
  unfold kappa; rw [if_pos h]

lemma kappa_eq_zero_of_ge {w : ℝ} (h : 4 ≤ w) : kappa w = 0 := by
  unfold kappa
  rw [if_neg (by linarith : ¬ (w ≤ 0)), if_neg (by linarith : ¬ (w ≤ 1)),
    if_neg (by linarith : ¬ (w ≤ 3))]
  by_cases h4 : w ≤ 4
  · rw [if_pos h4]; linarith
  · rw [if_neg h4]

lemma mwt_eq_zero_of_le {X x : ℝ} (hX : 0 < X) (hx : 0 < x) (h : x ≤ X * Real.exp (-1)) :
    mwt X x = 0 := by
  refine kappa_eq_zero_of_le ?_
  have hxX : x / X ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hX]; simpa [mul_comm] using h
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < x / X) hxX
  rw [Real.log_exp] at hlog
  linarith

lemma mwt_eq_zero_of_ge {X x : ℝ} (hX : 0 < X) (h : X * Real.exp 3 ≤ x) : mwt X x = 0 := by
  refine kappa_eq_zero_of_ge ?_
  have hxX : Real.exp 3 ≤ x / X := by
    rw [le_div_iff₀ hX]; simpa [mul_comm] using h
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < Real.exp 3) hxX
  rw [Real.log_exp] at hlog
  linarith


/-- Every element of `natIcc a b` is at least `1` when `1 ≤ a`. -/
lemma one_le_of_mem_natIccD {a b : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : n ∈ natIcc a b) : 1 ≤ n := by
  simp only [natIcc, Finset.mem_Icc] at hn
  have h1 : (1 : ℝ) ≤ (⌈a⌉₊ : ℕ) := le_trans ha (Nat.le_ceil a)
  have h2 : 1 ≤ ⌈a⌉₊ := by exact_mod_cast h1
  exact le_trans h2 hn.1

lemma one_add_I_mul_ne_zeroD (t : ℝ) : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- The truncated Perron step kernel as a `cpow` integral. -/
lemma stepKern_one_eq_integralD {z : ℝ} (hz : 0 < z) (T : ℝ) :
    Commons.Analysis.Complex.stepKern 1 T z
      = (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          ((z : ℂ) ^ (1 + Complex.I * (t : ℂ))) / (1 + Complex.I * (t : ℂ))) := by
  unfold Commons.Analysis.Complex.stepKern
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')]
  rw [Complex.ofReal_one]
  ring_nf

lemma cpow_neg_mul_cpow_ofRealD {y : ℝ} (hy : 0 < y) {n : ℕ} (_hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) * (y : ℂ) ^ (1 + Complex.I * (t : ℂ))
      = ((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by
  rw [← Complex.ofReal_natCast n, Complex.ofReal_div]
  rw [Complex.cpow_neg, ← div_eq_inv_mul]
  rw [← Complex.div_cpow_ofReal_nonneg hy.le (Nat.cast_nonneg n) (1 + Complex.I * (t : ℂ))]

lemma continuous_cpow_divD (c : ℂ) (hc : c ≠ 0) :
    Continuous (fun t : ℝ => c ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ))) := by
  apply Continuous.div
  · exact Continuous.const_cpow (by continuity) (Or.inl hc)
  · continuity
  · intro t; exact one_add_I_mul_ne_zeroD t

/-- `(2π)⁻¹ ∫_{-T}^{T} A(1+it) y^{1+it}/(1+it) dt = ∑_{n ∈ [X,3X]} a n · stepKern 1 T (y/n)`. -/
theorem dirP_perron_integral (a : ℕ → ℂ) {X y T : ℝ} (hX : 1 ≤ X) (hy : 0 < y) (hT : 0 < T) :
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        dirP a X t * ((y : ℂ) ^ (1 + Complex.I * (t : ℂ))) / (1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ natIcc X (3 * X),
          a n * Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ)) := by
  have key : (∫ t in (-T)..T,
        dirP a X t * (y : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ natIcc X (3 * X), a n * ∫ t in (-T)..T,
          ((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)) := by
    have hcongr : (fun t : ℝ =>
          dirP a X t * (y : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)))
        = fun t : ℝ => ∑ n ∈ natIcc X (3 * X), a n *
            (((y / (n : ℝ) : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ))) := by
      funext t
      rw [dirP]
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      rw [mul_assoc, cpow_neg_mul_cpow_ofRealD hy (one_le_of_mem_natIccD hX hn) t, mul_div_assoc]
    rw [hcongr]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast one_le_of_mem_natIccD hX hn
      have hc : ((y / (n : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      exact Continuous.intervalIntegrable ((continuous_cpow_divD _ hc).const_mul (a n)) (-T) T
  rw [key, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast one_le_of_mem_natIccD hX hn
  rw [stepKern_one_eq_integralD (show 0 < y / (n : ℝ) by positivity) T]
  ring



end

end Work.BMF
