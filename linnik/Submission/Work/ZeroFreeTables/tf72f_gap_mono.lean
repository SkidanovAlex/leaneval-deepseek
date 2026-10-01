/-
# ZeroFreeTables — monotonicity of the `F`-method gap for HB Lemma 7.2 at λ = 6/7

With `f = tf72f (6/7)` (Heath-Brown's test function, supported on `[0, 7/3]`) the
`F`-method gap is

  `G lam = F (-lam) - 2 F (6/7 - lam)`,   `F z = ∫_0^{7/3} e^{-z t} f t dt`.

Writing `F (-lam) = ∫_0^{7/3} e^{lam t} f t dt` and `F (6/7 - lam) = ∫_0^{7/3} e^{(lam-6/7)t} f`
turns the gap into the single integral

  `G lam = tf72fPhi lam = ∫_0^{7/3} e^{lam t} · tf72fK t dt`,
  `tf72fK t = (1 - 2 e^{-(6/7)t}) f t`.

The kernel `tf72fK` changes sign exactly once, at `τ = (7/6) log 2` (where `e^{(6/7)τ} = 2`).
That single sign change makes the *weighted* integral monotone: splitting at `τ`, and replacing
`e^{lam t}` by its value at `τ` (which is legitimate because on `[0,τ]` the weight is smaller and
`t · tf72fK t ≤ 0`, while on `[τ,7/3]` it is larger and `t · tf72fK t ≥ 0`), one gets

  `tf72fPhi' lam ≥ e^{lam τ} · tf72fPhi' 0 ≥ 0`  for `lam ≥ 0`,

since `tf72fPhi' 0 = ∫_0^{7/3} t · tf72fK t ≥ 0` (`tf72fK_t_moment_nonneg`).  Hence
`tf72fPhi` is monotone on `[0,∞)` and the gap is maximal at `lam = 792/1000`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72fK_defs
import Submission.Work.ZeroFreeTables.tf72f_moment
import Submission.Work.ZeroFreeTables.tf72fK_hasDerivAt
import Submission.Work.ZeroFreeTables.tf72fK_t_moment_nonneg

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables

/-! ## 1.  The gap as a single integral against the signed kernel -/

/-- `F (-lam) - 2 F (6/7 - lam) = ∫_0^{7/3} exp (lam t) * tf72fK t dt`. -/
lemma tf72fL_eq_Phi (lam : ℝ) :
    (∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t)
      - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t)
    = tf72fPhi lam := by
  have hcontf : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.Icc (0:ℝ) (7/3)) :=
    (tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self
  have hintA : IntervalIntegrable (fun t : ℝ => Real.exp (lam * t) * tf72f (6/7) t)
      volume (0:ℝ) (7/3) :=
    (ContinuousOn.mul (by fun_prop) hcontf).intervalIntegrable_of_Icc (by norm_num)
  have hintB : IntervalIntegrable
      (fun t : ℝ => 2 * (Real.exp (lam * t) * (Real.exp (-(6/7) * t) * tf72f (6/7) t)))
      volume (0:ℝ) (7/3) :=
    (ContinuousOn.mul continuousOn_const
      (ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) hcontf))).intervalIntegrable_of_Icc
      (by norm_num)
  have h2 : (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * (Real.exp (-(6/7) * t) * tf72f (6/7) t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((6/7 - lam) * t) = lam * t + -(6/7) * t by ring, Real.exp_add]
    ring
  have h3 : (∫ t in (0:ℝ)..(7/3), (Real.exp (lam * t) * tf72f (6/7) t
        - 2 * (Real.exp (lam * t) * (Real.exp (-(6/7) * t) * tf72f (6/7) t))))
      = (∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3),
            Real.exp (lam * t) * (Real.exp (-(6/7) * t) * tf72f (6/7) t)) := by
    rw [intervalIntegral.integral_sub hintA hintB, intervalIntegral.integral_const_mul]
  rw [h2, ← h3]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  unfold tf72fK
  ring

/-! ## 2.  The single sign change of the kernel at `τ = (7/6) log 2` -/

/-- The point where the kernel changes sign: `exp ((6/7) t) = 2`. -/
private def tf72fTau : ℝ := (7/6) * Real.log 2

private lemma tf72fTau_nonneg : 0 ≤ tf72fTau := by
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold tf72fTau
  nlinarith

private lemma tf72fTau_le : tf72fTau ≤ 7/3 := by
  have h : Real.log 2 ≤ 1 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  unfold tf72fTau
  linarith

private lemma tf72fTau_exp : Real.exp ((6/7) * tf72fTau) = 2 := by
  have h : (6/7) * tf72fTau = Real.log 2 := by unfold tf72fTau; ring
  rw [h, Real.exp_log (by norm_num)]

private lemma tf72fK_contOn : ContinuousOn tf72fK (Set.Icc (0:ℝ) (7/3)) := by
  unfold tf72fK
  exact ContinuousOn.mul (by fun_prop)
    ((tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self)

/-- On `[0, τ]` the kernel is non-positive. -/
private lemma tf72fK_nonpos_of_le_tau (t : ℝ) (ht : t ≤ tf72fTau) : tf72fK t ≤ 0 := by
  have hexp : Real.exp ((6/7) * t) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 6/7))
    rwa [tf72fTau_exp] at h
  have hone : 1 ≤ 2 * Real.exp (-(6/7) * t) := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t)
        ≤ Real.exp (-(6/7) * t) * 2 :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- On `[τ, ∞)` the kernel is non-negative. -/
private lemma tf72fK_nonneg_of_tau_le (t : ℝ) (ht : tf72fTau ≤ t) : 0 ≤ tf72fK t := by
  have hexp : 2 ≤ Real.exp ((6/7) * t) := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 6/7))
    rwa [tf72fTau_exp] at h
  have hone : 2 * Real.exp (-(6/7) * t) ≤ 1 := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * 2 ≤ Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- Weighted comparison on the negative part `[0, τ]`: since `t * tf72fK t ≤ 0` there and
`exp (lam t) ≤ exp (lam τ)` for `lam ≥ 0`, the weight-shifted integrand is the smaller one. -/
private lemma tf72fK_weight_le_left (lam t : ℝ) (hlam : 0 ≤ lam) (ht0 : 0 ≤ t)
    (htt : t ≤ tf72fTau) :
    t * (Real.exp (lam * tf72fTau) * tf72fK t) ≤ t * (Real.exp (lam * t) * tf72fK t) := by
  have hexp : Real.exp (lam * t) ≤ Real.exp (lam * tf72fTau) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt hlam)
  have hK : tf72fK t ≤ 0 := tf72fK_nonpos_of_le_tau t htt
  have htK : t * tf72fK t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hK
  calc t * (Real.exp (lam * tf72fTau) * tf72fK t)
      = Real.exp (lam * tf72fTau) * (t * tf72fK t) := by ring
    _ ≤ Real.exp (lam * t) * (t * tf72fK t) := mul_le_mul_of_nonpos_right hexp htK
    _ = t * (Real.exp (lam * t) * tf72fK t) := by ring

/-- Weighted comparison on the positive part `[τ, 7/3]`. -/
private lemma tf72fK_weight_le_right (lam t : ℝ) (hlam : 0 ≤ lam) (htt : tf72fTau ≤ t) :
    t * (Real.exp (lam * tf72fTau) * tf72fK t) ≤ t * (Real.exp (lam * t) * tf72fK t) := by
  have hexp : Real.exp (lam * tf72fTau) ≤ Real.exp (lam * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt hlam)
  have hK : 0 ≤ tf72fK t := tf72fK_nonneg_of_tau_le t htt
  have ht0 : 0 ≤ t := le_trans tf72fTau_nonneg htt
  have htK : 0 ≤ t * tf72fK t := mul_nonneg ht0 hK
  calc t * (Real.exp (lam * tf72fTau) * tf72fK t)
      = Real.exp (lam * tf72fTau) * (t * tf72fK t) := by ring
    _ ≤ Real.exp (lam * t) * (t * tf72fK t) := mul_le_mul_of_nonneg_right hexp htK
    _ = t * (Real.exp (lam * t) * tf72fK t) := by ring

/-- A function continuous on `[0, 7/3]` is interval integrable on every subinterval. -/
private lemma tf72fIcc_integrable {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc (0:ℝ) (7/3)))
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h3 : b ≤ 7/3) : IntervalIntegrable g volume a b :=
  (hg.mono (Set.Icc_subset_Icc h0 h3)).intervalIntegrable_of_Icc hab

/-- **The derivative of the gap functional is non-negative on `[0, ∞)`.**  Splitting at `τ` and
comparing with the weight frozen at `τ` exhibits `tf72fPhi' lam ≥ exp (lam τ) · tf72fPhi' 0`. -/
private lemma tf72fPhi_deriv_nonneg (lam : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam * t) * tf72fK t) := by
  have hG : ContinuousOn (fun t : ℝ => t * (Real.exp (lam * t) * tf72fK t))
      (Set.Icc (0:ℝ) (7/3)) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) tf72fK_contOn)
  have hH : ContinuousOn (fun t : ℝ => t * (Real.exp (lam * tf72fTau) * tf72fK t))
      (Set.Icc (0:ℝ) (7/3)) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) tf72fK_contOn)
  have iG1 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (lam * t) * tf72fK t))
      volume (0:ℝ) tf72fTau := tf72fIcc_integrable hG le_rfl tf72fTau_nonneg tf72fTau_le
  have iG2 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (lam * t) * tf72fK t))
      volume tf72fTau (7/3) := tf72fIcc_integrable hG tf72fTau_nonneg tf72fTau_le (by norm_num)
  have iH1 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (lam * tf72fTau) * tf72fK t))
      volume (0:ℝ) tf72fTau := tf72fIcc_integrable hH le_rfl tf72fTau_nonneg tf72fTau_le
  have iH2 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (lam * tf72fTau) * tf72fK t))
      volume tf72fTau (7/3) := tf72fIcc_integrable hH tf72fTau_nonneg tf72fTau_le (by norm_num)
  have e1 : (∫ t in (0:ℝ)..tf72fTau, t * (Real.exp (lam * tf72fTau) * tf72fK t))
      ≤ ∫ t in (0:ℝ)..tf72fTau, t * (Real.exp (lam * t) * tf72fK t) :=
    intervalIntegral.integral_mono_on tf72fTau_nonneg iH1 iG1
      (fun t ht => tf72fK_weight_le_left lam t hlam ht.1 ht.2)
  have e2 : (∫ t in tf72fTau..(7/3), t * (Real.exp (lam * tf72fTau) * tf72fK t))
      ≤ ∫ t in tf72fTau..(7/3), t * (Real.exp (lam * t) * tf72fK t) :=
    intervalIntegral.integral_mono_on tf72fTau_le iH2 iG2
      (fun t ht => tf72fK_weight_le_right lam t hlam ht.1)
  have hnum : 0 ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := tf72fK_t_moment_nonneg
  have hHval : (∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam * tf72fTau) * tf72fK t))
      = Real.exp (lam * tf72fTau) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) := by
    rw [show (∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam * tf72fTau) * tf72fK t))
        = ∫ t in (0:ℝ)..(7/3), Real.exp (lam * tf72fTau) * (t * tf72fK t) from by
      apply intervalIntegral.integral_congr
      intro t _
      ring]
    rw [intervalIntegral.integral_const_mul]
  calc 0 ≤ Real.exp (lam * tf72fTau) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) :=
        mul_nonneg (Real.exp_pos _).le hnum
    _ = (∫ t in (0:ℝ)..tf72fTau, t * (Real.exp (lam * tf72fTau) * tf72fK t))
          + ∫ t in tf72fTau..(7/3), t * (Real.exp (lam * tf72fTau) * tf72fK t) := by
        rw [intervalIntegral.integral_add_adjacent_intervals iH1 iH2, hHval]
    _ ≤ (∫ t in (0:ℝ)..tf72fTau, t * (Real.exp (lam * t) * tf72fK t))
          + ∫ t in tf72fTau..(7/3), t * (Real.exp (lam * t) * tf72fK t) := add_le_add e1 e2
    _ = ∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam * t) * tf72fK t) :=
        intervalIntegral.integral_add_adjacent_intervals iG1 iG2

/-! ## 3.  Monotonicity of the gap and the theorem -/

private lemma tf72fPhi_monotoneOn : MonotoneOn tf72fPhi (Set.Ici 0) := by
  have hdiff : ∀ x : ℝ, HasDerivAt tf72fPhi
      (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t)) x :=
    fun x => tf72fK_hasDerivAt x
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · intro x _
    exact (hdiff x).continuousAt.continuousWithinAt
  · intro x _
    exact ((hdiff x).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [(hdiff x).deriv]
    exact tf72fPhi_deriv_nonneg x (Set.mem_Ici.mp (interior_subset hx))

theorem tf72f_gap_mono :
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 792/1000 →
      (∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t)
      ≤ (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t) := by
  intro lam h0 h1
  have hL := tf72fL_eq_Phi lam
  have hR : (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t)
      = tf72fPhi (792/1000) := by
    have h := tf72fL_eq_Phi ((792/1000 : ℝ))
    have hexp : (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t)
        = (∫ t in (0:ℝ)..(7/3),
            Real.exp (-((6/7 - (792/1000:ℝ)) * t)) * tf72f (6/7) t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      have harg : -(57/875:ℝ) * t = -((6/7 - (792/1000:ℝ)) * t) := by ring_nf
      rw [harg]
    rw [hexp]
    simpa using h
  rw [hL, hR]
  exact tf72fPhi_monotoneOn (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (by norm_num)) h1

end Work.ZeroFreeTables
