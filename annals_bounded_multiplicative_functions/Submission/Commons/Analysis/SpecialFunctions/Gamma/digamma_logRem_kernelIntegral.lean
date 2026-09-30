import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Real Set MeasureTheory Filter
open scoped Real Topology

namespace Commons.Analysis.SpecialFunctions.Gamma

-- ============================================================
-- pointwise bounds for the kernel  K(t) = 1/(e^t-1) - 1/t + 1/2
-- ============================================================

private lemma exp_gt_one_of_pos {t : ℝ} (ht : 0 < t) : 1 < Real.exp t := by
  simpa using (Real.exp_strictMono ht)

private lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  linarith [exp_gt_one_of_pos ht]

private lemma exp_sub_one_ne_zero {t : ℝ} (ht : 0 < t) : Real.exp t - 1 ≠ 0 :=
  ne_of_gt (exp_sub_one_pos ht)

/-- If `f 0 = 0`, `f` continuous on `[0,∞)`, differentiable on `(0,∞)` with nonnegative
derivative there, then `f ≥ 0` on `[0,∞)`. -/
private lemma nonneg_of_zero_nonneg_deriv (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : DifferentiableOn ℝ f (Ioi 0))
    (hfder : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ deriv f x) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ f t := by
  intro t ht
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hfcont
      (by simpa [interior_Ici] using hfdiff)
      (by
        intro x hx
        have hx' : x ∈ Ioi (0 : ℝ) := by simpa [interior_Ici] using hx
        exact hfder x hx')
  have h0in : (0 : ℝ) ∈ Ici 0 := by simp
  have htin : t ∈ Ici 0 := ht
  have hle : f 0 ≤ f t := hmono h0in htin ht
  simpa [hf0] using hle

/-- derivative of `s ↦ s·e^s − 2·e^s + s + 2` is `s·e^s − e^s + 1`. -/
private lemma hasDerivAt_N (s : ℝ) :
    HasDerivAt (fun u : ℝ => u * Real.exp u - 2 * Real.exp u + u + 2)
      (s * Real.exp s - Real.exp s + 1) s := by
  have h_id : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
  have h_exp : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp s) s := Real.hasDerivAt_exp s
  have h_prod : HasDerivAt (fun u : ℝ => u * Real.exp u)
      (1 * Real.exp s + s * Real.exp s) s :=
    h_id.mul h_exp
  have h_neg2 : HasDerivAt (fun u : ℝ => 2 * Real.exp u) (2 * Real.exp s) s := by
    simpa using h_exp.const_mul (2 : ℝ)
  have h_aff : HasDerivAt (fun u : ℝ => u + 2) 1 s :=
    (hasDerivAt_id s).add_const (2 : ℝ)
  have hA : HasDerivAt (fun u : ℝ => u * Real.exp u - 2 * Real.exp u)
      ((1 * Real.exp s + s * Real.exp s) - 2 * Real.exp s) s :=
    h_prod.sub h_neg2
  have hT : HasDerivAt (fun u : ℝ => u * Real.exp u - 2 * Real.exp u + (u + 2))
      (((1 * Real.exp s + s * Real.exp s) - 2 * Real.exp s) + 1) s :=
    hA.add h_aff
  convert hT using 1 <;> ring

/-- derivative of `s ↦ s·e^s − e^s + 1` is `s·e^s`. -/
private lemma hasDerivAt_G (s : ℝ) :
    HasDerivAt (fun u : ℝ => (u * Real.exp u - Real.exp u) + 1) (s * Real.exp s) s := by
  have h_id : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
  have h_exp : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp s) s := Real.hasDerivAt_exp s
  have h_prod : HasDerivAt (fun u : ℝ => u * Real.exp u)
      (1 * Real.exp s + s * Real.exp s) s :=
    h_id.mul h_exp
  have hA : HasDerivAt (fun u : ℝ => u * Real.exp u - Real.exp u)
      ((1 * Real.exp s + s * Real.exp s) - Real.exp s) s :=
    h_prod.sub h_exp
  have hT : HasDerivAt (fun u : ℝ => (u * Real.exp u - Real.exp u) + 1)
      ((1 * Real.exp s + s * Real.exp s) - Real.exp s) s :=
    hA.add_const (1 : ℝ)
  convert hT using 1 <;> ring

/-- `s·e^s − e^s + 1 ≥ 0` for `s ≥ 0`. -/
private lemma G_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ t * Real.exp t - Real.exp t + 1 := by
  let G : ℝ → ℝ := fun s => s * Real.exp s - Real.exp s + 1
  apply nonneg_of_zero_nonneg_deriv G ?_ ?_ ?_ ?_ t ht
  · dsimp [G]
    norm_num
  · dsimp [G]
    fun_prop
  · dsimp [G]
    fun_prop
  · intro x hx
    dsimp [G]
    rw [(hasDerivAt_G x).deriv]
    have hxpos : 0 < x := hx
    exact mul_nonneg (le_of_lt hxpos) (Real.exp_nonneg x)

/-- `t·e^t − 2·e^t + t + 2 ≥ 0` for `t ≥ 0`. -/
private lemma N_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ t * Real.exp t - 2 * Real.exp t + t + 2 := by
  let N : ℝ → ℝ := fun s => s * Real.exp s - 2 * Real.exp s + s + 2
  apply nonneg_of_zero_nonneg_deriv N ?_ ?_ ?_ ?_ t ht
  · dsimp [N]
    norm_num
  · dsimp [N]
    fun_prop
  · dsimp [N]
    fun_prop
  · intro x hx
    dsimp [N]
    rw [(hasDerivAt_N x).deriv]
    exact G_nonneg x (le_of_lt hx)

/-- `K(t) ≥ 0` for `t > 0` where `K(t) = 1/(e^t-1) - 1/t + 1/2`. -/
private lemma kernel_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ 1 / (Real.exp t - 1) - 1 / t + 1 / 2 := by
  have hN : 0 ≤ t * Real.exp t - 2 * Real.exp t + t + 2 := N_nonneg t (le_of_lt ht)
  have hden : 0 < 2 * t * (Real.exp t - 1) :=
    mul_pos (mul_pos (by norm_num) ht) (exp_sub_one_pos ht)
  have hEq : (1 / (Real.exp t - 1) - 1 / t + 1 / 2) =
      (t * Real.exp t - 2 * Real.exp t + t + 2) / (2 * t * (Real.exp t - 1)) := by
    field_simp [ht.ne', exp_sub_one_ne_zero ht]
    ring
  rw [hEq]
  exact div_nonneg hN (le_of_lt hden)

/-- `e^t·(t²−6t+12) − (t²+6t+12) ≥ 0` for `t ≥ 0`. -/
private lemma psi_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
  let S : ℝ := ∑ i ∈ Finset.range 6, t ^ i / (i.factorial : ℝ)
  have hS : S = 1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 := by
    dsimp [S]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hSum : S ≤ Real.exp t := by
    dsimp [S]
    exact Real.sum_le_exp_of_nonneg ht 6
  have hA : 0 ≤ t ^ 2 - 6 * t + 12 := by
    have hsq : 0 ≤ (t - 3) ^ 2 := sq_nonneg (t - 3)
    nlinarith
  have hdiff1 : 0 ≤ (t ^ 2 - 6 * t + 12) * (Real.exp t - S) :=
    mul_nonneg hA (sub_nonneg.mpr hSum)
  have hquad : 0 ≤ t ^ 2 - t + 2 := by
    have hsq : 0 ≤ (t - 1 / 2) ^ 2 := sq_nonneg (t - 1 / 2)
    nlinarith
  have hRest : 0 ≤ (t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12) := by
    have hEq : (t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12) =
        t ^ 5 * (t ^ 2 - t + 2) / 120 := by
      rw [hS]
      ring
    rw [hEq]
    have hnum : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) :=
      mul_nonneg (pow_nonneg ht 5) hquad
    exact div_nonneg hnum (by norm_num)
  have hEqψ : Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) =
      (t ^ 2 - 6 * t + 12) * (Real.exp t - S) +
        ((t ^ 2 - 6 * t + 12) * S - (t ^ 2 + 6 * t + 12)) := by
    ring
  rw [hEqψ]
  exact add_nonneg hdiff1 hRest

/-- `K(t) ≤ t/12` for `t > 0`. -/
private lemma kernel_le_t_div_12 (t : ℝ) (ht : 0 < t) :
    1 / (Real.exp t - 1) - 1 / t + 1 / 2 ≤ t / 12 := by
  have hψ : 0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) :=
    psi_nonneg t (le_of_lt ht)
  have hden : 0 < 12 * t * (Real.exp t - 1) :=
    mul_pos (mul_pos (by norm_num) ht) (exp_sub_one_pos ht)
  have hEq : t / 12 - (1 / (Real.exp t - 1) - 1 / t + 1 / 2) =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) /
        (12 * t * (Real.exp t - 1)) := by
    field_simp [ht.ne', exp_sub_one_ne_zero ht]
    ring
  have hd : 0 ≤ t / 12 - (1 / (Real.exp t - 1) - 1 / t + 1 / 2) := by
    rw [hEq]
    exact div_nonneg hψ (le_of_lt hden)
  linarith

-- ============================================================
-- evaluation of ∫_0^∞ t·e^{−x·t} dt = 1/x²  and integrability
-- ============================================================

/-- `∫_0^∞ t·e^{−xt} dt = 1/x²` for `x > 0`. -/
private lemma integral_id_exp_neg_mul (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-x * t)) = 1 / x ^ 2 := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := x) (by norm_num) hx
  have hR : (1 / x) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.Gamma_two]
    rw [Real.rpow_two]
    field_simp [hx.ne']
  have hEqI : (∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t)) =
      (∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(x * t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change t * Real.exp (-x * t) = t ^ ((2 : ℝ) - 1) * Real.exp (-(x * t))
    have hpow : t ^ ((2 : ℝ) - 1) = t := by
      norm_num
    rw [hpow]
    congr 1
    ring
  calc
    (∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t))
        = ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(x * t)) := hEqI
    _ = (1 / x) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) := key
    _ = 1 / x ^ 2 := hR

/-- `t ↦ t·e^{−xt}` is integrable on `(0,∞)` for `x > 0`. -/
private lemma integrable_id_exp_neg_mul (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-x * t)) (Ioi (0 : ℝ)) := by
  refine Integrable.of_integral_ne_zero ?_
  change (∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-x * t)) ≠ 0
  rw [integral_id_exp_neg_mul x hx]
  positivity

/-- `t ↦ (t/12)·e^{−xt}` is integrable on `(0,∞)` for `x > 0`. -/
private lemma integrable_g (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t / 12) * Real.exp (-x * t)) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => t * Real.exp (-x * t)) (Ioi (0 : ℝ)) :=
    integrable_id_exp_neg_mul x hx
  have hcm : IntegrableOn (fun t : ℝ => (1 / 12) * (t * Real.exp (-x * t))) (Ioi (0 : ℝ)) := by
    exact Integrable.const_mul hbase (1 / 12)
  convert hcm using 1
  · ext t
    ring

-- ============================================================
-- main theorem
-- ============================================================

theorem digamma_logRem_kernelIntegral (x : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    (∫ t in Set.Ioi (0 : ℝ),
      (((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) *
        Real.exp (-x * t)) ≤ (1 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  let f : ℝ → ℝ := fun t => (1 / (Real.exp t - 1) - 1 / t + 1 / 2) * Real.exp (-x * t)
  let g : ℝ → ℝ := fun t => (t / 12) * Real.exp (-x * t)
  have hf_nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t := by
    intro t ht
    dsimp [f]
    exact mul_nonneg (kernel_nonneg t ht) (Real.exp_nonneg (-x * t))
  have hf_le_g : ∀ t ∈ Ioi (0 : ℝ), f t ≤ g t := by
    intro t ht
    dsimp [f, g]
    exact mul_le_mul_of_nonneg_right (kernel_le_t_div_12 t ht) (Real.exp_nonneg (-x * t))
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    dsimp [g]
    exact integrable_g x hxpos
  have hle1 : (∫ t in Ioi (0 : ℝ), f t) ≤ ∫ t in Ioi (0 : ℝ), g t := by
    exact setIntegral_mono_of_nonneg (s := Ioi (0 : ℝ)) hf_nonneg hf_le_g hg_int
  have hg_comp : (∫ t in Ioi (0 : ℝ), g t) =
      (1 / 12) * (∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t)) := by
    dsimp [g]
    rw [show (fun t : ℝ => (t / 12) * Real.exp (-x * t)) =
        fun t : ℝ => (1 / 12) * (t * Real.exp (-x * t)) by ext t; ring]
    rw [integral_const_mul]
  have hg_val : (∫ t in Ioi (0 : ℝ), g t) ≤ 1 / 2 := by
    rw [hg_comp, integral_id_exp_neg_mul x hxpos]
    have hx2 : (1 : ℝ) ≤ 6 * x ^ 2 := by nlinarith [hx]
    field_simp [hxpos.ne']
    nlinarith
  exact le_trans hle1 hg_val

end Commons.Analysis.SpecialFunctions.Gamma