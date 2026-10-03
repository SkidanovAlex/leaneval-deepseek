import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

open MeasureTheory
open scoped Pointwise

namespace Commons.Analysis.Fourier

/-- Integration by parts on the whole line for `cos`. -/
lemma integral_mul_cos_eq (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G)
    (l : ℝ) :
    ∫ s, G s * (l * Real.cos (l * s)) = - ∫ s, deriv G s * Real.sin (l * s) := by
  have hd : ∀ x, HasDerivAt G (deriv G x) x := fun x => (hG.differentiable_one x).hasDerivAt
  have hv : ∀ x, HasDerivAt (fun s => Real.sin (l * s)) (l * Real.cos (l * x)) x := by
    intro x
    have h := (Real.hasDerivAt_sin (l * x)).comp x (hasDerivAt_const_mul l (x := x))
    simpa [Function.comp_def, mul_comm] using h
  have hcont_v : Continuous (fun s : ℝ => l * Real.cos (l * s)) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hcont_s : Continuous (fun s : ℝ => Real.sin (l * s)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have huv' : Integrable (G * fun s => l * Real.cos (l * s)) :=
    (hG.continuous.mul hcont_v).integrable_of_hasCompactSupport
      (hc.mul_right (f' := fun s => l * Real.cos (l * s)))
  have hu'v : Integrable ((fun s => deriv G s) * fun s => Real.sin (l * s)) := by
    have hcg : Continuous (deriv G) := by
      have : ContDiff ℝ 0 (deriv G) := by
        have := ContDiff.deriv' (n := (0:ℕ)) hG
        simpa using this
      exact this.continuous
    exact (hcg.mul hcont_s).integrable_of_hasCompactSupport
      ((hc.deriv).mul_right (f' := fun s => Real.sin (l * s)))
  have huv : Integrable (G * fun s => Real.sin (l * s)) :=
    (hG.continuous.mul hcont_s).integrable_of_hasCompactSupport
      (hc.mul_right (f' := fun s => Real.sin (l * s)))
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := G) (v := fun s => Real.sin (l*s))
    (u' := fun s => deriv G s) (v' := fun s => l * Real.cos (l * s))
    (fun x _ => hd x) (fun x _ => hv x) huv' hu'v huv
  simpa using this

/-- Integration by parts on the whole line for `sin`. -/
lemma integral_mul_sin_eq (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G)
    (l : ℝ) :
    ∫ s, G s * (-(l * Real.sin (l * s))) = - ∫ s, deriv G s * Real.cos (l * s) := by
  have hd : ∀ x, HasDerivAt G (deriv G x) x := fun x => (hG.differentiable_one x).hasDerivAt
  have hv : ∀ x, HasDerivAt (fun s => Real.cos (l * s)) (-(l * Real.sin (l * x))) x := by
    intro x
    have h := (Real.hasDerivAt_cos (l * x)).comp x (hasDerivAt_const_mul l (x := x))
    simpa [Function.comp_def, mul_comm] using h
  have hcont_v : Continuous (fun s : ℝ => -(l * Real.sin (l * s))) :=
    (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).neg
  have hcont_s : Continuous (fun s : ℝ => Real.cos (l * s)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have huv' : Integrable (G * fun s => -(l * Real.sin (l * s))) :=
    (hG.continuous.mul hcont_v).integrable_of_hasCompactSupport
      (hc.mul_right (f' := fun s => -(l * Real.sin (l * s))))
  have hu'v : Integrable ((fun s => deriv G s) * fun s => Real.cos (l * s)) := by
    have hcg : Continuous (deriv G) := by
      have : ContDiff ℝ 0 (deriv G) := by
        have := ContDiff.deriv' (n := (0:ℕ)) hG
        simpa using this
      exact this.continuous
    exact (hcg.mul hcont_s).integrable_of_hasCompactSupport
      ((hc.deriv).mul_right (f' := fun s => Real.cos (l * s)))
  have huv : Integrable (G * fun s => Real.cos (l * s)) :=
    (hG.continuous.mul hcont_s).integrable_of_hasCompactSupport
      (hc.mul_right (f' := fun s => Real.cos (l * s)))
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := G) (v := fun s => Real.cos (l*s))
    (u' := fun s => deriv G s) (v' := fun s => -(l * Real.sin (l * s)))
    (fun x _ => hd x) (fun x _ => hv x) huv' hu'v huv
  simpa using this

private def P (K : ℕ) : Prop :=
  ∀ G : ℝ → ℝ, ContDiff ℝ K G → HasCompactSupport G → ∀ l : ℝ, 0 < l →
    |∫ s, G s * Real.cos (l * s)| ≤ (l⁻¹)^K * ∫ s, |iteratedDeriv K G s|

private def Q (K : ℕ) : Prop :=
  ∀ G : ℝ → ℝ, ContDiff ℝ K G → HasCompactSupport G → ∀ l : ℝ, 0 < l →
    |∫ s, G s * Real.sin (l * s)| ≤ (l⁻¹)^K * ∫ s, |iteratedDeriv K G s|

private lemma base_cos : P 0 := by
  intro G hG hc l hl
  have hIG : Integrable G := hG.continuous.integrable_of_hasCompactSupport hc
  have hcontc : Continuous (fun s : ℝ => G s * Real.cos (l*s)) :=
    hG.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hIc : Integrable (fun s : ℝ => G s * Real.cos (l*s)) :=
    hcontc.integrable_of_hasCompactSupport (hc.mul_right (f' := fun s => Real.cos (l*s)))
  calc |∫ s, G s * Real.cos (l*s)| ≤ ∫ s, |G s * Real.cos (l*s)| := abs_integral_le_integral_abs
    _ ≤ ∫ s, |G s| := integral_mono hIc.abs hIG.abs (fun s => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    _ = (l⁻¹)^0 * ∫ s, |iteratedDeriv 0 G s| := by rw [iteratedDeriv_zero, pow_zero, one_mul]

private lemma base_sin : Q 0 := by
  intro G hG hc l hl
  have hIG : Integrable G := hG.continuous.integrable_of_hasCompactSupport hc
  have hconts : Continuous (fun s : ℝ => G s * Real.sin (l*s)) :=
    hG.continuous.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hIs : Integrable (fun s : ℝ => G s * Real.sin (l*s)) :=
    hconts.integrable_of_hasCompactSupport (hc.mul_right (f' := fun s => Real.sin (l*s)))
  calc |∫ s, G s * Real.sin (l*s)| ≤ ∫ s, |G s * Real.sin (l*s)| := abs_integral_le_integral_abs
    _ ≤ ∫ s, |G s| := integral_mono hIs.abs hIG.abs (fun s => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    _ = (l⁻¹)^0 * ∫ s, |iteratedDeriv 0 G s| := by rw [iteratedDeriv_zero, pow_zero, one_mul]

private lemma step_cos (K : ℕ) (hsin : Q K) : P (K+1) := by
  intro G hG hc l hl
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hkey := integral_mul_cos_eq G hG1 hc l
  have hcontc : Continuous (fun s : ℝ => G s * Real.cos (l*s)) :=
    hG.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hIc : Integrable (fun s : ℝ => G s * Real.cos (l*s)) :=
    hcontc.integrable_of_hasCompactSupport (hc.mul_right (f' := fun s => Real.cos (l*s)))
  have hrew : ∫ s, G s * (l * Real.cos (l*s)) = l * ∫ s, G s * Real.cos (l*s) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    ring
  have hkey2 : l * (∫ s, G s * Real.cos (l*s)) = - ∫ s, deriv G s * Real.sin (l*s) := by
    rw [← hrew]; exact hkey
  have hGd : ContDiff ℝ K (deriv G) := by
    have := ContDiff.deriv' (n := K) hG
    simpa using this
  have hcd : HasCompactSupport (deriv G) := hc.deriv
  have ihb := hsin (deriv G) hGd hcd l hl
  have hlne : l ≠ 0 := ne_of_gt hl
  have hA : (∫ s, G s * Real.cos (l*s)) = - l⁻¹ * ∫ s, deriv G s * Real.sin (l*s) := by
    rw [← inv_mul_cancel_left₀ hlne (∫ s, G s * Real.cos (l*s)), hkey2]
    ring
  have hInt_obj : |∫ s, G s * Real.cos (l*s)| = l⁻¹ * |∫ s, deriv G s * Real.sin (l*s)| := by
    rw [hA, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hl)]
  calc |∫ s, G s * Real.cos (l*s)| = l⁻¹ * |∫ s, deriv G s * Real.sin (l*s)| := hInt_obj
    _ ≤ l⁻¹ * ((l⁻¹)^K * ∫ s, |iteratedDeriv K (deriv G) s|) :=
        mul_le_mul_of_nonneg_left ihb (le_of_lt (inv_pos.mpr hl))
    _ = (l⁻¹)^(K+1) * ∫ s, |iteratedDeriv (K+1) G s| := by
        rw [pow_succ, iteratedDeriv_succ']
        ring

private lemma step_sin (K : ℕ) (hcos : P K) : Q (K+1) := by
  intro G hG hc l hl
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hkey := integral_mul_sin_eq G hG1 hc l
  have hconts : Continuous (fun s : ℝ => G s * Real.sin (l*s)) :=
    hG.continuous.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hIs : Integrable (fun s : ℝ => G s * Real.sin (l*s)) :=
    hconts.integrable_of_hasCompactSupport (hc.mul_right (f' := fun s => Real.sin (l*s)))
  have hrew : ∫ s, G s * (-(l * Real.sin (l*s))) = -(l * ∫ s, G s * Real.sin (l*s)) := by
    rw [show (fun s => G s * (-(l * Real.sin (l*s)))) = (fun s => -(l * (G s * Real.sin (l*s)))) by
      ext s; ring]
    rw [integral_neg, integral_const_mul]
  have hkey2 : -(l * (∫ s, G s * Real.sin (l*s))) = - ∫ s, deriv G s * Real.cos (l*s) := by
    rw [← hrew]; exact hkey
  have hkey3 : l * (∫ s, G s * Real.sin (l*s)) = ∫ s, deriv G s * Real.cos (l*s) := by
    have := hkey2; linarith
  have hGd : ContDiff ℝ K (deriv G) := by
    have := ContDiff.deriv' (n := K) hG
    simpa using this
  have hcd : HasCompactSupport (deriv G) := hc.deriv
  have ihb := hcos (deriv G) hGd hcd l hl
  have hlne : l ≠ 0 := ne_of_gt hl
  have hA : (∫ s, G s * Real.sin (l*s)) = l⁻¹ * ∫ s, deriv G s * Real.cos (l*s) := by
    rw [← inv_mul_cancel_left₀ hlne (∫ s, G s * Real.sin (l*s)), hkey3]
  have hInt_obj : |∫ s, G s * Real.sin (l*s)| = l⁻¹ * |∫ s, deriv G s * Real.cos (l*s)| := by
    rw [hA, abs_mul, abs_of_pos (inv_pos.mpr hl)]
  calc |∫ s, G s * Real.sin (l*s)| = l⁻¹ * |∫ s, deriv G s * Real.cos (l*s)| := hInt_obj
    _ ≤ l⁻¹ * ((l⁻¹)^K * ∫ s, |iteratedDeriv K (deriv G) s|) :=
        mul_le_mul_of_nonneg_left ihb (le_of_lt (inv_pos.mpr hl))
    _ = (l⁻¹)^(K+1) * ∫ s, |iteratedDeriv (K+1) G s| := by
        rw [pow_succ, iteratedDeriv_succ']
        ring

private theorem decay_aux (K : ℕ) : P K ∧ Q K := by
  induction K with
  | zero => exact ⟨base_cos, base_sin⟩
  | succ K ih => exact ⟨step_cos K ih.2, step_sin K ih.1⟩

/-- The full-line cos decay estimate. -/
theorem fourier_cos_decay (K : ℕ) (G : ℝ → ℝ) (hG : ContDiff ℝ K G) (hc : HasCompactSupport G)
    (l : ℝ) (hl : 0 < l) :
    |∫ s, G s * Real.cos (l * s)| ≤ (l⁻¹)^K * ∫ s, |iteratedDeriv K G s| :=
  (decay_aux K).1 G hG hc l hl

/-- The full-line sin decay estimate. -/
theorem fourier_sin_decay (K : ℕ) (G : ℝ → ℝ) (hG : ContDiff ℝ K G) (hc : HasCompactSupport G)
    (l : ℝ) (hl : 0 < l) :
    |∫ s, G s * Real.sin (l * s)| ≤ (l⁻¹)^K * ∫ s, |iteratedDeriv K G s| :=
  (decay_aux K).2 G hG hc l hl

/-! ### Quadratic chain rule bound -/

lemma quad_deriv_one (x b : ℝ) :
    iteratedDeriv 1 (fun s : ℝ => x * s^2 + b^2) = fun s => 2 * x * s := by
  rw [iteratedDeriv_succ, iteratedDeriv_zero]
  ext s
  have h1 : HasDerivAt (fun t : ℝ => x * t^2) (2 * x * s) s := by
    have hh := (hasDerivAt_pow 2 s).const_mul x
    simpa [mul_assoc, mul_comm, mul_left_comm] using hh
  have h2 : HasDerivAt (fun t : ℝ => b^2) 0 s := hasDerivAt_const s (b^2)
  have hsum : HasDerivAt ((fun t : ℝ => x * t^2) + (fun t : ℝ => b^2)) (2 * x * s) s := by
    simpa using h1.add h2
  rw [show (fun t : ℝ => x * t^2 + b^2) = (fun t : ℝ => x * t^2) + (fun t : ℝ => b^2) by
    ext t; simp]
  exact hsum.deriv

lemma quad_deriv_two (x b : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => x * s^2 + b^2) = fun _ => 2 * x := by
  rw [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, quad_deriv_one]
  ext s
  have h : HasDerivAt (fun s : ℝ => 2 * x * s) (2 * x) s := by
    simpa using hasDerivAt_const_mul (2 * x) (x := s)
  exact h.deriv

lemma quad_deriv_three (x b : ℝ) :
    iteratedDeriv 3 (fun s : ℝ => x * s^2 + b^2) = 0 := by
  rw [show (3:ℕ) = 2+1 from rfl, iteratedDeriv_succ, quad_deriv_two]
  ext s
  simp [deriv_const]

lemma quad_deriv_ge_three (x b : ℝ) :
    ∀ k, iteratedDeriv (k+3) (fun s : ℝ => x * s^2 + b^2) = 0
  | 0 => quad_deriv_three x b
  | k+1 => by
      have ih := quad_deriv_ge_three x b k
      have hk : (k+1+3 : ℕ) = (k+3)+1 := by ring
      rw [hk, iteratedDeriv_succ, ih]
      ext s; simp

lemma quad_iteratedDeriv_bound (x b : ℝ) (hx : 0 < x) (s : ℝ)
    (hs : x * s^2 + b^2 ≤ x) :
    ∀ m : ℕ, |iteratedDeriv m (fun s : ℝ => x * s^2 + b^2) s| ≤ 2 * x := by
  have hs2 : s^2 ≤ 1 := by nlinarith [sq_nonneg b, hx]
  have hs1 : |s| ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  intro m
  match m with
  | 0 =>
      simp only [iteratedDeriv_zero]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hx.le]
  | 1 =>
      rw [quad_deriv_one]
      simp only
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hx.le]
      nlinarith [hs1, hx.le]
  | 2 =>
      rw [quad_deriv_two]
      simp only
      rw [abs_of_nonneg (by positivity)]
  | k+3 =>
      rw [quad_deriv_ge_three]
      simp only [Pi.zero_apply, abs_zero]
      nlinarith [hx.le]

lemma iteratedDeriv_comp_quad_bound
    (K : ℕ) (x y b : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ K f)
    (hbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ (y ^ j)⁻¹)
    (i : ℕ) (hi : i ≤ K) (s : ℝ) (hs : x * s^2 + b^2 ∈ Set.Icc 0 x) :
    |iteratedDeriv i (fun s => f (x * s^2 + b^2)) s| ≤
      (Fintype.card (OrderedFinpartition i) : ℝ) * (2 * x / y)^i := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hquad_bound : ∀ m, |iteratedDeriv m (fun t : ℝ => x * t^2 + b^2) s| ≤ 2*x :=
    quad_iteratedDeriv_bound x b hx0 s hs.2
  have hcontq : ContDiff ℝ (K : WithTop ℕ∞) (fun t : ℝ => x * t^2 + b^2) := by fun_prop
  have hcomp := iteratedDeriv_comp_eq_sum_orderedFinpartition
      (g := f) (f := fun t : ℝ => x * t^2 + b^2) (x := s)
      (hg := hf.contDiffAt) (hf := hcontq.contDiffAt) (hi := Nat.cast_le.mpr hi)
  rw [show iteratedDeriv i (fun s => f (x * s^2 + b^2)) s
        = iteratedDeriv i (f ∘ fun t : ℝ => x * t^2 + b^2) s from rfl, hcomp]
  have hle_div : (1:ℝ) ≤ 2 * x / y := by rw [le_div_iff₀ hy0]; nlinarith
  calc |∑ c : OrderedFinpartition i,
          iteratedDeriv c.length f (x * s^2 + b^2) * ∏ j, iteratedDeriv (c.partSize j) (fun t : ℝ => x * t^2 + b^2) s|
      ≤ ∑ c : OrderedFinpartition i,
          |iteratedDeriv c.length f (x * s^2 + b^2) * ∏ j, iteratedDeriv (c.partSize j) (fun t : ℝ => x * t^2 + b^2) s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : OrderedFinpartition i,
          |iteratedDeriv c.length f (x * s^2 + b^2)| * ∏ j, |iteratedDeriv (c.partSize j) (fun t : ℝ => x * t^2 + b^2) s| := by
        apply Finset.sum_congr rfl; intro c _
        rw [abs_mul, Finset.abs_prod]
    _ ≤ ∑ c : OrderedFinpartition i, (y ^ c.length)⁻¹ * (2 * x)^c.length := by
        apply Finset.sum_le_sum; intro c _
        have h1 : |iteratedDeriv c.length f (x * s^2 + b^2)| ≤ (y ^ c.length)⁻¹ :=
          hbd c.length (le_trans c.length_le hi) (x * s^2 + b^2) hs
        have h2 : ∏ j, |iteratedDeriv (c.partSize j) (fun t : ℝ => x * t^2 + b^2) s| ≤ (2 * x)^c.length := by
          calc ∏ j, |iteratedDeriv (c.partSize j) (fun t : ℝ => x * t^2 + b^2) s|
              ≤ ∏ _j : Fin c.length, (2 * x) :=
                Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hquad_bound (c.partSize j))
            _ = (2 * x)^c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul h1 h2 (Finset.prod_nonneg (fun j _ => abs_nonneg _)) (by positivity)
    _ ≤ ∑ _c : OrderedFinpartition i, (2 * x / y)^i := by
        apply Finset.sum_le_sum; intro c _
        have heq : (y ^ c.length)⁻¹ * (2 * x)^c.length = (2 * x / y)^c.length := by
          rw [div_pow, div_eq_mul_inv, mul_comm]
        rw [heq]
        exact pow_le_pow_right₀ hle_div c.length_le
    _ = (Fintype.card (OrderedFinpartition i) : ℝ) * (2 * x / y)^i := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]




/-- The half-line integral of an even function equals half the whole-line integral. -/
lemma integral_Ici_zero_eq_half_of_even (g : ℝ → ℝ) (hg : ∀ s, g (-s) = g s) :
    ∫ s in Set.Ici (0:ℝ), g s = (1/2) * ∫ s, g s := by
  have h1 : ∫ s : ℝ, g |s| = 2 * ∫ s in Set.Ioi (0:ℝ), g s := integral_comp_abs
  have h2 : ∫ s : ℝ, g |s| = ∫ s : ℝ, g s := by
    apply integral_congr_ae
    filter_upwards with s
    rcases lt_or_ge (0:ℝ) s with h | h
    · rw [abs_of_pos h]
    · rw [abs_of_nonpos h, hg s]
  rw [h2] at h1
  have h3 : ∫ s in Set.Ioi (0:ℝ), g s = ∫ s in Set.Ici (0:ℝ), g s :=
    (MeasureTheory.integral_Ici_eq_integral_Ioi).symm
  rw [h3] at h1
  linarith

lemma integral_Ici_comp_mul_right_pos (h : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ici (0:ℝ), h t = r * ∫ s in Set.Ici (0:ℝ), h (r * s) := by
  have hsmul : r • (Set.Ici (0:ℝ)) = Set.Ici 0 := by
    ext y
    simp only [Set.mem_smul_set, Set.mem_Ici]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_nonneg hr.le hz
    · intro hy
      exact ⟨y / r, div_nonneg hy hr.le, by rw [smul_eq_mul]; field_simp⟩
  have hkey := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (volume : Measure ℝ) h (Set.Ici (0:ℝ)) hr
  rw [hsmul, Module.finrank_self, pow_one] at hkey
  simp only [smul_eq_mul] at hkey
  have : r * ∫ s in Set.Ici (0:ℝ), h (r * s) = ∫ s in Set.Ici (0:ℝ), h s := by
    rw [hkey, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  exact this.symm

lemma iteratedDeriv_quad_comp_eq_zero_of_gt (K : ℕ) (x b : ℝ) (f : ℝ → ℝ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 x → f u = 0) (s : ℝ) (hs : x * s^2 + b^2 > x) :
    iteratedDeriv K (fun s => f (x * s^2 + b^2)) s = 0 := by
  have hcont : Continuous (fun t : ℝ => x * t^2 + b^2) := by fun_prop
  have hU : IsOpen {t : ℝ | x * t^2 + b^2 > x} := hcont.isOpen_preimage _ isOpen_Ioi
  have hEq : Set.EqOn (fun s => f (x * s^2 + b^2)) (fun _ => (0:ℝ)) {t | x * t^2 + b^2 > x} := by
    intro t ht
    exact hsupp _ (fun hmem => absurd hmem.2 (not_le.mpr ht))
  have h := (hEq.iteratedDeriv_of_isOpen hU K) hs
  rw [h]
  simp

lemma iteratedDeriv_quad_comp_le (K : ℕ) (x y b : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ K f)
    (hbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ (y ^ j)⁻¹)
    (hsupp : ∀ u, u ∉ Set.Icc 0 x → f u = 0) (s : ℝ) :
    |iteratedDeriv K (fun s => f (x * s^2 + b^2)) s| ≤
      (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  by_cases h : x * s^2 + b^2 ≤ x
  · have hmem : x * s^2 + b^2 ∈ Set.Icc 0 x := ⟨by nlinarith [sq_nonneg s, sq_nonneg b, hx], h⟩
    exact iteratedDeriv_comp_quad_bound K x y b hx hy hyx f hf hbd K le_rfl s hmem
  · rw [iteratedDeriv_quad_comp_eq_zero_of_gt K x b f hsupp s (not_le.mp h), abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by nlinarith [hx0]) hy0.le) K)


lemma algebra_key (K : ℕ) (x y c r : ℝ) (hr2 : r^2 = x) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r) :
    r * ((c*r)⁻¹)^K * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2*x/y)^K)
      = ((Fintype.card (OrderedFinpartition K) : ℝ) * 2^K) * (r * (r/(c*y))^K) := by
  have hpow : ((c*r)⁻¹)^K * (2*x/y)^K = (2 * (r/(c*y)))^K := by
    rw [← mul_pow]
    congr 1
    rw [← hr2]
    field_simp [hc.ne', hy.ne', hr.ne']
  calc r * ((c*r)⁻¹)^K * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2*x/y)^K)
      = r * (Fintype.card (OrderedFinpartition K) : ℝ) * (((c*r)⁻¹)^K * (2*x/y)^K) := by ring
    _ = r * (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * (r/(c*y)))^K := by rw [hpow]
    _ = ((Fintype.card (OrderedFinpartition K) : ℝ) * 2^K) * (r * (r/(c*y))^K) := by
        rw [mul_pow]; ring

theorem fourier_integral_decay (K : ℕ) (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ K f) (hsupp : ∀ u, u ∉ Set.Icc 0 x → f u = 0)
    (hbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ (y ^ j)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ c b : ℝ, 0 < c → b ^ 2 ≤ x →
      |∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (c * t)| ≤
        C * Real.sqrt x * (Real.sqrt x / (c * y)) ^ K := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  refine ⟨((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K, by positivity, ?_⟩
  intro c b hc hb2
  let r : ℝ := Real.sqrt x
  have hr0 : 0 < r := by
    change 0 < Real.sqrt x
    exact Real.sqrt_pos.mpr hx0
  have hr2 : r^2 = x := by
    change (Real.sqrt x)^2 = x
    exact Real.sq_sqrt hx0.le
  let l : ℝ := c * r
  have hl0 : 0 < l := by
    change 0 < c * r
    positivity
  let F : ℝ → ℝ := fun s => f (x * s^2 + b^2)
  have hFcd : ContDiff ℝ K F := by
    change ContDiff ℝ K (fun s : ℝ => f (x * s^2 + b^2))
    have hq : ContDiff ℝ (K : WithTop ℕ∞) (fun s : ℝ => x * s^2 + b^2) := by fun_prop
    have := hf.comp hq
    simpa [Function.comp_def] using this
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    rw [Function.support_subset_iff]
    intro s hs
    have hu : x * s^2 + b^2 ∈ Set.Icc 0 x := by
      by_contra h
      exact hs (hsupp _ h)
    have hs2 : s^2 ≤ 1 := by nlinarith [hu.2, sq_nonneg b, hx0]
    have hsabs : |s| ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
    simpa only [Set.mem_Icc] using (abs_le.mp hsabs)
  -- substitution t = r * s
  have key1 : (∫ t in Set.Ici (0:ℝ), f (t^2 + b^2) * Real.cos (c*t))
      = r * ∫ s in Set.Ici (0:ℝ), F s * Real.cos (l*s) := by
    rw [integral_Ici_comp_mul_right_pos (r := r)
        (fun t : ℝ => f (t^2 + b^2) * Real.cos (c*t)) hr0]
    congr 1
    apply integral_congr_ae
    filter_upwards with s
    change f ((r*s)^2 + b^2) * Real.cos (c*(r*s)) = f (x*s^2+b^2) * Real.cos ((c*r)*s)
    rw [show (r*s)^2 = r^2 * s^2 by ring, hr2, show c*(r*s) = (c*r)*s by ring]
  -- evenness
  have heven : ∀ s, (fun s => F s * Real.cos (l*s)) (-s) = (fun s => F s * Real.cos (l*s)) s := by
    intro s
    change f (x * (-s)^2 + b^2) * Real.cos ((c*r) * (-s)) = f (x * s^2 + b^2) * Real.cos ((c*r) * s)
    rw [show x * (-s)^2 + b^2 = x * s^2 + b^2 by ring,
        show (c*r) * (-s) = -((c*r) * s) by ring, Real.cos_neg]
  have key2 : ∫ s in Set.Ici (0:ℝ), F s * Real.cos (l*s) = (1/2) * ∫ s, F s * Real.cos (l*s) :=
    integral_Ici_zero_eq_half_of_even _ heven
  -- vanishing outside the support
  have hzero : ∀ s, x * s^2 + b^2 > x → iteratedDeriv K F s = 0 := by
    intro s hs
    change iteratedDeriv K (fun s : ℝ => f (x*s^2+b^2)) s = 0
    exact iteratedDeriv_quad_comp_eq_zero_of_gt K x b f hsupp s hs
  have hsuppK : ∀ s, s ∉ Set.Icc (-1:ℝ) 1 → |iteratedDeriv K F s| = 0 := by
    intro s hs
    have hs' : (1:ℝ) < |s| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hsq : 1 < s^2 := by nlinarith [sq_abs s, abs_nonneg s]
    have hgt : x * s^2 + b^2 > x := by nlinarith [hsq, hx0, sq_nonneg b]
    rw [hzero s hgt, abs_zero]
  -- bound on the L1 norm of the K-th derivative
  have hC0nn : 0 ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by linarith [hx0]) hy0.le) K)
  have hint : ∫ s, |iteratedDeriv K F s| ≤ 2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by
    have hbnd : ∀ s ∈ Set.Icc (-1:ℝ) 1,
        |iteratedDeriv K F s| ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K := by
      intro s _
      change |iteratedDeriv K (fun s : ℝ => f (x*s^2+b^2)) s| ≤ _
      exact iteratedDeriv_quad_comp_le K x y b hx hy hyx f hf hbd hsupp s
    have hnle : ‖∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s|‖
        ≤ ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K)
            * volume.real (Set.Icc (-1:ℝ) 1) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
        isCompact_Icc.measure_lt_top
        (fun s hs => by rw [Real.norm_eq_abs, abs_abs]; exact hbnd s hs)
    have hnn : 0 ≤ ∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s| :=
      setIntegral_nonneg measurableSet_Icc (fun s _ => abs_nonneg _)
    calc ∫ s, |iteratedDeriv K F s|
        = ∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s| :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hsuppK).symm
      _ = ‖∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s|‖ := (Real.norm_of_nonneg hnn).symm
      _ ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K * volume.real (Set.Icc (-1:ℝ) 1) := hnle
      _ = 2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by
          rw [Real.volume_real_Icc]; norm_num; ring
  have hPF := fourier_cos_decay K F hFcd hFc l hl0
  rw [key1, abs_mul, abs_of_pos hr0, key2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < (1:ℝ)/2)]
  calc r * ((1/2) * |∫ s, F s * Real.cos (l*s)|)
      ≤ r * ((1/2) * ((l⁻¹)^K * (2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K)))) := by
        apply mul_le_mul_of_nonneg_left _ hr0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact le_trans hPF (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = r * (l⁻¹)^K * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by ring
    _ = ((Fintype.card (OrderedFinpartition K) : ℝ) * 2^K) * (r * (r/(c*y))^K) := by
        rw [show l = c * r from rfl]
        exact algebra_key K x y c r hr2 hc hy0 hr0
    _ ≤ (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * (r * (r/(c*y))^K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        · positivity
    _ = (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * Real.sqrt x * (Real.sqrt x / (c*y))^K := by
        change _ = (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * r * (r/(c*y))^K
        ring

end Commons.Analysis.Fourier