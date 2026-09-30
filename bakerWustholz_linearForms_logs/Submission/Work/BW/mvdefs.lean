import Mathlib
import Submission.Work.BW.fejer_cos_sum_ge
import Submission.Work.BW.log_norm_exp_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions and elementary lemmas for the Blanksby–Montgomery mean value estimates

This module sets up the Fejér cosine sum `fejerT K θ` and the real Fourier series
`cosFourier ρ t = ∑' m, (ρ^m/m) cos(2πmt)` (which equals `-log ‖ρ e^{2πit} - 1‖` for
`0 ≤ ρ < 1`), together with the elementary positivity and identity lemmas used by the
proof of `Work.BW.mean_value_bounds`.
-/

namespace Work.BW

open Finset

/-- The Fejér weight `1 - k/(K+1)`. -/
noncomputable def fejerW (K k : ℕ) : ℝ := 1 - (k : ℝ) / (K + 1)

/-- The Fejér cosine sum `T_K(θ) = ∑_{k=1}^K (1 - k/(K+1)) cos(2πkθ)`. -/
noncomputable def fejerT (K : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, fejerW K k * Real.cos (2 * Real.pi * k * θ)

/-- The real Fourier series `∑_{m≥1} (ρ^m / m) cos(2πmt)`.  For `0 ≤ ρ < 1` it equals
`-log ‖ρ e^{2πit} - 1‖` (see `cosFourier_eq_log`). -/
noncomputable def cosFourier (ρ : ℝ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, (ρ^m / m) * Real.cos (2 * Real.pi * m * t)

/-- The Fejér cosine sum is bounded below by `-1/2` (Fejér kernel nonnegativity). -/
theorem fejerT_ge (K : ℕ) (θ : ℝ) : -(1/2 : ℝ) ≤ fejerT K θ := by
  simpa only [fejerT, fejerW] using fejer_cos_sum_ge K θ

theorem fejerW_nonneg {K k : ℕ} (hk : k ≤ K + 1) : 0 ≤ fejerW K k := by
  rw [fejerW]
  have h : (k:ℝ)/((K:ℝ)+1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (k:ℝ) ≤ ((K+1 : ℕ) : ℝ) := by exact_mod_cast hk
    simpa using this
  linarith

/-- `∑_{k=1}^K k = K(K+1)/2` over the reals. -/
theorem sum_Icc_cast_id (K : ℕ) : ∑ k ∈ Finset.Icc 1 K, (k:ℝ) = (K:ℝ)*((K:ℝ)+1)/2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K+1), ih]
    push_cast
    ring

/-- The Fejér sum at `0` is `K/2`. -/
theorem fejerT_zero (K : ℕ) : fejerT K 0 = (K:ℝ)/2 := by
  have h1 : fejerT K 0 = ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) := by
    simp only [fejerT, fejerW, mul_zero, Real.cos_zero, mul_one]
  rw [h1, Finset.sum_sub_distrib, ← Finset.sum_div, sum_Icc_cast_id,
      Finset.sum_const, Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hK : ((K:ℝ)+1) ≠ 0 := by positivity
  field_simp
  ring

/-- The Fejér cosine sum is bounded above by `K/2`. -/
theorem fejerT_le (K : ℕ) (θ : ℝ) : fejerT K θ ≤ (K:ℝ)/2 := by
  have h := fejerT_zero K
  rw [← h]
  simp only [fejerT, mul_zero, Real.cos_zero, mul_one]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ K + 1 := by
    have := Finset.mem_Icc.mp hk; omega
  calc fejerW K k * Real.cos (2*Real.pi*k*θ) ≤ fejerW K k * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (fejerW_nonneg hk')
      _ = fejerW K k := by ring

/-- `1 + T_K(a) + T_K(b) ≥ 0` for all `a b` (a rewrite of Fejér nonnegativity). -/
theorem fejer_quad_nonneg (K : ℕ) (a b : ℝ) : 0 ≤ 1 + fejerT K a + fejerT K b := by
  have ha := fejerT_ge K a; have hb := fejerT_ge K b; linarith

/-- On the diagonal: `1 + T_K(a) + T_K(0) ≥ (K+1)/2`. -/
theorem fejer_diag (K : ℕ) (a : ℝ) : ((K:ℝ)+1)/2 ≤ 1 + fejerT K a + fejerT K 0 := by
  have ha := fejerT_ge K a; rw [fejerT_zero] at *; linarith

/-- The product formula for the Fejér cosine sum:
`1 + 2∑_k w_k cos(2πkA)cos(2πkB) = 1 + T_K(A+B) + T_K(A-B)`. -/
theorem fejer_prod_cos (K : ℕ) (A B : ℝ) :
    1 + 2 * ∑ k ∈ Finset.Icc 1 K, fejerW K k * (Real.cos (2*Real.pi*k*A) * Real.cos (2*Real.pi*k*B))
      = 1 + fejerT K (A+B) + fejerT K (A-B) := by
  have key : 2 * ∑ k ∈ Finset.Icc 1 K, fejerW K k *
        (Real.cos (2*Real.pi*k*A) * Real.cos (2*Real.pi*k*B))
      = fejerT K (A+B) + fejerT K (A-B) := by
    simp only [fejerT]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hAB : (2:ℝ)*Real.pi*k*(A+B) = 2*Real.pi*k*A + 2*Real.pi*k*B := by ring
    have hAmB : (2:ℝ)*Real.pi*k*(A-B) = 2*Real.pi*k*A - 2*Real.pi*k*B := by ring
    rw [hAB, hAmB, Real.cos_add, Real.cos_sub]
    ring_nf
  rw [key]; ring

/-- The Fourier series `∑ (ρ^m/m) cos(2πmt)` is summable for `0 ≤ ρ < 1`. -/
theorem cosFourier_summable (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (t : ℝ) :
    Summable (fun m : ℕ => (ρ^m / m) * Real.cos (2 * Real.pi * m * t)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one h0 h1)
  intro m
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have h1m : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
    have hρm : 0 ≤ (ρ:ℝ)^m := pow_nonneg h0 m
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ρ:ℝ)^m / m)]
    calc (ρ:ℝ)^m / m * |Real.cos (2*Real.pi*m*t)| ≤ (ρ:ℝ)^m/m * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.abs_cos_le_one _
      _ = (ρ:ℝ)^m/m := by ring
      _ ≤ (ρ:ℝ)^m := by
          rw [div_le_iff₀ (by linarith)]; nlinarith [hρm, h1m]

/-- The series `∑ ρ^m/m` is summable for `0 ≤ ρ < 1`. -/
theorem summable_pow_div (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun m : ℕ => ρ^m / m) := by
  have h := cosFourier_summable ρ h0 h1 0
  refine h.congr ?_
  intro m
  simp [Real.cos_zero]

/-- `cosFourier ρ t = -log ‖ρ e^{2πit} - 1‖`. -/
theorem cosFourier_eq_log (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (t : ℝ) :
    cosFourier ρ t = - Real.log ‖(ρ:ℂ) * Complex.exp (Complex.I * ((2*Real.pi*t : ℝ) : ℂ)) - 1‖ := by
  have hsum := log_norm_exp_sub_one ρ h0 h1 (2*Real.pi*t)
  rw [hsum, neg_neg, cosFourier, Summable.tsum_eq_zero_add (cosFourier_summable ρ h0 h1 t)]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_mul, zero_add]
  apply tsum_congr; intro k
  have h : (2:ℝ)*Real.pi*↑(k+1)*t = ((k:ℝ)+1) * (2*Real.pi*t) := by push_cast; ring
  rw [h]; simp only [Nat.cast_add_one]

/-- `cosFourier ρ 0 = log (1/(1-ρ)) = -log(1-ρ)`. -/
theorem cosFourier_zero (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    cosFourier ρ 0 = Real.log (1 / (1 - ρ)) := by
  rw [cosFourier_eq_log ρ h0 h1 0]
  have hz : (ρ:ℂ) * Complex.exp (Complex.I * ((2*Real.pi*(0:ℝ) : ℝ) : ℂ)) - 1 = ((ρ-1:ℝ):ℂ) := by
    simp
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : ρ-1 < 0)]
  rw [Real.log_div (by norm_num) (by linarith : (1-ρ) ≠ 0), Real.log_one]
  ring_nf

end Work.BW
