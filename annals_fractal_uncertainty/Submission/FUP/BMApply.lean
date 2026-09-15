import Submission.FUP.Spec
import Submission.FUP.WeightGrowth
import Submission.FUP.Assembly
import Submission.FUP.GrowthSum
import Submission.Commons.Measure.Real.integrableOn_log_rpow_decay

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# From the higher-dimensional Beurling–Malliavin theorem to damping functions (§6.1)

This module proves Cohen's `prop:existence_damping` **assuming** his higher-dimensional
Beurling–Malliavin theorem (`thm:higher_dim_BM`, recorded in `Submission.FUP.Spec`) in the form
that includes the `⟨x⟩^{-d}` bound coming from multiplying the BM output by a fixed Schwartz
function.

The weight `ω` of §6.1 (constructed in `WeightSum`, `WeightReg`, `WeightGrowth`) is checked to
satisfy the hypotheses of BM with constants that depend only on `ν`, `μ` and `d` (and neither on
the set `Y` nor on the reciprocal scale `h⁻¹`).  The output is rescaled to produce an `ℓ₂`
damping function with parameters `c₁ = σ`, `c₂ = c₂f σ`, `c₃ = c₃f σ` and the exponent `α` of
the weight.
-/

section Parameters

/-- The fixed exponent `s = 1/5` of the weight construction. -/
noncomputable def sExp : ℝ := 1/5

lemma sExp_pos : 0 < sExp := by norm_num [sExp]

lemma three_sExp_lt_one : 3 * sExp < 1 := by norm_num [sExp]

/-- The index `K` at which the sum defining `ω` is truncated: at least `k₀` and at least the
dyadic scale of `12√d·h⁻¹`. -/
noncomputable def Kfun (k₀ : ℕ) (h : ℝ) : ℕ := max k₀ ⌈12 * Real.sqrt (d:ℝ) * h⁻¹⌉₊

lemma le_Kfun (k₀ : ℕ) (h : ℝ) : k₀ ≤ Kfun (d := d) k₀ h := le_max_left _ _

lemma lt_Kfun (k₀ : ℕ) (h : ℝ) :
    12 * Real.sqrt (d:ℝ) * h⁻¹ ≤ (Kfun (d := d) k₀ h : ℝ) := by
  have h1 : 12 * Real.sqrt (d:ℝ) * h⁻¹ ≤ (⌈12 * Real.sqrt (d:ℝ) * h⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  exact h1.trans (by exact_mod_cast le_max_right k₀ ⌈12 * Real.sqrt (d:ℝ) * h⁻¹⌉₊)

/-- There is an index `k` beyond which the two conditions `A ≤ k^s` and `B ≤ 2^k / k^s` hold
(for `s ∈ (0,1)` and `A, B ≥ 0`). -/
lemma exists_parameter {s A B : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ k : ℕ, 8 ≤ k ∧ A ≤ (k:ℝ)^s ∧ B ≤ (2:ℝ)^k / (k:ℝ)^s := by
  have hs1' : 0 < 1 - s := by linarith
  set k : ℕ := max 8 (max ⌈A ^ (1/s)⌉₊ ⌈B ^ (1/(1-s))⌉₊) with hk
  have hk8 : 8 ≤ k := le_max_left _ _
  have hkA : (⌈A ^ (1/s)⌉₊ : ℝ) ≤ (k:ℝ) := by
    rw [hk]; exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
  have hkB : (⌈B ^ (1/(1-s))⌉₊ : ℝ) ≤ (k:ℝ) := by
    rw [hk]; exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by
    have : (1:ℕ) ≤ k := le_trans (by norm_num) hk8
    exact_mod_cast this
  have hk0 : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le one_pos hk1
  have hkpow : (k:ℝ) ≤ (2:ℝ)^k := by
    have : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
    exact_mod_cast this
  refine ⟨k, hk8, ?_, ?_⟩
  · have h1 : A ^ (1/s) ≤ (k:ℝ) := (Nat.le_ceil _).trans hkA
    calc A = (A ^ (1/s)) ^ s := by
          rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ (ne_of_gt hs0), Real.rpow_one]
      _ ≤ (k:ℝ) ^ s := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h1 hs0.le
  · have h3 : B ≤ (k:ℝ) ^ (1 - s) := by
      have h1 : B ^ (1/(1-s)) ≤ (k:ℝ) := (Nat.le_ceil _).trans hkB
      calc B = (B ^ (1/(1-s))) ^ (1-s) := by
            rw [← Real.rpow_mul hB, one_div, inv_mul_cancel₀ (ne_of_gt hs1'), Real.rpow_one]
        _ ≤ (k:ℝ) ^ (1 - s) := Real.rpow_le_rpow (Real.rpow_nonneg hB _) h1 hs1'.le
    have hpow : ((2:ℝ)^k : ℝ) = (2:ℝ)^((k:ℝ)) := (Real.rpow_natCast 2 k).symm
    have hks : (k:ℝ) ^ s ≤ (2:ℝ) ^ ((k:ℝ) * s) := by
      calc (k:ℝ)^s ≤ ((2:ℝ)^k)^s := Real.rpow_le_rpow (le_of_lt hk0) hkpow hs0.le
        _ = (2:ℝ)^((k:ℝ) * s) := by
            rw [hpow]
            exact (Real.rpow_mul (by norm_num) (k:ℝ) s).symm
    calc B ≤ (k:ℝ) ^ (1 - s) := h3
      _ ≤ ((2:ℝ)^k) ^ (1 - s) :=
          Real.rpow_le_rpow (show (0:ℝ) ≤ (k:ℝ) by positivity) hkpow hs1'.le
      _ = ((2:ℝ)^((k:ℝ))) ^ (1 - s) := by rw [hpow]
      _ = (2:ℝ) ^ ((k:ℝ) * (1 - s)) := (Real.rpow_mul (by norm_num) (k:ℝ) (1 - s)).symm
      _ = ((2:ℝ) ^ ((k:ℝ))) / ((2:ℝ) ^ ((k:ℝ) * s)) := by
          rw [← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
          ring_nf
      _ ≤ ((2:ℝ)^((k:ℝ))) / ((k:ℝ)^s) :=
          div_le_div_of_nonneg_left (show (0:ℝ) ≤ (2:ℝ)^((k:ℝ)) by positivity)
            (Real.rpow_pos_of_pos hk0 s) hks
      _ = (2:ℝ)^k / (k:ℝ)^s := by rw [hpow]

section Monotone

/-- `Wk s j = 2^j / j^s` is increasing in `j` for `s ∈ (0,1]`. -/
lemma Wk_mono {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : Monotone (fun j : ℕ => Wk s j) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Wk]
  · have hn1 : 1 ≤ n := hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Wk_eq s hn1]
    have hsucc : Wk s (n+1) = (2:ℝ)^(n+1) / ((n:ℝ)+1)^s := by
      rw [Wk_eq s (by omega : 1 ≤ n+1), Nat.cast_add, Nat.cast_one]
    rw [hsucc]
    have h1 : (0:ℝ) < ((n:ℝ)+1)^s := Real.rpow_pos_of_pos (by positivity) s
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hnpos s) h1]
    have hsplit : ((n:ℝ)+1)^s = (n:ℝ)^s * (1 + 1/(n:ℝ))^s := by
      rw [show (n:ℝ)+1 = (n:ℝ) * (1 + 1/(n:ℝ)) by
        rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hnpos)]]
      rw [Real.mul_rpow (le_of_lt hnpos) (by positivity)]
    have hb : (1 + 1/(n:ℝ))^s ≤ 2 := by
      have hbase : (1:ℝ) ≤ 1 + 1/(n:ℝ) := by
        have h0 : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
        linarith
      have h2 : (1 + 1/(n:ℝ))^s ≤ (1 + 1/(n:ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_le hbase hs1
        rwa [Real.rpow_one] at h
      have h3 : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have h2n : (2:ℝ)^(n+1) = 2 * (2:ℝ)^n := by rw [pow_succ]; ring
    have hnx : (0:ℝ) ≤ (n:ℝ)^s := Real.rpow_nonneg (le_of_lt hnpos) s
    have h2npos : (0:ℝ) < (2:ℝ)^n := by positivity
    rw [hsplit, h2n]
    have h3 : (n:ℝ)^s * (2:ℝ)^n * (1 + 1/(n:ℝ))^s ≤ (n:ℝ)^s * (2:ℝ)^n * 2 :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hnx h2npos.le)
    nlinarith [h3]

/-- Once `Wk s k₀ ≥ B`, the same holds for all `j ≥ k₀`. -/
lemma Wk_ge_of_le {s B : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hB : B ≤ Wk s k₀) {j : ℕ} (hj : k₀ ≤ j) : B ≤ Wk s j :=
  hB.trans (Wk_mono hs hs1 hj)

end Monotone

end Parameters



section Uniform

/-- **The weight of §6.1 satisfies the hypotheses of `thm:higher_dim_BM`**, with constants that
depend only on `ν`, `μ` and `d` (and not on `Y` or on the reciprocal scale `h⁻¹`). -/
theorem omega_uniform_bound (hd : 1 ≤ d) {ν μ : ℝ} (hν : 0 < ν) (hμ : 1 < μ) :
    ∃ (s α Creg Cgr C₀ : ℝ) (k₀ : ℕ),
      0 < s ∧ s < 1 ∧ 0 < α ∧ α < 1 ∧
      0 < Creg ∧ 0 < Cgr ∧ 0 < C₀ ∧
      ∀ (h : ℝ), 0 < h → ∀ (Y : Set ℝᵈ),
        Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹) → PorousOnLines ν μ h⁻¹ Y →
        (∀ x, omega s α k₀ (Kfun (d := d) k₀ h) Y x ≤ 0) ∧
        (∀ x, ‖x‖ ≤ 2 → omega s α k₀ (Kfun (d := d) k₀ h) Y x = 0) ∧
        ContDiff ℝ 3 (omega s α k₀ (Kfun (d := d) k₀ h) Y) ∧
        (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
          ‖iteratedFDeriv ℝ a (omega s α k₀ (Kfun (d := d) k₀ h) Y) x‖ ≤
            Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) ∧
        HasFiniteGrowth (omega s α k₀ (Kfun (d := d) k₀ h) Y) Cgr ∧
        (∀ x ∈ Y, omega s α k₀ (Kfun (d := d) k₀ h) Y x ≤
          -(1/20) * (‖x‖ / (Real.log (2 + ‖x‖))^α) + C₀) := by
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hsqd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd0
  obtain ⟨γ, C_ann, hγ, hC_ann, hann⟩ :=
    Commons.Measure.EuclideanSpace.porous_line_measure_annulus d (ν := ν / 2) (by positivity)
  have hs0 : (0:ℝ) < 1/5 := by norm_num
  have hs1 : (1:ℝ)/5 < 1 := by norm_num
  set α : ℝ := 1 - min ((1/5)*γ/2) (1/4) with hαdef
  have hminpos : 0 < min ((1/5)*γ/2) (1/4) := lt_min (by positivity) (by norm_num)
  have hminle : min ((1/5)*γ/2) (1/4) ≤ 1/4 := min_le_right _ _
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hα3s : 3*(1/5) < α := by rw [hαdef]; linarith
  have hβ1 : 1 < α + (1/5)*γ := by
    have h1 : min ((1/5)*γ/2) (1/4) ≤ (1/5)*γ/2 := min_le_left _ _
    rw [hαdef]; nlinarith [hγ]
  obtain ⟨k₀, hk₀8, hk₀A, hk₀B⟩ := exists_parameter (s := 1/5) (A := 4*Real.sqrt (d:ℝ))
    (B := μ*ν/(8*Real.sqrt (d:ℝ))) hs0 hs1 (by positivity) (by positivity)
  have hk₀1 : 1 ≤ k₀ := by omega
  set C₂ : ℝ := (4 * C_ann * ((Real.sqrt (d:ℝ)/ν)^γ + (192*(d:ℝ)/ν)^γ)) * (3:ℝ)^d with hC₂def
  have hC₂ : 0 < C₂ := by
    rw [hC₂def]
    have h1 : 0 < (Real.sqrt (d:ℝ)/ν)^γ := Real.rpow_pos_of_pos (div_pos hsqd hν) γ
    have h2 : 0 < (192*(d:ℝ)/ν)^γ :=
      Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num) hd0) hν) γ
    positivity
  obtain ⟨Cint, hCint, hint⟩ :=
    Commons.Measure.Real.integral_log_rpow_decay (α + (1/5)*γ) hβ1
  set Cgr : ℝ := Cint * (2048 * C₂ * (8*Real.log 2)^(α + (1/5)*γ)) with hCgrdef
  have hCgr : 0 < Cgr := by
    rw [hCgrdef]
    have h2 : 0 < (8*Real.log 2)^(α + (1/5)*γ) :=
      Real.rpow_pos_of_pos (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]) (α + (1/5)*γ)
    exact mul_pos hCint (mul_pos (mul_pos (by norm_num) hC₂) h2)
  set Creg : ℝ := 128 * (3:ℝ)^d * bumpConst d + 1 with hCregdef
  have hCreg : 0 < Creg := by
    rw [hCregdef]
    have h1 : (0:ℝ) < (3:ℝ)^d := pow_pos (by norm_num) d
    have h2 : (0:ℝ) ≤ bumpConst d := bumpConst_nonneg (d := d)
    nlinarith
  set C₀ : ℝ := (1/20) * (2:ℝ)^k₀ / (Real.log 2)^α with hC₀def
  have hC₀ : 0 < C₀ := by
    rw [hC₀def]
    have h2 : 0 < (Real.log 2)^α := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) α
    have h3 : (0:ℝ) < (2:ℝ)^k₀ := pow_pos (by norm_num) k₀
    exact div_pos (mul_pos (by norm_num) h3) h2
  refine ⟨1/5, α, Creg, Cgr, C₀, k₀, hs0, hs1, hα0, hα1, hCreg, hCgr, hC₀, ?_⟩
  intro h hh Y hYbox hYpor
  have hkK : k₀ ≤ Kfun (d := d) k₀ h := le_Kfun k₀ h
  -- uniform scale conditions
  have hWs : ∀ j ∈ Finset.Icc k₀ (Kfun (d := d) k₀ h),
      2 * Real.sqrt (d:ℝ) * Wk (1/5) j ≤ (2:ℝ)^(j-1) := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans hk₀1 (Finset.mem_Icc.mp hj).1
    have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjs : (4*Real.sqrt (d:ℝ)) ≤ (j:ℝ)^((1:ℝ)/5) := by
      have h1 : (k₀:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      exact hk₀A.trans (Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0:ℝ) ≤ (1:ℝ)/5))
    rw [Wk_eq (1/5) hj1, ← mul_div_assoc]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hjpos (1/5))]
    have h2jm : (2:ℝ)^(j-1) * 2 = (2:ℝ)^j := by
      rw [← pow_succ, Nat.sub_add_cancel hj1]
    have hpos : (0:ℝ) < (2:ℝ)^(j-1) := by positivity
    have h2 : (2:ℝ)^(j-1) * (4*Real.sqrt (d:ℝ)) ≤ (2:ℝ)^(j-1) * (j:ℝ)^((1:ℝ)/5) :=
      mul_le_mul_of_nonneg_left hjs hpos.le
    have h3 : 2 * Real.sqrt (d:ℝ) * (2:ℝ)^j = (2:ℝ)^(j-1) * (4*Real.sqrt (d:ℝ)) := by
      rw [← h2jm]; ring
    linarith [h2, h3]
  have hW : ∀ j ∈ Finset.Icc k₀ (Kfun (d := d) k₀ h),
      Real.sqrt (d:ℝ) * Wk (1/5) j ≤ (2:ℝ)^(j-1) := by
    intro j hj
    have h0 : (0:ℝ) ≤ Real.sqrt (d:ℝ) * Wk (1/5) j :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Wk_pos (1/5) j))
    linarith [hWs j hj, h0]
  have hμW : ∀ j ∈ Finset.Icc k₀ (Kfun (d := d) k₀ h),
      μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk (1/5) j) / ν := by
    intro j hj
    have hjge : k₀ ≤ j := (Finset.mem_Icc.mp hj).1
    have hWkj : Wk (1/5) k₀ ≤ Wk (1/5) j :=
      Wk_mono (by norm_num) (by norm_num) hjge
    have hB : μ*ν/(8*Real.sqrt (d:ℝ)) ≤ Wk (1/5) k₀ := by
      have hB' := hk₀B
      rw [Wk_eq (1/5) hk₀1]
      exact hB'
    have hmain : μ*ν/(8*Real.sqrt (d:ℝ)) ≤ Wk (1/5) j := hB.trans hWkj
    rw [show 4 * (2 * Real.sqrt (d:ℝ) * Wk (1/5) j) / ν = 8*Real.sqrt (d:ℝ)*Wk (1/5) j/ν by ring]
    rw [le_div_iff₀ hν]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*Real.sqrt (d:ℝ))] at hmain
    linarith [hmain]
  -- the segment bound
  have hseg : ∀ j ∈ Finset.Icc k₀ (Kfun (d := d) k₀ h), ∀ x : ℝᵈ, x ≠ 0 →
      ∫ t in (1/2:ℝ)..2, |omegaK (1/5) α j Y (t • x)| ≤
        (1 / ‖x‖) * (C₂ * (4:ℝ)^j * (j:ℝ)^(-(α + (1/5)*γ))) := by
    intro j hj x hx
    have hμpos : 0 < μ := lt_trans zero_lt_one hμ
    have hj1 : 1 ≤ j := le_trans hk₀1 (Finset.mem_Icc.mp hj).1
    have := omegaK_segment_bound (ν := ν) (μ := μ) (s := 1/5) (α := α) (h := h)
      (γ := γ) (C₀ := C_ann) (j := j) (Y := Y)
      hν hγ hC_ann hann hμpos hd hs0 hh hj1 hYpor hYbox (hμW j hj) (hWs j hj) hx
    rw [hC₂def]
    exact this
  refine ⟨fun x => omega_nonpos _ _ _ _ _ x, ?_, omega_contDiff _ _ _ _ _, ?_, ?_, ?_⟩
  · intro x hx
    refine omega_eq_zero_of_norm_lt (s := 1/5) (α := α) (k₀ := k₀)
      (K := Kfun (d := d) k₀ h) (Y := Y) hk₀1 hW ?_
    have h2 : (2:ℝ) < (2:ℝ)^(k₀-1) := by
      have h3 : (2:ℝ)^3 ≤ (2:ℝ)^(k₀-1) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h3
      linarith
    linarith
  · intro a ha x
    have h := norm_iteratedFDeriv_omega_le (d := d) (s := 1/5) (α := α) (k₀ := k₀)
      (K := Kfun (d := d) k₀ h) hs0 hα3s hk₀1 hkK hW a ha Y x
    refine h.trans ?_
    have hle : (128 * (3:ℝ)^d * bumpConst d) ≤ Creg := by rw [hCregdef]; linarith
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by positivity) _)
  · have hbd := omega_growth (d := d) hd hγ (by linarith [hα0]) hC₂ hk₀8 hkK hW hseg
    have hval := omega_growth_integral_le (d := d) (s := 1/5) (α := α) (β := α + (1/5)*γ)
      (C := 2048 * C₂ * (8*Real.log 2)^(α + (1/5)*γ)) (Cint := Cint) (k₀ := k₀)
      (K := Kfun (d := d) k₀ h) (Y := Y) (by positivity) hint hbd
    refine ⟨?_, ?_⟩
    · -- the growth integral is finite: dominate by the integrable comparison function
      have hβp : 1 < α + (1/5) * γ := by linarith [hβ1]
      have hcmp : IntegrableOn (fun r : ℝ => (2048 * C₂ * (8 * Real.log 2) ^ (α + (1/5)*γ)) *
          (r / (Real.log (2 + r)) ^ (α + (1/5)*γ) / (1 + r ^ 2))) (Set.Ioi (0 : ℝ)) :=
        (Commons.Measure.Real.integrableOn_log_rpow_decay _ hβp).const_mul _
      refine Integrable.mono hcmp ?_ ?_
      · have hA : AEStronglyMeasurable
            (fun r : ℝ => Gstar (omega (1/5) α k₀ (Kfun (d := d) k₀ h) Y) r)
            (volume.restrict (Set.Ioi (0 : ℝ))) :=
          aestronglyMeasurable_Gstar (d := d) hd
            (omega_contDiff (1/5) α k₀ (Kfun (d := d) k₀ h) Y).continuous
        have hB : AEStronglyMeasurable (fun r : ℝ => 1 + r ^ 2)
            (volume.restrict (Set.Ioi (0 : ℝ))) :=
          (continuous_const.add (continuous_id.pow 2)).aestronglyMeasurable
        exact ((hA.aemeasurable).div (hB.aemeasurable)).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with r hr
        have hr0 : (0 : ℝ) < r := hr
        have hlog : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
        have hCpos : (0 : ℝ) < 2048 * C₂ * (8 * Real.log 2) ^ (α + (1/5)*γ) := by
          have h1 : (0 : ℝ) < (8 * Real.log 2) ^ (α + (1/5)*γ) :=
            Real.rpow_pos_of_pos (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]) _
          positivity
        have h1 : (0 : ℝ) ≤ Gstar (omega (1/5) α k₀ (Kfun (d := d) k₀ h) Y) r / (1 + r ^ 2) :=
          div_nonneg (Gstar_nonneg _ r) (by positivity)
        have h2 : (0 : ℝ) ≤ 2048 * C₂ * (8 * Real.log 2) ^ (α + (1/5)*γ) *
            (r / (Real.log (2 + r)) ^ (α + (1/5)*γ) / (1 + r ^ 2)) :=
          mul_nonneg hCpos.le (div_nonneg (div_nonneg hr0.le (Real.rpow_pos_of_pos hlog _).le)
            (by positivity))
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
        calc Gstar (omega (1/5) α k₀ (Kfun (d := d) k₀ h) Y) r / (1 + r ^ 2)
            ≤ (2048 * C₂ * (8 * Real.log 2) ^ (α + (1/5)*γ) * r
                / (Real.log (2 + r)) ^ (α + (1/5)*γ)) / (1 + r ^ 2) :=
              div_le_div_of_nonneg_right (hbd r hr) (by positivity)
          _ = 2048 * C₂ * (8 * Real.log 2) ^ (α + (1/5)*γ) *
                (r / (Real.log (2 + r)) ^ (α + (1/5)*γ) / (1 + r ^ 2)) := by ring
    · rw [hCgrdef]
      show (∫ r in Set.Ioi (0:ℝ),
            (⨆ x : {x : ℝᵈ // ‖x‖ = r},
              ∫ t in (1/2:ℝ)..2, |omega (1/5) α k₀ (Kfun (d := d) k₀ h) Y (t • (x:ℝᵈ))|)
              / (1 + r^2))
          ≤ Cint * (2048 * C₂ * (8*Real.log 2)^(α + (1/5)*γ))
      calc (∫ r in Set.Ioi (0:ℝ),
            (⨆ x : {x : ℝᵈ // ‖x‖ = r},
              ∫ t in (1/2:ℝ)..2, |omega (1/5) α k₀ (Kfun (d := d) k₀ h) Y (t • (x:ℝᵈ))|)
              / (1 + r^2))
          ≤ (2048 * C₂ * (8*Real.log 2)^(α + (1/5)*γ)) * Cint := hval
        _ = Cint * (2048 * C₂ * (8*Real.log 2)^(α + (1/5)*γ)) := by ring
  · intro x hxY
    have hxK : ‖x‖ ≤ (2:ℝ)^(Kfun (d := d) k₀ h + 1) := by
      have h1 : ‖x‖ ≤ Real.sqrt (d:ℝ) * (12 * h⁻¹) :=
        norm_le_of_mem_cube_center (by positivity) (hYbox hxY)
      have h2 : 12*Real.sqrt (d:ℝ) * h⁻¹ ≤ (Kfun (d := d) k₀ h : ℝ) := lt_Kfun k₀ h
      have h3 : ((Kfun (d := d) k₀ h : ℕ) : ℝ) ≤ (2:ℝ)^(Kfun (d := d) k₀ h) := by
        exact_mod_cast le_of_lt Nat.lt_two_pow_self
      have h4 : (2:ℝ)^(Kfun (d := d) k₀ h) ≤ (2:ℝ)^(Kfun (d := d) k₀ h + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h5 : Real.sqrt (d:ℝ) * (12 * h⁻¹) = 12*Real.sqrt (d:ℝ) * h⁻¹ := by ring
      linarith [h1, h2, h3, h4, h5]
    have h := omega_le_on_Y (s := 1/5) (α := α) (k₀ := k₀) (K := Kfun (d := d) k₀ h)
      hs0 hα0 hα1.le hk₀1 hkK hxY hxK
    refine h.trans (le_of_eq ?_)
    rw [hC₀def]
    ring

end Uniform

end Submission.FUP

section Final

/-- **Cohen's `prop:existence_damping` from the higher-dimensional Beurling–Malliavin
theorem.**  The weight of §6.1 is fed into BM; the resulting function, rescaled, is an `ℓ₂`
damping function for `Y` with parameters `c₁ = σ`, `c₃ = cσ/20` and `c₂` (and the exponent `α`)
depending only on `σ`, `ν`, `μ` and `d`. -/
theorem existence_damping_of_BM (hd : 1 ≤ d)
    (hBM : Spec.higher_dim_BM_damping_statement (d := d)) :
    Spec.existence_damping_statement (d := d) := by
  intro ν hν μ hμ1
  obtain ⟨s, α, Creg, Cgr, C₀, k₀, hs0, hs1, hα0, hα1, hCreg, hCgr, hC₀, hω⟩ :=
    omega_uniform_bound hd hν hμ1
  have hchoose : ∀ σ : Set.Ioo (0:ℝ) 1,
      ∃ (c rmin M c₂ : ℝ), 0 < c ∧ 0 < rmin ∧ 0 < M ∧ 0 < c₂ ∧
        ∀ (ω' : ℝᵈ → ℝ), (∀ x, ω' x ≤ 0) → (∀ x, ‖x‖ ≤ 2 → ω' x = 0) →
          ContDiff ℝ 3 ω' →
          (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
            ‖iteratedFDeriv ℝ a ω' x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) →
          HasFiniteGrowth ω' Cgr →
          ∃ f : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0 : ℝᵈ) σ →
                ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) ∧
            (∀ᵐ x ∂((volume : Measure ℝᵈ).restrict (closedBall (0 : ℝᵈ) rmin)),
                (1 / 2 : ℝ) ≤ ‖(f : ℝᵈ → ℂ) x‖) ∧
            (c₂ ≤ ∫ x in ball (0 : ℝᵈ) 1, ‖(f : ℝᵈ → ℂ) x‖ ^ 2) ∧
            (∀ᵐ x ∂(volume : Measure ℝᵈ),
                ‖(f : ℝᵈ → ℂ) x‖ ≤ M * Real.exp (c * σ * ω' x)) ∧
            (∀ᵐ x ∂(volume : Measure ℝᵈ),
                ‖(f : ℝᵈ → ℂ) x‖ ≤ M * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2)) :=
    fun σ => hBM Creg Cgr hCreg hCgr σ σ.2.1 σ.2.2
  choose c rm M c₂ hspec using hchoose
  -- the damping constants as functions of `σ`
  let lam : Set.Ioo (0:ℝ) 1 → ℝ := fun σ => min 1 (Real.exp (-(c σ * σ.1 * C₀))) / M σ
  let c₂f : ℝ → ℝ := fun σ => if h : σ ∈ Set.Ioo (0:ℝ) 1 then
      min (1/2) (lam ⟨σ, h⟩ * Real.sqrt (c₂ ⟨σ, h⟩)) else 1/2
  let c₃f : ℝ → ℝ := fun σ => if h : σ ∈ Set.Ioo (0:ℝ) 1 then c ⟨σ, h⟩ * σ / 20 else 1
  have hlam_pos : ∀ σ : Set.Ioo (0:ℝ) 1, 0 < lam σ := by
    intro σ
    obtain ⟨hc, -, hM, -, -⟩ := hspec σ
    have hmin : 0 < min (1:ℝ) (Real.exp (-(c σ * σ.1 * C₀))) :=
      lt_min one_pos (Real.exp_pos _)
    simpa only [lam] using div_pos hmin hM
  refine ⟨α, c₂f, c₃f, hα1, hα0, ?_, ?_⟩
  · intro σ hσ
    have hlp := hlam_pos ⟨σ, hσ⟩
    obtain ⟨hc, -, hM, hc₂, -⟩ := hspec ⟨σ, hσ⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [c₂f, dif_pos hσ]
      have h2 : 0 < Real.sqrt (c₂ ⟨σ, hσ⟩) := Real.sqrt_pos.mpr hc₂
      exact lt_min (by norm_num) (mul_pos hlp h2)
    · simp only [c₂f, dif_pos hσ]
      have h1 := min_le_left (1/2 : ℝ) (lam ⟨σ, hσ⟩ * Real.sqrt (c₂ ⟨σ, hσ⟩))
      exact lt_of_le_of_lt h1 (by norm_num : (1:ℝ)/2 < 1)
    · simp only [c₃f, dif_pos hσ]
      exact div_pos (mul_pos hc hσ.1) (by norm_num)
  · intro h hh Y hYbox hYpor σ hσ
    obtain ⟨hc, hrm, hM, hc₂, hmain⟩ := hspec ⟨σ, hσ⟩
    obtain ⟨hω0, hωz, hωsm, hωreg, hωgr, hωlow⟩ := hω h hh Y hYbox hYpor
    obtain ⟨f, hfsupp, hflow, hfnorm, hfexp, hfdec⟩ :=
      hmain (omega s α k₀ (Kfun (d := d) k₀ h) Y) hω0 hωz hωsm hωreg hωgr
    have hlp : 0 < lam ⟨σ, hσ⟩ := hlam_pos ⟨σ, hσ⟩
    have hnorm_lam : ‖((lam ⟨σ, hσ⟩ : ℝ) : ℂ)‖ = lam ⟨σ, hσ⟩ := by
      rw [show ‖((lam ⟨σ, hσ⟩ : ℝ) : ℂ)‖ = |lam ⟨σ, hσ⟩| from by simp]
      exact abs_of_pos hlp
    have hMne : M ⟨σ, hσ⟩ ≠ 0 := ne_of_gt hM
    have hlamM : lam ⟨σ, hσ⟩ * M ⟨σ, hσ⟩ ≤ 1 := by
      have h := min_le_left (1:ℝ) (Real.exp (-(c ⟨σ,hσ⟩ * σ * C₀)))
      rw [show lam ⟨σ, hσ⟩ * M ⟨σ, hσ⟩
          = min (1:ℝ) (Real.exp (-(c ⟨σ,hσ⟩ * σ * C₀))) from by
        simp only [lam]; field_simp] at *
      exact h
    have hlamMe : lam ⟨σ, hσ⟩ * M ⟨σ, hσ⟩ * Real.exp (c ⟨σ,hσ⟩ * σ * C₀) ≤ 1 := by
      have hEq : lam ⟨σ, hσ⟩ * M ⟨σ, hσ⟩ = min (1:ℝ) (Real.exp (-(c ⟨σ,hσ⟩ * σ * C₀))) := by
        simp only [lam]; field_simp
      rw [hEq]
      calc min (1:ℝ) (Real.exp (-(c ⟨σ,hσ⟩ * σ * C₀))) * Real.exp (c ⟨σ,hσ⟩ * σ * C₀)
          ≤ Real.exp (-(c ⟨σ,hσ⟩ * σ * C₀)) * Real.exp (c ⟨σ,hσ⟩ * σ * C₀) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    refine ⟨((lam ⟨σ, hσ⟩ : ℝ) : ℂ) • f, ?_, ?_, ?_, ?_⟩
    · -- Fourier support in `closedBall 0 σ`
      filter_upwards [hfsupp, MeasureTheory.Lp.coeFn_smul ((lam ⟨σ,hσ⟩ : ℝ) : ℂ)
        (𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ))] with ξ hξ hcoe
      intro hξσ
      rw [fourier_smul, hcoe]
      simp only [Pi.smul_apply, hξ hξσ, smul_zero]
    · -- `L²` normalisation
      have hae : ∀ᵐ x ∂(volume : Measure ℝᵈ),
          ‖(((lam ⟨σ,hσ⟩ : ℝ) : ℂ) • f : Lp ℂ 2 (volume : Measure ℝᵈ)) x‖ ^ 2 =
            (lam ⟨σ, hσ⟩) ^ 2 * ‖(f : ℝᵈ → ℂ) x‖ ^ 2 := by
        filter_upwards [MeasureTheory.Lp.coeFn_smul ((lam ⟨σ,hσ⟩ : ℝ) : ℂ) f] with x hcoe
        rw [hcoe, Pi.smul_apply, norm_smul, hnorm_lam, mul_pow]
      have hInt : ∫ x in ball (0:ℝᵈ) 1,
            ‖(((lam ⟨σ,hσ⟩ : ℝ) : ℂ) • f : Lp ℂ 2 (volume : Measure ℝᵈ)) x‖ ^ 2 =
          (lam ⟨σ, hσ⟩) ^ 2 * ∫ x in ball (0:ℝᵈ) 1, ‖(f : ℝᵈ → ℂ) x‖ ^ 2 := by
        rw [MeasureTheory.setIntegral_congr_ae measurableSet_ball
          (hae.mono (fun x h _ => h)), MeasureTheory.integral_const_mul]
      have hc₂f_le : c₂f σ ≤ lam ⟨σ, hσ⟩ * Real.sqrt (c₂ ⟨σ, hσ⟩) := by
        simp only [c₂f, dif_pos hσ]
        exact min_le_right _ _
      have hsq : (lam ⟨σ, hσ⟩ * Real.sqrt (c₂ ⟨σ, hσ⟩)) ^ 2 =
          (lam ⟨σ, hσ⟩) ^ 2 * c₂ ⟨σ, hσ⟩ := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hc₂)]
      rw [hInt]
      have h3 : (lam ⟨σ, hσ⟩) ^ 2 * c₂ ⟨σ, hσ⟩ ≤
          (lam ⟨σ, hσ⟩) ^ 2 * ∫ x in ball (0:ℝᵈ) 1, ‖(f : ℝᵈ → ℂ) x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hfnorm (sq_nonneg _)
      have hnn : 0 ≤ c₂f σ := by
        simp only [c₂f, dif_pos hσ]
        exact le_min (by norm_num) (by positivity)
      have hsq2 : (c₂f σ) ^ 2 ≤ (lam ⟨σ, hσ⟩ * Real.sqrt (c₂ ⟨σ, hσ⟩)) ^ 2 :=
        pow_le_pow_left₀ hnn hc₂f_le 2
      rw [hsq] at hsq2
      exact hsq2.trans h3
    · -- the `⟨x⟩^{-d}` bound
      filter_upwards [hfdec, MeasureTheory.Lp.coeFn_smul ((lam ⟨σ,hσ⟩ : ℝ) : ℂ) f]
        with x hdec hcoe
      rw [hcoe, Pi.smul_apply, norm_smul, hnorm_lam]
      calc lam ⟨σ,hσ⟩ * ‖(f : ℝᵈ → ℂ) x‖
          ≤ lam ⟨σ,hσ⟩ * (M ⟨σ,hσ⟩ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2)) :=
            mul_le_mul_of_nonneg_left hdec hlp.le
        _ = (lam ⟨σ,hσ⟩ * M ⟨σ,hσ⟩) * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) := by ring
        _ ≤ 1 * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hlamM (Real.rpow_nonneg (by positivity) _)
        _ = bracket x ^ (-(d:ℝ)) := by
            rw [one_mul, bracket_pow]
    · -- exponential decay on `Y`
      filter_upwards [hfexp, MeasureTheory.Lp.coeFn_smul ((lam ⟨σ,hσ⟩ : ℝ) : ℂ) f]
        with x hexp hcoe
      intro hxY
      rw [hcoe, Pi.smul_apply, norm_smul, hnorm_lam]
      have hωx := hωlow x hxY
      have hcs : 0 < c ⟨σ,hσ⟩ * σ := mul_pos hc hσ.1
      have hexp_le : Real.exp (c ⟨σ,hσ⟩ * σ * omega s α k₀ (Kfun (d := d) k₀ h) Y x)
          ≤ Real.exp (c ⟨σ,hσ⟩ * σ *
              (-(1/20) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) + C₀)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hωx, hcs]
      have harg : c ⟨σ,hσ⟩ * σ * (-(1/20) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) + C₀)
          = -(c ⟨σ,hσ⟩ * σ / 20 * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α))
            + c ⟨σ,hσ⟩ * σ * C₀ := by ring
      rw [harg, Real.exp_add] at hexp_le
      calc lam ⟨σ,hσ⟩ * ‖(f : ℝᵈ → ℂ) x‖
          ≤ lam ⟨σ,hσ⟩ * (M ⟨σ,hσ⟩ *
              Real.exp (c ⟨σ,hσ⟩ * σ * omega s α k₀ (Kfun (d := d) k₀ h) Y x)) :=
            mul_le_mul_of_nonneg_left hexp hlp.le
        _ = (lam ⟨σ,hσ⟩ * M ⟨σ,hσ⟩) *
              Real.exp (c ⟨σ,hσ⟩ * σ * omega s α k₀ (Kfun (d := d) k₀ h) Y x) := by ring
        _ ≤ (lam ⟨σ,hσ⟩ * M ⟨σ,hσ⟩) *
              (Real.exp (-(c ⟨σ,hσ⟩ * σ / 20 * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α))) *
                Real.exp (c ⟨σ,hσ⟩ * σ * C₀)) :=
            mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hlp.le hM.le)
        _ = (lam ⟨σ,hσ⟩ * M ⟨σ,hσ⟩ * Real.exp (c ⟨σ,hσ⟩ * σ * C₀)) *
              Real.exp (-(c ⟨σ,hσ⟩ * σ / 20 * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α))) := by ring
        _ ≤ 1 * Real.exp (-(c ⟨σ,hσ⟩ * σ / 20 * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α))) :=
            mul_le_mul_of_nonneg_right hlamMe (Real.exp_pos _).le
        _ = Real.exp (-(c₃f σ * ‖x‖ / (Real.log (2 + ‖x‖)) ^ α)) := by
            rw [one_mul]
            congr 1
            simp only [c₃f, dif_pos hσ]
            ring

end Final

section Assembly

/-- **Cohen's Theorem 1.1 from two deep inputs.**  Assuming Han–Schlag's conditional fractal
uncertainty principle (`FUP_conditional_damping_statement`) and the higher-dimensional
Beurling–Malliavin theorem in the form used in §6.1 (`higher_dim_BM_damping_statement`), the
main theorem holds.  Compared with `Assembly.theorem_1_1_of_black_boxes`, the derivation of
damping functions from line porosity (§6.1) is proved here rather than assumed. -/
theorem theorem_1_1_of_BM_and_FUP (hd : 1 ≤ d)
    (hFUP : Spec.FUP_conditional_damping_statement (d := d))
    (hBM : Spec.higher_dim_BM_damping_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_black_boxes hFUP (existence_damping_of_BM hd hBM)

end Assembly
