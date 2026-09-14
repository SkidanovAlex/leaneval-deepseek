import Submission.NBody.LYZLength
import Submission.Commons.Analysis.Asymptotics.tsum_sqrt_log_div_pow_le
import Mathlib

/-!
# The correction functions `Ψ` and `Ψ̄` of Liu--Yan--Zhou

Liu--Yan--Zhou control the length of `m_λ`-geodesics by `l(γ) ≤ |γ(τ) - x*| + Ψ(|γ(τ) - x*|)`,
where `Ψ` grows like a logarithm; the induction of their Section 6 then needs the *tail sums* of
the dyadic series `∑_j √(Ψ(2^j)/2^j)`, dominated by the function `Ψ̄` below, which is the one that
actually tends to `0`.

We use the concrete normalisation

* `Ψ(T) = A + B * log (2T + 2M + 1)` (`lyzPsi`),
* `Ψ̄(t) = C * √(Ψ(2t)/(2t))`   (`lyzPsibar`, for `t > 0`),

with parameters `A B M C : ℝ`, `A, B, M ≥ 0`.  This file proves: `Ψ ≥ 0` and monotone;
`√(Ψ(t)/t) ≤ Ψ̄(t)`; `Ψ̄(t) → 0`; `Ψ̄(t) ≤ 2Ψ̄(s)` for `s ≤ t ≤ 2s`; and `Ψ(T) ≤ εT` for `T`
large.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The Liu--Yan--Zhou correction function `Ψ(T) = A + B log(2T + 2M + 1)`. -/
noncomputable def lyzPsi (A B M T : ℝ) : ℝ := A + B * Real.log (2 * T + 2 * M + 1)

/-- The Liu--Yan--Zhou tail-sum bound `Ψ̄(t) = C √(Ψ(2t)/(2t))`. -/
noncomputable def lyzPsibar (A B M C t : ℝ) : ℝ := C * Real.sqrt (lyzPsi A B M (2 * t) / (2 * t))

lemma lyzPsi_nonneg {A B M T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ lyzPsi A B M T := by
  have h1 : (1:ℝ) ≤ 2 * T + 2 * M + 1 := by linarith
  have h2 : 0 ≤ Real.log (2 * T + 2 * M + 1) := Real.log_nonneg h1
  rw [lyzPsi]
  exact add_nonneg hA (mul_nonneg hB h2)

lemma lyzPsi_le_lyzPsi {A B M T T' : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hTT' : T ≤ T') :
    lyzPsi A B M T ≤ lyzPsi A B M T' := by
  have h1 : (0:ℝ) < 2 * T + 2 * M + 1 := by linarith
  have h2 : 2 * T + 2 * M + 1 ≤ 2 * T' + 2 * M + 1 := by linarith
  have hlog := Real.log_le_log h1 h2
  rw [lyzPsi, lyzPsi]
  linarith [mul_le_mul_of_nonneg_left hlog hB]

lemma lyzPsibar_nonneg {A B M C t : ℝ} (hC : 0 ≤ C)
    (_h : 0 ≤ lyzPsi A B M (2 * t) / (2 * t)) : 0 ≤ lyzPsibar A B M C t :=
  mul_nonneg hC (Real.sqrt_nonneg _)

/-- `Ψ(4s) ≤ 4 Ψ(2s)`. -/
lemma lyzPsi_four_le {A B M s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hs : 0 ≤ s) :
    lyzPsi A B M (4 * s) ≤ 4 * lyzPsi A B M (2 * s) := by
  have hkey : 8 * s + 2 * M + 1 ≤ (4 * s + 2 * M + 1) ^ 4 := by
    have h1 : (4 * s + 2 * M + 1) ^ 2 ≤ (4 * s + 2 * M + 1) ^ 4 := by
      have h2 : (1:ℝ) ≤ (4 * s + 2 * M + 1) ^ 2 := by nlinarith [sq_nonneg (4 * s + 2 * M)]
      nlinarith [h2, sq_nonneg ((4 * s + 2 * M + 1) ^ 2)]
    have h3 : 8 * s + 2 * M + 1 ≤ (4 * s + 2 * M + 1) ^ 2 := by
      nlinarith [sq_nonneg (4 * s + 2 * M), sq_nonneg s, sq_nonneg M, mul_nonneg hs hM]
    linarith
  have hpos : (0:ℝ) < 8 * s + 2 * M + 1 := by linarith
  have hlog : Real.log (8 * s + 2 * M + 1) ≤ 4 * Real.log (4 * s + 2 * M + 1) := by
    have h4 : Real.log (8 * s + 2 * M + 1) ≤ Real.log ((4 * s + 2 * M + 1) ^ 4) :=
      Real.log_le_log hpos hkey
    rwa [Real.log_pow] at h4
  have hexp : lyzPsi A B M (4 * s) = A + B * Real.log (8 * s + 2 * M + 1) := by
    rw [lyzPsi]; ring_nf
  have hexp2 : lyzPsi A B M (2 * s) = A + B * Real.log (4 * s + 2 * M + 1) := by
    rw [lyzPsi]; ring_nf
  rw [hexp, hexp2]
  nlinarith [mul_le_mul_of_nonneg_left hlog hB]

/-- `log (a t + b + 1) / t → 0` as `t → ∞` (for `a > 0`). -/
lemma tendsto_log_lin_div (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.log (a * t + b + 1) / t) atTop (nhds 0) := by
  have hx : Tendsto (fun t : ℝ => a * t + b + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha))
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => Real.log (a * t + b + 1) / (a * t + b + 1)) atTop (nhds 0) :=
    h1.comp hx
  have h3 : Tendsto (fun t : ℝ => (a * t + b + 1) / t) atTop (nhds a) := by
    have h4 : Tendsto (fun t : ℝ => (b + 1) / t) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h5 : (fun t : ℝ => (a * t + b + 1) / t) =ᶠ[atTop] fun t : ℝ => a + (b + 1) / t := by
      filter_upwards [eventually_gt_atTop (max 0 (-(b + 1) / a))] with t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt (le_max_left _ _) ht)
      have ht1 : a * t + b + 1 ≠ 0 := by
        have hlt : -(b + 1) / a < t := lt_of_le_of_lt (le_max_right _ _) ht
        have hlt' : -(b + 1) < t * a := (div_lt_iff₀ ha).mp hlt
        have : 0 < a * t + b + 1 := by linarith
        exact ne_of_gt this
      field_simp
      ring
    have h5' : Tendsto (fun t : ℝ => a + (b + 1) / t) atTop (nhds a) := by
      simpa using h4.const_add a
    exact h5'.congr' h5.symm
  have h6 : Tendsto (fun t : ℝ => (Real.log (a * t + b + 1) / (a * t + b + 1))
      * ((a * t + b + 1) / t)) atTop (nhds (0 * a)) := h2.mul h3
  rw [zero_mul] at h6
  have h7 : (fun t : ℝ => Real.log (a * t + b + 1) / t) =ᶠ[atTop]
      fun t : ℝ => (Real.log (a * t + b + 1) / (a * t + b + 1))
        * ((a * t + b + 1) / t) := by
    filter_upwards [eventually_gt_atTop (max 0 (-(b + 1) / a))] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt (le_max_left _ _) ht)
    have ht1 : a * t + b + 1 ≠ 0 := by
      have hlt : -(b + 1) / a < t := lt_of_le_of_lt (le_max_right _ _) ht
      have hlt' : -(b + 1) < t * a := (div_lt_iff₀ ha).mp hlt
      have : 0 < a * t + b + 1 := by linarith
      exact ne_of_gt this
    field_simp
  exact h6.congr' h7.symm

lemma tendsto_lyzPsi_div (A B M : ℝ) : Tendsto (fun T : ℝ => lyzPsi A B M T / T) atTop (nhds 0) := by
  have h1 : Tendsto (fun T : ℝ => A / T) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun T : ℝ => B * (Real.log (2 * T + 2 * M + 1) / T)) atTop (nhds 0) := by
    have := (tendsto_log_lin_div 2 (2 * M) (by norm_num)).const_mul B
    simpa using this
  have h3 := h1.add h2
  simp only [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [lyzPsi]
  field_simp

/-- **The `rel` inequality.**  If `C ≥ √2` then `√(Ψ(t)/t) ≤ Ψ̄(t)` for `t > 0`. -/
lemma sqrt_lyzPsi_div_le_lyzPsibar {A B M C t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hC : Real.sqrt 2 ≤ C) (ht : 0 < t) :
    Real.sqrt (lyzPsi A B M t / t) ≤ lyzPsibar A B M C t := by
  have hC0 : 0 ≤ C := le_trans (Real.sqrt_nonneg 2) hC
  have hC2 : (2:ℝ) ≤ C ^ 2 := by
    nlinarith [hC, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have h2t : 0 < 2 * t := by linarith
  have hmono : lyzPsi A B M t ≤ lyzPsi A B M (2 * t) := lyzPsi_le_lyzPsi hB hM ht.le (by linarith)
  have hpsi : 0 ≤ lyzPsi A B M t := lyzPsi_nonneg hA hB hM ht.le
  have hpsi2 : 0 ≤ lyzPsi A B M (2 * t) := lyzPsi_nonneg hA hB hM h2t.le
  have hz : 0 ≤ lyzPsi A B M (2 * t) / (2 * t) := div_nonneg hpsi2 h2t.le
  have hkey : lyzPsi A B M t / t ≤ C ^ 2 * (lyzPsi A B M (2 * t) / (2 * t)) := by
    have h1 : lyzPsi A B M t / t ≤ lyzPsi A B M (2 * t) / t := by
      rw [div_le_div_iff_of_pos_right ht]; exact hmono
    have h2 : lyzPsi A B M (2 * t) / t = 2 * (lyzPsi A B M (2 * t) / (2 * t)) := by
      field_simp
    have h3 : 2 * (lyzPsi A B M (2 * t) / (2 * t)) ≤ C ^ 2 * (lyzPsi A B M (2 * t) / (2 * t)) :=
      mul_le_mul_of_nonneg_right hC2 hz
    linarith
  have hCsq : C ^ 2 * (lyzPsi A B M (2 * t) / (2 * t))
      = (C * Real.sqrt (lyzPsi A B M (2 * t) / (2 * t))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hz]
  have hnonneg : 0 ≤ lyzPsi A B M t / t := div_nonneg hpsi ht.le
  have hsqrt := Real.sqrt_le_sqrt hkey
  rw [hCsq, Real.sqrt_sq (mul_nonneg hC0 (Real.sqrt_nonneg _))] at hsqrt
  rw [lyzPsibar]
  exact hsqrt

/-- **`Ψ̄` is slowly varying**: `Ψ̄(t) ≤ 2 Ψ̄(s)` when `0 < s ≤ t ≤ 2s`. -/
lemma lyzPsibar_le_two {A B M C s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hs : 0 < s) (hst : s ≤ t) (ht2s : t ≤ 2 * s) :
    lyzPsibar A B M C t ≤ 2 * lyzPsibar A B M C s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h2s : 0 < 2 * s := by linarith
  have h2t : 0 < 2 * t := by linarith
  have hfour : lyzPsi A B M (2 * t) ≤ 4 * lyzPsi A B M (2 * s) := by
    have h1 : lyzPsi A B M (2 * t) ≤ lyzPsi A B M (4 * s) :=
      lyzPsi_le_lyzPsi hB hM h2t.le (by linarith)
    have h2 : lyzPsi A B M (4 * s) ≤ 4 * lyzPsi A B M (2 * s) := lyzPsi_four_le hA hB hM hs.le
    linarith
  have hpsi2s : 0 ≤ lyzPsi A B M (2 * s) := lyzPsi_nonneg hA hB hM h2s.le
  have hpsi2t : 0 ≤ lyzPsi A B M (2 * t) := lyzPsi_nonneg hA hB hM h2t.le
  have hsq : lyzPsibar A B M C t ^ 2 ≤ (2 * lyzPsibar A B M C s) ^ 2 := by
    have hexp : lyzPsibar A B M C t ^ 2 = C ^ 2 * (lyzPsi A B M (2 * t) / (2 * t)) := by
      rw [lyzPsibar, mul_pow, Real.sq_sqrt (div_nonneg hpsi2t h2t.le)]
    have hexp2 : (2 * lyzPsibar A B M C s) ^ 2
        = 4 * (C ^ 2 * (lyzPsi A B M (2 * s) / (2 * s))) := by
      rw [lyzPsibar, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hpsi2s h2s.le)]
      ring
    rw [hexp, hexp2]
    have h1 : C ^ 2 * (lyzPsi A B M (2 * t) / (2 * t))
        ≤ C ^ 2 * (4 * lyzPsi A B M (2 * s) / (2 * t)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      rw [div_le_div_iff_of_pos_right h2t]
      linarith
    have h1b : C ^ 2 * (4 * lyzPsi A B M (2 * s) / (2 * t))
        ≤ 4 * (C ^ 2 * (lyzPsi A B M (2 * s) / (2 * s))) := by
      have hden : 4 * lyzPsi A B M (2 * s) / (2 * t) ≤ 4 * lyzPsi A B M (2 * s) / (2 * s) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      calc C ^ 2 * (4 * lyzPsi A B M (2 * s) / (2 * t))
          ≤ C ^ 2 * (4 * lyzPsi A B M (2 * s) / (2 * s)) :=
            mul_le_mul_of_nonneg_left hden (sq_nonneg C)
        _ = 4 * (C ^ 2 * (lyzPsi A B M (2 * s) / (2 * s))) := by ring
    linarith
  have h1 : 0 ≤ lyzPsibar A B M C t :=
    lyzPsibar_nonneg hC (div_nonneg hpsi2t h2t.le)
  have h2 : 0 ≤ lyzPsibar A B M C s := lyzPsibar_nonneg hC (div_nonneg hpsi2s h2s.le)
  nlinarith [hsq, h1, h2]

/-- **`Ψ̄` tends to `0`.** -/
lemma tendsto_lyzPsibar_zero (A B M C : ℝ) :
    Tendsto (fun t : ℝ => lyzPsibar A B M C t) atTop (nhds 0) := by
  have h : Tendsto (fun t : ℝ => lyzPsi A B M (2 * t) / (2 * t)) atTop (nhds 0) := by
    have h5 : Tendsto (fun t : ℝ => (A + B * Real.log (4 * t + 2 * M + 1)) / (2 * t)) atTop (nhds 0) := by
      have h6 : Tendsto (fun t : ℝ => (A + B * Real.log (4 * t + 2 * M + 1)) / t) atTop (nhds 0) := by
        have h61 : Tendsto (fun t : ℝ => A / t) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
        have h62 : Tendsto (fun t : ℝ => B * (Real.log (4 * t + 2 * M + 1) / t)) atTop (nhds 0) := by
          have := (tendsto_log_lin_div 4 (2 * M) (by norm_num)).const_mul B
          simpa using this
        have h63 := h61.add h62
        simp only [add_zero] at h63
        refine h63.congr' ?_
        filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
        field_simp
      have h7 : Tendsto (fun t : ℝ => ((A + B * Real.log (4 * t + 2 * M + 1)) / t) / 2) atTop (nhds (0/2)) :=
        h6.div_const 2
      rw [zero_div] at h7
      refine h7.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [div_div]
      ring_nf
    refine h5.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [lyzPsi]
    ring_nf
  have h2 := h.sqrt
  rw [Real.sqrt_zero] at h2
  have h3 := h2.const_mul C
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards with t
  rw [lyzPsibar]

/-- **The `size2` estimate.**  For every `ε > 0` there is `T₀` with `Ψ(T) ≤ ε T` for `T ≥ T₀`. -/
lemma eventually_lyzPsi_le_mul (A B M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, lyzPsi A B M T ≤ ε * T := by
  rw [eventually_atTop]
  have hev : ∀ᶠ T : ℝ in atTop, lyzPsi A B M T / T < ε := by
    have h0 := tendsto_lyzPsi_div A B M
    exact (tendsto_order.1 h0).2 ε hε
  rw [eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : (0:ℝ) < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  rw [div_lt_iff₀ hT1] at h
  linarith

/-- **The dyadic tail sums are dominated by `Ψ̄`.**  There is a constant `D > 0` such that for
every `C' > 0` and every `N`,
`∑_{k} √(Ψ(2^{N+k})/2^{N+k}) ≤ D Ψ̄(2^N)/C'`. -/
theorem tsum_sqrt_lyzPsi_div_le (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, ∀ C' : ℝ, 0 < C' →
      (∑' k : ℕ, Real.sqrt (lyzPsi A B M ((2:ℝ) ^ (N + k)) / (2:ℝ) ^ (N + k)))
        ≤ D * lyzPsibar A B M C' ((2:ℝ) ^ N) / C' := by
  obtain ⟨D, hD, hDle⟩ := Commons.Analysis.Asymptotics.tsum_sqrt_log_div_pow_le A B M hA hB hM
  refine ⟨D, hD, fun N C' hC' => ?_⟩
  have h := hDle N
  have hbar : lyzPsibar A B M C' ((2:ℝ) ^ N)
      = C' * Real.sqrt ((A + B * Real.log (4 * (2:ℝ) ^ N + 2 * M + 1)) / (2 * (2:ℝ) ^ N)) := by
    rw [lyzPsibar, lyzPsi]
    have h1 : (2:ℝ) * (2 * (2:ℝ) ^ N) + 2 * M + 1 = 4 * (2:ℝ) ^ N + 2 * M + 1 := by ring
    rw [h1]
  have hcongr : (∑' k : ℕ, Real.sqrt (lyzPsi A B M ((2:ℝ) ^ (N + k)) / (2:ℝ) ^ (N + k)))
      = ∑' k : ℕ, Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1))
          / (2:ℝ) ^ (N + k)) := by
    refine tsum_congr fun k => ?_
    rw [lyzPsi]
  rw [hcongr, hbar]
  have hfinal : D * (C' * Real.sqrt ((A + B * Real.log (4 * (2:ℝ) ^ N + 2 * M + 1)) / (2 * (2:ℝ) ^ N))) / C'
      = D * Real.sqrt ((A + B * Real.log (4 * (2:ℝ) ^ N + 2 * M + 1)) / (2 * (2:ℝ) ^ N)) := by
    field_simp
  rw [hfinal]
  exact h

end Submission.NBody
