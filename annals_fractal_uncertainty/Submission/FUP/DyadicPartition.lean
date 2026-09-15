import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Submission.Commons.Analysis.Calculus.iteratedDeriv_smoothTransition_scale_bound

open Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# A dyadic partition of unity on `(0, ∞)`

The paper's §4 writes the weight `ω` as a sum `ω = ∑_k ω_k` using a partition of unity
`1 = ∑_k ψ_k` of `ℝ_{≥ 0}` where `ψ_k` is supported in the dyadic annulus
`A_k = [2^{k-1}, 2^{k+1}]` and satisfies `|D^a ψ_k| ≲ 2^{-ak}`.

This module constructs the partition of unity (with `Real.smoothTransition` as the basic cutoff)
and proves its elementary properties: nonnegativity, boundedness by `1`, the support condition,
the telescoping of the partial sums and the resulting `HasSum`.
-/

/-- The smooth cutoff `φ` with `φ = 0` on `(-∞, 1]` and `φ = 1` on `[2, ∞)`. -/
noncomputable def dyadCut (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

lemma dyadCut_nonneg (t : ℝ) : 0 ≤ dyadCut t := Real.smoothTransition.nonneg _

lemma dyadCut_le_one (t : ℝ) : dyadCut t ≤ 1 := Real.smoothTransition.le_one _

lemma dyadCut_zero_of_le_one {t : ℝ} (h : t ≤ 1) : dyadCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma dyadCut_one_of_two_le {t : ℝ} (h : 2 ≤ t) : dyadCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma dyadCut_monotone : Monotone dyadCut :=
  fun _ _ h => Real.smoothTransition.monotone (by linarith)

lemma dyadCut_contDiff {n : ℕ∞} : ContDiff ℝ n dyadCut :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma continuous_dyadCut : Continuous dyadCut :=
  Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)

/-- The `k`-th cutoff: `φ_0 = 1` and `φ_{k+1}(t) = φ(t/2^k)`; it is `0` for `t ≤ 2^k`. -/
noncomputable def dyadPhi : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | (k + 1) => fun t => dyadCut (t / 2 ^ k)

lemma dyadPhi_zero (t : ℝ) : dyadPhi 0 t = 1 := rfl

lemma dyadPhi_succ (k : ℕ) (t : ℝ) : dyadPhi (k + 1) t = dyadCut (t / 2 ^ k) := rfl

/-- The `k`-th element of the dyadic partition of unity: `ψ_k = φ_k - φ_{k+1}`. -/
noncomputable def dyadPsi (k : ℕ) (t : ℝ) : ℝ := dyadPhi k t - dyadPhi (k + 1) t

lemma dyadPsi_nonneg (k : ℕ) (t : ℝ) : 0 ≤ dyadPsi k t := by
  cases k with
  | zero =>
      have h : dyadPhi 1 t = dyadCut t := by simp [dyadPhi_succ]
      rw [dyadPsi, dyadPhi_zero, h]
      linarith [dyadCut_le_one t]
  | succ k =>
      simp only [dyadPsi, dyadPhi_succ]
      rcases lt_or_ge t 0 with ht | ht
      · have h1 : dyadCut (t / 2 ^ k) = 0 := dyadCut_zero_of_le_one (by
          have : t / 2 ^ k ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht.le (by positivity)
          linarith)
        have h2 : dyadCut (t / 2 ^ (k + 1)) = 0 := dyadCut_zero_of_le_one (by
          have : t / 2 ^ (k + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht.le (by positivity)
          linarith)
        rw [h1, h2]
        norm_num
      · refine sub_nonneg.mpr ?_
        have h : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := by
          rw [pow_succ]
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
        have h2 : t / 2 ^ (k + 1) ≤ t / 2 ^ k := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h) ht
        exact dyadCut_monotone h2

lemma dyadPsi_le_one (k : ℕ) (t : ℝ) : dyadPsi k t ≤ 1 := by
  cases k with
  | zero =>
      have h : dyadPhi 1 t = dyadCut t := by simp [dyadPhi_succ]
      rw [dyadPsi, dyadPhi_zero, h]
      linarith [dyadCut_nonneg t]
  | succ k =>
      simp only [dyadPsi, dyadPhi_succ]
      linarith [dyadCut_le_one (t / 2 ^ k), dyadCut_nonneg (t / 2 ^ (k + 1))]

lemma dyadPhi_le_one (k : ℕ) (t : ℝ) : dyadPhi k t ≤ 1 := by
  cases k with
  | zero => simp [dyadPhi]
  | succ k => simpa [dyadPhi_succ] using dyadCut_le_one (t / 2 ^ k)

lemma dyadPhi_nonneg (k : ℕ) (t : ℝ) : 0 ≤ dyadPhi k t := by
  cases k with
  | zero => simp [dyadPhi]
  | succ k => simpa [dyadPhi_succ] using dyadCut_nonneg (t / 2 ^ k)

/-- One step of monotonicity in `k` of the cutoffs, for `t ≥ 0`. -/
lemma dyadPhi_succ_le (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : dyadPhi (j + 1) t ≤ dyadPhi j t := by
  cases j with
  | zero =>
      simp only [dyadPhi_zero, dyadPhi_succ, pow_zero, div_one]
      exact dyadCut_le_one t
  | succ j =>
      simp only [dyadPhi_succ]
      refine dyadCut_monotone ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ ht
      refine inv_anti₀ (by positivity) ?_
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]

/-- For `t ≥ 0` the cutoffs are antitone in `k`. -/
lemma dyadPhi_antitone {k l : ℕ} (hkl : k ≤ l) {t : ℝ} (ht : 0 ≤ t) :
    dyadPhi l t ≤ dyadPhi k t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction m with
  | zero => simp
  | succ m ih =>
      refine le_trans ?_ ih
      rw [show k + (m + 1) = (k + m) + 1 by omega]
      exact dyadPhi_succ_le (k + m) ht

/-- The support condition: `ψ_k` vanishes below the dyadic scale. -/
lemma dyadPsi_zero_of_le (k : ℕ) {t : ℝ} (h : t ≤ (2 : ℝ) ^ k) : dyadPsi (k + 1) t = 0 := by
  simp only [dyadPsi, dyadPhi_succ]
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : dyadCut (t / 2 ^ k) = 0 := dyadCut_zero_of_le_one (by
    rw [div_le_one hk]
    exact h)
  have h2 : dyadCut (t / 2 ^ (k + 1)) = 0 := dyadCut_zero_of_le_one (by
    rw [div_le_one (by positivity)]
    calc t ≤ (2 : ℝ) ^ k := h
      _ ≤ 2 ^ (k + 1) := by
          rw [pow_succ]
          nlinarith [hk])
  rw [h1, h2]
  ring

/-- The support condition: `ψ_k` vanishes above the dyadic scale. -/
lemma dyadPsi_zero_of_ge (k : ℕ) {t : ℝ} (h : (2 : ℝ) ^ (k + 2) ≤ t) : dyadPsi (k + 1) t = 0 := by
  simp only [dyadPsi, dyadPhi_succ]
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hEq : (2 : ℝ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [pow_succ]
    ring
  rw [hEq] at h
  have hp : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    ring
  have hsplit : 2 * (2 : ℝ) ^ k ≤ t := by nlinarith [hk, h]
  have h1 : dyadCut (t / 2 ^ k) = 1 := dyadCut_one_of_two_le (by
    rw [le_div_iff₀ hk]
    exact hsplit)
  have h2 : dyadCut (t / 2 ^ (k + 1)) = 1 := dyadCut_one_of_two_le (by
    rw [le_div_iff₀ (by positivity)]
    exact h)
  rw [h1, h2]
  ring

/-- Telescoping of the partial sums. -/
lemma dyadPsi_sum_range (K : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range K, dyadPsi k t = 1 - dyadPhi K t := by
  induction K with
  | zero => simp [dyadPhi]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, dyadPsi]
      ring

/-- The dyadic partition of unity: for `t > 0`, `∑_k ψ_k(t) = 1`. -/
lemma dyadPsi_hasSum {t : ℝ} (ht : 0 < t) : HasSum (fun k => dyadPsi k t) 1 := by
  have hbase : Tendsto (fun K : ℕ => t / 2 ^ K) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hcut : Tendsto (fun K : ℕ => dyadPhi K t) atTop (𝓝 0) := by
    have h2 : Tendsto (fun K : ℕ => 2 * (t / 2 ^ K)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hbase
    have hev : (fun K : ℕ => dyadCut (2 * (t / 2 ^ K))) =ᶠ[atTop]
        (fun K : ℕ => dyadPhi K t) := by
      filter_upwards [eventually_gt_atTop 0] with K hK
      obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hK)
      rw [dyadPhi_succ]
      congr 1
      rw [pow_succ]
      field_simp
    have h2' : Tendsto (fun K : ℕ => dyadCut (2 * (t / 2 ^ K))) atTop (𝓝 0) := by
      have h0 : dyadCut 0 = 0 := dyadCut_zero_of_le_one (by norm_num)
      have := (continuous_dyadCut.tendsto 0).comp h2
      rwa [h0] at this
    exact h2'.congr' hev
  have hlim : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, dyadPsi k t) atTop (𝓝 1) := by
    have h1 : Tendsto (fun K : ℕ => 1 - dyadPhi K t) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hcut
    rw [sub_zero] at h1
    exact h1.congr' (Filter.Eventually.of_forall (fun K => (dyadPsi_sum_range K t).symm))
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => dyadPsi_nonneg k t)]
  simpa using hlim

/-- `dyadCut (· / 2^k)` is `smoothTransition (c * · - 1)` with `c = (2^k)⁻¹`. -/
lemma dyadCut_div_eq (k : ℕ) :
    (fun s : ℝ => dyadCut (s / 2 ^ k))
      = fun s : ℝ => Real.smoothTransition (((2 : ℝ) ^ k)⁻¹ * s - 1) := by
  funext s
  rw [dyadCut]
  congr 1
  field_simp

/-- **Derivative bounds for the dyadic partition of unity.**  The `a`-th derivative of `ψ_k` is
bounded by `C_a 2^{-ak}`, uniformly in `t` (this is the estimate of §4 of the paper). -/
lemma exists_iteratedDeriv_dyadPsi_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (t : ℝ),
      |iteratedDeriv a (dyadPsi (k + 1)) t| ≤ C * (((2 : ℝ) ^ k)⁻¹) ^ a := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Calculus.iteratedDeriv_smoothTransition_scale_bound a
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro k t
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfun : (fun s : ℝ => dyadCut (s / 2 ^ k) - dyadCut (s / 2 ^ (k + 1)))
      = (fun s : ℝ => dyadCut (s / 2 ^ k)) - (fun s : ℝ => dyadCut (s / 2 ^ (k + 1))) := rfl
  have hd1 : ContDiffAt ℝ (a : ℕ∞) (fun s : ℝ => dyadCut (s / 2 ^ k)) t := by
    rw [dyadCut_div_eq k]
    fun_prop
  have hd2 : ContDiffAt ℝ (a : ℕ∞) (fun s : ℝ => dyadCut (s / 2 ^ (k + 1))) t := by
    rw [dyadCut_div_eq (k + 1)]
    fun_prop
  have h1 : |iteratedDeriv a (fun s : ℝ => dyadCut (s / 2 ^ k)) t|
      ≤ C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a := by
    rw [dyadCut_div_eq k]
    exact hC₀ _ (by positivity) t
  have h2 : |iteratedDeriv a (fun s : ℝ => dyadCut (s / 2 ^ (k + 1))) t|
      ≤ C₀ * (((2 : ℝ) ^ k)⁻¹) ^ a := by
    have h2' : |iteratedDeriv a (fun s : ℝ => dyadCut (s / 2 ^ (k + 1))) t|
        ≤ C₀ * (((2 : ℝ) ^ (k + 1))⁻¹) ^ a := by
      rw [dyadCut_div_eq (k + 1)]
      exact hC₀ _ (by positivity) t
    have h3 : (((2 : ℝ) ^ (k + 1))⁻¹) ^ a ≤ (((2 : ℝ) ^ k)⁻¹) ^ a := by
      refine pow_le_pow_left₀ (by positivity) ?_ a
      refine inv_anti₀ (by positivity) ?_
      rw [pow_succ]
      nlinarith [hpow]
    have h4 : (0 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ a := by positivity
    nlinarith [h2', h3, hC₀pos, h4]
  have hrew : dyadPsi (k + 1)
      = (fun s : ℝ => dyadCut (s / 2 ^ k)) - (fun s : ℝ => dyadCut (s / 2 ^ (k + 1))) := by
    rw [show dyadPsi (k + 1) = fun s : ℝ => dyadCut (s / 2 ^ k) - dyadCut (s / 2 ^ (k + 1))
      from by funext s; rw [dyadPsi, dyadPhi_succ, dyadPhi_succ]]
    exact hfun
  rw [hrew, iteratedDeriv_sub hd1 hd2]
  have hx1 := (abs_le.mp h1).1
  have hx2 := (abs_le.mp h1).2
  have hy1 := (abs_le.mp h2).1
  have hy2 := (abs_le.mp h2).2
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith

/-- The dyadic partition of unity, as a `tsum`. -/
lemma dyadPsi_tsum {t : ℝ} (ht : 0 < t) : ∑' k, dyadPsi k t = 1 :=
  (dyadPsi_hasSum ht).tsum_eq

section Radial

/-- The radial cutoff `x ↦ dyadCut (c‖x‖)` on `ℝᵈ`. -/
noncomputable def radialCut (c : ℝ) (x : ℝᵈ) : ℝ := dyadCut (c * ‖x‖)

/-- The radial version `x ↦ ψ_k(‖x‖)` of the dyadic partition of unity. -/
noncomputable def radialPsi (k : ℕ) (x : ℝᵈ) : ℝ := dyadPsi k ‖x‖

lemma radialPsi_nonneg (k : ℕ) (x : ℝᵈ) : 0 ≤ radialPsi k x := dyadPsi_nonneg k ‖x‖

lemma radialPsi_le_one (k : ℕ) (x : ℝᵈ) : radialPsi k x ≤ 1 := dyadPsi_le_one k ‖x‖

/-- The radial dyadic partition of unity on `ℝᵈ \ {0}`. -/
lemma radialPsi_tsum {x : ℝᵈ} (hx : x ≠ 0) : ∑' k, radialPsi k x = 1 :=
  dyadPsi_tsum (norm_pos_iff.mpr hx)

/-- The support condition: `ψ_{k+1}(‖x‖) = 0` for `‖x‖ ≤ 2^k`. -/
lemma radialPsi_zero_of_norm_le (k : ℕ) {x : ℝᵈ} (h : ‖x‖ ≤ (2 : ℝ) ^ k) :
    radialPsi (k + 1) x = 0 :=
  dyadPsi_zero_of_le k h

/-- The support condition: `ψ_{k+1}(‖x‖) = 0` for `‖x‖ ≥ 2^{k+2}`. -/
lemma radialPsi_zero_of_norm_ge (k : ℕ) {x : ℝᵈ} (h : (2 : ℝ) ^ (k + 2) ≤ ‖x‖) :
    radialPsi (k + 1) x = 0 :=
  dyadPsi_zero_of_ge k h

/-- Only the `ψ_k` with `k` in the dyadic range of `‖x‖` can be nonzero. -/
lemma radialPsi_zero_of_norm_lt (k : ℕ) {x : ℝᵈ} (h : ‖x‖ < (2 : ℝ) ^ (k + 1)) :
    radialPsi (k + 2) x = 0 :=
  dyadPsi_zero_of_le (k + 1) h.le

lemma radialPsi_zero_of_norm_gt (k : ℕ) {x : ℝᵈ} (h : (2 : ℝ) ^ (k + 3) < ‖x‖) :
    radialPsi (k + 2) x = 0 :=
  dyadPsi_zero_of_ge (k + 1) h.le

end Radial

end Submission.FUP
