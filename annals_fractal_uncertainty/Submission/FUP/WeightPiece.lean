import Submission.FUP.DyadicPartition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Commons.Analysis.Calculus.radialPsi_iteratedFDeriv_bound
import Submission.Commons.Analysis.Real.rpow_one_add_sq_dyadic_bound
import Submission.Commons.Analysis.Real.rpow_one_add_sq_small_bound
import Submission.Commons.Analysis.Real.dyadic_piece_arith

open Filter Metric
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The dyadic pieces `ω_k = ψ_k(‖·‖)·ω` of §4

Section 4 of the paper writes a weight `ω` as a sum of dyadic pieces `ω_k = ψ_k(‖x‖) ω(x)`, where
`1 = ∑_k ψ_k` is a partition of unity of `ℝ_{≥0}` with `ψ_k` supported in the dyadic annulus
`[2^{k-1}, 2^{k+1}]` and `|D^a ψ_k| ≤ C_a 2^{-ak}`.  The key estimate
(`eq:omega_reg_pieces` of the paper) is

`‖D^a ω_k‖_∞ ≤ C_reg' 2^{(1-a)k}` for `0 ≤ a ≤ 3`,

which is another way of writing the Kohn–Nirenberg regularity condition

`‖D^b ω(x)‖ ≤ C_reg (1 + ‖x‖²)^{(1-b)/2}`.

This module provides the "Leibniz" estimate for the pieces, in the form needed by §4.
-/

section Support

/-- `ψ_k(t) = 0` for `t ≥ 2^{k+1}` (for every `k ≥ 0`). -/
lemma dyadPsi_eq_zero_of_ge_two_pow (k : ℕ) {t : ℝ} (h : (2 : ℝ) ^ (k + 1) ≤ t) :
    dyadPsi k t = 0 := by
  cases k with
  | zero =>
    have h2 : (2 : ℝ) ≤ t := by simpa using h
    have h1 : dyadPhi 1 t = 1 := by
      rw [dyadPhi_succ]
      simpa using dyadCut_one_of_two_le h2
    show dyadPhi 0 t - dyadPhi 1 t = 0
    rw [dyadPhi_zero, h1]
    norm_num
  | succ j => exact dyadPsi_zero_of_ge j (by simpa using h)

/-- `ψ_{j+1}(t) = 0` for `t ≤ 1`. -/
lemma dyadPsi_succ_zero_of_le_one (j : ℕ) {t : ℝ} (h : t ≤ 1) : dyadPsi (j + 1) t = 0 :=
  dyadPsi_zero_of_le j (h.trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))

/-- `ψ_k(‖x‖) = 0` for `‖x‖ ≥ 2^{k+1}`. -/
lemma radialPsi_eq_zero_of_norm_ge (k : ℕ) {x : ℝᵈ} (h : (2 : ℝ) ^ (k + 1) ≤ ‖x‖) :
    radialPsi k x = 0 :=
  dyadPsi_eq_zero_of_ge_two_pow k h

/-- The topological support of `x ↦ ψ_k(‖x‖)` is contained in the ball of radius `2^{k+1}`. -/
lemma tsupport_radialPsi_subset_le (k : ℕ) :
    tsupport (radialPsi k) ⊆ {x : ℝᵈ | ‖x‖ ≤ (2 : ℝ) ^ (k + 1)} := by
  refine (isClosed_le continuous_norm continuous_const).closure_subset_iff.mpr ?_
  intro x hx
  by_contra h
  exact hx (radialPsi_eq_zero_of_norm_ge k (lt_of_not_ge h).le)

/-- The topological support of `x ↦ ψ_{k+1}(‖x‖)` is contained in the complement of the ball of
radius `2^k`. -/
lemma tsupport_radialPsi_subset_ge (k : ℕ) :
    tsupport (radialPsi (k + 1)) ⊆ {x : ℝᵈ | (2 : ℝ) ^ k ≤ ‖x‖} := by
  refine (isClosed_le continuous_const continuous_norm).closure_subset_iff.mpr ?_
  intro x hx
  by_contra h
  exact hx (radialPsi_zero_of_norm_le k (lt_of_not_ge h).le)

end Support

section Smooth

lemma contDiff_dyadPhi (m : ℕ) : ContDiff ℝ ∞ (dyadPhi m) := by
  cases m with
  | zero =>
    show ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))
    exact contDiff_const
  | succ j =>
    have hfun : dyadPhi (j + 1) = fun t : ℝ => dyadCut (t / 2 ^ j) := by
      funext t; exact dyadPhi_succ j t
    rw [hfun]
    have hdiv : ContDiff ℝ ∞ (fun t : ℝ => t / 2 ^ j) := contDiff_id.div_const _
    simpa [Function.comp_def] using ContDiff.comp (dyadCut_contDiff (n := ⊤)) hdiv

/-- Smoothness of a radial function vanishing near the origin. -/
lemma contDiff_radial_of_contDiff_infty {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hsupp : ∀ t : ℝ, t ≤ 1 → ψ t = 0) :
    ContDiff ℝ ∞ (fun y : ℝᵈ => ψ ‖y‖) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝᵈ) zero_lt_one] with z hz
    apply hsupp
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hz.le
  · exact (hψ.contDiffAt).comp y (contDiffAt_norm ℝ hy)

/-- `x ↦ ψ_k(‖x‖)` is smooth. -/
lemma contDiff_radialPsi (k : ℕ) : ContDiff ℝ 3 (radialPsi (d := d) k) := by
  cases k with
  | zero =>
    have hrad : ContDiff ℝ ∞ (fun x : ℝᵈ => Real.smoothTransition (‖x‖ - 1)) :=
      Commons.Analysis.Calculus.smoothTransition_radial_contDiff (E := ℝᵈ)
    have hfun : radialPsi (d := d) 0 = fun x : ℝᵈ => 1 - Real.smoothTransition (‖x‖ - 1) := by
      funext x
      show dyadPsi 0 ‖x‖ = 1 - Real.smoothTransition (‖x‖ - 1)
      rw [dyadPsi, dyadPhi_zero, dyadPhi_succ]
      simp [dyadCut]
    rw [hfun]
    exact (contDiff_const.sub hrad).of_le (WithTop.coe_le_coe.mpr le_top)
  | succ j =>
    have h := contDiff_radial_of_contDiff_infty (d := d)
      ((contDiff_dyadPhi (j + 1)).sub (contDiff_dyadPhi (j + 2)))
      (fun t ht => dyadPsi_succ_zero_of_le_one j ht)
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)

end Smooth


section RadialBound

/-- The function `x ↦ ψ_{k+1}(‖x‖)` is the difference of two rescaled smooth transitions. -/
lemma radialPsi_succ_eq (k : ℕ) :
    radialPsi (d := d) (k + 1) = fun y : ℝᵈ =>
      Real.smoothTransition (‖y‖ / 2 ^ k - 1) - Real.smoothTransition (‖y‖ / 2 ^ (k + 1) - 1) := by
  funext y
  show dyadPhi (k + 1) ‖y‖ - dyadPhi (k + 1 + 1) ‖y‖ = _
  rw [dyadPhi_succ k, dyadPhi_succ (k + 1)]
  rfl

/-- The derivative constant of the dyadic piece `ψ_{k+1}`. -/
noncomputable def rpsC (d : ℕ) (i : ℕ) : ℝ :=
  Classical.choose (Commons.Analysis.Calculus.radialPsi_iteratedFDeriv_bound i d)

lemma rpsC_pos (d i : ℕ) : 0 < rpsC d i :=
  (Classical.choose_spec (Commons.Analysis.Calculus.radialPsi_iteratedFDeriv_bound i d)).1

lemma radialPsi_succ_iteratedFDeriv_le (i k : ℕ) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ i (radialPsi (d := d) (k + 1)) x‖ ≤ rpsC d i * (((2 : ℝ) ^ k)⁻¹) ^ i := by
  have h := (Classical.choose_spec
    (Commons.Analysis.Calculus.radialPsi_iteratedFDeriv_bound i d)).2 k x
  rwa [← radialPsi_succ_eq (d := d) k] at h

/-- A single constant dominating all the derivative bounds of the pieces `ψ_{k+1}`, `i ≤ 3`. -/
noncomputable def rpsCps (d : ℕ) : ℝ :=
  (rpsC d 0 + rpsC d 1 + rpsC d 2 + rpsC d 3 + 1) * 8

lemma rpsCps_pos (d : ℕ) : 0 < rpsCps d := by
  rw [rpsCps]
  nlinarith [rpsC_pos d 0, rpsC_pos d 1, rpsC_pos d 2, rpsC_pos d 3]

lemma rpsC_le_sum_succ (i : ℕ) (hi : i ≤ 3) :
    rpsC d i ≤ rpsC d 0 + rpsC d 1 + rpsC d 2 + rpsC d 3 + 1 := by
  have h0 := rpsC_pos d 0; have h1 := rpsC_pos d 1
  have h2 := rpsC_pos d 2; have h3 := rpsC_pos d 3
  interval_cases i <;> nlinarith

lemma rpsC_mul_pow_le_rpsCps (i : ℕ) (hi : i ≤ 3) : rpsC d i * (2 : ℝ) ^ i ≤ rpsCps d := by
  have hpow : (2 : ℝ) ^ i ≤ 8 := by
    calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 3 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 8 := by norm_num
  have hsum := rpsC_le_sum_succ (d := d) i hi
  have hpos := rpsC_pos d i
  rw [rpsCps]
  nlinarith

/-- `((2^{j+1})⁻¹)^i = ((2^j)⁻¹)^i * (2^i)⁻¹`. -/
lemma inv_pow_succ_eq (i j : ℕ) :
    (((2 : ℝ) ^ (j + 1))⁻¹) ^ i = (((2 : ℝ) ^ j)⁻¹) ^ i * ((2 : ℝ) ^ i)⁻¹ := by
  rw [pow_succ, mul_inv_rev, mul_pow, inv_pow, mul_comm]

/-- `(((2)^j)⁻¹)^i = (((2)^{j+1})⁻¹)^i * 2^i`. -/
lemma pow_inv_succ_eq (i j : ℕ) :
    (((2 : ℝ) ^ j)⁻¹) ^ i = (((2 : ℝ) ^ (j + 1))⁻¹) ^ i * (2 : ℝ) ^ i := by
  rw [inv_pow_succ_eq i j, mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ i ≠ 0), mul_one]

/-- The derivative bound for the dyadic pieces `ψ_k`, `k ≥ 1`. -/
lemma radialPsi_iteratedFDeriv_le (i : ℕ) (hi : i ≤ 3) (k : ℕ) (hk : 1 ≤ k) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ i (radialPsi (d := d) k) x‖ ≤ rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hX : (0 : ℝ) ≤ (((2 : ℝ) ^ (j + 1))⁻¹) ^ i := by positivity
  calc ‖iteratedFDeriv ℝ i (radialPsi (d := d) (j + 1)) x‖
      ≤ rpsC d i * (((2 : ℝ) ^ j)⁻¹) ^ i := radialPsi_succ_iteratedFDeriv_le (d := d) i j x
    _ = rpsC d i * ((((2 : ℝ) ^ (j + 1))⁻¹) ^ i * (2 : ℝ) ^ i) := by rw [pow_inv_succ_eq]
    _ = (rpsC d i * (2 : ℝ) ^ i) * (((2 : ℝ) ^ (j + 1))⁻¹) ^ i := by ring
    _ ≤ rpsCps d * (((2 : ℝ) ^ (j + 1))⁻¹) ^ i :=
        mul_le_mul_of_nonneg_right (rpsC_mul_pow_le_rpsCps (d := d) i hi) hX

end RadialBound

section Piece

/-- The dyadic piece `w_k = ψ_k(‖x‖)·w(x)` of §4. -/
noncomputable def omegaPiece (k : ℕ) (w : ℝᵈ → ℝ) : ℝᵈ → ℝ :=
  fun x => radialPsi (d := d) k x * w x

lemma omegaPiece_apply (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    omegaPiece k w x = radialPsi (d := d) k x * w x := rfl

/-- For a weight vanishing on `B(0,2)` the first dyadic piece vanishes identically. -/
lemma omegaPiece_zero (w : ℝᵈ → ℝ) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) :
    omegaPiece (d := d) 0 w = fun _ => 0 := by
  funext y
  show radialPsi (d := d) 0 y * w y = 0
  by_cases hy : ‖y‖ ≤ 2
  · rw [hwzero y hy, mul_zero]
  · rw [radialPsi_eq_zero_of_norm_ge 0 (by simpa using (not_le.mp hy).le), zero_mul]

lemma iteratedFDeriv_fun_zero_apply (a : ℕ) (x : ℝᵈ) :
    iteratedFDeriv ℝ a (fun _ : ℝᵈ => (0 : ℝ)) x = 0 := by
  simp

/-- **The key estimate of §4** (`eq:omega_reg_pieces` of the paper): for a weight `w` satisfying the
Kohn–Nirenberg regularity condition `‖D^b w(x)‖ ≤ C_reg (1+‖x‖²)^{(1-b)/2}` (`b ≤ 3`) and vanishing
on `B(0,2)`, the dyadic pieces `w_k = ψ_k(‖·‖)·w` satisfy
`‖D^a w_k‖_∞ ≤ C_reg C 2^{(1-a)k}` for `a ≤ 3`. -/
theorem norm_iteratedFDeriv_omegaPiece_le (a : ℕ) (ha : a ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Creg : ℝ) (w : ℝᵈ → ℝ), 0 < Creg → ContDiff ℝ 3 w →
      (∀ x, ‖x‖ ≤ 2 → w x = 0) →
      (∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
        ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2)) →
      ∀ (k : ℕ) (x : ℝᵈ),
        ‖iteratedFDeriv ℝ a (omegaPiece (d := d) k w) x‖
          ≤ Creg * ((∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * (rpsCps d * 4) + 1)
              * (2 : ℝ) ^ ((k : ℝ) * (1 - (a : ℝ))) := by
  refine ⟨(∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * (rpsCps d * 4) + 1, ?_, ?_⟩
  · have := rpsCps_pos d; positivity
  · intro Creg w hCreg hwcd hwzero hwbound k x
    cases k with
    | zero =>
      rw [omegaPiece_zero (d := d) w hwzero, iteratedFDeriv_fun_zero_apply]
      simp only [norm_zero]
      have hC : 0 < (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * (rpsCps d * 4) + 1 := by
        have h1 := rpsCps_pos d
        have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) := by positivity
        nlinarith
      exact mul_nonneg (mul_nonneg hCreg.le hC.le) (by positivity)
    | succ j =>
      have hC : 0 < (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * (rpsCps d * 4) + 1 := by
        have h1 := rpsCps_pos d
        have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) := by positivity
        nlinarith
      by_cases hx : x ∈ tsupport (radialPsi (d := d) (j + 1))
      · have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
          (contDiff_radialPsi (d := d) (j + 1)) hwcd x (n := a) (by exact_mod_cast ha)
        have hlow : (2 : ℝ) ^ j ≤ ‖x‖ := tsupport_radialPsi_subset_ge j hx
        have hhigh : ‖x‖ ≤ (2 : ℝ) ^ (j + 2) := by
          have := tsupport_radialPsi_subset_le (d := d) (j + 1) hx
          simpa using this
        refine hleib.trans ?_
        have hterm : ∀ i ∈ Finset.range (a + 1),
            (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i (radialPsi (d := d) (j + 1)) x‖ *
              ‖iteratedFDeriv ℝ (a - i) w x‖
            ≤ (a.choose i : ℝ) * rpsCps d * 4 * Creg
                * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - (a : ℝ))) := by
          intro i hi
          have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hb : a - i ≤ 3 := by omega
          have hrad := radialPsi_iteratedFDeriv_le (d := d) i (by omega) (j + 1) (by omega) x
          have hom := hwbound (a - i) hb x
          have hnum := Commons.Analysis.Real.rpow_one_add_sq_dyadic_bound (j + 1) (a - i) ‖x‖
            (by omega) hb (by simpa using hlow) (by simpa using hhigh)
          have harith := Commons.Analysis.Real.dyadic_piece_arith i a j hia
          have hX : (0 : ℝ) ≤ (((2 : ℝ) ^ (j + 1))⁻¹) ^ i := by positivity
          have hY : (0 : ℝ) ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - ((a - i : ℕ) : ℝ))) :=
            (Real.rpow_pos_of_pos (by norm_num) _).le
          have hbi : (0 : ℝ) ≤ (a.choose i : ℝ) := by positivity
          have hT : (0 : ℝ) ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - (a : ℝ))) :=
            (Real.rpow_pos_of_pos (by norm_num) _).le
          calc (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i (radialPsi (d := d) (j + 1)) x‖ *
                ‖iteratedFDeriv ℝ (a - i) w x‖
              ≤ (a.choose i : ℝ) * (rpsCps d * (((2 : ℝ) ^ (j + 1))⁻¹) ^ i) *
                  (Creg * (4 * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - ((a - i : ℕ) : ℝ))))) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hrad hbi) ?_ (norm_nonneg _) ?_
                · exact hom.trans (mul_le_mul_of_nonneg_left hnum hCreg.le)
                · have := rpsCps_pos d; positivity
            _ = ((a.choose i : ℝ) * rpsCps d * 4 * Creg)
                  * ((((2 : ℝ) ^ (j + 1))⁻¹) ^ i
                      * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - ((a - i : ℕ) : ℝ)))) := by ring
            _ = (a.choose i : ℝ) * rpsCps d * 4 * Creg
                  * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - (a : ℝ))) := by rw [harith]
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.sum_mul]
        have hsum : (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * rpsCps d * 4 * Creg)
            = (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * rpsCps d * 4 * Creg := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        rw [hsum]
        have hT : (0 : ℝ) ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 - (a : ℝ))) :=
          (Real.rpow_pos_of_pos (by norm_num) _).le
        have hle : (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * rpsCps d * 4 * Creg
            ≤ Creg * ((∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) * (rpsCps d * 4) + 1) := by
          nlinarith [hCreg, hC, rpsCps_pos d]
        exact mul_le_mul_of_nonneg_right hle hT
      · have heq : omegaPiece (d := d) (j + 1) w =ᶠ[𝓝 x] 0 := by
          rw [notMem_tsupport_iff_eventuallyEq] at hx
          filter_upwards [hx] with y hy
          show radialPsi (d := d) (j + 1) y * w y = 0
          rw [hy]
          simp
        have h1 : iteratedFDeriv ℝ a (omegaPiece (d := d) (j + 1) w) =ᶠ[𝓝 x]
            iteratedFDeriv ℝ a (fun _ : ℝᵈ => (0 : ℝ)) := heq.iteratedFDeriv ℝ a
        have h2 : iteratedFDeriv ℝ a (omegaPiece (d := d) (j + 1) w) x = 0 := by
          have h3 := h1.eq_of_nhds
          rwa [iteratedFDeriv_fun_zero_apply] at h3
        rw [h2]
        simp only [norm_zero]
        exact mul_nonneg (mul_nonneg hCreg.le hC.le) (by positivity)

end Piece
