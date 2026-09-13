import Submission.Savin.IterationBound

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **Savin's interior Hessian estimate (Theorem 1.3), concrete form.**  For a base `A` of the
ellipticity class `(c, c')` with `σ₂(A) = 1` and `tr A > 0`, any `C²` solution of `σ₂(A + D²u) = 1`
on `ball 0 2` on the positive branch which is small on `ball 0 2` has a bounded trace of `A + D²u`
on the half ball. -/
theorem savin_hessian_bound {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ (C Λ₀ : ℝ), 0 < C ∧ 0 < Λ₀ ∧
      ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (u : ℝ⁴ → ℝ) (Λ : ℝ),
        A.IsSymmetric → s2 A = 1 → 0 < trOp A →
        (∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫) →
        (∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2) →
        0 < Λ → Λ ≤ Λ₀ →
        ContDiffOn ℝ 2 u (ball 0 2) →
        (∀ x ∈ ball 0 2, s2 (A + hessOp u x) = 1) →
        (∀ x ∈ ball 0 2, 0 < trOp (A + hessOp u x)) →
        (∀ x ∈ ball 0 2, |u x| ≤ Λ) →
        ∀ x ∈ closedBall 0 (1 / 2), trOp (A + hessOp u x) ≤ C := by
  obtain ⟨θ, hθpos, hθ256, ε, hεpos, hFlat⟩ :=
    improvement_of_flatness (c := c / 2) (c' := 2 * c') (by positivity) (by positivity)
  have hq1 : qDecay θ < 1 := by
    have h := qDecay_le_quarter hθ256
    linarith
  have h1mq : 0 < 1 - qDecay θ := by linarith
  have hθ2 : θ < 2 := by linarith
  have hKc : 0 < Kcof θ := Kcof_pos hθpos
  set Λ₀ : ℝ := min (ε / 64) (min (c / 2) c' * (1 - qDecay θ) / (64 * Kcof θ)) with hΛ₀def
  have hΛ₀pos : 0 < Λ₀ := by
    rw [hΛ₀def]
    refine lt_min (by linarith) (div_pos (mul_pos (lt_min (by linarith) hc') h1mq) (by linarith))
  have hΛ₀ε : Λ₀ ≤ ε / 64 := by rw [hΛ₀def]; exact min_le_left _ _
  have hΛ₀d : Λ₀ ≤ min (c / 2) c' * (1 - qDecay θ) / (64 * Kcof θ) := by
    rw [hΛ₀def]; exact min_le_right _ _
  refine ⟨4 * c' / 3 + 256 * Kquad θ * Λ₀ / (1 - qDecay θ), Λ₀, ?_, hΛ₀pos, ?_⟩
  · have h1 : 0 < 4 * c' / 3 := by positivity
    have h2 : 0 < 256 * Kquad θ * Λ₀ / (1 - qDecay θ) :=
      div_pos (mul_pos (by linarith [Kquad_pos hθpos]) hΛ₀pos) h1mq
    linarith
  intro A u Λ hAsym hA1 hAtr hAcq hAcq' hΛpos hΛle hu hueq hupos hflat x₀ hx₀
  have hx₀n : ‖x₀‖ ≤ 1 / 2 := by rwa [mem_closedBall, dist_zero_right] at hx₀
  -- the rescaled, recentred function
  set U : ℝ⁴ → ℝ := fun y => u (x₀ + ((1 : ℝ) / 4) • y) / ((1 : ℝ) / 4) ^ 2 with hUdef
  have hmem : ∀ y ∈ ball 0 2, x₀ + ((1 : ℝ) / 4) • y ∈ ball 0 2 := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy ⊢
    calc ‖x₀ + ((1 : ℝ) / 4) • y‖ ≤ ‖x₀‖ + ‖((1 : ℝ) / 4) • y‖ := norm_add_le _ _
      _ = ‖x₀‖ + (1 / 4) * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      _ < 1 / 2 + (1 / 4) * 2 := by linarith
      _ = 1 := by norm_num
      _ < 2 := by norm_num
  have h0mem : x₀ ∈ ball 0 2 := by
    rw [mem_ball, dist_zero_right]; linarith
  have hhess : ∀ y ∈ ball 0 2, hessOp U y = hessOp u (x₀ + ((1 : ℝ) / 4) • y) := by
    intro y hy
    rw [hUdef]
    exact hessOp_comp_affine_div (by norm_num)
      (hu.contDiffAt (isOpen_ball.mem_nhds (hmem y hy)))
  have hUcd : ContDiffOn ℝ 2 U (ball 0 2) := by
    have h1 : ContDiffOn ℝ 2 (fun y : ℝ⁴ => u (x₀ + ((1 : ℝ) / 4) • y)) (ball 0 2) :=
      hu.comp ((contDiffOn_const.add (contDiffOn_id.const_smul ((1 : ℝ) / 4)))) hmem
    have h2 := h1.div_const (((1 : ℝ) / 4) ^ 2)
    refine h2.congr fun y hy => ?_
    rw [hUdef]
  have hUeq : ∀ y ∈ ball 0 2, s2 (A + hessOp U y) = 1 := by
    intro y hy
    rw [hhess y hy]
    exact hueq _ (hmem y hy)
  have hUpos : ∀ y ∈ ball 0 2, 0 < trOp (A + hessOp U y) := by
    intro y hy
    rw [hhess y hy]
    exact hupos _ (hmem y hy)
  have hUflat : ∀ y ∈ ball 0 (2 * (1 / 2)), |U y| ≤ (64 * Λ) * (1 / 2) ^ 2 := by
    intro y hy
    have hy2 : y ∈ ball 0 2 := by
      rw [mem_ball, dist_zero_right] at hy ⊢
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hy
      linarith
    have h1 : |U y| = |u (x₀ + ((1 : ℝ) / 4) • y)| / ((1 : ℝ) / 4) ^ 2 := by
      rw [hUdef, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < ((1 : ℝ) / 4) ^ 2)]
    rw [h1]
    have h2 := hflat _ (hmem y hy2)
    have h3 : ((1 : ℝ) / 4) ^ 2 = 1 / 16 := by norm_num
    rw [h3]
    have h4 : (64 * Λ) * (1 / 2) ^ 2 = 16 * Λ := by ring
    rw [h4]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 16)]
    linarith
  have hdriftc : (64 * Λ) * Kcof θ / (1 - qDecay θ) ≤ c / 2 := by
    have h1 : Λ ≤ (c / 2) * (1 - qDecay θ) / (64 * Kcof θ) := by
      refine le_trans hΛle (le_trans hΛ₀d ?_)
      refine div_le_div_of_nonneg_right ?_ (by linarith : (0 : ℝ) ≤ 64 * Kcof θ)
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) h1mq.le
    have h2 : 64 * Kcof θ / (1 - qDecay θ) * Λ ≤ c / 2 := by
      have h3 : 0 ≤ 64 * Kcof θ / (1 - qDecay θ) := by positivity
      calc 64 * Kcof θ / (1 - qDecay θ) * Λ
          ≤ 64 * Kcof θ / (1 - qDecay θ) * ((c / 2) * (1 - qDecay θ) / (64 * Kcof θ)) :=
            mul_le_mul_of_nonneg_left h1 h3
        _ = c / 2 := by field_simp
    calc (64 * Λ) * Kcof θ / (1 - qDecay θ)
        = 64 * Kcof θ / (1 - qDecay θ) * Λ := by ring
      _ ≤ c / 2 := h2
  have hdriftc' : (64 * Λ) * Kcof θ / (1 - qDecay θ) ≤ c' := by
    have h1 : Λ ≤ c' * (1 - qDecay θ) / (64 * Kcof θ) := by
      refine le_trans hΛle (le_trans hΛ₀d ?_)
      refine div_le_div_of_nonneg_right ?_ (by linarith : (0 : ℝ) ≤ 64 * Kcof θ)
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) h1mq.le
    have h2 : 64 * Kcof θ / (1 - qDecay θ) * Λ ≤ c' := by
      have h3 : 0 ≤ 64 * Kcof θ / (1 - qDecay θ) := by positivity
      calc 64 * Kcof θ / (1 - qDecay θ) * Λ
          ≤ 64 * Kcof θ / (1 - qDecay θ) * (c' * (1 - qDecay θ) / (64 * Kcof θ)) :=
            mul_le_mul_of_nonneg_left h1 h3
        _ = c' := by field_simp
    calc (64 * Λ) * Kcof θ / (1 - qDecay θ)
        = 64 * Kcof θ / (1 - qDecay θ) * Λ := by ring
      _ ≤ c' := h2
  have hΛε : 64 * Λ ≤ ε := by
    have := le_trans hΛle hΛ₀ε
    linarith
  have hdata : ∀ k : ℕ, ∃ s : IterState, IterInv c c' θ (64 * Λ) (1 / 2) A U k s :=
    iteration_data hc hc' hθpos hθ256 hFlat (by linarith) hΛε (by norm_num) (by norm_num)
      hAsym hA1 hAtr hAcq hAcq' hdriftc hdriftc' hUcd hUeq hUpos hUflat
  have hq0 : 0 ≤ qDecay θ := (qDecay_pos hθpos).le
  have hb := hess_bound_of_iterates hdata (by linarith) (by norm_num) hθpos hθ2 hq1
    (hUcd.contDiffAt (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; norm_num)))
  -- back to `u`
  have hU0 : hessOp U 0 = hessOp u x₀ := by
    rw [hhess 0 (by rw [mem_ball, dist_zero_right]; norm_num)]
    simp
  have htrace : trOp (hessOp u x₀) ≤ 256 * Kquad θ * Λ / (1 - qDecay θ) := by
    rw [← hU0, trOp_eq_sum]
    have hsum : (∑ i : Fin 4, ⟪hessOp U 0 (stdB4 i), stdB4 i⟫)
        ≤ ∑ _i : Fin 4, (Kquad θ * (64 * Λ) / (1 - qDecay θ)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h := hb (stdB4 i)
      rw [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h
      linarith [(abs_le.mp h).2]
    calc (∑ i : Fin 4, ⟪hessOp U 0 (stdB4 i), stdB4 i⟫)
        ≤ ∑ _i : Fin 4, (Kquad θ * (64 * Λ) / (1 - qDecay θ)) := hsum
      _ = 256 * Kquad θ * Λ / (1 - qDecay θ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have htrA : trOp A ≤ 4 * c' / 3 := by
    have h1 : trOp (cofOp A) = 3 * trOp A := trOp_cofOp A
    have h2 : trOp (cofOp A) ≤ 4 * c' := by
      rw [trOp_eq_sum]
      calc (∑ i : Fin 4, ⟪cofOp A (stdB4 i), stdB4 i⟫) ≤ ∑ _i : Fin 4, c' := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := hAcq' (stdB4 i)
            rwa [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h
          _ = 4 * c' := by simp
    linarith
  have hmono : 256 * Kquad θ * Λ / (1 - qDecay θ) ≤ 256 * Kquad θ * Λ₀ / (1 - qDecay θ) := by
    have hnum : 256 * Kquad θ * Λ ≤ 256 * Kquad θ * Λ₀ :=
      mul_le_mul_of_nonneg_left hΛle (by linarith [Kquad_pos hθpos])
    exact div_le_div_of_nonneg_right hnum h1mq.le
  rw [trOp_add]
  linarith [htrace, htrA, hmono]

end
end Submission
