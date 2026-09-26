import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.EpsForm.critNearBase

namespace Work.Drive.Mono.Band

open scoped RealInnerProductSpace
open LeanEval.KnotTheory.PardonDistortion

/-- The derivative of the height in direction `n` is `(innerSL ℝ n) ∘L (fderiv of par)`.  Recorded
here for convenience (it is `Work.Drive.EpsForm.fderiv_height_eq` together with the definition of
`heightOf`). -/
theorem fderiv_heightOf_eq_compl (ψ : Submission.Diffeo) (n : R3) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) p
      = (innerSL ℝ n) ∘L Work.Drive.EpsForm.parDeriv ψ p :=
  Work.Drive.EpsForm.fderiv_height_eq ψ n p

/-- Near a direction `n₀` at which the critical set of the height `⟪n₀, par ψ ·⟫` inside the compact
set `K` is contained in the finite set `X`, every critical point in `K` of the height `⟪n, par ψ ·⟫`
for a nearby direction `n` lies within distance `r` of `X`.  (Proof as in
`Work.Drive.EpsForm.no_crit_off_balls`: the critical derivative is
`fderiv (heightOf ψ n) = ∑_i n_i • fderiv (Φ_i)`; on the compact set
`K ∖ ⋃_{x ∈ X} ball x r` it is bounded below in norm at `n₀` and converges uniformly to
`fderiv (heightOf ψ n₀)` as `n → n₀`.) -/
theorem no_crit_off_isCompact (ψ : Submission.Diffeo)
    (n₀ : LeanEval.KnotTheory.PardonDistortion.R3) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (X : Finset (ℝ × ℝ))
    (hX : ∀ p ∈ K, fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) p = 0 → p ∈ X)
    {r : ℝ} (hr : 0 < r) :
    ∃ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U ∧ n₀ ∈ U ∧
      ∀ n ∈ U, ∀ p ∈ K, fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) p = 0 →
        ∃ x ∈ X, ‖p - x‖ < r := by
  classical
  -- The union of the `r`-balls around the elements of `X`, and its complement in `K`.
  set U : Set (ℝ × ℝ) := ⋃ x ∈ (X : Set (ℝ × ℝ)), Metric.ball x r with hU
  set A : Set (ℝ × ℝ) := K \ U with hA
  have hUopen : IsOpen U := by rw [hU]; exact isOpen_biUnion fun x _ => Metric.isOpen_ball
  have hmem_ball : ∀ {p x : ℝ × ℝ}, p ∈ Metric.ball x r ↔ ‖p - x‖ < r := by
    intro p x; rw [Metric.mem_ball, dist_eq_norm]
  have hmemU : ∀ p : ℝ × ℝ, p ∈ U ↔ ∃ x ∈ X, ‖p - x‖ < r := by
    intro p
    rw [hU, Set.mem_iUnion₂]
    constructor
    · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, hmem_ball.mp hpx⟩
    · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, hmem_ball.mpr hpx⟩
  have hAcomp : IsCompact A := hK.of_isClosed_subset (hK.isClosed.sdiff hUopen) Set.sdiff_subset
  -- No point of `A` is critical for the base direction `n₀`.
  have hA_nocrit : ∀ p ∈ A, fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) p ≠ 0 := by
    intro p hp hzero
    have hp' : p ∈ K ∧ p ∉ U := by simpa [hA] using hp
    exact hp'.2 ((hmemU p).mpr ⟨p, hX p hp'.1 hzero, by simpa using hr⟩)
  -- Continuity of `p ↦ fderiv ℝ (heightOf ψ n₀) p`.
  have hF0cont : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) p) := by
    have heq : (fun p : ℝ × ℝ => fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) p)
        = fun p : ℝ × ℝ => (innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p := by
      funext p; exact fderiv_heightOf_eq_compl ψ n₀ p
    rw [heq]
    exact ((((ContinuousLinearMap.compL ℝ (ℝ × ℝ) R3 ℝ) (innerSL ℝ n₀))).continuous).comp
      (Work.Drive.EpsForm.parDeriv_continuous ψ)
  by_cases hAne : A.Nonempty
  · -- On the nonempty compact set `A` the norm of the base derivative has a positive minimum.
    obtain ⟨c, hcA, hcmin⟩ := hAcomp.exists_isMinOn hAne hF0cont.continuousOn.norm
    have hcA' : c ∈ K ∧ c ∉ U := by simpa [hA] using hcA
    have hm_pos : 0 < ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ := by
      rw [norm_pos_iff]; exact hA_nocrit c hcA
    -- `M` bounds `‖parDeriv ψ‖` on `A`.
    obtain ⟨M, hM⟩ := hAcomp.exists_bound_of_continuousOn
      (Work.Drive.EpsForm.parDeriv_continuous ψ).continuousOn
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM c hcA)
    have hδpos : 0 < ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1)) := by
      apply div_pos hm_pos; linarith
    refine ⟨Metric.ball n₀ (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))),
      Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
    intro n hn p hpK hcrit
    by_contra hcon
    have hcon' : ∀ x ∈ X, r ≤ ‖p - x‖ := by
      intro x hx
      by_contra hlt
      exact hcon ⟨x, hx, not_le.mp hlt⟩
    have hpnotU : p ∉ U := fun hmem => by
      obtain ⟨x, hx, hpx⟩ := (hmemU p).mp hmem
      exact absurd hpx (not_lt.mpr (hcon' x hx))
    have hpA : p ∈ A := by rw [hA]; exact ⟨hpK, hpnotU⟩
    have hcrit' : (innerSL ℝ n) ∘L Work.Drive.EpsForm.parDeriv ψ p = 0 := by
      rw [← fderiv_heightOf_eq_compl ψ n p]; exact hcrit
    -- decomposition of the derivative in direction `n`
    have hdecomp : (innerSL ℝ n) ∘L Work.Drive.EpsForm.parDeriv ψ p =
        ((innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p)
          + ((innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p) := by
      refine ContinuousLinearMap.ext fun y => ?_
      simp only [add_apply, ContinuousLinearMap.comp_apply]
      rw [innerSL_apply_apply, innerSL_apply_apply, innerSL_apply_apply, inner_sub_left]
      ring
    have hb : ‖(innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ ≤ ‖n - n₀‖ * M := by
      calc ‖(innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p‖
          ≤ ‖(innerSL ℝ (n - n₀))‖ * ‖Work.Drive.EpsForm.parDeriv ψ p‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖n - n₀‖ * ‖Work.Drive.EpsForm.parDeriv ψ p‖ := by rw [innerSL_apply_norm]
        _ ≤ ‖n - n₀‖ * M := mul_le_mul_of_nonneg_left (hM p hpA) (norm_nonneg _)
    have hδM : (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))) * M
        ≤ ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / 2 := by
      have h1 : (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))) * M
          ≤ (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))) * (M + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hδpos.le
      have h2 : (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))) * (M + 1)
          = ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / 2 := by
        rw [div_mul_eq_mul_div, mul_comm (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖) (M + 1),
          mul_comm 2 (M + 1)]
        exact mul_div_mul_left _ 2 (by linarith)
      linarith
    have hlt : ‖n - n₀‖ * M < ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ := by
      have h1 : ‖n - n₀‖ * M
          ≤ (‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / (2 * (M + 1))) * M :=
        mul_le_mul_of_nonneg_right (le_of_lt hn) hMnn
      have h2 : ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ / 2
          < ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖ := by linarith
      linarith
    -- hence the derivative in direction `n` does not vanish at `p ∈ A`
    have hnorm : 0 < ‖(innerSL ℝ n) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ := by
      rw [hdecomp]
      have htri : ‖(innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ ≤
          ‖((innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p)
              + ((innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p)‖
            + ‖(innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ := by
        calc ‖(innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p‖
            = ‖(((innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p)
                + ((innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p))
                - ((innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p)‖ := by
              rw [add_sub_cancel_right]
          _ ≤ ‖((innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p)
                + ((innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p)‖
                + ‖(innerSL ℝ (n - n₀)) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ := norm_sub_le _ _
      have hmin : ‖fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) c‖
          ≤ ‖(innerSL ℝ n₀) ∘L Work.Drive.EpsForm.parDeriv ψ p‖ := by
        rw [← fderiv_heightOf_eq_compl ψ n₀ p]; exact hcmin hpA
      linarith
    exact (norm_pos_iff.mp hnorm) hcrit'
  · -- `A` is empty: every point of `K` is already within `r` of an element of `X`.
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ n₀, ?_⟩
    intro n _ p hpK _
    have hpU : p ∈ U := by
      by_contra hmem
      exact hAne ⟨p, by rw [hA]; exact ⟨hpK, hmem⟩⟩
    exact (hmemU p).mp hpU

end Work.Drive.Mono.Band
