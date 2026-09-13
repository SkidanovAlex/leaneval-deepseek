import Submission.Savin.Iteration
import Submission.Commons.Analysis.Calculus.FDeriv.second_difference_quotient

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The arithmetic behind the final Hessian bound: the drift of the flatness ratio is absorbed
by the geometric series. -/
theorem hess_bound_arith {Λ θ q : ℝ} (hΛ : 0 ≤ Λ) (hθ : 0 < θ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℕ) :
    4 * (Λ * q ^ k) / θ ^ 2 + Kquad θ * Λ * (1 - q ^ k) / (1 - q) ≤ Kquad θ * Λ / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hmain : Kquad θ * Λ / (1 - q)
      - (4 * (Λ * q ^ k) / θ ^ 2 + Kquad θ * Λ * (1 - q ^ k) / (1 - q))
      = Λ * q ^ k * (1 + q) * (4 / (θ ^ 2 * (1 - q))) := by
    rw [Kquad]
    field_simp
    ring
  have h1 : 0 ≤ Λ * q ^ k := mul_nonneg hΛ (pow_nonneg hq0 k)
  have h2 : 0 ≤ 1 + q := by linarith
  have hnn : 0 ≤ Λ * q ^ k * (1 + q) * (4 / (θ ^ 2 * (1 - q))) :=
    mul_nonneg (mul_nonneg h1 h2) (by positivity)
  linarith [hmain, hnn]

/-- The invariant of the Caffarelli iteration holds at every level. -/
theorem iteration_data {c c' θ Λ R₀ : ℝ} {A₀ : ℝ⁴ →L[ℝ] ℝ⁴} {u : ℝ⁴ → ℝ}
    (hc : 0 < c) (hc' : 0 < c') (hθpos : 0 < θ) (hθ256 : θ ≤ 1 / 256)
    {ε : ℝ} (hFlat : FlatGood (c / 2) (2 * c') θ ε)
    (hΛpos : 0 < Λ) (hΛε : Λ ≤ ε) (hR₀pos : 0 < R₀) (hR₀1 : R₀ ≤ 1)
    (hA₀sym : A₀.IsSymmetric) (hA₀1 : s2 A₀ = 1) (hA₀tr : 0 < trOp A₀)
    (hA₀cq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A₀ v, v⟫)
    (hA₀cq' : ∀ v : ℝ⁴, ⟪cofOp A₀ v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hdriftc : Λ * Kcof θ / (1 - qDecay θ) ≤ c / 2)
    (hdriftc' : Λ * Kcof θ / (1 - qDecay θ) ≤ c')
    (hu : ContDiffOn ℝ 2 u (ball 0 2))
    (hueq : ∀ x ∈ ball 0 2, s2 (A₀ + hessOp u x) = 1)
    (hupos : ∀ x ∈ ball 0 2, 0 < trOp (A₀ + hessOp u x))
    (hflat0 : ∀ x ∈ ball 0 (2 * R₀), |u x| ≤ Λ * R₀ ^ 2) :
    ∀ k : ℕ, ∃ s : IterState, IterInv c c' θ Λ R₀ A₀ u k s := by
  intro k
  induction k with
  | zero => exact ⟨_, IterInv_zero hΛpos hR₀pos hA₀sym hA₀1 hA₀tr hA₀cq hA₀cq' hflat0⟩
  | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨s', hs'⟩ := IterInv_step hc hc' hθpos hθ256 hFlat hΛpos hΛε hR₀pos hR₀1 hA₀sym
        hdriftc hdriftc' hu hueq hupos hs
      exact ⟨s', hs'⟩

/-- **The final step of the Caffarelli iteration.**  From the flatness data at all levels we obtain
the bound on the quadratic form of the Hessian at the centre. -/
theorem hess_bound_of_iterates {c c' θ Λ R₀ : ℝ} {A₀ : ℝ⁴ →L[ℝ] ℝ⁴} {u : ℝ⁴ → ℝ}
    (hdata : ∀ k : ℕ, ∃ s : IterState, IterInv c c' θ Λ R₀ A₀ u k s)
    (hΛ : 0 ≤ Λ) (hR₀ : 0 < R₀) (hθpos : 0 < θ) (hθ2 : θ < 2)
    (hq1 : qDecay θ < 1) (hu : ContDiffAt ℝ 2 u 0) :
    ∀ v : ℝ⁴, |⟪hessOp u 0 v, v⟫| ≤ Kquad θ * Λ / (1 - qDecay θ) * ‖v‖ ^ 2 := by
  choose s hs using hdata
  have hRk : ∀ k, (s k).R = R₀ * (θ / 2) ^ k := fun k => (hs k).2.2.1
  have hq0 : 0 ≤ qDecay θ := (qDecay_pos hθpos).le
  have htpos : ∀ k, 0 < θ * (s k).R := fun k => mul_pos hθpos (hs k).2.1
  have htne : ∀ k, θ * (s k).R ≠ 0 := fun k => ne_of_gt (htpos k)
  have htend : Tendsto (fun k : ℕ => θ * (s k).R) atTop (𝓝 0) := by
    have hb : Tendsto (fun k : ℕ => (θ / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith)
    have h : Tendsto (fun k : ℕ => (θ * R₀) * (θ / 2) ^ k) atTop (𝓝 ((θ * R₀) * 0)) :=
      hb.const_mul (θ * R₀)
    rw [mul_zero] at h
    exact Tendsto.congr' (Eventually.of_forall (fun k => by
      show θ * R₀ * (θ / 2) ^ k = θ * (s k).R
      rw [hRk k]; ring)) h
  -- ## the unit case
  have hunit : ∀ v : ℝ⁴, ‖v‖ = 1 → |⟪hessOp u 0 v, v⟫| ≤ Kquad θ * Λ / (1 - qDecay θ) := by
    intro v hv
    have hbound : ∀ k : ℕ,
        |(u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0) / (θ * (s k).R) ^ 2|
          ≤ Kquad θ * Λ / (1 - qDecay θ) := by
      intro k
      obtain ⟨hMsym, hRpos, hRk', hρpos, hρk', hd0, hdle, hMbd, hA1, hAtr, hAcq, hAcq', hflat⟩ := hs k
      have hRne : (s k).R ≠ 0 := ne_of_gt hRpos
      have hapos : 0 < θ * (s k).R := htpos k
      have hane : θ * (s k).R ≠ 0 := htne k
      have ht2 : (θ * (s k).R) ^ 2 = θ ^ 2 * (s k).R ^ 2 := by ring
      have hQa : ⟪(s k).M ((θ * (s k).R) • v), (θ * (s k).R) • v⟫
          = (θ * (s k).R) ^ 2 * ⟪(s k).M v, v⟫ := by
        rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
      have hQb : ⟪(s k).M (-((θ * (s k).R) • v)), -((θ * (s k).R) • v)⟫
          = (θ * (s k).R) ^ 2 * ⟪(s k).M v, v⟫ := by
        rw [show -((θ * (s k).R) • v) = (-(θ * (s k).R)) • v from by rw [neg_smul],
          map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      have hLa : (s k).L ((θ * (s k).R) • v) = (θ * (s k).R) * ((s k).L v) := by
        rw [map_smul, smul_eq_mul]
      have hLb : (s k).L (-((θ * (s k).R) • v)) = -((θ * (s k).R) * ((s k).L v)) := by
        rw [show -((θ * (s k).R) • v) = (-(θ * (s k).R)) • v from by rw [neg_smul],
          map_smul, smul_eq_mul]
        ring
      have hL0 : (s k).L 0 = 0 := map_zero _
      have hM0 : ⟪(s k).M 0, 0⟫ = 0 := by rw [map_zero, inner_zero_left]
      have hQ : (⟪(s k).M ((θ * (s k).R) • v), (θ * (s k).R) • v⟫ / 2
            + (s k).L ((θ * (s k).R) • v) + (s k).c)
          + (⟪(s k).M (-((θ * (s k).R) • v)), -((θ * (s k).R) • v)⟫ / 2
            + (s k).L (-((θ * (s k).R) • v)) + (s k).c)
          - 2 * (⟪(s k).M 0, 0⟫ / 2 + (s k).L 0 + (s k).c)
          = (θ * (s k).R) ^ 2 * ⟪(s k).M v, v⟫ := by
        rw [hQa, hQb, hLa, hLb, hL0, hM0]; ring
      have h1 : |u ((θ * (s k).R) • v)
          - (⟪(s k).M ((θ * (s k).R) • v), (θ * (s k).R) • v⟫ / 2
              + (s k).L ((θ * (s k).R) • v) + (s k).c)| ≤ (s k).ρ * (s k).R ^ 2 :=
        hflat _ (by
          rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (mul_pos hθpos hRpos), hv, mul_one]
          nlinarith)
      have h2 : |u (-((θ * (s k).R) • v))
          - (⟪(s k).M (-((θ * (s k).R) • v)), -((θ * (s k).R) • v)⟫ / 2
              + (s k).L (-((θ * (s k).R) • v)) + (s k).c)| ≤ (s k).ρ * (s k).R ^ 2 :=
        hflat _ (by
          rw [mem_ball, dist_zero_right, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_pos (mul_pos hθpos hRpos), hv, mul_one]
          nlinarith)
      have h3 : |u 0 - (⟪(s k).M 0, 0⟫ / 2 + (s k).L 0 + (s k).c)| ≤ (s k).ρ * (s k).R ^ 2 :=
        hflat 0 (by rw [mem_ball, dist_zero_right, norm_zero]; positivity)
      set E : ℝ := (u ((θ * (s k).R) • v)
            - (⟪(s k).M ((θ * (s k).R) • v), (θ * (s k).R) • v⟫ / 2
              + (s k).L ((θ * (s k).R) • v) + (s k).c))
          + (u (-((θ * (s k).R) • v))
            - (⟪(s k).M (-((θ * (s k).R) • v)), -((θ * (s k).R) • v)⟫ / 2
              + (s k).L (-((θ * (s k).R) • v)) + (s k).c))
          - 2 * (u 0 - (⟪(s k).M 0, 0⟫ / 2 + (s k).L 0 + (s k).c)) with hEdef
      have h1a := (abs_le.mp h1).1
      have h1b := (abs_le.mp h1).2
      have h2a := (abs_le.mp h2).1
      have h2b := (abs_le.mp h2).2
      have h3a := (abs_le.mp h3).1
      have h3b := (abs_le.mp h3).2
      have hE1 : E ≤ 4 * ((s k).ρ * (s k).R ^ 2) := by rw [hEdef]; linarith
      have hE2 : -(4 * ((s k).ρ * (s k).R ^ 2)) ≤ E := by rw [hEdef]; linarith
      have hE : |E| ≤ 4 * ((s k).ρ * (s k).R ^ 2) := abs_le.mpr ⟨hE2, hE1⟩
      have hΔeq : (u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
            / (θ * (s k).R) ^ 2 - ⟪(s k).M v, v⟫ = E / (θ * (s k).R) ^ 2 := by
        rw [hEdef]
        field_simp
        linarith [hQ]
      have hkey : |(u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
            / (θ * (s k).R) ^ 2 - ⟪(s k).M v, v⟫|
          ≤ 4 * (s k).ρ / θ ^ 2 := by
        have h4 : |E| / (θ * (s k).R) ^ 2 ≤ 4 * (s k).ρ / θ ^ 2 := by
          rw [div_le_iff₀ (pow_pos hapos 2)]
          rw [show 4 * (s k).ρ / θ ^ 2 * (θ * (s k).R) ^ 2
              = 4 * ((s k).ρ * (s k).R ^ 2) by field_simp]
          exact hE
        rwa [hΔeq, abs_div, abs_of_nonneg (sq_nonneg (θ * (s k).R))]
      have hMv : |⟪(s k).M v, v⟫| ≤ Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) := by
        have h := hMbd v
        rwa [hv, one_pow, mul_one] at h
      have hb : |(u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
            / (θ * (s k).R) ^ 2|
          ≤ 4 * ((s k).ρ) / θ ^ 2 + Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) := by
        have hsplit : (u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
              / (θ * (s k).R) ^ 2
            = ((u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
              / (θ * (s k).R) ^ 2 - ⟪(s k).M v, v⟫) + ⟪(s k).M v, v⟫ := by ring
        rw [hsplit]
        calc |((u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
              / (θ * (s k).R) ^ 2 - ⟪(s k).M v, v⟫) + ⟪(s k).M v, v⟫|
            ≤ |(u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0)
              / (θ * (s k).R) ^ 2 - ⟪(s k).M v, v⟫| + |⟪(s k).M v, v⟫| := abs_add_le _ _
          _ ≤ 4 * (s k).ρ / θ ^ 2 + Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) := by
              linarith [hkey, hMv]
      calc |(u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v)) - 2 * u 0) / (θ * (s k).R) ^ 2|
          ≤ 4 * ((s k).ρ) / θ ^ 2 + Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) := hb
        _ = 4 * (Λ * qDecay θ ^ k) / θ ^ 2 + Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) := by
              rw [hρk']
        _ ≤ Kquad θ * Λ / (1 - qDecay θ) :=
              hess_bound_arith hΛ hθpos hq0 hq1 k
    have htW : Tendsto (fun k : ℕ => θ * (s k).R) atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨htend, Eventually.of_forall (fun k => by simpa using htne k)⟩
    have hlim := (Commons.Analysis.Calculus.FDeriv.second_difference_quotient
      (E := ℝ⁴) (v := v) hu).comp htW
    have hlim' : Tendsto (fun k : ℕ => (u ((θ * (s k).R) • v) + u (-((θ * (s k).R) • v))
        - 2 * u 0) / (θ * (s k).R) ^ 2) atTop (𝓝 ⟪hessOp u 0 v, v⟫) := by
      have h2 : ⟪hessOp u 0 v, v⟫ = (fderiv ℝ (fderiv ℝ u) 0) v v := by
        simp only [hessOp, InnerProductSpace.continuousLinearMapOfBilin_apply]
      rw [h2]
      refine Tendsto.congr' ?_ hlim
      filter_upwards with k
      simp only [Function.comp_apply]
    exact le_of_tendsto hlim'.abs (Eventually.of_forall hbound)
  -- ## the general case by homogeneity
  intro v
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 := hunit (‖v‖⁻¹ • v) (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)])
    have h2 : ⟪hessOp u 0 (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫
        = (‖v‖⁻¹ * ‖v‖⁻¹) * ⟪hessOp u 0 v, v⟫ := by
      simp only [hessOp, map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [h2, abs_mul, abs_of_nonneg (mul_self_nonneg _)] at h1
    have h3 : ‖v‖ ^ 2 * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 := by field_simp
    have hK : 0 ≤ Kquad θ * Λ / (1 - qDecay θ) := by
      have h1q : 0 < 1 - qDecay θ := by linarith
      exact div_nonneg (mul_nonneg (Kquad_pos hθpos).le hΛ) h1q.le
    nlinarith [h1, h3, abs_nonneg ⟪hessOp u 0 v, v⟫, sq_nonneg ‖v‖, hK]

end
end Submission
