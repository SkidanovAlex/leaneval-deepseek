import Mathlib

/-!
# Bump translations

The basic tool for moving the endpoint of a smooth arc a little: in `ℝⁿ`, the map
`v ↦ v + φ v • d` with `φ` a smooth bump around a point `u` is a smooth self-map which is the
identity away from `u`, is injective when `‖d‖` is small, and sends `u` to `u + d`.  Lifting this
construction through a chart of a smooth manifold gives, for every chart `c`, base point `y` and
radius `R` with `closedBall (c y) R ⊆ c.target`, a smooth self-map `ψ` of the manifold with
`ψ y = z` for every `z` close enough to `y` (in the chart), `ψ = id` outside the chart ball of
radius `R`, and `ψ` injective.  The crucial feature for us is that the "close enough" constant is
*uniform*: it is a fixed multiple `ε * R` of the radius.
-/

namespace Work.Whitney

open Set Metric Function
open scoped Manifold ContDiff

/-- **The bump translation in `ℝⁿ`.**  There is a universal constant `κ > 0` such that for every
centre `u`, radius `σ > 0` and displacement `d` with `‖d‖ < κ * σ`, there is a smooth injective
map `Ψ` which fixes everything outside the closed ball of radius `σ` around `u`, sends `u` to
`u + d`, and maps the ball of radius `σ` into itself. -/
theorem exists_bumpTranslation {n : ℕ} :
    ∃ κ > 0, ∀ (u : EuclideanSpace ℝ (Fin n)) (σ : ℝ), 0 < σ →
      ∀ d : EuclideanSpace ℝ (Fin n), ‖d‖ < κ * σ →
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ∞ Ψ ∧ Function.Injective Ψ ∧ Ψ u = u + d ∧
        (∀ v, σ/2 ≤ dist v u → Ψ v = v) ∧
        (∀ v, dist v u < σ → dist (Ψ v) u < σ) := by
  classical
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  have hbC : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin n) => b v) := b.contDiff (n := 1)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
      (n := ((1 : ℕ∞) : WithTop ℕ∞)) (f := fun v : EuclideanSpace ℝ (Fin n) => b v)
      b.hasCompactSupport hbC (by simp)
  have hCnn : (0:ℝ) ≤ C := NNReal.coe_nonneg C
  have hCpos : (0:ℝ) < 4*((C:ℝ)+1) := by linarith
  refine ⟨1/(4*((C:ℝ)+1)), by positivity, ?_⟩
  intro u σ hσ d hd
  have hκ4 : 1/(4*((C:ℝ)+1)) ≤ 1/4 := by
    rw [div_le_div_iff₀ hCpos (by norm_num : (0:ℝ) < 4)]
    nlinarith
  have hd4 : ‖d‖ < σ/4 := by
    calc ‖d‖ < (1/(4*((C:ℝ)+1))) * σ := hd
      _ ≤ (1/4) * σ := mul_le_mul_of_nonneg_right hκ4 hσ.le
      _ = σ/4 := by ring
  have hdC : (C:ℝ) * ‖d‖ < σ := by
    have h2 : (C:ℝ) * (1/(4*((C:ℝ)+1))) ≤ 1/4 := by
      rw [mul_one_div, div_le_div_iff₀ hCpos (by norm_num : (0:ℝ) < 4)]
      nlinarith
    rcases lt_or_eq_of_le hCnn with hCpos | hC0
    · calc (C:ℝ) * ‖d‖ < (C:ℝ) * ((1/(4*((C:ℝ)+1))) * σ) :=
            mul_lt_mul_of_pos_left hd hCpos
        _ = ((C:ℝ) * (1/(4*((C:ℝ)+1)))) * σ := by ring
        _ ≤ (1/4) * σ := mul_le_mul_of_nonneg_right h2 hσ.le
        _ < σ := by linarith
    · rw [← hC0]; simp [hσ]
  refine ⟨fun v => v + b ((σ⁻¹ : ℝ) • (v - u)) • d, ?_, ?_, ?_, ?_, ?_⟩
  · have hinner : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (σ⁻¹:ℝ) • (v - u)) := by
      fun_prop
    have hbm : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => b ((σ⁻¹:ℝ) • (v - u))) :=
      (b.contDiff (n := ⊤)).comp hinner
    exact contDiff_id.add (hbm.smul_const d)
  · intro v w hvw
    have hvw' : v + b ((σ⁻¹:ℝ) • (v - u)) • d = w + b ((σ⁻¹:ℝ) • (w - u)) • d := hvw
    have hkey : v - w = (b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))) • d := by
      calc v - w = (v + b ((σ⁻¹:ℝ) • (v-u)) • d) - (w + b ((σ⁻¹:ℝ) • (w-u)) • d)
            + (b ((σ⁻¹:ℝ) • (w-u)) • d - b ((σ⁻¹:ℝ) • (v-u)) • d) := by abel
        _ = 0 + (b ((σ⁻¹:ℝ) • (w-u)) • d - b ((σ⁻¹:ℝ) • (v-u)) • d) := by rw [hvw']; abel
        _ = (b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))) • d := by rw [sub_smul]; abel
    have hdiff : ‖(σ⁻¹:ℝ) • (w - u) - σ⁻¹ • (v - u)‖ = ‖w - v‖ / σ := by
      rw [← smul_sub, show w - u - (v - u) = w - v from by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹), inv_mul_eq_div]
    have hlip : |b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))| ≤ ((C:ℝ)/σ) * ‖w - v‖ := by
      have h := hC.dist_le_mul ((σ⁻¹:ℝ) • (w - u)) ((σ⁻¹:ℝ) • (v - u))
      rw [Real.dist_eq, dist_eq_norm, hdiff] at h
      calc |b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))| ≤ (C:ℝ) * (‖w-v‖/σ) := h
        _ = ((C:ℝ)/σ) * ‖w - v‖ := by ring
    have hnorm : ‖v - w‖ =
        |b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))| * ‖d‖ := by
      rw [hkey, norm_smul, Real.norm_eq_abs]
    have hle : ‖v - w‖ ≤ ((C:ℝ)/σ) * ‖d‖ * ‖v - w‖ := by
      nth_rewrite 1 [hnorm]
      have hwv : ‖w - v‖ = ‖v - w‖ := norm_sub_rev w v
      calc |b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))| * ‖d‖
            ≤ (((C:ℝ)/σ) * ‖w - v‖) * ‖d‖ :=
              mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        _ = ((C:ℝ)/σ) * ‖d‖ * ‖v - w‖ := by rw [hwv]; ring
    have h1 : ((C:ℝ)/σ) * ‖d‖ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hσ]
      exact hdC
    have hnn : 0 ≤ ‖v - w‖ := norm_nonneg _
    have hzero : ‖v - w‖ = 0 := by nlinarith [hle, h1, hnn]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · have hu : b ((σ⁻¹:ℝ) • (u - u)) = 1 := by
      have : (σ⁻¹:ℝ) • (u - u) = 0 := by simp
      rw [this]
      exact b.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact b.rIn_pos.le)
    show u + b ((σ⁻¹:ℝ) • (u - u)) • d = u + d
    rw [hu, one_smul]
  · intro v hv
    have hge : (1:ℝ)/2 ≤ ‖(σ⁻¹:ℝ) • (v - u)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹),
        inv_mul_eq_div, le_div_iff₀ hσ]
      rw [dist_eq_norm] at hv
      linarith
    have hb0 : b ((σ⁻¹:ℝ) • (v - u)) = 0 := by
      apply b.zero_of_le_dist
      rw [show b.rOut = (1:ℝ)/2 from rfl]
      rw [dist_zero_right]
      exact hge
    simp [hb0]
  · intro v hv
    by_cases h : dist v u < σ/2
    · have hbv : ‖b ((σ⁻¹:ℝ) • (v - u))‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]; exact b.le_one
      have h1 : dist (v + b ((σ⁻¹:ℝ) • (v - u)) • d) u ≤
          dist v u + ‖b ((σ⁻¹:ℝ) • (v - u))‖ * ‖d‖ := by
        rw [dist_eq_norm]
        have h2 : v + b ((σ⁻¹:ℝ) • (v - u)) • d - u =
            (v - u) + b ((σ⁻¹:ℝ) • (v - u)) • d := by abel
        rw [h2]
        calc ‖(v - u) + b ((σ⁻¹:ℝ) • (v-u)) • d‖ ≤ ‖v - u‖ + ‖b ((σ⁻¹:ℝ) • (v-u)) • d‖ :=
              norm_add_le _ _
          _ = ‖v - u‖ + ‖b ((σ⁻¹:ℝ) • (v-u))‖ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = dist v u + ‖b ((σ⁻¹:ℝ) • (v-u))‖ * ‖d‖ := by rw [dist_eq_norm]
      have h2 : ‖b ((σ⁻¹:ℝ) • (v - u))‖ * ‖d‖ ≤ 1 * (σ/4) :=
        mul_le_mul hbv hd4.le (norm_nonneg _) (by norm_num)
      linarith
    · push Not at h
      have hb0 : b ((σ⁻¹:ℝ) • (v - u)) = 0 := by
        apply b.zero_of_le_dist
        rw [show b.rOut = (1:ℝ)/2 from rfl]
        rw [dist_zero_right]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹),
          inv_mul_eq_div, le_div_iff₀ hσ]
        rw [dist_eq_norm] at h
        linarith
      simpa [hb0] using hv

end Work.Whitney
