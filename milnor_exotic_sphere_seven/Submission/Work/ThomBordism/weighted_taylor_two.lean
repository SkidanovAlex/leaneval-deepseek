import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism

/-- Second order Taylor estimate on a closed ball.  If `f` is differentiable on the closed
ball of radius `ρ` with `fderiv ℝ f` differentiable there and second derivative bounded by `M`,
then for `z, w` in that ball the "second order Taylor remainder" is bounded by `M ‖w - z‖²`. -/
private lemma ball_taylor_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {ρ M : ℝ}
    (hd1 : ∀ w, ‖w‖ ≤ ρ → HasFDerivAt f (fderiv ℝ f w) w)
    (hd2 : ∀ w, ‖w‖ ≤ ρ → HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) w) w)
    (hM : ∀ w, ‖w‖ ≤ ρ → ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M)
    (hMnn : 0 ≤ M) {z w : E} (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖f w - f z - (fderiv ℝ f z) (w - z)‖ ≤ M * ‖w - z‖ ^ 2 := by
  -- the derivative of `f` is Lipschitz with constant `M` on the closed ball
  have hLip : ∀ u v : E, ‖u‖ ≤ ρ → ‖v‖ ≤ ρ → ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ M * ‖u - v‖ := by
    intro u v hu hv
    have mem_ball : ∀ q : E, ‖q‖ ≤ ρ → q ∈ Metric.closedBall (0:E) ρ := fun q hq => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hq
    have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fderiv ℝ f) (f' := fun q => fderiv ℝ (fderiv ℝ f) q) (C := M)
      (s := Metric.closedBall (0:E) ρ)
      (fun q hq => (hd2 q (by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hq)).hasFDerivWithinAt)
      (fun q hq => hM q (by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hq))
      (convex_closedBall (0:E) ρ) (mem_ball v hv) (mem_ball u hu)
    simpa using key
  set A : ℝ → E := fun t => (1 - t) • z + t • w with hA_def
  have hA_deriv : ∀ t, HasDerivAt A (w - z) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (1 - s) • z) (-z) t := by
      have := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const z
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa using (hasDerivAt_id t).smul_const w
    have h3 : HasDerivAt (fun s : ℝ => (1 - s) • z + s • w) (-z + w) t := h1.add h2
    have h4 : -z + w = w - z := by abel
    rw [h4] at h3
    rw [hA_def]
    exact h3
  have hA_ball : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖A t‖ ≤ ρ := by
    intro t ht
    simp only [A]
    calc ‖(1 - t) • z + t • w‖ ≤ ‖(1 - t) • z‖ + ‖t • w‖ := norm_add_le _ _
      _ = (1 - t) * ‖z‖ + t * ‖w‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * ρ + t * ρ := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hz (by linarith [ht.2])
            · exact mul_le_mul_of_nonneg_left hw ht.1
      _ = ρ := by ring
  set φ : ℝ → E := fun t => f (A t) - f z - t • ((fderiv ℝ f z) (w - z)) with hφ_def
  have hφ_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt φ ((fderiv ℝ f (A t)) (w - z) - (fderiv ℝ f z) (w - z)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => f (A s) - f z) ((fderiv ℝ f (A t)) (w - z)) t :=
      ((hd1 (A t) (hA_ball t ht)).comp_hasDerivAt t (hA_deriv t)).sub_const (f z)
    have h2 : HasDerivAt (fun s : ℝ => s • ((fderiv ℝ f z) (w - z))) ((fderiv ℝ f z) (w - z)) t := by
      simpa using (hasDerivAt_id t).smul_const ((fderiv ℝ f z) (w - z))
    have key := h1.sub h2
    rw [show ((fun s : ℝ => f (A s) - f z) - fun s => s • ((fderiv ℝ f z) (w - z))) = φ from by
          funext s; simp only [hφ_def, Pi.sub_apply]] at key
    exact key
  have hφ_bound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖(fderiv ℝ f (A t)) (w - z) - (fderiv ℝ f z) (w - z)‖ ≤ M * ‖w - z‖ ^ 2 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hL : ‖fderiv ℝ f (A t) - fderiv ℝ f z‖ ≤ M * ‖A t - z‖ := hLip (A t) z (hA_ball t htIcc) hz
    have hAz : ‖A t - z‖ = t * ‖w - z‖ := by
      have h : A t - z = t • (w - z) := by
        simp only [A]
        module
      rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hstep : M * ‖A t - z‖ ≤ M * ‖w - z‖ := by
      rw [hAz]; exact mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (w - z), ht.2.le]) hMnn
    calc ‖(fderiv ℝ f (A t)) (w - z) - (fderiv ℝ f z) (w - z)‖
        = ‖(fderiv ℝ f (A t) - fderiv ℝ f z) (w - z)‖ := by rw [sub_apply]
      _ ≤ ‖fderiv ℝ f (A t) - fderiv ℝ f z‖ * ‖w - z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * ‖w - z‖) * ‖w - z‖ := mul_le_mul_of_nonneg_right (hL.trans hstep) (norm_nonneg _)
      _ = M * ‖w - z‖ ^ 2 := by ring
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := φ) (f' := fun t => (fderiv ℝ f (A t)) (w - z) - (fderiv ℝ f z) (w - z))
    (C := M * ‖w - z‖ ^ 2) (fun t ht => (hφ_deriv t ht).hasDerivWithinAt) hφ_bound
  have hφ1 : φ 1 = f w - f z - (fderiv ℝ f z) (w - z) := by simp [φ, A]
  have hφ0 : φ 0 = 0 := by simp [φ, A]
  rw [hφ1, hφ0, sub_zero] at hmain
  exact hmain

theorem weighted_taylor_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {ρ M : ℝ}
    (hd1 : ∀ w, ‖w‖ ≤ ρ → HasFDerivAt f (fderiv ℝ f w) w)
    (hd2 : ∀ w, ‖w‖ ≤ ρ → HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) w) w)
    (hM : ∀ w, ‖w‖ ≤ ρ → ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M)
    {x y : E} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • f x + b • f y - f (a • x + b • y)‖ ≤ M * (a * b) * ‖x - y‖ ^ 2 := by
  by_cases hρ : 0 ≤ ρ
  · obtain hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simpa using hρ))
    set z : E := a • x + b • y with hz_def
    have hz : ‖z‖ ≤ ρ := by
      rw [hz_def]
      calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖x‖ + b * ‖y‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * ρ + b * ρ :=
              add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = ρ := by rw [← add_mul, hab, one_mul]
    have hxa := ball_taylor_remainder hd1 hd2 hM hMnn hz hx
    have hya := ball_taylor_remainder hd1 hd2 hM hMnn hz hy
    -- linear algebra: express the second difference through the two Taylor remainders
    have hzx : a • (x - z) + b • (y - z) = 0 := by
      have h : a • (x - z) + b • (y - z) = (a • x + b • y) - (a + b) • z := by module
      rw [h, ← hz_def, hab, one_smul, sub_self]
    have hD : a • (fderiv ℝ f z) (x - z) + b • (fderiv ℝ f z) (y - z) = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, hzx, map_zero]
    have hkey : a • (f x - f z - (fderiv ℝ f z) (x - z))
        + b • (f y - f z - (fderiv ℝ f z) (y - z)) = a • f x + b • f y - f z := by
      calc a • (f x - f z - (fderiv ℝ f z) (x - z))
              + b • (f y - f z - (fderiv ℝ f z) (y - z))
          = (a • f x + b • f y) - (a • f z + b • f z)
              - (a • (fderiv ℝ f z) (x - z) + b • (fderiv ℝ f z) (y - z)) := by module
        _ = (a • f x + b • f y) - (a • f z + b • f z) - 0 := by rw [hD]
        _ = (a • f x + b • f y) - (a • f z + b • f z) := by rw [sub_zero]
        _ = (a • f x + b • f y) - (a + b) • f z := by rw [add_smul]
        _ = (a • f x + b • f y) - f z := by rw [hab, one_smul]
    -- the two points expressed in terms of the segment
    have hxz : x - z = b • (x - y) := by
      have : a = 1 - b := by linarith
      rw [hz_def, this]
      module
    have hyz : y - z = a • (y - x) := by
      have : b = 1 - a := by linarith
      rw [hz_def, this]
      module
    have hxzn : ‖x - z‖ = b * ‖x - y‖ := by
      rw [hxz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have hyzn : ‖y - z‖ = a * ‖x - y‖ := by
      rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, norm_sub_rev]
    rw [← hkey]
    refine (calc ‖a • (f x - f z - (fderiv ℝ f z) (x - z))
              + b • (f y - f z - (fderiv ℝ f z) (y - z))‖
          ≤ ‖a • (f x - f z - (fderiv ℝ f z) (x - z))‖
              + ‖b • (f y - f z - (fderiv ℝ f z) (y - z))‖ := norm_add_le _ _
        _ = a * ‖f x - f z - (fderiv ℝ f z) (x - z)‖
              + b * ‖f y - f z - (fderiv ℝ f z) (y - z)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * (M * ‖x - z‖ ^ 2) + b * (M * ‖y - z‖ ^ 2) :=
              add_le_add (mul_le_mul_of_nonneg_left hxa ha) (mul_le_mul_of_nonneg_left hya hb)).trans ?_
    rw [hxzn, hyzn]
    have hfin : a * (M * (b * ‖x - y‖) ^ 2) + b * (M * (a * ‖x - y‖) ^ 2)
        = M * (a * b) * ‖x - y‖ ^ 2 := by
      linear_combination (M * ‖x - y‖ ^ 2 * a * b) * hab
    exact le_of_eq hfin
  · exfalso
    linarith [norm_nonneg x, hx, not_le.mp hρ]

end Work.ThomBordism
