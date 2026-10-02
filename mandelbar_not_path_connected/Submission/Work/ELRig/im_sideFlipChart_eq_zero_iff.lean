import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.sideFlip_at_ray
import Submission.Work.ELRig.exists_local_angle_at_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- For `|x| < 1/2`, the vanishing of `sin (2π x)` forces `x = 0`. -/
theorem sin_two_pi_eq_zero_of_abs_lt {x : ℝ} (hx : |x| < 1 / 2) :
    Real.sin (2 * Real.pi * x) = 0 ↔ x = 0 := by
  constructor
  · intro hsin
    have h1 : ¬ (0 < x) := fun h => by
      have hpos := (sin_two_pi_pos x hx).mpr h
      rw [hsin] at hpos
      exact lt_irrefl 0 hpos
    have h2 : ¬ (x < 0) := fun h => by
      have hneg := (sin_two_pi_neg x hx).mpr h
      rw [hsin] at hneg
      exact lt_irrefl 0 hneg
    exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  · rintro rfl
    simp

/-- Near the point `p = L.γ₁ s₀` of the lift (which lies in the far-left half plane), the
straightening chart `sideFlipChart c d fl L s₀` is real exactly on the lift `γ₁`: the zero set of
the chart's imaginary part is `Set.range L.γ₁`.

The reason: on the lift the chart equals the positive real level ratio
(`sideFlipChart_eq_ofReal`), giving `⟸`; conversely, writing the chart as
`(‖·‖/τ s₀) · exp (2πi (θ - α₁))` with `θ` the external angle (`sideFlipChart_eq_exp`), reality of
the chart forces `θ = α₁` (the angle lies within `1/2` of `α₁` near `p`, by
`exists_extAngle_close_at_lift`, so the other real branch `θ = α₁ + 1/2` is excluded), and
`θ = α₁` is exactly `Ψ w ∈ paramRay α₁`, which by the `TailId` field is `w ∈ Set.range L.γ₁`. -/
theorem im_sideFlipChart_eq_zero_iff {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ρ > 0, ∀ w : ℂ, dist w (L.γ₁ s₀) < ρ →
      ((sideFlipChart c d fl L s₀ w).im = 0 ↔ w ∈ Set.range L.γ₁) := by
  classical
  -- a ball around `p` on which `Ψ` misses `K c` and the far-left half plane is entered
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ :=
    exists_ball_sideFlip (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) hre
  -- numerical data on the root angle and on the level
  have hα1pos : 0 < Work.EL.alpha1 := by rw [Work.EL.alpha1]; norm_num
  have hα1lt1 : Work.EL.alpha1 < 1 := by rw [Work.EL.alpha1]; norm_num
  have hτ1 : 1 < L.τ s₀ := L.hτ1 s₀
  have hτpos : 0 < L.τ s₀ := lt_trans zero_lt_one hτ1
  -- a level of `Φ` closeness at which the external angle is within `1/2` of `α₁`
  obtain ⟨δcl, _hδclpos, hδcl⟩ :=
    Work.Top.extAngle_close_of_Phi_close (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c d.φ) d.hN
      hα1pos hα1lt1 hτ1 (η := (1 : ℝ) / 2) (by norm_num)
  -- a radius on which the chart is close to its value `1` at `p`
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := Metric.continuousAt_iff.mp
    (sideFlipChart_continuousAt (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀))
    (δcl / L.τ s₀) (by positivity)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁pos hρ₂pos, fun w hw => ?_⟩
  have hw₁ : dist w (L.γ₁ s₀) < ρ₁ := lt_of_lt_of_le hw (min_le_left _ _)
  have hw₂ : dist w (L.γ₁ s₀) < ρ₂ := lt_of_lt_of_le hw (min_le_right _ _)
  obtain ⟨hwre, hwK⟩ := hρ₁ (Metric.mem_ball.mpr hw₁)
  -- closeness of `Φ (Ψ w)` to the ray point of level `τ s₀` at angle `α₁`
  have hchart_lt : ‖sideFlipChart c d fl L s₀ w - 1‖ < δcl / L.τ s₀ := by
    have h := hρ₂ hw₂
    rw [sideFlipChart_at_p] at h
    rwa [dist_eq_norm] at h
  have hmul : Work.EL.dynPhi c d.φ (fl.Ψ w)
        - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)
      = Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)
        * (sideFlipChart c d fl L s₀ w - 1) := by
    rw [sideFlipChart_apply, mul_sub, mul_one]
    rw [mul_div_cancel₀ _ (rayPoint_alpha1_ne_zero (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀))]
  have hnorm_eq : ‖Work.EL.dynPhi c d.φ (fl.Ψ w)
        - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)‖
      = L.τ s₀ * ‖sideFlipChart c d fl L s₀ w - 1‖ := by
    rw [hmul, norm_mul, Work.Top.NakaneData.norm_rayPoint, abs_of_pos hτpos]
  have hdist_cl : ‖Work.EL.dynPhi c d.φ (fl.Ψ w)
        - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)‖ < δcl := by
    rw [hnorm_eq]
    calc L.τ s₀ * ‖sideFlipChart c d fl L s₀ w - 1‖
        < L.τ s₀ * (δcl / L.τ s₀) := mul_lt_mul_of_pos_left hchart_lt hτpos
      _ = δcl := by field_simp
  have hθclose : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) - Work.EL.alpha1|
      < 1 / 2 := hδcl (fl.Ψ w) hwK hdist_cl
  -- the chart in polar form, with positive modulus
  have hrpos : 0 < ‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀ :=
    div_pos (norm_pos_iff.mpr (d.hN.Phi_ne_zero hwK)) hτpos
  have him : (sideFlipChart c d fl L s₀ w).im =
      (‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀) *
        Real.sin (2 * Real.pi *
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)
            - Work.EL.alpha1)) := by
    rw [sideFlipChart_eq_exp s₀ w hwK, mul_im_exp_two_pi]
  constructor
  · -- reality forces the external angle to be `α₁`, hence the point to lie on the lift
    intro him0
    have hsin0 : Real.sin (2 * Real.pi *
        (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)
          - Work.EL.alpha1)) = 0 := by
      rw [him] at him0
      rcases mul_eq_zero.mp him0 with h | h
      · exact absurd h (ne_of_gt hrpos)
      · exact h
    have hx0 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)
        - Work.EL.alpha1 = 0 := (sin_two_pi_eq_zero_of_abs_lt hθclose).mp hsin0
    have hθa : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) = Work.EL.alpha1 := by
      linarith
    have hmem : fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
      have h := Work.Top.mem_paramRay_extAngle (Mb := Work.EL.K c)
        (Φ := Work.EL.dynPhi c d.φ) d.hN hwK
      rw [hθa] at h
      exact h
    exact L.tailId₁ w hwre hmem
  · -- on the lift the chart is the real level ratio
    rintro ⟨s, rfl⟩
    rw [sideFlipChart_eq_ofReal (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) (s := s)]
    simp

end Work.ELRig
