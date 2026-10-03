import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.DevH.deriv_setup
import Submission.Work.Fatou.Surface.devH_fundStrip

/-!
# FX8, step 0: the inverse branch of a near-translation on a small disc

For a near-translation `F` on Shishikura's region `Q = Qreg b₁ b₂` (i.e. `‖F z - (z+1)‖ ≤ 1/32`
and `‖F' z - 1‖ ≤ 1/32` on `Q`), every point `z` whose `1/32`-neighbourhood of `z - 1` lies in `Q`
has a *unique, explicit* preimage in that disc: the map
`T w = (z - 1) - ε w`, with `ε w = F w - (w + 1)`, is a `1/32`-contraction of the closed disc
`B = B̄(z-1, 1/32)` into itself (the contraction estimate comes from the mean value inequality
applied to the real Fréchet derivative `D ε w = ` multiplication by `F' w - 1`), so it has a fixed
point `w ∈ B`; there `F w = w + 1 + ε w = z`.

This is the "FX0 inverse" step of the uniformization route: it produces the inverse branch of `F`
used to iterate backwards, and pins down *where* the preimage lies (within `1/32` of `z - 1`),
which is what the downstream estimates on the fundamental domain need.
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric
open scoped Topology

noncomputable section

/-- The operator norm of the real-linear map `v ↦ a * v` on `ℂ` is `‖a‖`. -/
theorem norm_mulCLM (a : ℂ) : ‖ContinuousLinearMap.mul ℝ ℂ a‖ = ‖a‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    show ‖a * v‖ ≤ ‖a‖ * ‖v‖
    rw [norm_mul]
  · have h := ContinuousLinearMap.le_opNorm (ContinuousLinearMap.mul ℝ ℂ a) (1 : ℂ)
    simpa using h

/-- **The inverse branch of a near-translation on a small disc.**  If the closed disc of radius
`1/32` around `z - 1` is contained in `Qreg b₁ b₂`, then `z` has a preimage under `F` which lies in
that disc (and hence, by hypothesis, in `Qreg b₁ b₂`). -/
theorem preimageOfBall {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) {z : ℂ}
    (hball : ∀ u : ℂ, dist u (z - 1) ≤ (1 / 32 : ℝ) → u ∈ MandelDim.Qreg b₁ b₂) :
    ∃ w ∈ MandelDim.Qreg b₁ b₂, F w = z ∧ dist w (z - 1) ≤ 1 / 32 := by
  have hhalf : (0 : ℝ) < 1 / 32 := by norm_num
  -- the disc on which we solve the equation
  set B : Set ℂ := closedBall (z - 1) (1 / 32 : ℝ) with hB
  -- every point of `B` lies in `Q`, by hypothesis
  have hmemQ : ∀ u ∈ B, u ∈ MandelDim.Qreg b₁ b₂ := by
    intro u hu
    rw [hB, mem_closedBall] at hu
    exact hball u hu
  -- the real derivative of `ε = F - (· + 1)` is bounded by `1/32` on `B`
  have hdereps : ∀ u ∈ B, ‖fderiv ℝ (Work.Fatou.eps F) u‖ ≤ 1 / 32 := by
    intro u hu
    have hda : DifferentiableAt ℂ F u :=
      Work.Fatou.DevH.differentiableAt_of_mem_Qreg hF (hmemQ u hu)
    rw [(Work.Fatou.DevH.hasFDerivAt_eps hda).fderiv, norm_mulCLM]
    exact Work.Fatou.DevH.norm_deriv_sub_one_le hF (hmemQ u hu)
  -- mean value inequality: `ε` is `1/32`-Lipschitz on the (convex) disc `B`
  have heps_lip : ∀ x ∈ B, ∀ y ∈ B,
      ‖Work.Fatou.eps F x - Work.Fatou.eps F y‖ ≤ (1 / 32 : ℝ) * ‖x - y‖ := by
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := Work.Fatou.eps F)
      (s := B) (x := y) (y := x) (C := 1 / 32) ?_ ?_ ?_ hy hx
    · intro u hu
      exact (Work.Fatou.DevH.hasFDerivAt_eps (Work.Fatou.DevH.differentiableAt_of_mem_Qreg hF
        (hmemQ u hu))).differentiableAt
    · exact hdereps
    · rw [hB]; exact convex_closedBall _ _
  -- the contraction `T w = (z-1) - ε w`, whose fixed points are exactly the preimages of `z`
  set T : ℂ → ℂ := fun w => (z - 1) - Work.Fatou.eps F w with hT
  have hmaps : MapsTo T B B := by
    intro u hu
    rw [hB, mem_closedBall] at hu ⊢
    rw [hT]
    simp only
    rw [dist_eq_norm]
    have h0 : ((z - 1) - Work.Fatou.eps F u) - (z - 1) = -(Work.Fatou.eps F u) := by ring
    rw [h0, norm_neg]
    exact Work.Fatou.DevH.norm_eps_le hF (hmemQ u hu)
  have hTlip : ∀ x ∈ B, ∀ y ∈ B, dist (T x) (T y) ≤ ((1 / 32 : NNReal) : ℝ) * dist x y := by
    intro x hx y hy
    have h := heps_lip x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    have h0 : T x - T y = -(Work.Fatou.eps F x - Work.Fatou.eps F y) := by
      simp only [hT]; ring
    rw [h0, norm_neg]
    calc ‖Work.Fatou.eps F x - Work.Fatou.eps F y‖ ≤ (1 / 32 : ℝ) * ‖x - y‖ := h
      _ = ((1 / 32 : NNReal) : ℝ) * ‖x - y‖ := by push_cast; ring
  have hcontr : ContractingWith (1 / 32 : NNReal)
      (fun w : ↥B => (⟨T w.1, hmaps w.2⟩ : ↥B)) := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Subtype.dist_eq] using hTlip x.1 x.2 y.1 y.2
  -- Banach's fixed point theorem on the complete disc `B`
  have hBc : IsComplete B := by rw [hB]; exact Metric.isClosed_closedBall.isComplete
  let : CompleteSpace ↥B := hBc.completeSpace_coe
  obtain ⟨w, hwfix, -, -⟩ := hcontr.exists_fixedPoint
    ⟨(z - 1), by rw [hB]; exact mem_closedBall_self hhalf.le⟩ (by simp)
  obtain ⟨u, hu⟩ := w
  have hfixv : T u = u := by
    have h := congrArg Subtype.val hwfix
    simpa using h
  have hFfix : F u = z := by
    have h := hfixv
    simp only [hT, Work.Fatou.eps_apply] at h
    linear_combination -h
  refine ⟨u, hmemQ u hu, hFfix, ?_⟩
  have hud : dist u (z - 1) ≤ 1 / 32 := by
    have h := hu
    rw [hB, mem_closedBall] at h
    exact h
  exact hud

end

end Work.Fatou.FX8
