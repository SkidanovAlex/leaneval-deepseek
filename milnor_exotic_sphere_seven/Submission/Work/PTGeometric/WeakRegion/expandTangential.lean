import Mathlib
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

noncomputable section

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

variable {n : ℕ} [NeZero n]

/-- **Uniform first-order expansion in the tangential variable.** For every `ε > 0` there is `η > 0`
such that for all `u` with `‖u - x₀.1‖ < η` and all `b ∈ [0,δ]` with `|b - x₀.2| < η`,
`‖F (u,b) - F (x₀.1,b) - (∂_u F) (u - x₀.1)‖ ≤ ε ‖u - x₀.1‖`: the derivative `u ↦ Du (u,b)` is
uniformly close to `Du x₀` on a box around `x₀` (continuity of `Du` on the relative domain), and the
mean-value inequality on the convex ball around `x₀.1` gives the estimate. -/
theorem expandTangential {n : ℕ} [NeZero n] (S : Work.PTGeometric.WeakRegion.HalfSpaceGraphSetup n)
    {ρ δ M : ℝ} (B : S.Box ρ δ M) (x₀ : Work.PTGeometric.WeakRegion.hsTang n × ℝ)
    (hx₀ : x₀ ∈ S.dom) (hx₀ρ : x₀.1 ∈ Metric.ball (Work.PTGeometric.WeakRegion.hsMk S.p) ρ) :
    ∀ ε > 0, ∃ η > 0, ∀ u : Work.PTGeometric.WeakRegion.hsTang n, ‖u - x₀.1‖ < η →
      ∀ b ∈ Set.Icc 0 δ, |b - x₀.2| < η →
      ‖S.F (u, b) - S.F (x₀.1, b) - S.Du x₀ (u - x₀.1)‖ ≤ ε * ‖u - x₀.1‖ := by
  intro ε hε
  -- `Du` is continuous within the relative domain at `x₀`, hence uniformly `ε`-close to `Du x₀`
  -- on a relative neighbourhood of `x₀`.
  have hcont : ContinuousWithinAt S.Du S.dom x₀ := S.continuousWithinAt_Du_at x₀ hx₀
  have hev : ∀ᶠ y in 𝓝[S.dom] x₀, dist (S.Du y) (S.Du x₀) < ε :=
    hcont.eventually (Metric.ball_mem_nhds (S.Du x₀) hε)
  obtain ⟨ηc, hηcpos, hηc⟩ := Metric.mem_nhdsWithin_iff.mp hev
  -- the tangential slack: `x₀.1` is strictly inside the ball around `S.p` of radius `ρ`
  have hR : 0 < ρ - dist x₀.1 (hsMk S.p) := by
    have h := hx₀ρ
    rw [Metric.mem_ball] at h
    linarith
  refine ⟨min ηc (ρ - dist x₀.1 (hsMk S.p)), lt_min hηcpos hR, ?_⟩
  intro u hu b hb hdb
  set r : ℝ := min ηc (ρ - dist x₀.1 (hsMk S.p)) with hr
  have hrpos : 0 < r := lt_min hηcpos hR
  have hrle_c : r ≤ ηc := min_le_left _ _
  have hrle_ρ : r ≤ ρ - dist x₀.1 (hsMk S.p) := min_le_right _ _
  -- the tangential ball of radius `r` around `x₀.1` is still contained in the box of `B`
  have hsub : Metric.ball x₀.1 r ⊆ Metric.ball (hsMk S.p) ρ := by
    intro v hv
    rw [Metric.mem_ball] at hv ⊢
    calc dist v (hsMk S.p) ≤ dist v x₀.1 + dist x₀.1 (hsMk S.p) := dist_triangle _ _ _
      _ < r + dist x₀.1 (hsMk S.p) := by linarith
      _ ≤ ρ := by linarith
  -- on that ball the derivative `Du (·,b)` is `ε`-close to `Du x₀`
  have hbound : ∀ v ∈ Metric.ball x₀.1 r, ‖S.Du (v, b) - S.Du x₀‖ ≤ ε := by
    intro v hv
    have hvρ : v ∈ Metric.ball (hsMk S.p) ρ := hsub hv
    have hvdom : (v, b) ∈ S.dom := B.hmem v hvρ b hb
    have hdist : dist (v, b) x₀ < ηc := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Metric.mem_ball] at hv
        linarith
      · rw [dist_eq_norm, Real.norm_eq_abs]
        linarith
    have hε' := hηc ⟨hdist, hvdom⟩
    have hD := dist_eq_norm (S.Du (v, b)) (S.Du x₀)
    exact le_of_lt (hD ▸ hε')
  -- mean value inequality for `v ↦ F (v,b) - Du x₀ v` on the convex ball around `x₀.1`
  have hMV := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun v : hsTang n => S.F (v, b)) (f' := fun v : hsTang n => S.Du (v, b))
    (φ := S.Du x₀) (C := ε) (s := Metric.ball x₀.1 r)
    (fun v hv => (S.hasFDerivWithinAt_F_slice B b hb v (hsub hv)).mono hsub)
    hbound (convex_ball x₀.1 r) (Metric.mem_ball_self hrpos)
    (by rw [Metric.mem_ball, dist_eq_norm]; exact hu)
  exact hMV

end

end Work.PTGeometric.WeakRegion
