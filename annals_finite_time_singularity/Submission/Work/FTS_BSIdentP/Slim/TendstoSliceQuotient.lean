import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-!
# The slice difference quotient of a `C²` function

If a two-variable function `f` is `C²` near `(w₀, θ₀)` and vanishes identically on the vertical
line `θ = θ₀` (near `w₀`), then the difference quotient `(w, θ) ↦ f w θ / (θ - θ₀)` extends
continuously to `(w₀, θ₀)` with value `∂_θ f (w₀, θ₀)`.

The proof is the mean value theorem applied to the `θ`-slice `s ↦ f w s`: the quotient equals
`∂_θ f (w, ξ)` for some `ξ` strictly between `θ` and `θ₀`, and the map
`(w, ξ) ↦ ∂_θ f (w, ξ)` is continuous at `(w₀, θ₀)` because `f` is `C²` there.  (The latter is
the statement that `fderiv ℝ` of a `C¹` map is continuous, together with the identification of
the one-dimensional `deriv` of the slice with `fderiv` of the uncurried function evaluated in
the direction `(0,1)`.)
-/

/-- The affine map `s ↦ (w, s)` has derivative the linear map `(0, 1)`. -/
private lemma hasFDerivAt_prodMk_const_left (w s : ℝ) :
    HasFDerivAt (fun s' : ℝ => ((w, s') : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) s :=
  (hasFDerivAt_const (x := s) w).prodMk (hasFDerivAt_id (x := s))

/-- The `θ`-slice derivative `(w, θ) ↦ ∂_θ f (w, θ)` of a `C²` function is continuous. -/
private lemma continuousAt_slice_deriv {f : ℝ → ℝ → ℝ} {w₀ θ₀ : ℝ}
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀)) :
    ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) := by
  set F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 with hFdef
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), DifferentiableAt ℝ F p :=
    (h.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (w₀, θ₀) := h.fderiv_right (m := 1) (by norm_num)
  have hΦ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) (w₀, θ₀) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.continuousAt.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  -- the `deriv` of the slice is `fderiv F` evaluated at `(0,1)` (chain rule)
  have hcomp := hp.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_const_left p.1 p.2)
  have h1 : deriv (fun s : ℝ => f p.1 s) p.2
      = ((fderiv ℝ F p).comp ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 :=
    hcomp.hasDerivAt.deriv
  rw [h1, ContinuousLinearMap.comp_apply]
  simp

/-- A point of the interval `[min a b, max a b]` is at least as close to `b` as `a` is. -/
private lemma abs_sub_le_of_mem_Icc_min_max {a b s : ℝ}
    (hs : s ∈ Set.Icc (min a b) (max a b)) : |s - b| ≤ |a - b| := by
  rcases le_total a b with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
    linarith [hs.1]
  · rw [min_eq_right hle, max_eq_left hle] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
    linarith [hs.2]

/-- Continuity of a slice of a function that is `C²` at every relevant point. -/
private lemma continuousOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    ContinuousOn (fun s => f w s) U := fun s hs =>
  ((h s hs).continuousAt.comp (hasFDerivAt_prodMk_const_left w s).continuousAt).continuousWithinAt

/-- Differentiability of a slice of a function that is `C²` at every relevant point. -/
private lemma differentiableOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    DifferentiableOn ℝ (fun s => f w s) U := fun s hs =>
  (((h s hs).differentiableAt (by norm_num)).comp s
    (hasFDerivAt_prodMk_const_left w s).differentiableAt).differentiableWithinAt

/-- **Mean value theorem for the slice quotient.**  If the slice `s ↦ f w s` is continuous on
`[min θ θ₀, max θ θ₀]` and differentiable on the open interval, and `f w θ₀ = 0`, then the
difference quotient `f w θ / (θ - θ₀)` is the value of the slice derivative at some interior
point. -/
private lemma slice_quotient_eq_deriv {f : ℝ → ℝ → ℝ} {w θ θ₀ : ℝ} (hne : θ ≠ θ₀)
    (hz : f w θ₀ = 0)
    (hcont : ContinuousOn (fun s => f w s) (Set.Icc (min θ θ₀) (max θ θ₀)))
    (hdiff : DifferentiableOn ℝ (fun s => f w s) (Set.Ioo (min θ θ₀) (max θ θ₀))) :
    ∃ ξ ∈ Set.Ioo (min θ θ₀) (max θ θ₀),
      deriv (fun s => f w s) ξ = f w θ / (θ - θ₀) := by
  have hlt : min θ θ₀ < max θ θ₀ := min_lt_max.mpr hne
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun s => f w s) hlt hcont hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [hξeq]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, hz, zero_sub,
      show θ₀ - θ = -(θ - θ₀) from by ring, div_neg, neg_div, neg_neg]
  · rw [min_eq_right h.le, max_eq_left h.le, hz, sub_zero]

/-- Every point of `[min θ θ₀, max θ θ₀]` lies within the `δ`-neighbourhood of `θ₀` whenever
`θ` does. -/
private lemma slice_contDiffAt_of_mem_Icc {f : ℝ → ℝ → ℝ} {w w₀ θ₀ θ δ : ℝ}
    (hw : |w - w₀| < δ) (hθ : |θ - θ₀| < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ)) :
    ∀ s ∈ Set.Icc (min θ θ₀) (max θ θ₀),
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s) := by
  intro s hs
  have hs' : |s - θ₀| < δ := lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max hs) hθ
  exact hsm w s hw hs'

theorem tendsto_slice_quotient {f : ℝ → ℝ → ℝ} {w₀ θ₀ δ : ℝ} (hδ : 0 < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ))
    (hz : ∀ w, |w - w₀| < δ → f w θ₀ = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / (p.2 - θ₀))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀))
      (𝓝 (deriv (fun θ => f w₀ θ) θ₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- `f` is `C²` at the base point, so the slice derivative is continuous there
  have hbase : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀) :=
    hsm w₀ θ₀ (by simpa using hδ) (by simpa using hδ)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) :=
    continuousAt_slice_deriv hbase
  obtain ⟨η₁, hη₁pos, hη₁⟩ :=
    Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcont ε hε)
  -- shrink the neighbourhood so that it stays inside the `δ`-box
  set η : ℝ := min η₁ δ with hηdef
  have hηpos : 0 < η := lt_min hη₁pos hδ
  have hηδ : η ≤ δ := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hbox : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), |p.1 - w₀| < η ∧ |p.2 - θ₀| < η := by
    filter_upwards [Metric.ball_mem_nhds (w₀, θ₀) hηpos] with p hp
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
    exact hp
  have hboxS : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      |p.1 - w₀| < η ∧ |p.2 - θ₀| < η :=
    hbox.filter_mono nhdsWithin_le_nhds
  have hSne : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      p.2 ≠ θ₀ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.2.2
  refine (hboxS.and hSne).mono ?_
  rintro p ⟨⟨hp1, hp2⟩, hpne⟩
  rw [Real.dist_eq]
  have hwδ : |p.1 - w₀| < δ := lt_of_lt_of_le hp1 hηδ
  have hθδ : |p.2 - θ₀| < δ := lt_of_lt_of_le hp2 hηδ
  have hz' : f p.1 θ₀ = 0 := hz p.1 hwδ
  -- the mean value theorem on the `θ`-slice at fixed first coordinate
  have hC2 := slice_contDiffAt_of_mem_Icc hwδ hθδ hsm
  obtain ⟨ξ, hξ, hξeq⟩ := slice_quotient_eq_deriv hpne hz'
    (continuousOn_slice hC2)
    (differentiableOn_slice (fun s hs => hC2 s (Ioo_subset_Icc_self hs)))
  -- `(p.1, ξ)` is still in the small box, so the derivative is close to the limit
  have hξb : |ξ - θ₀| < η :=
    lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max (Ioo_subset_Icc_self hξ)) hp2
  have hdist : dist ((p.1, ξ) : ℝ × ℝ) (w₀, θ₀) < η := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hp1, hξb⟩
  have hb := hη₁ (y := (p.1, ξ)) (lt_of_lt_of_le hdist hηη₁)
  rw [Real.dist_eq] at hb
  rw [← hξeq]
  exact hb

end Work.FTS.BSIdentP.Levels
