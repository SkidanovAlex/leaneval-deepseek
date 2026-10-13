/-
  WilE2 / Ebc — component locality of the zero set of a `C¹` map in general Banach spaces.

  This is the infinite-dimensional generalisation of
  `Work.WilE9.Sharp.AE.zero_set_component_locality` (there formulated for `ℝⁿ × ℝ^q → ℝ^q` and
  `C^∞` maps).  The statement is the local-connectedness form of the implicit function theorem:
  if `F : E₁ × E₂ → E₂` is `C¹` at `u`, `F u = 0`, the fibre Jacobian
  `(fderiv ℝ F u).comp (ContinuousLinearMap.inr ℝ E₁ E₂)` is invertible, and the zero set of `F`
  germ-wise near `u` lies in `T`, then every near-by zero of `F` lies in the connected component
  of `T` through `u`.

  The proof is the one of the implicit function theorem: the zeros of `F` near `u` are the graph
  of the implicit function `g` of the first variable, which is `C¹`, so the graph over a small
  ball is connected and consists of zeros; by hypothesis it lies in `T`, and every near-by zero
  is on it.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.AE.zero_set_component_locality

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE2.Ebc

theorem zero_set_component_locality_general
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    (F : E₁ × E₂ → E₂) (u : E₁ × E₂)
    (hcdf : ContDiffAt ℝ 1 F u) (hF0 : F u = 0)
    (hif : ((fderiv ℝ F u) ∘SL ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible)
    (T : Set (E₁ × E₂)) (hT : ∀ᶠ v in nhds u, F v = 0 → v ∈ T) :
    ∀ᶠ v in nhds u, F v = 0 → v ∈ connectedComponentIn T u := by
  classical
  have hpn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  set g : E₁ → E₂ := hcdf.implicitFunction hpn hif with hg
  have hg0 : g u.1 = u.2 := hcdf.implicitFunction_apply_self hpn hif
  have hgcd : ContDiffAt ℝ 1 g u.1 := hcdf.contDiffAt_implicitFunction hpn hif
  -- the zeros of `F` near `u` are exactly the graph of `g`
  have huniq : ∀ᶠ v in 𝓝 u, F v = 0 → g v.1 = v.2 := by
    have h := hcdf.eventually_apply_eq_iff_implicitFunction hpn hif
    filter_upwards [h] with v hv hv0
    exact hv.mp (by rw [hv0, hF0])
  have hgr : ∀ᶠ x in 𝓝 u.1, F (x, g x) = 0 := by
    have h := hcdf.eventually_apply_implicitFunction hpn hif
    filter_upwards [h] with x hx
    rw [hx, hF0]
  -- extract the radii
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp huniq
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hT
  -- the graph of `g` stays close to `u` (hence, by `hT`, in `T`) as `x` approaches `u.1`
  have hgball : ∀ᶠ x in 𝓝 u.1, dist (g x) u.2 < δ₂ := by
    have h := hgcd.continuousAt.eventually (Metric.ball_mem_nhds (g u.1) hδ₂pos)
    filter_upwards [h] with x hx
    rwa [hg0] at hx
  have hdist : ∀ᶠ x in 𝓝 u.1, dist (x, g x) u < δ₂ := by
    filter_upwards [Metric.ball_mem_nhds u.1 hδ₂pos, hgball] with x hx1 hx2
    rw [Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hx1) hx2
  have hΓT : ∀ᶠ x in 𝓝 u.1, (x, g x) ∈ T := by
    filter_upwards [hdist, hgr] with x hx1 hx2
    exact hδ₂ hx1 hx2
  obtain ⟨ρT, hρTpos, hρT⟩ := Metric.eventually_nhds_iff.mp hΓT
  obtain ⟨s, hs_mem, hgs⟩ :=
    hgcd.contDiffOn (m := 1) le_rfl (fun h => absurd h (by norm_num))
  obtain ⟨ρs, hρspos, hρs⟩ := Metric.mem_nhds_iff.mp hs_mem
  have hball_sub : Metric.closedBall u.1 (ρs / 2) ⊆ s := fun x hx =>
    hρs (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
  set ρ : ℝ := min ρT (min (ρs / 2) δ₁) / 2 with hρdef
  have hmid_pos : 0 < min ρT (min (ρs / 2) δ₁) :=
    lt_min hρTpos (lt_min (by linarith) hδ₁pos)
  have hρ_pos : 0 < ρ := by rw [hρdef]; linarith
  have hρT' : ρ < ρT := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ ρT := min_le_left _ _
    rw [hρdef]; linarith
  have hρs' : ρ < ρs / 2 := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ ρs / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hρdef]; linarith
  have hδ₁' : ρ < δ₁ := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ δ₁ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [hρdef]; linarith
  -- the graph over the closed ball is a connected piece of `T` containing `u`
  have hcontOn : ContinuousOn (fun x : E₁ => (x, g x)) (Metric.closedBall u.1 ρ) :=
    continuousOn_id.prodMk (hgs.continuousOn.mono fun x hx =>
      hball_sub (Metric.closedBall_subset_closedBall (by linarith) hx))
  have hSpre : IsPreconnected
      ((fun x : E₁ => (x, g x)) '' Metric.closedBall u.1 ρ) :=
    (convex_closedBall u.1 ρ).isPreconnected.image _ hcontOn
  have huS : u ∈ (fun x : E₁ => (x, g x)) '' Metric.closedBall u.1 ρ :=
    ⟨u.1, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρ_pos,
      by show (u.1, g u.1) = u; rw [hg0]⟩
  have hST : (fun x : E₁ => (x, g x)) '' Metric.closedBall u.1 ρ ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hρT (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hρT'))
  have hScomp : (fun x : E₁ => (x, g x)) '' Metric.closedBall u.1 ρ ⊆
      connectedComponentIn T u :=
    IsPreconnected.subset_connectedComponentIn hSpre huS hST
  -- every zero of `F` in the ball of radius `ρ` is on that graph
  refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρ_pos, fun v hv hv0 => ?_⟩
  have hv2 : g v.1 = v.2 := hδ₁ (lt_of_lt_of_le hv (le_of_lt hδ₁')) hv0
  refine hScomp ⟨v.1, ?_, ?_⟩
  · rw [Metric.mem_closedBall]
    calc dist v.1 u.1 ≤ dist v u := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ ρ := le_of_lt hv
  · show (v.1, g v.1) = v
    exact Prod.ext rfl hv2

end Work.WilE2.Ebc
