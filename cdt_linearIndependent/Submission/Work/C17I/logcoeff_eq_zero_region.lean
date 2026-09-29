import Mathlib
import Submission.Work.C17.acl_log_compare
import Submission.Work.C17I.logcoeff_eq_zero

namespace Work.C17I

open Filter Metric
open scoped Topology

/-- **Extraction of the coefficient of `log (s - ·)`, regional version.**

Let `A , G : ℂ → ℂ` be holomorphic on the disc `ball s δ` (`s > 0`, `δ > 0`).  Suppose the
combination
`F z = A z * (z - s)^m * log (s - z) + G z`
vanishes on the *small* lens `ball s δ ∩ ball 0 ρ` with `ρ < s` (which is assumed nonempty).
Then `A` vanishes on all of `ball s δ`.

The small lens is contained in the *big* lens `ball s δ ∩ ball 0 s`, on which `F` is holomorphic
(`s - z` has positive real part there, so the principal logarithm is single valued).  The identity
principle (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, applied to the convex —
hence preconnected — big lens) upgrades `F = 0` from the small lens to the big lens, and then the
already established `logcoeff_eq_zero` (the `ρ = s` case) finishes. -/
theorem logcoeff_eq_zero_region {s δ ρ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hρ : ρ < s) {m : ℕ}
    (hne : (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ).Nonempty)
    {A G : ℂ → ℂ} (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ))
    (hG : DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ))
    (hid : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      A z * (z - s) ^ m * Complex.log (s - z) + G z = 0) :
    ∀ z ∈ Metric.ball (s : ℂ) δ, A z = 0 := by
  -- the big lens (where the principal logarithm is holomorphic) and the small lens
  set W : Set ℂ := Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s with hW
  set U : Set ℂ := Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ with hU
  set F : ℂ → ℂ := fun z => A z * (z - s) ^ m * Complex.log (s - z) + G z with hF
  have hWopen : IsOpen W := by rw [hW]; exact Metric.isOpen_ball.inter Metric.isOpen_ball
  have hUopen : IsOpen U := by rw [hU]; exact Metric.isOpen_ball.inter Metric.isOpen_ball
  have hWpc : IsPreconnected W := by
    rw [hW]
    exact ((convex_ball (s : ℂ) δ).inter (convex_ball (0 : ℂ) s)).isPreconnected
  have hUsubW : U ⊆ W := by
    rw [hU, hW]
    exact Set.inter_subset_inter_right _ (Metric.ball_subset_ball hρ.le)
  -- the logarithm is holomorphic on the big lens
  have hlog : DifferentiableOn ℂ (fun z : ℂ => Complex.log (s - z)) W := by
    intro z hz
    have hz' : z ∈ Metric.ball (0 : ℂ) s := by rw [hW] at hz; exact hz.2
    have hzn : ‖z‖ < s := by
      have h := hz'
      rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at h
    have hre : 0 < (s - z).re := by
      rw [Complex.sub_re, Complex.ofReal_re]
      have hle := Complex.re_le_norm z
      linarith
    have hmem : s - z ∈ Complex.slitPlane := (Complex.mem_slitPlane_iff).mpr (Or.inl hre)
    exact ((Complex.differentiableAt_log hmem).comp z
      ((differentiableAt_const (s : ℂ)).sub differentiableAt_id)).differentiableWithinAt
  have hA' : DifferentiableOn ℂ A W := hA.mono (by rw [hW]; exact Set.inter_subset_left)
  have hG' : DifferentiableOn ℂ G W := hG.mono (by rw [hW]; exact Set.inter_subset_left)
  have hFdiff : DifferentiableOn ℂ F W := by
    rw [hF]
    exact ((hA'.mul ((differentiableOn_id.sub (differentiableOn_const (s : ℂ))).pow m)).mul
      hlog).add hG'
  have hFan : AnalyticOnNhd ℂ F W := hFdiff.analyticOnNhd hWopen
  -- the identity principle upgrades `F = 0` to the big lens
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀W : z₀ ∈ W := hUsubW hz₀
  have hFev : F =ᶠ[nhds z₀] 0 := by
    filter_upwards [hUopen.mem_nhds hz₀] with z hz
    rw [hF, Pi.zero_apply]
    exact hid z hz
  have hFzero : Set.EqOn F 0 W :=
    hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWpc hz₀W hFev
  -- apply the `ρ = s` case
  exact fun z hz => logcoeff_eq_zero hδ hs hA hG (fun w hw => by
    have hwW : w ∈ W := by rw [hW]; exact hw
    simpa only [hF, Pi.zero_apply] using hFzero hwW) z hz

end Work.C17I
