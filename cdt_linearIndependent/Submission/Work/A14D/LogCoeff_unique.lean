import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.logCoeff_growth_contra

/-!
# `Work.A14D.LogCoeff_unique`

The logarithmic coefficient `κ` of a function `f` at the singular point `1/9` (`LogCoeff`) is
independent of the open piece on which it is read off, as long as the piece meets another such
piece.

The point is that `LogCoeff y9 δ V f κ` requires the remainder `f - κ · y9 · log(· - 1/9)` to be
holomorphic on the *whole* disc `ball (1/9) δ` (not merely on `V`), whereas `log(· - 1/9)` has a
genuine singularity at `1/9` (because `y9 1/9 ≠ 0`).  Concretely:

* `slitDisk δ = ball (1/9) δ ∩ slitComp` is the disc cut along `(-∞, 1/9]`, on which the principal
  logarithm `log(· - 1/9)` is holomorphic; it is open and preconnected (`isOpen_slitDisk`,
  `isPreconnected_slitDisk`).  Both `V` and `W` lie in it (`z - 1/9 ∈ slitPlane`).
* Hence `Ψ z = (κ - κ') · y9 z · log(z - 1/9) - (h' z - h z)` is holomorphic on `slitDisk δ` and
  vanishes on the nonempty open set `V ∩ W`, so the identity theorem forces `Ψ ≡ 0` on
  `slitDisk δ`.
* Along the positive real direction `z = 1/9 + ε → 1/9` the left-hand side blows up like
  `(κ - κ')·y9(1/9)·log ε` while the right-hand side stays bounded; so `κ = κ'` (this is
  `logCoeff_growth_contra`).
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

theorem LogCoeff_unique {y9 : ℂ → ℂ} {δ : ℝ} (hy9 : DifferentiableOn ℂ y9 (Metric.ball Work.A14D.ninth δ))
    (hy9ne : y9 Work.A14D.ninth ≠ 0) {V W : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVsub : V ⊆ Metric.ball Work.A14D.ninth δ) (hVslit : ∀ z ∈ V, z - Work.A14D.ninth ∈ Complex.slitPlane)
    (hWo : IsOpen W) (hWne : W.Nonempty)
    (hWsub : W ⊆ Metric.ball Work.A14D.ninth δ) (hWslit : ∀ z ∈ W, z - Work.A14D.ninth ∈ Complex.slitPlane)
    (hVW : (V ∩ W).Nonempty)
    {f : ℂ → ℂ} {κ κ' : ℂ} (hκ : Work.A14D.LogCoeff y9 δ V f κ) (hκ' : Work.A14D.LogCoeff y9 δ W f κ') :
    κ = κ' := by
  obtain ⟨h, hhd, hhV⟩ := hκ
  obtain ⟨h', hh'd, hh'W⟩ := hκ'
  by_contra hne
  have hc : κ - κ' ≠ 0 := sub_ne_zero.mpr hne
  -- the disc radius is positive because `V` is a nonempty subset of `ball ninth δ`
  have hδpos : 0 < δ := by
    obtain ⟨z₀, hz₀⟩ := hVne
    have hmem := Metric.mem_ball.mp (hVsub hz₀)
    rw [Complex.dist_eq] at hmem
    exact lt_of_le_of_lt (norm_nonneg _) hmem
  -- both pieces lie in the slit disc
  have hVsubd : V ⊆ slitDisk δ :=
    fun z hz => ⟨hVsub hz, by simpa using slitPlane_slitComp (hVslit z hz)⟩
  -- the difference of the two log-expansions is holomorphic on the slit disc
  have hΨdiff : DifferentiableOn ℂ
      (fun z : ℂ => (κ - κ') * y9 z * Complex.log (z - ninth) - (h' z - h z)) (slitDisk δ) := by
    have hlog : DifferentiableOn ℂ (fun z : ℂ => Complex.log (z - ninth)) (slitDisk δ) := by
      intro z hz
      exact ((Complex.differentiableAt_log (slitComp_slitPlane hz.2)).comp z
        (differentiableAt_id.sub_const ninth)).differentiableWithinAt
    exact (((differentiableOn_const (κ - κ')).mul (hy9.mono Set.inter_subset_left)).mul hlog).sub
      ((hh'd.mono Set.inter_subset_left).sub (hhd.mono Set.inter_subset_left))
  -- it vanishes on the nonempty open set `V ∩ W`
  obtain ⟨z₀, hz₀V, hz₀W⟩ := hVW
  have hΨzero : ∀ z ∈ V ∩ W,
      (κ - κ') * y9 z * Complex.log (z - ninth) - (h' z - h z) = 0 := by
    intro z hz
    obtain ⟨hzV, hzW⟩ := hz
    have h1 := hhV z hzV
    have h2 := hh'W z hzW
    have key : κ * y9 z * Complex.log (z - ninth) + h z
        = κ' * y9 z * Complex.log (z - ninth) + h' z := by rw [← h1, h2]
    linear_combination key
  have hΨev : (fun z : ℂ => (κ - κ') * y9 z * Complex.log (z - ninth) - (h' z - h z))
      =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [(hVo.inter hWo).mem_nhds ⟨hz₀V, hz₀W⟩] with z hz
    exact hΨzero z hz
  -- identity theorem: it vanishes on the whole slit disc
  have hΨall : ∀ z ∈ slitDisk δ,
      (κ - κ') * y9 z * Complex.log (z - ninth) - (h' z - h z) = 0 :=
    hΨdiff.analyticOnNhd (isOpen_slitDisk δ)
      |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_slitDisk hδpos)
        (hVsubd hz₀V) hΨev
  -- the growth contradiction
  exact logCoeff_growth_contra hδpos hy9 hy9ne (hh'd.sub hhd) hc
    (fun z hz => sub_eq_zero.mp (hΨall z hz))

end Work.A14D
