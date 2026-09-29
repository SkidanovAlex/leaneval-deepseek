import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.dy_step_ninth

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-- One step of `∂_y = (1/y')·d/dz` on an open piece `V` of the disc `ball (1/9) δ` that avoids
the real axis.

Setting: `δ ≤ 1/20` keeps `0`, `1`, `2` out of `Metric.ball ninth δ`, so the factor
`(z-1)²/(z²-2z)` of `Dy` is holomorphic on the disc.  Any `z` with `z.im ≠ 0` satisfies
`(z - 1/9).im ≠ 0`, hence `z - 1/9 ∈ Complex.slitPlane` (both the upper and the lower half plane
are contained in the slit plane of the principal logarithm), so on such a `V` the principal
`Complex.log (· - 1/9)` is holomorphic with derivative `1/(· - 1/9)`.

Claim: if `A`, `G` are holomorphic on `Metric.ball ninth δ` and on `V` the function `F` agrees
with `A · log (· - 1/9) + G / (· - 1/9)^m`, then `Dy F` agrees on `V` with
`(Dy A) · log (· - 1/9) + G' / (· - 1/9)^(m+1)` for some `G'` holomorphic on the whole disc. -/
theorem dy_step_slitIm {δ : ℝ} (hδ : δ ≤ 1 / 20) {V : Set ℂ}
    (hVopen : IsOpen V) (hVsub : V ⊆ Metric.ball Work.A14D.ninth δ)
    (hVim : ∀ z ∈ V, z.im ≠ 0)
    {m : ℕ} {F A G : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball Work.A14D.ninth δ))
    (hG : DifferentiableOn ℂ G (Metric.ball Work.A14D.ninth δ))
    (h : ∀ z ∈ V, F z = A z * Complex.log (z - Work.A14D.ninth)
        + G z / (z - Work.A14D.ninth) ^ m) :
    ∃ G' : ℂ → ℂ, DifferentiableOn ℂ G' (Metric.ball Work.A14D.ninth δ) ∧
      ∀ z ∈ V, Work.A14D.Dy F z = Work.A14D.Dy A z * Complex.log (z - Work.A14D.ninth)
        + G' z / (z - Work.A14D.ninth) ^ (m + 1) := by
  classical
  have hball : IsOpen (Metric.ball ninth δ) := Metric.isOpen_ball
  refine ⟨fun z => ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) *
      (A z * (z - ninth) ^ m + deriv G z * (z - ninth) - (m : ℂ) * G z),
    dy_step_ninth_witness_holo hδ hA hG, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball ninth δ := hVsub hz
  have hzim : z.im ≠ 0 := hVim z hz
  have hninth_im : ninth.im = 0 := by simp [ninth]
  -- `z ≠ 1/9` since `z` is off the real axis
  have hu : z - ninth ≠ 0 := by
    intro h0
    have h1 : (z - ninth).im = 0 := by rw [h0]; simp
    simp only [Complex.sub_im, hninth_im, sub_zero] at h1
    exact hzim h1
  -- `z - 1/9` lies in the slit plane: its imaginary part is nonzero
  have hsl : z - ninth ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [Complex.sub_im, hninth_im, sub_zero]
    exact hzim
  -- `V` is a neighbourhood of `z`, so `F` and the model function have the same derivative
  have hmem : V ∈ 𝓝 z := hVopen.mem_nhds hz
  have heq : F =ᶠ[𝓝 z] (fun w : ℂ => A w * Complex.log (w - ninth) + G w / (w - ninth) ^ m) :=
    Filter.eventually_of_mem hmem h
  have hderivF : deriv F z
      = deriv (fun w : ℂ => A w * Complex.log (w - ninth) + G w / (w - ninth) ^ m) z :=
    heq.deriv_eq
  have hAat : HasDerivAt A (deriv A z) z :=
    (hA.differentiableAt (hball.mem_nhds hzball)).hasDerivAt
  have hGat : HasDerivAt G (deriv G z) z :=
    (hG.differentiableAt (hball.mem_nhds hzball)).hasDerivAt
  have hH := dy_step_ninth_log_deriv (m := m) hsl hAat hGat
  have hAlg := dy_step_ninth_algebra (m := m) (z - ninth) (A z) (deriv A z) (G z) (deriv G z) hu
  rw [Dy, Dy, hderivF, hH.deriv, hAlg]
  ring

end Work.A14D
