import Mathlib
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.slitPieces

/-!
# A14D — the logarithmic coefficient of the continuation of `u_h` is non-zero

Let `F` be a global solution of `LZ = 0` on the slit plane `Om1 = ℂ ∖ (−∞,1]` which agrees with the
holomorphic solution `u_h` of `LZ = 0` at `x = 1` on the overlap `Om1 ∩ ball 1 (8/9)`.  Then `F`
has a *non-zero* logarithmic coefficient at `1/9` on the upper half-disc `halfU δ`.

The existence of a coefficient is `logCoeff_exists` (`halfU δ` is open, convex and inside the slit
disc).  Its non-vanishing is the point: if the coefficient `κ` vanished, `F` would agree on
`halfU δ` with a function `h` holomorphic on the whole ball `ball (1/9) δ`; but on the non-empty
open wedge `halfU δ ∩ ball 1 (8/9)` we have `F = h = u_h`, so by the identity theorem `h = u_h` on
`ball (1/9) δ ∩ ball 1 (8/9)`, contradicting `uh_not_holo_at_ninth` (`u_h` is not holomorphic at
`1/9`).
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

theorem logCoeff_uh_cont_ne_zero {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F Om1) (hFL : ∀ z ∈ Om1, LZ F z = 0)
    (hFuh : ∀ z ∈ Om1 ∩ Metric.ball (1 : ℂ) (8 / 9), F z = uh z) :
    ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δ (halfU δ) F lam := by
  have hYc : Y9 y9 δ := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  -- `halfU δ` is an open convex piece of the slit disc
  have hUOm1 : halfU δ ⊆ Om1 := fun z hz => Or.inl (ne_of_gt hz.2)
  have hUsub : halfU δ ⊆ ball ninth δ ∩ {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re} :=
    fun z hz => ⟨hz.1, Or.inl (ne_of_gt hz.2)⟩
  -- existence of a logarithmic coefficient
  obtain ⟨κ, hκ⟩ :=
    logCoeff_exists hYc (halfU δ) (isOpen_halfUp δ) (convex_halfUp δ) hUsub F
      (hF.mono hUOm1) (fun z hz => hFL z (hUOm1 hz))
  refine ⟨κ, ?_, hκ⟩
  intro hκ0
  obtain ⟨h, hhd, hheq⟩ := hκ
  -- with `κ = 0`, `F` agrees with `h` on `halfU δ`
  have hFh : ∀ z ∈ halfU δ, F z = h z := by
    intro z hz
    have h1 := hheq z hz
    rw [hκ0] at h1
    simpa using h1
  -- a point of `halfU δ ∩ ball 1 (8/9)`
  set z0 : ℂ := ninth + (((δ / 4 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I with hz0
  have hz0im : z0.im = δ / 4 := by rw [hz0]; simp [ninth]
  have hz0b9 : z0 ∈ ball ninth δ := by
    rw [mem_ball, Complex.dist_eq]
    have hsub : z0 - ninth = (((δ / 4 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I := by
      rw [hz0]; ring
    rw [hsub]
    have h4 : (0 : ℝ) ≤ δ / 4 := by linarith
    calc ‖(((δ / 4 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I‖
        ≤ ‖(((δ / 4 : ℝ)) : ℂ)‖ + ‖(((δ / 4 : ℝ)) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = δ / 4 + δ / 4 := by
          rw [norm_ofReal_nonneg h4, norm_mul, Complex.norm_I, mul_one, norm_ofReal_nonneg h4]
      _ < δ := by linarith
  have hz0b1 : z0 ∈ ball (1 : ℂ) (8 / 9) := by
    rw [mem_ball, Complex.dist_eq]
    have hsub : z0 - 1 = (((δ / 4 - 8 / 9 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I := by
      rw [hz0]; simp only [ninth]; push_cast; ring
    rw [hsub]
    have hnorm2 : ‖(((δ / 4 - 8 / 9 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I‖ ^ 2
        = (δ / 4 - 8 / 9) ^ 2 + (δ / 4) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hlt : ‖(((δ / 4 - 8 / 9 : ℝ)) : ℂ) + (((δ / 4 : ℝ)) : ℂ) * Complex.I‖ ^ 2
        < (8 / 9 : ℝ) ^ 2 := by
      rw [hnorm2]; nlinarith [hδpos, hδ20]
    have hsq := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 9)] at hsq
  have hz0mem : z0 ∈ halfU δ ∩ ball (1 : ℂ) (8 / 9) :=
    ⟨⟨hz0b9, by show 0 < z0.im; rw [hz0im]; linarith⟩, hz0b1⟩
  have hz0U : z0 ∈ ball ninth δ ∩ ball (1 : ℂ) (8 / 9) := ⟨hz0b9, hz0b1⟩
  -- `h` and `u_h` are both holomorphic on `ball (1/9) δ ∩ ball 1 (8/9)` and agree on the open
  -- non-empty wedge `halfU δ ∩ ball 1 (8/9)`, hence everywhere on it
  have hAnalH : AnalyticOnNhd ℂ h (ball ninth δ ∩ ball (1 : ℂ) (8 / 9)) :=
    (hhd.mono Set.inter_subset_left).analyticOnNhd (Metric.isOpen_ball.inter Metric.isOpen_ball)
  have hAnalUh : AnalyticOnNhd ℂ uh (ball ninth δ ∩ ball (1 : ℂ) (8 / 9)) :=
    (uh_ode.1.mono Set.inter_subset_right).analyticOnNhd
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
  have hpre : IsPreconnected (ball ninth δ ∩ ball (1 : ℂ) (8 / 9)) :=
    ((convex_ball ninth δ).inter (convex_ball (1 : ℂ) (8 / 9))).isPreconnected
  have hev : h =ᶠ[𝓝 z0] uh := by
    filter_upwards [((isOpen_halfUp δ).inter Metric.isOpen_ball).mem_nhds hz0mem] with z hz
    calc h z = F z := (hFh z hz.1).symm
      _ = uh z := hFuh z ⟨hUOm1 hz.1, hz.2⟩
  have hEqOn : Set.EqOn h uh (ball ninth δ ∩ ball (1 : ℂ) (8 / 9)) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAnalH hAnalUh hpre hz0U hev
  -- contradicting non-holomorphy of `u_h` at `1/9`
  exact uh_not_holo_at_ninth ⟨h, δ, hδpos, hhd, fun z hz => hEqOn hz⟩

end Work.A14D
