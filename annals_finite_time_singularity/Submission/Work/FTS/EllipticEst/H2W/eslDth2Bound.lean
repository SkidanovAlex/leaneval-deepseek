import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-- On the *open* interval `(0, π/2)` — where the second iterate of `D_θ = sin(2θ) ∂_θ`
can be computed by the product rule — the second iterate of the one-dimensional angular
operator `Dth1Iter 2` of an arbitrary `C²` function is

`D_θ²u = 2 sin(2θ)cos(2θ)·u' + sin(2θ)²·u''`.

Only two orders of regularity are needed (`ContDiffOn ℝ 2`), which is what the weak
`H²` estimate `eslDth2Bound` has at its disposal. -/
theorem Dth1Iter_two_expand (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Dth1Iter 2 u θ
      = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv u θ
        + (Real.sin (2 * θ)) ^ 2 * deriv (fun t => deriv u t) θ := by
  have hder : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hu.deriv_of_isOpen isOpen_Ioo (m := 1) (n := 2) (by norm_num)
    simpa using h
  have hd1 : DifferentiableAt ℝ (deriv u) θ :=
    (hder.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * θ) * 2) θ := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id θ).const_mul (2 : ℝ))).sin
    convert h2 using 1
    ring
  have hprod : HasDerivAt (fun t : ℝ => Real.sin (2 * t) * deriv u t)
      (2 * Real.cos (2 * θ) * deriv u θ
        + Real.sin (2 * θ) * deriv (fun t => deriv u t) θ) θ :=
    hsin.mul hd1.hasDerivAt
  have hderiv := hprod.deriv
  show Real.sin (2 * θ) * deriv (fun t : ℝ => Real.sin (2 * t) * deriv u t) θ = _
  rw [hderiv]
  ring

/-- The pointwise algebraic (weighted) inequality behind `eslDth2Bound`: for `θ ∈ [0, π/2]`
and arbitrary reals `u₁ u₂`, the square of `2 sin(2θ)cos(2θ)u₁ + sin(2θ)²u₂` against the
mixed-angular weight `sin(2θ)^{-γ}` is dominated by the two pure weights `sin(2θ)^{-η}`.

The gain is exactly the factor `sin(2θ)^{η-γ}`: since `γ ≥ η` and `sin(2θ) ≤ 1` one has
`sin(2θ)^{-γ} ≤ sin(2θ)^{-η}·sin(2θ)^{η-γ}`, and `sin(2θ)^{η-γ} sin(2θ)^{2}` and
`sin(2θ)^{η-γ} sin(2θ)^{4}` are both `≤ 1`, which converts the two terms of the elementary
inequality `(A + B)² ≤ 2A² + 2B²` into the constants `8 = 2·4` and `2 = 2·1`. -/
theorem sGam_mul_sq_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u₁ u₂ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (2 * Real.sin (2 * θ) * Real.cos (2 * θ) * u₁ + (Real.sin (2 * θ)) ^ 2 * u₂) ^ 2
        * Work.FTS.EllipticEst.sGam α θ
      ≤ 8 * (u₁ ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 2 * (u₂ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  set s := Real.sin (2 * θ) with hs_def
  set c := Real.cos (2 * θ) with hc_def
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := hθ.2
  have hs0 : 0 ≤ s := by
    rw [hs_def]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs_def]; exact Real.sin_le_one _
  have hc2 : c ^ 2 ≤ 1 := by rw [hc_def]; exact Real.cos_sq_le_one _
  have hsGam : Work.FTS.EllipticEst.sGam α θ = s ^ (-(Work.Spaces.gam α)) := by
    simp only [Work.FTS.EllipticEst.sGam]; rw [← hs_def]
  have hsEta : Work.FTS.EllipticEst.sEta θ = s ^ (-(Work.Spaces.eta)) := by
    simp only [Work.FTS.EllipticEst.sEta]; rw [← hs_def]
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    simp only [Work.Spaces.eta, Work.Spaces.gam]; linarith
  have heta0 : 0 ≤ Work.Spaces.eta := by simp only [Work.Spaces.eta]; norm_num
  have hgam2 : Work.Spaces.gam α ≤ 2 := by
    simp only [Work.Spaces.gam]; linarith
  have hexp2 : 0 ≤ Work.Spaces.eta - Work.Spaces.gam α + 2 := by linarith
  have hexp4 : 0 ≤ Work.Spaces.eta - Work.Spaces.gam α + 4 := by linarith
  rcases eq_or_lt_of_le hs0 with hs_zero | hs_pos
  · have hsz : s = 0 := hs_zero.symm
    have hX : 2 * s * c * u₁ + s ^ 2 * u₂ = 0 := by rw [hsz]; ring
    have hsg : Work.FTS.EllipticEst.sGam α θ = 0 := by
      rw [hsGam, hsz,
        Real.zero_rpow (by simp only [Work.Spaces.gam]; linarith : -(Work.Spaces.gam α) ≠ 0)]
    have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
      rw [hsEta, hsz, Real.zero_rpow (by simp [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    rw [hX, hsg, hse]
    norm_num
  · have hX2 : (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2
        ≤ 2 * (2 * s * c * u₁) ^ 2 + 2 * (s ^ 2 * u₂) ^ 2 := by
      nlinarith [sq_nonneg (2 * s * c * u₁ - s ^ 2 * u₂)]
    set k := s ^ (Work.Spaces.eta - Work.Spaces.gam α) with hk_def
    have hk0 : 0 ≤ k := Real.rpow_nonneg hs0 _
    have hks2 : k * s ^ 2 ≤ 1 := by
      rw [hk_def, ← Real.rpow_natCast s 2, ← Real.rpow_add hs_pos]
      exact Real.rpow_le_one hs0 hs1 hexp2
    have hks4 : k * s ^ 4 ≤ 1 := by
      rw [hk_def, ← Real.rpow_natCast s 4, ← Real.rpow_add hs_pos]
      exact Real.rpow_le_one hs0 hs1 hexp4
    have hkey : k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 ≤ 8 * u₁ ^ 2 + 2 * u₂ ^ 2 := by
      calc k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2
          ≤ k * (2 * (2 * s * c * u₁) ^ 2 + 2 * (s ^ 2 * u₂) ^ 2) :=
            mul_le_mul_of_nonneg_left hX2 hk0
        _ = (k * s ^ 2) * (8 * c ^ 2 * u₁ ^ 2) + (k * s ^ 4) * (2 * u₂ ^ 2) := by ring
        _ ≤ 1 * (8 * c ^ 2 * u₁ ^ 2) + 1 * (2 * u₂ ^ 2) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hks2 (by positivity)
            · exact mul_le_mul_of_nonneg_right hks4 (by positivity)
        _ ≤ 8 * u₁ ^ 2 + 2 * u₂ ^ 2 := by nlinarith [sq_nonneg u₁, sq_nonneg u₂, sq_nonneg c]
    have hgEq : Work.FTS.EllipticEst.sGam α θ = Work.FTS.EllipticEst.sEta θ * k := by
      rw [hsGam, hsEta, hk_def, ← Real.rpow_add hs_pos]
      congr 1
      ring
    have hsk : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [hsEta]; exact Real.rpow_nonneg hs0 _
    calc (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        = Work.FTS.EllipticEst.sGam α θ * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 := by ring
      _ = Work.FTS.EllipticEst.sEta θ * (k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2) := by
            rw [hgEq]; ring
      _ ≤ Work.FTS.EllipticEst.sEta θ * (8 * u₁ ^ 2 + 2 * u₂ ^ 2) :=
            mul_le_mul_of_nonneg_left hkey hsk
      _ = 8 * (u₁ ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + 2 * (u₂ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

theorem eslDth2Bound (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter 2 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ 8 * ((deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  intro θ hθ
  by_cases hs : Real.sin (2 * θ) = 0
  · have hX : Work.Elliptic.Dth1Iter 2 u θ = 0 := by
      simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
      rw [hs]; ring
    have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
      simp only [Work.FTS.EllipticEst.sEta]
      rw [hs, Real.zero_rpow (by simp [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    rw [hX, hse]
    norm_num
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; exact hs (by rw [← h]; simp)
      · intro h
        exact hs (by rw [h]; norm_num [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
    rw [Dth1Iter_two_expand u hu hθ']
    exact sGam_mul_sq_le α hα hα4 (deriv u θ) (deriv (fun t => deriv u t) θ) hθ

end Work.FTS.EllipticEst.H2W
