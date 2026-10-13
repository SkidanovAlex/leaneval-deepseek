/-
# `Work.FTS.StrongPersist.N6Trans.T1SixAux.excMeanSide6`

The **mean-side bound for the top radial slot** `D_z⁵`: for `f` with `SmoothOpen f` and
honest `HkMem α 6 f`, the `θ`-slice `θ ↦ D_z⁵f(z,θ)` obeys the angular Agmon-type inequality

  `(D_z⁵f(z,θ))² ≤ C (∫_θ (D_z⁵f(z,·))² + (γ-1)⁻¹ ∫_θ (D_z⁵D_θf(z,·))² sin(2·)^{-γ})`

at every interior angle `θ ∈ (0,π/2)` and every `z > 0`, with `C` a universal constant.

The proof is `Work.FTS.OpenPkg.ProdOpen.sob_theta_mean` (constant `204`) applied to the slice
`h := θ ↦ D_z⁵f(z,θ)`:

* `sob_theta_mean` needs `h` differentiable on `(0,π/2)` with continuous derivative — provided
  by `SmoothOpen.curry_θ` of `DzIter 5 f` (the slice of a `C^∞` function on the open quadrant);
* its derivative term `∫ (∂_θh)² sin(2·)^{2-γ}` is the mixed slot `∫ (mixed 5 1 f)² sin(2·)^{-γ}`
  by `deriv_mixed_weight` (this is where the weight shifts `sin^{2-γ} ↦ sin^{-γ}`);
* the two integrability hypotheses are `integrableOn_dzIter5_sq` and
  `integrableOn_slice_neg_gam6` (slot `(b,a) = (5,1)`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.Spaces
open Work.FTS.OpenPkg.ProdOpen (sob_theta_mean sin_two_pos ae_mem_Ioo_Iθ deriv_mixed_weight)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem excMeanSide6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.DzIter 5 f z θ) ^ 2
        ≤ C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ∫ σ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 5 1 f z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
  obtain ⟨C1, hC1pos, hC1⟩ := sob_theta_mean
  refine ⟨C1, hC1pos, ?_⟩
  intro α f hα hα1 hF hmem z hz θ hθ
  -- the slice `θ ↦ D_z⁵f(z,θ)` is differentiable on the open interval, with continuous derivative
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => DzIter 5 f z σ')
        (deriv (fun σ' : ℝ => DzIter 5 f z σ') x) x := by
    intro x hx
    exact (((hF.DzIter 5).curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ' : ℝ => DzIter 5 f z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun σ => pth (DzIter 5 f) z σ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter 5).pth.curry_θ hz).continuousOn
    simpa only [pth] using h
  -- the mean term is integrable
  have hint1 : IntegrableOn (fun σ => (DzIter 5 f z σ) ^ 2) Iθ :=
    Work.FTS.StrongPersist.N6.integrableOn_dzIter5_sq hα hF hmem hz
  -- the derivative term is the `(5,1)`-mixed slot carrying the `sin(2·)^{-γ}` weight
  have hBeq : (∫ σ in Iθ, (deriv (fun σ' : ℝ => DzIter 5 f z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α))
      = ∫ σ in Iθ, (mixed 5 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
    have h := deriv_mixed_weight α hF 5 0 hz hσ
    rwa [show mixed 5 (0 + 1) f = mixed 5 1 f from by norm_num] at h
  have hint2 : IntegrableOn (fun σ => (deriv (fun σ' : ℝ => DzIter 5 f z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
    have h := Work.FTS.StrongPersist.N6.integrableOn_slice_neg_gam6 hα hF hmem 5 1
      (le_refl 1) (by norm_num) hz
    refine h.congr ?_
    filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
    exact (deriv_mixed_weight α hF 5 0 hz hσ).symm
  have hmain := hC1 α (fun σ' : ℝ => DzIter 5 f z σ') θ hα hα1 hθ hder hcontd hint1 hint2
  rwa [hBeq] at hmain

end Work.FTS.StrongPersist.N6Trans.T1SixAux
