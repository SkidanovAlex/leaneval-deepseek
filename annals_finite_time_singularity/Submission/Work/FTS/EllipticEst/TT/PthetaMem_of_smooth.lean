/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PthetaMem` is automatic for smooth Dirichlet slices

The angular functional `Ptheta α m u = ∫_{Iθ} u² sin(2θ)^{-η} + ∑_{i=1}^{m} ∫_{Iθ} (D_θ^i u)² sin(2θ)^{-γ}`
of `Submission/Work/FTS/EllipticEst/StraightDefs.lean` is *honest* (`PthetaMem`) as soon as `u`
is smooth on an open neighbourhood of `[0, π/2]` and vanishes at both endpoints: every one of
its `m + 1` integrands is `θ`-integrable.

Mathematics.  Since `u` is `C^∞` near `[0, π/2]` and `u 0 = u (π/2) = 0`, the classical
one-dimensional bounds give a constant `C` with `|u θ| ≤ C sin(2θ)` on `(0, π/2)`; and for
`i ≥ 1`, `D_θ^i u = sin(2θ) · ∂_θ (D_θ^{i-1} u)` with `∂_θ (D_θ^{i-1} u)` again `C^∞` near
`[0, π/2]`, hence bounded, so `|D_θ^i u θ| ≤ K sin(2θ)`.  Consequently each integrand is
dominated by `C' sin(2θ)^{2-q}` with `q ∈ {η, γ}`; since `2 - q ≥ 0` (indeed `η = 99/100 ≤ 2`
and `γ = 1 + α/10 ≤ 2` for `α ≤ 1/4`) and `sin(2θ) ≤ 1` on `Iθ`, the integrands are bounded,
hence integrable on the finite-measure set `Iθ`.  (At the two endpoints `sin(2θ) = 0`, so the
integrands actually vanish there.)

The two analytic inputs are proved in the sibling modules
`Submission/Work/FTS/EllipticEst/TT/dth1Iter_smooth_bound.lean` (smoothness of the iterates and
the `sin(2θ)` bound) and `Submission/Work/FTS/EllipticEst/TT/integrableOn_sq_mul_sin_rpow_neg.lean`
(the measurability/domination step); the `i = 0` bound is the first clause of
`Work.Elliptic.DivSinSmoothBounds`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.TT.dth1Iter_smooth_bound
import Submission.Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sin_rpow_neg
import Submission.Work.Elliptic.DivSinSmoothBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

theorem PthetaMem_of_smooth (α : ℝ) (m : ℕ) (u : ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hu : Work.Elliptic.SmoothSlice u) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0) :
    Work.FTS.EllipticEst.PthetaMem α m u := by
  have hU : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    Set.Ioo_subset_Ioo (by linarith) (by linarith)
  unfold Work.FTS.EllipticEst.PthetaMem
  refine ⟨?_, ?_⟩
  · -- the `i = 0` group: `|u θ| ≤ C sin(2θ)`
    obtain ⟨C, hCpos, hCbd, _⟩ := Work.Elliptic.DivSinSmoothBounds u hu h0 h1
    have hcont : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn.mono hU
    have hq0 : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
    have hq2 : Work.Spaces.eta ≤ 2 := by rw [Work.Spaces.eta]; norm_num
    have h := integrableOn_sq_mul_sin_rpow_neg (f := u) (q := Work.Spaces.eta) (K := C)
      hq0 hq2 hCpos.le hcont hCbd
    simpa [Work.FTS.EllipticEst.sEta] using h
  · -- the `i ≥ 1` groups: `|D_θ^i u θ| ≤ K sin(2θ)`
    intro i hi
    obtain ⟨hsmooth, hbound⟩ := dth1Iter_smooth_bound u hu
    obtain ⟨K, hK0, hKb⟩ := hbound i (Finset.mem_Icc.mp hi).1
    have hcont : ContinuousOn (Work.Elliptic.Dth1Iter i u) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsmooth i).continuousOn.mono hU
    have hq0 : (0 : ℝ) < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have hq2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
    have h := integrableOn_sq_mul_sin_rpow_neg (f := Work.Elliptic.Dth1Iter i u)
      (q := Work.Spaces.gam α) (K := K) hq0 hq2 hK0 hcont hKb
    simpa [Work.FTS.EllipticEst.sGam] using h

end Work.FTS.EllipticEst.TT
