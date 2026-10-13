/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slicewise vocabulary for the straightened-solution estimate

This module fixes the *one-dimensional* (in `θ`) vocabulary used to state the slicewise
angular coercivity that underlies `Work.FTS.EllipticEst.Straight_Hk_input`.

The `ℋ^k` norm of the paper is a sum over the mixed derivatives `D_z^j D_θ^i`
(`D_z = z∂_z`, `D_θ = sin(2θ)∂_θ`), with the angular weights `w_θ = sin(2θ)^{-γ/2}` for
`i ≥ 1` and `sin(2θ)^{-η/2}` for `i = 0`.  Because `D_z` acts only on the radial variable,

  `HkSq α k f = ∑_{j=0}^{k} ∫_z w(z)^2 · P_{α}^{k-j}(f_j(z)) dz`,   `f_j(z) = D_z^j f(z,·)`,

so *every* estimate of the chapter splits into a radial integral of the one-dimensional
angular functional `Ptheta α m` below.  The definitions here are the `θ`-slice part.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The one-dimensional angular operator `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` of the elliptic
section, acting on functions of `θ` alone.  It is the `θ`-slice of
`Work.Elliptic.Lzero`. -/
def Lzero1 (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ

/-- The angular weight of the `i = 0` (pure radial) group: `sin(2θ)^{-η}` with `η = 99/100`. -/
def sEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight of the mixed (`i ≥ 1`) groups: `sin(2θ)^{-γ}` with `γ = 1 + α/10`. -/
def sGam (α : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- `Ptheta α m u`: the angular quadratic functional of the `ℋ^k` norm at slice level `m`,
`∫_θ u² sin(2θ)^{-η} + ∑_{i=1}^{m} ∫_θ (D_θ^i u)² sin(2θ)^{-γ}`. -/
def Ptheta (α : ℝ) (m : ℕ) (u : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * sEta θ)
    + ∑ i ∈ Finset.Icc 1 m,
        ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ

/-- Honesty of the `Ptheta α m` functional: every one of its `m + 1` integrands is
`θ`-integrable.  Without this the totalised integral takes the junk value `0`. -/
def PthetaMem (α : ℝ) (m : ℕ) (u : ℝ → ℝ) : Prop :=
  (IntegrableOn (fun θ => (u θ) ^ 2 * sEta θ) Work.Spaces.Iθ)
    ∧ ∀ i ∈ Finset.Icc 1 m,
        IntegrableOn (fun θ => (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ)
          Work.Spaces.Iθ

/-- `Lzero1` is the `θ`-slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_eq_Lzero (u : ℝ → ℝ) (z : ℝ) :
    Lzero1 u = fun θ => Work.Elliptic.Lzero (fun _ θ' => u θ') z θ := by
  funext θ
  simp only [Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `Work.Elliptic.Dth1Iter` is the `θ`-restriction of `Work.Spaces.DthIter`. -/
theorem Dth1Iter_eq_DthIter (i : ℕ) (u : ℝ → ℝ) :
    ∀ θ : ℝ, Work.Elliptic.Dth1Iter i u θ = Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ := by
  induction i with
  | zero => intro θ; rfl
  | succ i ih =>
      intro θ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Spaces.DthIter_succ]
      have hfun : Work.Elliptic.Dth1Iter i u
          = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ') := by
        funext θ'; exact ih θ'
      rw [hfun]
      simp only [Work.Elliptic.Dth1, Work.Spaces.Dth, Work.Spaces.pth]

end Work.FTS.EllipticEst
