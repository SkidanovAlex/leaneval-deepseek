/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/DiagEstEllT/FiniteFacts` — the singular term in the trace-free class, at finite order

This module collects, for the datum class `EllHypT` of
`Submission/Work/FTS/EllipticEst/RegQ.lean` (Elgindi's *RemovingL12* class, the one of
`Cores/DiagEst_ellT.lean`), the *sharp finite-order* regularity and the two Euler identities of
the singular term `Gsing α F = Gstar α F + Gbar α F`:

* `honest_Fstar_cDiff` — `F_*(F) ∈ C^{k-1}` on `(0,∞)`;
* `honest_L12_data` — `L₁₂(F) ∈ C^{k-1}` with `∂_z L₁₂(F) = -3 F_*(F)/z`;
* `honest_Jfun_data` — the primitive `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds` is `C^{k-1}` with the
  expected derivative;
* `honest_Gsing_cDiff` — `Gsing α F ∈ C^{k+1}` and `Gbar α F ∈ C^k` on `(0,∞)`;
* `honest_Gsing_deriv_rel` — the first integral of the ODE: `α z ∂_z Gsing = -5 Gbar`;
* `honest_Gsing_ode` / `honest_Gsing_ode_deriv` — the second-order form, in the two shapes the
  straightening uses;
* `honest_lambda_zero` — the `θ → 0⁺` trace of `Ψ` vanishes.

## Why this is the honest replacement for `Cores.honestFstarFacts`

`Cores/honestFstarFacts` asks for the same identities together with the *`∀ m`* smoothness of
`F_*`, `Gsing` and `Gbar`, and that part is false (`Cores/honestFstarFacts.lean`'s docstring and
`UopHk/NOTES_removingL12Honest.md` §2): the class `EllHypT α k` bounds the moment ladder only at
order `k - 1`, and `F_*^{(k-1)}` need not be differentiable.  The *identities* need only finite
order, and that is what is proved here; the proofs are those of `UopHk.Gsing_cDiff_kp1` (for the
regularity) and of `Work.FTS.EllipticEst.Gsing_deriv_rel` / `Work.Elliptic.Gsing_ode` (for the
relations, whose inputs are exactly `honest_L12_data`, `honest_Fstar_hasDerivAt` and
`honest_Jfun_data`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open-quadrant smoothness of the datum -/

theorem honest_smoothOpen_F {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.UopHk.smoothOpen_of_smoothQuad h.quadF

theorem honest_smoothOpen_Psi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ :=
  Work.FTS.EllipticEst.UopHk.smoothOpen_of_smoothQuad h.quadPsi

/-! ## The moment ladder, `L₁₂` and the primitive `J` -/

/-- `F_*(F)` is `C^{k-1}` on `(0,∞)` for a datum of `EllHypT α k`. -/
theorem honest_Fstar_cDiff {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α k F
    (honest_smoothOpen_F h) h.regF.2.1 hk

/-- `F_*(F)` is differentiable on `(0,∞)` for `k ≥ 2` (the input `hFc` of the `Gsing` calculus). -/
theorem honest_Fstar_hasDerivAt {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
  intro z hz
  have h1 : ContDiffOn ℝ 1 (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
    have hle : ((1 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
      exact_mod_cast (by omega : 1 ≤ k - 1)
    exact (honest_Fstar_cDiff (by omega) h).of_le hle
  exact ((h1.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)).hasDerivAt

/-- `L₁₂(F) ∈ C^{k-1}` and `∂_z L₁₂(F) = -3 F_*(F)/z` on `(0,∞)`. -/
theorem honest_L12_data {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.L12 F) (Set.Ioi 0) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
  Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α k F
    (honest_smoothOpen_F h) h.regF.2.1 hk

/-- The primitive `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`: regularity and derivative. -/
theorem honest_Jfun_data {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ (k - 1)
        (fun z : ℝ => ∫ s in (0 : ℝ)..z,
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
            s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
          (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
  Work.FTS.EllipticEst.UopHk.contDiffOn_Jfun_of_smoothOpen_Hk α k F hα hα1
    (honest_smoothOpen_F h) h.regF.2.1 hk

/-- `Jfun α F` has the expected derivative (the `hJ` input of the `Gsing` calculus). -/
theorem honest_Jfun_hasDerivAt {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  intro z hz
  have h' := (honest_Jfun_data hα hα1 hk h).2 z hz
  have hfun : (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
      s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) = Work.Elliptic.Jfun α F := rfl
  rwa [hfun] at h'

/-- The available smoothness of the singular term: `Gsing α F ∈ C^{k+1}`, `Gbar α F ∈ C^k`. -/
theorem honest_Gsing_cDiff {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    (∀ m : ℕ, m ≤ k + 1 → ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      (∀ m : ℕ, m ≤ k → ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0)) :=
  Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1 α k F hα hα1 hk h.regF

/-! ## The two Euler identities -/

/-- **The first integral of the ODE of the singular term**: `α z ∂_z Gsing = -5 Gbar`. -/
theorem honest_Gsing_deriv_rel {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z :=
  Work.FTS.EllipticEst.Gsing_deriv_rel α F hα
    (honest_L12_data hk h).2 (honest_Fstar_hasDerivAt hk h)
    (honest_Jfun_hasDerivAt hα hα1 hk h)

/-- The same relation solved for the derivative. -/
theorem honest_Gsing_deriv_eq {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (Work.Elliptic.Gsing α F) z = -(5 * Work.Elliptic.Gbar α F z) / (α * z) := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hr := honest_Gsing_deriv_rel hα hα1 hk h z hz
  field_simp at hr ⊢
  linarith [hr]

/-- **The ODE of the singular term**: `α² z² ∂_zz Gsing + α(5+α) z ∂_z Gsing = (15/4) F_*`. -/
theorem honest_Gsing_ode {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z :=
  Work.Elliptic.Gsing_ode α F hα
    (honest_L12_data hk h).2 (honest_Fstar_hasDerivAt hk h)
    (honest_Jfun_hasDerivAt hα hα1 hk h)

/-- The ODE in the shape used by the straightening transfer
(`RPFresh.straight_transfers.zsq_G2_sin_ode`): `α² z² ∂_zz Gsing = (15/4)F_* + 5(5+α)Ḡ`. -/
theorem honest_Gsing_ode_deriv {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        = (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z := by
  intro z hz
  have hr := honest_Gsing_deriv_rel hα hα1 hk h z hz
  have ho := honest_Gsing_ode hα hα1 hk h z hz
  have hr2 : α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = -5 * (5 + α) * Work.Elliptic.Gbar α F z := by
    linear_combination (5 + α) * hr
  linarith [ho, hr2]

/-- The ODE in the pure `F_*`-form (no `Ḡ`), used when the source moment is available. -/
theorem honest_Gsing_ode_deriv' {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * (-(5 * Work.Elliptic.Gbar α F z) / (α * z))
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  intro z hz
  have hd := honest_Gsing_deriv_eq hα hα1 hk h z hz
  have ho := honest_Gsing_ode hα hα1 hk h z hz
  rw [← hd]
  exact ho

/-! ## The vanishing of the `θ → 0⁺` trace -/

/-- Under the orthogonality condition the slice limit of `Ψ` at `θ = 0⁺` vanishes
(`Cores.OrthCond_lambda_zero`, proved). -/
theorem honest_lambda_zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero α k hk F Ψ hα hα4 h hOrth

end Work.FTS.EllipticEst.Cores.DiagEstEllT
