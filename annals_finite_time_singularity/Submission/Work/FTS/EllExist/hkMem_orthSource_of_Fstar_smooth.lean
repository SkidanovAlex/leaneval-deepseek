import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllExist.Shift
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllExist.SmoothOpenSep
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

/-- **Honesty of the orthogonalised source, from the angular moment alone.**

`Work.Elliptic.orthSource g = g - (15/4)·sin 2θ·F_*(g)`, so for `g` smooth on the open quadrant
and honestly in `ℋ^k`, with `0 < α ≤ 1` and `F_*(g)` `C^∞` on `(0,∞)`, the orthogonalised source
is again honestly in `ℋ^k`.  This is the transfer the new class `ClassC`
(`Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`) needs in order to feed the area's existence node
`Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth k`, whose hypotheses are stated for the
source `orthSource g` (it is what the elliptic node `bslOp_sol_exists k` consumes).

The upper bound `α ≤ 1` is necessary: the mixed slot `(i=1, j=0)` of `orthSource g` is
`(D_θ(sin 2θ)·F_*(g))² · Wt²`, of order `θ^{2-γ}` with `γ = 1 + α/10`, which is `θ`-integrable
only for `γ < 3`, i.e. `α < 20`; the paper's range is `α ≤ 1/4` and the companion
`Work.FTS.EllipticEst.HkMem_orthSource` carries the same bound.

Expected proof: the pointwise subadditivity
`Work.FTS.LocData.HkIntegrand_add_le` (`HkIntegrand (a+b) ≤ 2 HkIntegrand a + 2 HkIntegrand b`)
reduces the claim to `HkMem α k (fun z θ => sin 2θ * F_*(g) z)`.  For that, bound each derivative
slot of `Φ z θ = sin 2θ · F_*(g) z` by the corresponding slot of `g`: `|D_θ^i(sin 2·)| ≤ 4^i`
and `(D_z^j F_*(g) z)² ≤ (π/2)·∫_θ (D_z^j g z θ)²` by Cauchy–Schwarz against `sinθcos²θ`, while
`∫_θ (D_z^j g)² ≤ w(z)^{-2}·∫_θ (D_z^j g · w(z)/sin(2θ)^{η/2})²` (the factor `sin^{-η} ≥ 1` only
helps).  `HkMem` then transfers by domination (`Work.FTS.LocData.HkMem_of_majorant`), the
`θ`-integrability at every `z ∈ Iz` coming from `α ≤ 1` (so that all `θ`-powers are integrable:
the worst slot is `θ^{2-γ}` with `γ ≤ 1.1`, and `1 + γ`-type exponents for the higher `<i>`), and
the `z`-integrability from `hmem`.  The companion facts making the `z`-derivatives of `F_*` exist
are supplied by `hF`. -/
theorem hkMem_orthSource_of_Fstar_smooth {α : ℝ} {k : ℕ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    Work.Spaces.HkMem α k (Work.Elliptic.orthSource g) := by
  -- The angular-moment term `Φ z θ = F_*(g) z · sin 2θ`.
  have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
    sep_mul_open (g := Work.Elliptic.Fstar g)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hF hsin
  -- `Φ ∈ ℋ^k`: the certificate for the angular moment of an open-quadrant datum.
  have hΦmem : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
    have h := Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α k g hα hα1 hsm hmem
    simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
  -- the scaled term `-(15/4)·Φ`.
  have hSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    const_mul_open (-(15 / 4)) hΦsm
  have hSmem : Work.Spaces.HkMem α k
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hΦmem
  -- `orthSource g` is the sum of the two summands.
  have horth : Work.Elliptic.orthSource g
      = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
    funext z θ
    simp only [Work.Elliptic.orthSource]
    ring
  rw [horth]
  exact Work.FTS.EllipticEst.HkMem_add_smoothOpen α k hα hsm hSsm hmem hSmem

end Work.FTS.EllExist
