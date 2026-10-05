import Mathlib
import Submission.Work.RPCore.Flow.HamFlow
import Submission.Work.RPCore.Flow.clampedField_bounds
import Submission.Work.RPCore.Flow.Basic
import Submission.Work.RPV.Defs
import Submission.Work.RPCore.GenFun.exists_type2GF
import Submission.Work.RPCore.GenFun.wrot_isType2GF
import Submission.Work.RPCore.Chain.chainAction_crit
import Submission.Work.RPCore.Saddle.saddle_point_periodic
import Submission.Work.RPCore.Core.core

/-!
# Block CORE: the node statements in namespace `RectPeg`

Re-exports of the node contracts of `RECTPEG_ROUTE_LEAD.md` under the names the route document uses
(namespace `RectPeg`), each proved in the corresponding module of this directory:

* `RectPeg.exists_flow`           (`Work.RPCore.Flow.exists_flow`)      — C0,
* `RectPeg.exists_type2GF`        (`Work.RPCore.GenFun.exists_type2GF`) — C1,
* `RectPeg.wrot_isType2GF`        (`Work.RPCore.GenFun.wrot_isType2GF`) — C1,
* `RectPeg.chainAction_crit`      (`Work.RPCore.Chain.chainAction_crit`)— C3,
* `RectPeg.saddle_point_periodic` (`Work.RPCore.Saddle.saddle_point_periodic`) — C5,
* `RectPeg.core`                  (`Work.RPCore.Core.core`)            — the assembly.

The shared vocabulary (`PS`, `symp`, `Tk`, `Zsec`, `K0`, `tau`, `hamVF`, `CptPerHam`, `IsFlow`,
`dq`, `dP`, `IsType2GF`, `Wrot`, `chainAction`) is **not** redeclared here: it is the vocabulary of
`Submission/Work/RPV/Defs.lean` (namespace `Work.RPV`), opened below, so that the statements read
exactly as in the route document.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace RectPeg

open Work.RPV

/-- C1: global type-2 generating functions of near-identity symplectic maps, compactly
supported mod `2π` and periodic when `ψ` is. -/
theorem exists_type2GF (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ)
    (hsymp : ∀ x a b, symp (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = symp a b)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ PS‖ ≤ 1 / 4)
    (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x)) (R : ℝ)
    (hid : ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → ψ x = x) :
    ∃ W : PS → ℝ, ContDiff ℝ 3 W ∧ IsType2GF ψ W ∧ (∀ x, W (Tk 1 x) = W x) ∧
      ∃ R' : ℝ, ∀ x, R' ≤ |x.1.1| + |x.2.1| + |x.2.2| → W x = 0 :=
  Work.RPCore.GenFun.exists_type2GF ψ hψ hsymp hnear hper R hid

/-- The explicit type-2 generating function `Wrot δ` of the rotation `tau δ` (`|δ| < π/2`). -/
theorem wrot_isType2GF (δ : ℝ) (hδ : |δ| < π / 2) : IsType2GF (tau δ) (Wrot δ) :=
  Work.RPCore.GenFun.wrot_isType2GF δ hδ

/-- C3: critical points of the chain action are orbits from `Z` to `Z`. -/
theorem chainAction_crit (n : ℕ) (ψ : Fin (n + 1) → PS → PS) (W : Fin (n + 1) → PS → ℝ)
    (hW : ∀ j, IsType2GF (ψ j) (W j)) (hWd : ∀ j, Differentiable ℝ (W j))
    (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ)
    (hcrit : fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      chainAction n W z.1 z.2) (q, P) = 0) :
    ∃ x ∈ Zsec, ∃ y ∈ Zsec, (List.ofFn ψ).foldl (fun acc f => f acc) x = y :=
  Work.RPCore.Chain.chainAction_crit n ψ W hW hWd q P hcrit

/-- C5: saddle-point theorem on `(ℝ / Pℤ) × ℝ^M` for a bounded `C²` perturbation of a
nondegenerate quadratic form. -/
theorem saddle_point_periodic {M : ℕ} (F : ℝ × EuclideanSpace ℝ (Fin M) → ℝ)
    (hF : ContDiff ℝ 2 F) (Pd : ℝ) (hPd : 0 < Pd) (hper : ∀ a v, F (a + Pd, v) = F (a, v))
    (A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M))
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) (hAinj : Function.Injective A)
    (C : ℝ) (hC0 : ∀ a v, |F (a, v) - inner ℝ (A v) v / 2| ≤ C)
    (hC1 : ∀ a v, ‖fderiv ℝ F (a, v) - (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A v))‖ ≤ C) :
    ∃ z, fderiv ℝ F z = 0 :=
  Work.RPCore.Saddle.saddle_point_periodic F hF Pd hPd hper A hA hAinj C hC0 hC1

/-- **CORE.**  If `Φ` is a compactly supported (mod `2π` in `q₂`) Hamiltonian diffeomorphism and
`0 < θ < π`, then `Φ(Z)` meets `τ_θ Φ(Z)`. -/
theorem core (Hh : CptPerHam) (Φ : ℝ → PS → PS) (hΦ : IsFlow Hh.H Φ) (θ : ℝ)
    (h0 : 0 < θ) (h1 : θ < π) :
    ∃ x ∈ Zsec, ∃ y ∈ Zsec, tau θ (Φ 1 x) = Φ 1 y :=
  Work.RPCore.Core.core Hh Φ hΦ θ h0 h1

end RectPeg
