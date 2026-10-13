/-
Copyright: work module for the Elgindi finite-time singularity project.

# `|Ḡ(α,F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}` for sources smooth on the open quadrant

This module proves

  `Work.FTS.EllipticEst.Gbar_Hk_le_open`:
for every `k` there is `C_k > 0`, independent of `α ∈ (0,1]`, such that

  `|Ḡ(α,F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`,

for every source `F` which is `C^∞` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)` (i.e. the
hypothesis `∀ n, ContDiffOn ℝ n (uncurry F) Q0` of the statement, the class
`Work.FTS.EllipticEst.SmoothOpen`) and which lies in the weighted space `ℋ^k`
(`Work.Spaces.HkMem`).  Here `Ḡ(α,F) = Work.Elliptic.Gbar α F` is the singular term of
§'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

i.e. `Ḡ = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds` with `F_*` the angular moment of `F`.

This is the open-quadrant (and hence weaker-hypothesis) counterpart of
`Work.FTS.EllipticEst.Gbar_Hk_fts`, which assumes smoothness on a neighbourhood of the *closed*
quadrant: the estimate is proved here for the class in which the application actually lives (a
cut-off is `C^∞` but never analytic on a neighbourhood of the closed quadrant).

## The proof

Everything is assembled in `Work.FTS.EllipticEst.Gbar_le_open_core`; this module only weakens
the smoothness hypothesis to the raw shape of the statement (`smoothOpen_of_forall`).  The shape
of the argument, with `β = 5/α`, `c = -(3/(4α))` and `U_j = F_*(D_z^j F)`, is

1. Cauchy–Schwarz on the angular slice: `(U_j z)² w(z)² ≤ (π/2) A_j(z)` where
   `A_j = ∫_θ (D_z^j F · w/sin(2θ)^{η/2})²` is a summand of the `ℋ^k`-integrand of `F`
   (`FstarDzIter_sq_mul_w_le_open`);
2. the chain rule `U_j z - U_j s = ∫_s^z U_{j+1}(r)/r dr` (a Fubini/FTC argument on the open
   quadrant), making `U_j` an absolutely continuous primitive of a locally integrable function
   and hence *continuous* (`continuousOn_of_primitive_of_sqrt_bound`);
3. differentiating the Hardy operator (`rDz_HarOp_of_continuousAt`, whose measurability input is
   `aestronglyMeasurable_integral_Itheta_Q0`) and the integration by parts
   `HarOp β (D_z U) = U - β HarOp β U`, giving by induction the exact radial identity
   `D_z^j Ḡ = c·HarOp β U_j`;
4. the weighted Hardy inequality `∫ w² (HarOp β U_j)² ≤ (100/β²) ∫ w² U_j²`
   (`Gbar_hardy_le`), whose factor `1/β²` cancels the `1/α²` of `c²` and yields the
   `α`-independent constant `(9/4)(π/2)` for every `j ≤ k`;
5. the pointwise domination of the `ℋ^k`-integrand of `Ḡ sin 2θ` by the angular constants:
   `D_z^i (Ḡ sin 2θ) = (D_z^i Ḡ)·sin 2θ` and `(D_θ^i (sin 2θ))² sin(2θ)^{-γ} ≤ angC i`.

The two auxiliary real-analysis facts (2) and (3) are proved in the sibling modules
`Work.FTS.EllipticEst.GbarSin` and `Work.FTS.EllipticEst.Cert.GbarSin` and are re-exported in
`Work.FTS.EllipticEst.Gbar_le_open_core` under the names used there.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Gbar_le_open_core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem Gbar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hC, h⟩ := Gbar_Hk_le_open_SmoothOpen k
  exact ⟨C, hC, fun α F hα hα1 hFraw hmem =>
    h α F hα hα1 (smoothOpen_of_forall hFraw) hmem⟩

end Work.FTS.EllipticEst
