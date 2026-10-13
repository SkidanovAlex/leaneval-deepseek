import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/RegFromVolterraD.lean` — OPEN LEAF-D `regFromVolterra'` (+ the `RegDataD` bundle)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §2 last bullet, §4.3; REVIEW (d),
F2).  TRUE.  The tree's `EpsE4Thr.RegFromVolterra` (PROVED) takes `hG`: `C¹` IN THE FAKE TIME of
`σ ↦ F (w_σ)`, which is NOT available for `F = Feps` with `E` unconstrained.  Its proof uses `hG`
only to obtain `hA`'s continuity and `hB` (via `RegSlab.continuousOn_sliceFderiv_slab`); so adapt
it: `∂_τ w = A` is continuous by `hAc`; `∂_y w = ∂_y h₀ + ∫ ∂_y A`, with local boundedness from `hB`
on the closed-`τ` slab (`RegSlab.hasFDerivAt_intervalIntegral_slab`,
`continuousOn_intervalIntegral_slab_normed`, `RXT0.slabC1Flat`).

`RegDataD F h₀ δ` bundles the three hypotheses (joint continuity of the integrand, per-slice `C¹`
in space, joint continuity of the spatial `fderiv`); its producer for `F = Feps` along the limit
family is LEAF-D2 `regData_of_xball` (`EpsE4Thr/RegDataOfXBall.lean`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **OPEN LEAF-D: `RegFromVolterra`, corrected** (TRUE): the joint `C¹` of a Volterra curve needs
of the right-hand side only *joint continuity* on the slab and a *jointly continuous spatial
derivative* — not `C¹` in the fake time. -/
theorem regFromVolterra' {F : Fn → Fn} {h₀ : Fn} {δ : ℝ} (hδ : 0 < δ)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Ioo 0 (Real.pi / 2) → τ ∈ Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) s) z θ)
    (hAc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2) p.1 p.2.1)
      (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ))
    (hAy : ∀ σ ∈ Icc 0 δ, ContDiffOn ℝ 1 (Function.uncurry
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ))) Work.FTS.EllipticEst.Q0)
    (hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2))) (p.1, p.2.1))
      (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ) :=
  -- proof by the delegated twin `EpsE4Thr.Leaves.regFromVolterra` (same statement, proved in a
  -- separate namespace; see `NOTES_EpsE4Thr_session25.md` §3)
  Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra hδ hsm0 hvol hAc hAy hB

/-- the weaker regularity data of the right-hand side along the limit curve (the three hypotheses
of `regFromVolterra'`). -/
def RegDataD (F : Fn → Fn) (h₀ : Fn) (δ : ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2) p.1 p.2.1)
    (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ) ∧
  (∀ σ ∈ Icc 0 δ, ContDiffOn ℝ 1 (Function.uncurry
      (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ))) Work.FTS.EllipticEst.Q0) ∧
  ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderiv ℝ (Function.uncurry
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2))) (p.1, p.2.1))
    (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ)

/-- `regFromVolterra'` in bundled form (PROVED from LEAF-D). -/
theorem regFromVolterra'_of_regData {F : Fn → Fn} {h₀ : Fn} {δ : ℝ} (hδ : 0 < δ)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Ioo 0 (Real.pi / 2) → τ ∈ Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) s) z θ)
    (hD : RegDataD F h₀ δ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Ioo 0 (Real.pi / 2) ×ˢ Icc 0 δ) :=
  regFromVolterra' hδ hsm0 hvol hD.1 hD.2.1 hD.2.2

end Work.FTS.StrongEps.EpsE4Thr.E4R5
