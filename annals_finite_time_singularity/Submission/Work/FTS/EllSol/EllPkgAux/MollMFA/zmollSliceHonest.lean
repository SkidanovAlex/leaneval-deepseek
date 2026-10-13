/-
# `zmollSliceHonest` — the mixed slice of the doubly-mollified datum is honest

For the doubly-mollified datum `Φ = zmoll G δ ε` (`K5c.MollDefs`) the hypothesis
`Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε` says that `Φ` is `C^n` on the open half strip
`(0,∞) × (-1, π/2+1)` for *every* `n : ℕ`.  In particular the mixed second partial
`∂_z∂_θΦ` is continuous there, hence — at a fixed `z > 0`, on the compact interval
`Iθ = [0, π/2] ⊂ (-1, π/2+1)` — bounded.  The weight `thEta θ = sin(2θ)^{-η}` is integrable
on `Iθ` (because `η = 99/100 < 1`), so the product `(D_z∂_θΦ)² · thEta` is integrable on
`Iθ`: bounded-continuous times integrable on a compact set.

The only analytic input is the *finite-order* chain rule "a partial derivative of a `C^n`
function is `C^{n-1}`", which the workspace has only for the analytic order `⊤`
(`Work.Spaces.contDiffOn_uncurry_pz`, `..._pth`); the two helper lemmas below supply the
finite-order versions actually needed.

Statement and name are exactly those of the requested lemma.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollMFA

set_option autoImplicit false

/-! ## The finite-order chain rule for the curried partials

`Work.Spaces.contDiffOn_uncurry_pz`/`_pth` state that `pz`/`pth` preserve `C^∞`-smoothness
*for the analytic order* `⊤`.  The version used below only has the *finite* orders of the
mollification hypothesis; the proofs are the same, with `ContDiffOn.fderivWithin` at the
finite order. -/

/-- `∂_z` lowers the smoothness order by one: the `z`-partial of a `C^{n+1}` function is
`C^n`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {n : ℕ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin hV.uniqueDiffOn (m := (n : WithTop ℕ∞)) (by simp)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers the smoothness order by one: the `θ`-partial of a `C^{n+1}` function is
`C^n`. -/
theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {n : ℕ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin hV.uniqueDiffOn (m := (n : WithTop ℕ∞)) (by simp)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The target -/

theorem zmollSliceHonest (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hstrip : Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  intro z hz
  set F : ℝ → ℝ → ℝ := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε with hF
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry F)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hstrip.1 2
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth F))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    contDiffOn_uncurry_pth_succ hU h2
  -- the mixed partial `∂_z∂_θF` is continuous on the half strip, hence on `{z} × Iθ`
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pz (Work.Spaces.pth F) z θ)
      Work.Spaces.Iθ := by
    have hinner : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth F)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      (contDiffOn_uncurry_pz_succ hU h1).continuousOn
    have hmap : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
      intro θ hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      show (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)
      rw [Set.mem_prod]
      exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    exact (hinner.comp hmap hmaps).congr (fun θ _ => rfl)
  have hcsq : ContinuousOn
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth F) z θ) ^ 2) Work.Spaces.Iθ :=
    (continuousOn_const.mul hcont).pow 2
  -- bounded continuous factor times the integrable weight `thEta` on the compact `Iθ`
  have hint : IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (z * Work.Spaces.pz (Work.Spaces.pth F) z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1 |>.mul_continuousOn hcsq
      (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  refine hint.congr_fun ?_ (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
  intro θ hθ
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS.EllSol.EllPkgAux.MollMFA
