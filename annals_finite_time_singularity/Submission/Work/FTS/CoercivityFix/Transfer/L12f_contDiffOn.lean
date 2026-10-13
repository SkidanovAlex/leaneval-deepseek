/-
# `L₁₂(g) ∈ C³((0,∞))` in the *localised* class (`SmoothQuad` + `ℋ⁴`)

The fundamental-model operator `L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds` is `C^∞` on
`(0,∞)` for a datum which is analytic on a neighbourhood of the closed quadrant
(`Work.Coercivity.L12f_contDiffOn_infty`).  The localised data of the route
(`Work.FTS.LocData.SmoothQuad`, genuine `C^∞` on the *open* quadrant plus
`Work.Spaces.HkMem α 4 g`) are **not** of that kind — a cut-off is never analytic — and there
the `θ`-integral defining the density `L12dens g s = ∫_θ K(θ)g(s,θ)/s dθ` is not a priori
differentiable in `s` (differentiating under the integral sign needs domination at
`θ = 0, π/2`, which `SmoothQuad` does not supply).  What *is* available is the localised
`z`-calculus of `Work.FTS.H2.QangDiff`: the angular moments

  `Qang g j z = ∫_θ K(θ) · (D_z^j g)(z,θ) dθ`

are continuous on `(0,∞)` for `j ≤ 3` and differentiable (with derivative
`Qang g (j+1) z / z`) for `j ≤ 2`, the proof integrating the slice FTC in `z` against `K`
and using the fourth `D_z`-slot of `HkMem α 4 g` for the Fubini step.  Hence

* `L12dens g = Qang g 0 / z` is `C²` on `(0,∞)` (`Qang g 0` is `C²`, because `Qang g 1` is
  `C¹`, because `Qang g 2 / z` is continuous);
* `L₁₂(g)` — the tail integral of `L12dens g`, integrable on `(0,∞)` by
  `Work.FTS.H2.L12densIntegrable` — has derivative `−L12dens g` at every `z > 0`
  (`Work.FM.hasDerivAt_L12`, whose two hypotheses are exactly that tail-integrability and the
  continuity of the density), so it is `C³` on the open half-line.

All constants being existential, no smallness of `α` is used beyond the standing
`0 < α ≤ 1` of the localised chapter (which `QangDiff` needs).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

theorem L12f_contDiffOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ContDiffOn ℝ 3 (Work.Coercivity.L12f g) (Set.Ioi 0) := by
  obtain ⟨hQderiv, hQcont⟩ := Work.FTS.H2.QangDiff α g hα hα1 hsm hmem
  -- the density is the `0`-th angular moment divided by `z`
  have hdens : Work.Elliptic.L12dens g = fun z => Work.Elliptic.Qang g 0 z / z :=
    funext (Work.Elliptic.L12dens_eq_Qang_div g)
  have hcontQ1 : ContinuousOn (fun z => Work.Elliptic.Qang g 1 z / z) (Set.Ioi 0) :=
    (hQcont 1 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  have hcontQ2 : ContinuousOn (fun z => Work.Elliptic.Qang g 2 z / z) (Set.Ioi 0) :=
    (hQcont 2 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  have hdens_cont : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    rw [hdens]
    exact (hQcont 0 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  -- `L₁₂(g)` is the tail integral of `L12dens g`, hence has derivative `−L12dens g`
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Coercivity.L12f g) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi (z / 2)) :=
      (Work.FTS.H2.L12densIntegrable α g hα hα1 hsm hmem).mono_set
        (Set.Ioi_subset_Ioi (by linarith))
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z :=
      hdens_cont.continuousAt (isOpen_Ioi.mem_nhds hz)
    exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := g) (a := z / 2) (ρ := z)
      hint hcont (by linarith)
  -- `Qang g 1` and `Qang g 0` are `C¹` on `(0,∞)`
  have hCd1Q1 : ContDiffOn ℝ 1 (Work.Elliptic.Qang g 1) (Set.Ioi 0) := by
    rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
    refine ⟨fun z hz => (hQderiv 1 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine hcontQ2.congr (fun z hz => ?_)
    rw [derivWithin_of_isOpen isOpen_Ioi hz, (hQderiv 1 (by norm_num) z hz).deriv]
  have hCd1Q0 : ContDiffOn ℝ 1 (Work.Elliptic.Qang g 0) (Set.Ioi 0) := by
    rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
    refine ⟨fun z hz => (hQderiv 0 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine hcontQ1.congr (fun z hz => ?_)
    rw [derivWithin_of_isOpen isOpen_Ioi hz, (hQderiv 0 (by norm_num) z hz).deriv]
  -- `Qang g 0` is `C²`, hence the density is `C²`
  have hCd2Q0 : ContDiffOn ℝ 2 (Work.Elliptic.Qang g 0) (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).mpr
      ⟨fun z hz => (hQderiv 0 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · refine (hCd1Q1.div contDiffOn_id (fun z hz => ne_of_gt hz)).congr (fun z hz => ?_)
      exact (hQderiv 0 (by norm_num) z hz).deriv
  have hCd2dens : ContDiffOn ℝ 2 (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    rw [hdens]
    exact hCd2Q0.div contDiffOn_id (fun z hz => ne_of_gt hz)
  -- assemble: `deriv L₁₂(g) = −L12dens g` is `C²`
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 2) isOpen_Ioi).mpr ⟨?_, ?_, ?_⟩
  · exact fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  · intro h; exact absurd h (by simp)
  · refine hCd2dens.neg.congr (fun z hz => ?_)
    exact (hderiv z hz).deriv

end Work.FTS.CoercivityFix.Transfer
