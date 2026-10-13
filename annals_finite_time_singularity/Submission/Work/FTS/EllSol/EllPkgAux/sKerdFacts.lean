/-
# `Work.FTS.EllSol.EllPkgAux.sKerdFacts`

The elementary properties of the *derivative kernel* `sKerd 1 = deriv (sKer 1)` of the
normalised smooth mollifying bump `sKer 1` (`Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs`):
continuity, compact support, vanishing for `|u| ≥ 1`, the two moment identities
`∫ sKerd 1 = 0` and `∫ u * sKerd 1 u = -1`, integrability of `sKerd 1` against `1`, `u` and
`u²`, and the parabolic scaling `sKerd t u = t⁻² sKerd 1 (u / t)`.

All the analytic content lives in `Submission.Work.FTS.EllSol.EllPkgAux.mollKerdMoments`
(the `mk_*` lemmas there are stated for a general scale `ε > 0`); this file specialises them
to `ε = 1`, adds continuity of the derivative, and supplies the two boundary cases of the
pointwise vanishing (with `IsLocalMin.deriv_eq_zero` when `|u| = 1`, and by local constancy
when `|u| > 1`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollKerdMoments

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c

/-- `sKerd 1` vanishes *strictly* beyond the support: at a point `u` with `|u| > 1` the
function `sKer 1` is identically zero on a neighbourhood, hence so is its derivative. -/
private theorem skerd_eq_zero_of_one_lt_abs {u : ℝ} (hu : 1 < |u|) : sKerd 1 u = 0 := by
  have hzero : ∀ x : ℝ, 1 ≤ |x| → sKer 1 x = 0 := fun x hx =>
    sKer_eq_zero_of_le_abs (ε := 1) one_pos hx
  have hev : sKer 1 =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    rcases (lt_abs.mp hu) with h | h
    · refine ⟨Set.Ioi 1, isOpen_Ioi.mem_nhds (show u ∈ Set.Ioi 1 from h), ?_⟩
      intro x hx
      have hx' : (1 : ℝ) < x := hx
      exact hzero x (by rw [abs_of_pos (by linarith)]; linarith)
    · refine ⟨Set.Iio (-1), isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith), ?_⟩
      intro x hx
      have hx' : x < (-1 : ℝ) := hx
      exact hzero x (by rw [abs_of_neg (by linarith)]; linarith)
  show deriv (sKer 1) u = 0
  rw [hev.deriv_eq, deriv_const]

/-- At the two endpoints `u = ±1` of the support the kernel `sKer 1` is nonnegative with a
zero, so `u` is a local minimum and the derivative vanishes there. -/
private theorem skerd_eq_zero_of_abs_eq_one {u : ℝ} (hu : |u| = 1) : sKerd 1 u = 0 := by
  have hzu : sKer 1 u = 0 := sKer_eq_zero_of_le_abs (ε := 1) one_pos (le_of_eq hu.symm)
  have hmin : IsLocalMin (sKer 1) u := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hzu]
    exact sKer_nonneg one_pos x
  show deriv (sKer 1) u = 0
  exact hmin.deriv_eq_zero

theorem sKerdFacts :
    Continuous (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    (∀ u : ℝ, 1 ≤ |u| → Work.FTS.EllSol.EllPkgAux.sKerd 1 u = 0) ∧
    (∫ u : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd 1 u = 0) ∧
    (∫ u : ℝ, u * Work.FTS.EllSol.EllPkgAux.sKerd 1 u = -1) ∧
    MeasureTheory.Integrable (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    MeasureTheory.Integrable (fun u : ℝ => u * Work.FTS.EllSol.EllPkgAux.sKerd 1 u) ∧
    MeasureTheory.Integrable (fun u : ℝ => u ^ 2 * Work.FTS.EllSol.EllPkgAux.sKerd 1 u) ∧
    (∀ t : ℝ, 0 < t → ∀ u : ℝ,
            Work.FTS.EllSol.EllPkgAux.sKerd t u = (1 / t ^ 2) * Work.FTS.EllSol.EllPkgAux.sKerd 1 (u / t)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity: `sKer 1` is `C^∞`, so its derivative is continuous
    exact (contDiff_sKer (1 : ℝ)).continuous_deriv_one
  · -- compact support: the support of the derivative is contained in that of `sKer 1`
    simpa [sKerd] using (mk_hasCompactSupport_sKer (ε := 1) one_pos).deriv
  · -- vanishing for `|u| ≥ 1`
    intro u hu
    rcases lt_or_eq_of_le hu with h | h
    · exact skerd_eq_zero_of_one_lt_abs h
    · exact skerd_eq_zero_of_abs_eq_one h.symm
  · -- `∫ sKerd 1 = 0`
    simpa [sKerd] using mk_integral_sKerd_eq_zero (ε := 1) one_pos
  · -- `∫ u * sKerd 1 u = -1`
    simpa [sKerd] using mk_integral_id_sKerd (ε := 1) one_pos
  · -- integrability of `sKerd 1`
    simpa [sKerd] using mk_integrable_deriv_sKer (ε := 1) one_pos
  · -- integrability of `u * sKerd 1 u`
    simpa [sKerd] using mk_integrable_id_deriv_sKer (ε := 1) one_pos
  · -- integrability of `u ^ 2 * sKerd 1 u`
    simpa [sKerd] using mk_integrable_sq_deriv_sKer (ε := 1) one_pos
  · -- the parabolic scaling of the derivative kernel
    intro t ht u
    show deriv (sKer t) u = (1 / t ^ 2) * deriv (sKer 1) (u / t)
    rw [mk_deriv_sKerd_scale]
    have h2 : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
    field_simp

end Work.FTS.EllSol.EllPkgAux
