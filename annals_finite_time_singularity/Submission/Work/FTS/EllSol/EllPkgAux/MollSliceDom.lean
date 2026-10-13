/-
# `Work.FTS.EllSol.EllPkgAux.MollSliceDom` — the slice domination, second (independent) proof

The dominating function `MG G w = |G w (π/4)| + |∂_θG w (π/4)| + √(E2sl G w)` controls the
whole angular slice `G w ·` on `(0,π/2)`.  This is an *independent* proof of the same statement
as `Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom`, by the second-order Taylor formula
(`MollSmooth.slice_taylor_two`) at the midpoint `π/4` plus the weighted Cauchy–Schwarz
(`Work.EllipticEst.Core.weightedCS`) for the angular weight `thEta`; the interval from `π/4` to
`τ` has length `≤ π/4`, which is exactly what makes the constant `(π/4)·√(π/4) ≤ 1` fit.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.EllipticEst.Core.thEtaFacts
import Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Geometric and integrability facts about the interval spanned by `π/4` and `τ` -/

/-- The endpoints `π/4` and `τ ∈ (0,π/2)` span an interval contained in `(0,π/2)`. -/
theorem Ioo_minmax_pi4_subset {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h1 : 0 < min (Real.pi / 4) τ :=
    lt_min (by linarith [Real.pi_pos]) hτ.1
  have h2 : max (Real.pi / 4) τ < Real.pi / 2 :=
    max_lt (by linarith [Real.pi_pos]) hτ.2
  exact fun x hx => ⟨lt_trans h1 hx.1, lt_trans hx.2 h2⟩

/-- The interval spanned by `π/4` and `τ` has length at most `π/4`. -/
theorem minmax_pi4_length {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    max (Real.pi / 4) τ - min (Real.pi / 4) τ ≤ Real.pi / 4 := by
  rcases le_total (Real.pi / 4) τ with h | h
  · rw [min_eq_left h, max_eq_right h]; linarith [hτ.2]
  · rw [min_eq_right h, max_eq_left h]; linarith [hτ.1]

/-- The constant `1` integrates to the length of the interval. -/
theorem setIntegral_one_minmax {τ : ℝ} :
    (∫ t in Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ), (1 : ℝ))
      = max (Real.pi / 4) τ - min (Real.pi / 4) τ := by
  have hle : min (Real.pi / 4) τ ≤ max (Real.pi / 4) τ := min_le_max
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]

/-- The reciprocal angular weight is integrable on the interval spanned by `π/4` and `τ`. -/
theorem integrableOn_thEta_inv_minmax {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Work.FTS.EllipticEst.thEta t)⁻¹)
      (Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ)) := by
  have hsub := Ioo_minmax_pi4_subset hτ
  exact (Work.EllipticEst.Core.integrableOn_sin_two_rpow_eta_Ioo _ _).congr_fun
    (fun t ht => (Work.EllipticEst.Core.thEta_inv_eq_sin_two_rpow (hsub ht)).symm)
    measurableSet_Ioo

/-- The reciprocal weight integrates to at most the length `π/4` of the interval. -/
theorem thEta_inv_integral_minmax_le {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ t in Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ),
        (Work.FTS.EllipticEst.thEta t)⁻¹)
      ≤ Real.pi / 4 := by
  obtain ⟨hpos, hone, hinv, hcont⟩ := Work.EllipticEst.Core.thEtaFacts
  have hsub := Ioo_minmax_pi4_subset hτ
  set J := Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ) with hJ
  have hle : ∀ t ∈ J, (Work.FTS.EllipticEst.thEta t)⁻¹ ≤ (1 : ℝ) :=
    fun t ht => inv_le_one_of_one_le₀ (hone t (hsub ht))
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) J :=
    MeasureTheory.integrableOn_const (by
      rw [hJ, Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  refine le_trans (MeasureTheory.setIntegral_mono_on (s := J)
    (f := fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) (g := fun _ => (1 : ℝ))
    (integrableOn_thEta_inv_minmax hτ) hconst measurableSet_Ioo hle) ?_
  rw [setIntegral_one_minmax]
  exact minmax_pi4_length hτ

/-- **Weighted Cauchy–Schwarz on the interval spanned by `π/4` and `τ`.** -/
theorem cs_minmax {g : ℝ → ℝ} {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hgc : ContinuousOn g (Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ)))
    (hg2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (g t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ)))
    (hgi : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.FTS.EllipticEst.thEta t)⁻¹)
      (Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ))) :
    (∫ t in Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ), g t) ^ 2
      ≤ (∫ t in Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ),
          (g t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        * (∫ t in Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ),
          (Work.FTS.EllipticEst.thEta t)⁻¹) := by
  obtain ⟨hpos, hone, hinv, hcont⟩ := Work.EllipticEst.Core.thEtaFacts
  exact Work.EllipticEst.Core.weightedCS
    (s := Set.Ioo (min (Real.pi / 4) τ) (max (Real.pi / 4) τ)) measurableSet_Ioo
    (fun t ht => hpos t (Ioo_minmax_pi4_subset hτ ht))
    (hcont.mono (Ioo_minmax_pi4_subset hτ)) hgc hg2 hgi

/-! ## Note

The full slice-domination statement (`|G w τ| ≤ MG G w`) is *proved* in
`Submission/Work/FTS/EllSol/EllPkgAux/MollSmooth/sliceDom.lean`
(`Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom`, which `mollAdm` imports).  The lemmas above
are the ingredients of a second, independent proof of the same statement (via the weighted
Cauchy–Schwarz `cs_minmax` and the interval-length bound `thEta_inv_integral_minmax_le`); they
are kept because they are reusable, but they are not (yet) assembled into that second proof.
-/

end Work.FTS.EllSol.EllPkgAux
