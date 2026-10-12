import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseRowsFS.LatRiemann.Geom
import Submission.Work.BoseRowsFS.LatRiemann.radialDecay2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.hboxSumMajorantLe`

The radial weight `p ↦ ((1+‖p‖)²‖p‖²)⁻¹` integrated over any finite family of
half-open lattice cells `hbox h m` (`m ∈ ℤ³`, `h > 0`) is bounded by its total
integral over `ℝ³`, which is at most `4π`:

    `∑_{m ∈ Kr} ∫_{hbox h m} ((1+‖p‖)²‖p‖²)⁻¹ dp ≤ 4π`.

The reason is purely measure-theoretic: the cells `hbox h m` are pairwise
*disjoint* subsets of `ℝ³` (`Work.BoseRowsFS.LatRiemann.disjoint_hbox`), hence
the sum of the integrals over a finite subfamily is the integral over their
union, which is at most the integral over all of `ℝ³`.  The latter is `4π` by
polar coordinates (`Submission.BoseGases.integral_fun_norm_r3`, packaged as
`Work.BoseRowsFS.LatRiemann.radialDecay2` at threshold `L = 0`) together with
`∫_0^∞ (1+r)^{-2} dr = 1`.

No hypothesis on `Kr` is needed beyond finiteness: even a cell containing the
origin contributes a *finite* amount, because `‖p‖⁻²` is integrable in
dimension three.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseRowsFS.LatRiemann

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The total-weight bound: for a nonnegative integrable weight `f` on `ℝ³`, the sum
of its integrals over any finite family of half-open lattice cells is at most its
integral over all of `ℝ³`.  This is just the disjointness of the cells. -/
lemma sum_hbox_le_integral {f : ℝ³ → ℝ} {h : ℝ} (hh : 0 < h) (Kr : Finset (Fin 3 → ℤ))
    (hfint : Integrable f volume) (hfnn : ∀ p, 0 ≤ f p) :
    ∑ m ∈ Kr, (∫ p in hbox h m, f p) ≤ ∫ p, f p := by
  classical
  have hmeas : ∀ m ∈ Kr, MeasurableSet (hbox h m) := fun m _ => measurableSet_hbox h m
  have hdisj : Set.Pairwise (↑Kr : Set (Fin 3 → ℤ))
      (fun m m' => Disjoint (hbox h m) (hbox h m')) :=
    fun m _ m' _ hne => disjoint_hbox hh hne
  have hcell : ∀ m ∈ Kr, IntegrableOn f (hbox h m) volume := fun m _ => hfint.integrableOn
  rw [← integral_biUnion_finset Kr hmeas hdisj hcell]
  exact setIntegral_le_integral hfint (Filter.Eventually.of_forall hfnn)

/-- The weight `p ↦ ((1+‖p‖)²‖p‖²)⁻¹` is integrable on `ℝ³`. -/
lemma integrable_majorant_inv :
    Integrable (fun p : ℝ³ => 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) volume := by
  have h := (radialDecay2 0 (le_refl (0 : ℝ))).1
  refine h.congr ?_
  filter_upwards with p
  rw [if_pos (norm_nonneg p)]

/-- `∫_{ℝ³} ((1+‖p‖)²‖p‖²)⁻¹ dp ≤ 4π`. -/
lemma integral_majorant_inv_le :
    (∫ p : ℝ³, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) ≤ 4 * Real.pi := by
  have h := (radialDecay2 0 (le_refl (0 : ℝ))).2
  have hcongr : (∫ p : ℝ³,
        (if (0 : ℝ) ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) else 0))
      = ∫ p : ℝ³, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards with p
    rw [if_pos (norm_nonneg p)]
  rw [hcongr] at h
  simpa using h

theorem hboxSumMajorantLe {h : ℝ} (hh : 0 < h) (Kr : Finset (Fin 3 → ℤ)) :
    ∑ m ∈ Kr, (∫ p in Work.BoseRowsFS.LatRiemann.hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
      ≤ 4 * Real.pi := by
  have hle : ∑ m ∈ Kr, (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
      ≤ ∫ p : ℝ³, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) :=
    sum_hbox_le_integral hh Kr integrable_majorant_inv
      (fun p => div_nonneg zero_le_one (mul_nonneg (sq_nonneg (1 + ‖p‖)) (sq_nonneg ‖p‖)))
  exact le_trans hle integral_majorant_inv_le

end Work.BoseRowsFS.LatRiemann
