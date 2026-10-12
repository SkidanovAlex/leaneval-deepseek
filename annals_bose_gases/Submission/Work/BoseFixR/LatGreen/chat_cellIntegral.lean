import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseB7AK.W1low.chat_sub_le
import Submission.Work.BoseFixR.LatGreen.CellDefs
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-! Fourier-coefficient identity of the cell-Parseval reduction (piece of `Work.BoseFixR.LatGreen.CellParseval`):
the real Fourier kernel of an integrable charge equals the cell integral of its ℓ-periodisation against the
cosine of the lattice momentum.  Route: `chat W q = Re ∫_y e^{-i⟨q,y⟩}W y dy`; the tiling identity
`Work.BoseFixR.tiling_integral` (in `Submission.Work.BoseFixR.SamplingSqSumLeChiR0`) writes the ℝ³-integral
as the sum over `n` of the integrals over `cell ℓ` of `x ↦ e^{-i⟨q,x+lat ℓ n⟩}W(x+lat ℓ n)`, the phase
`e^{-i⟨q,lat ℓ n⟩} = 1` drops out (`Work.BoseFixR.exp_inner_kmomLab_lat`), the `tsum`/integral exchange is
`MeasureTheory.hasSum_integral_of_summable_integral_norm` (whose summability input is again `tiling_integral`,
applied to `|W|`), and `Re ∫_cell e^{-i⟨q,x⟩}P x dx = ∫_cell P x cos⟨q,x⟩dx` (`Complex.reCLM.integral_comp_comm`).
The same computation restricted to compactly supported `W` is `hcoeff` in `Submission.Work.BoseFixR.SamplingSqSumLeChiR0`. -/

open scoped Real BigOperators RealInnerProductSpace

-- `hper` is not needed for the identity as stated (the reindexing `n ↦ -n` is unconditional, and the
-- absolute summability used by the exchange comes from the tiling identity applied to `|W|`); keep the
-- binder for the interface, but do not let the linter complain.
set_option linter.unusedVariables false

/-- The cosine of a lattice momentum is invariant under the lattice `ℓℤ³`: the pairing
`⟨q, ℓn⟩` is a multiple of `2π`, so `cos⟨q, x + ℓn⟩ = cos⟨q,x⟩`. -/
lemma cos_inner_kmomLab_add_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (k : Work.BoseBoxFock.Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) (x + Work.BoseFixR.lat ℓ n))
      = Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x) := by
  rw [inner_add_right, Work.BoseFixR.inner_kmomLab_lat hℓ N k n,
    show 2 * Real.pi * ((∑ i, Work.BoseBoxFock.labVec N k i * n i : ℤ) : ℝ)
        = ((∑ i, Work.BoseBoxFock.labVec N k i * n i : ℤ) : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

/-- The periodisation sum is invariant under `n ↦ -n` (the lattice is symmetric). -/
lemma tsum_lat_add_eq_tsum_lat_sub (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ, W (x + Work.BoseFixR.lat ℓ n))
      = ∑' n : Fin 3 → ℤ, W (x - Work.BoseFixR.lat ℓ n) := by
  rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq (fun n => W (x - Work.BoseFixR.lat ℓ n))]
  refine tsum_congr fun n => ?_
  have hneg : Work.BoseFixR.lat ℓ ((Equiv.neg (Fin 3 → ℤ)) n) = -(Work.BoseFixR.lat ℓ n) := by
    simpa using (Work.BoseFixR.latHom ℓ).map_neg n
  rw [hneg, sub_neg_eq_add]

/-- **Absolute summability of the translated cell integrals.**  For an integrable `W`, the family
`n ↦ ∫_{cell ℓ} |W(x + ℓn)| dx` is summable: by the tiling identity its `tsum` is `∫|W|`, and all of its
terms are nonnegative. -/
lemma summable_setIntegral_abs_lat {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W) :
    Summable (fun n : Fin 3 → ℤ =>
      ∫ x in Work.BoseFixR.cell ℓ, |W (x + Work.BoseFixR.lat ℓ n)|) := by
  have htsum : (∑' n : Fin 3 → ℤ,
        ∫ x in Work.BoseFixR.cell ℓ, |W (x + Work.BoseFixR.lat ℓ n)|)
      = ∫ x : EuclideanSpace ℝ (Fin 3), |W x| :=
    (Work.BoseFixR.tiling_integral hℓ (fun x => |W x|) hW.abs).symm
  by_cases h0 : ∫ x : EuclideanSpace ℝ (Fin 3), |W x| = 0
  · have hz : ∀ n : Fin 3 → ℤ,
        ∫ x in Work.BoseFixR.cell ℓ, |W (x + Work.BoseFixR.lat ℓ n)| = 0 := by
      intro n
      refine le_antisymm ?_ (MeasureTheory.integral_nonneg fun x => abs_nonneg _)
      calc ∫ x in Work.BoseFixR.cell ℓ, |W (x + Work.BoseFixR.lat ℓ n)|
          ≤ ∫ x : EuclideanSpace ℝ (Fin 3), |W (x + Work.BoseFixR.lat ℓ n)| :=
            MeasureTheory.setIntegral_le_integral (hW.abs.comp_add_right (Work.BoseFixR.lat ℓ n))
              (Filter.Eventually.of_forall fun x => abs_nonneg _)
        _ = ∫ x : EuclideanSpace ℝ (Fin 3), |W x| :=
            MeasureTheory.integral_add_right_eq_self (fun x => |W x|) (Work.BoseFixR.lat ℓ n)
        _ = 0 := h0
    rw [show (fun n : Fin 3 → ℤ =>
          ∫ x in Work.BoseFixR.cell ℓ, |W (x + Work.BoseFixR.lat ℓ n)|)
        = fun _ => (0 : ℝ) from funext hz]
    exact summable_zero
  · by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at htsum
    exact h0 htsum.symm

theorem chat_cellIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (k : Work.BoseBoxFock.Lab N) :
    Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)
      = ∫ x in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period W ℓ x
            * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x) := by
  set q : EuclideanSpace ℝ (Fin 3) := Work.BoseBoxFock.kmomLab ℓ N k with hq
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hW q]
  -- the cosine is measurable and bounded by one
  have hcosbdd : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Real.cos (inner ℝ q y)‖ ≤ (1 : ℝ) := by
    intro y
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hfint : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      W y * Real.cos (inner ℝ q y)) :=
    hW.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall hcosbdd)
  -- the tiling identity turns the `ℝ³` integral into a lattice sum of cell integrals
  rw [Work.BoseFixR.tiling_integral hℓ (fun y => W y * Real.cos (inner ℝ q y)) hfint]
  -- the phase drops out, so each cell integrand only sees `cos⟨q,x⟩`
  have hstep2 : (∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q (x + Work.BoseFixR.lat ℓ n)))
      = ∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x) :=
    tsum_congr fun n => by
      refine MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet (Work.BoseFixR.cell ℓ) from Work.BoseFixR.measurableSet_boxL ℓ)
        (fun x _ => ?_)
      rw [hq, cos_inner_kmomLab_add_lat (ne_of_gt hℓ) N k x n]
  rw [hstep2]
  -- exchange the lattice sum and the cell integral
  have hFint : ∀ n : Fin 3 → ℤ, MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) := by
    intro n
    have h := ((hW.comp_add_right (Work.BoseFixR.lat ℓ n)).integrableOn
      (s := Work.BoseFixR.cell ℓ)).mul_bdd
      (c := 1) (by fun_prop) (Filter.Eventually.of_forall hcosbdd)
    simpa only using h
  have hB : Summable (fun n : Fin 3 → ℤ =>
      ∫ x : EuclideanSpace ℝ (Fin 3),
        ‖W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x)‖
        ∂(MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := by
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (summable_setIntegral_abs_lat hℓ hW)
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      ((hW.abs.comp_add_right (Work.BoseFixR.lat ℓ n)).integrableOn
        (s := Work.BoseFixR.cell ℓ)) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hexch := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) hFint hB
  have hstep3 : (∑' n : Fin 3 → ℤ, ∫ x in Work.BoseFixR.cell ℓ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      = ∫ x in Work.BoseFixR.cell ℓ, ∑' n : Fin 3 → ℤ,
        W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x) :=
    hexch.tsum_eq
  rw [hstep3]
  -- identify the pointwise `tsum` with the periodisation (reindexing `n ↦ -n`)
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show (∑' n : Fin 3 → ℤ, W (x + Work.BoseFixR.lat ℓ n) * Real.cos (inner ℝ q x))
      = Work.BoseFixR.LatGreen.period W ℓ x * Real.cos (inner ℝ q x)
  rw [tsum_mul_right, Work.BoseFixR.LatGreen.period]
  congr 1
  exact tsum_lat_add_eq_tsum_lat_sub ℓ W x

end Work.BoseFixR.LatGreen
