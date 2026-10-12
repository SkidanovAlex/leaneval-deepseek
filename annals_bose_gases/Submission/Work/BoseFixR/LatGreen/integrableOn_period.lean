import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.CellDefs
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open scoped BigOperators
open MeasureTheory

/-! The ℓ-periodisation `P x = Σ'_n W (x - lat ℓ n)` of an integrable charge is integrable on the cell,
under the pointwise summability hypothesis.  Route: `P` is `AEMeasurable` as a pointwise `tsum` of measurable
functions (`AEMeasurable.tsum`); it is dominated pointwise by `Q x = Σ'_n ‖W (x - lat ℓ n)‖ₑ` (real-valued:
`‖P x‖ ≤ Σ'_n ‖W (x - lat ℓ n)‖`, from `Summable.norm` + `norm_tsum_le_tsum_norm`), whose cell-lintegral is
finite by `MeasureTheory.lintegral_tsum` (valid on the restricted measure) plus the fundamental-domain identity
`MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum` for `Work.BoseFixR.isAddFundamentalDomain_cellI`
(together with `cell = cellI` a.e., `volume_cell_sdiff_cellI`, and translation invariance of Lebesgue measure);
then `MeasureTheory.Integrable.mono'` / `HasFiniteIntegral` finishes.  Note that `lintegral_tsum` over the
*whole* space gives `⊤` (infinitely many translates each carry the same mass); the restriction to the cell
with the disjoint translates is exactly what makes it finite. -/

/-- The ambient Euclidean space, as a local shorthand for readability. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Negation of the lattice labels, as an equivalence of `ℤ³`. -/
def negLab : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun n := -n
  invFun n := -n
  left_inv n := neg_neg n
  right_inv n := neg_neg n

lemma negLab_apply (n : Fin 3 → ℤ) : negLab n = -n := rfl

/-- Negation of the lattice vectors. -/
lemma lat_neg (ℓ : ℝ) (n : Fin 3 → ℤ) :
    Work.BoseFixR.lat ℓ (-n) = -Work.BoseFixR.lat ℓ n := by
  have h := map_neg (Work.BoseFixR.latHom ℓ) n
  simpa using h

/-- **The lattice-sum identity for the `ENNReal`-valued norm.**  Integrating `ofReal ‖W ·‖` over the whole
space equals the sum, over the lattice, of the integrals of its translates against one period cell.  This is
the fundamental-domain identity `IsAddFundamentalDomain.lintegral_eq_tsum''` for `cellI ℓ`, reindexed by
`latEquiv` and then by the negation `n ↦ -n` of the lattice labels. -/
theorem lintegral_period_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∫⁻ y, ENNReal.ofReal ‖W y‖
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖ := by
  have hplus : ∫⁻ y, ENNReal.ofReal ‖W y‖
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (x + Work.BoseFixR.lat ℓ n)‖ := by
    haveI : Countable (Work.BoseFixR.latHom ℓ).range :=
      Work.BoseFixR.countable_range_latHom (ne_of_gt hℓ)
    rw [(Work.BoseFixR.isAddFundamentalDomain_cellI hℓ).lintegral_eq_tsum''
        (fun y => ENNReal.ofReal ‖W y‖),
      ← (Work.BoseFixR.latEquiv (ne_of_gt hℓ)).tsum_eq
        (fun g : (Work.BoseFixR.latHom ℓ).range =>
          ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (g +ᵥ x)‖)]
    refine tsum_congr fun n => ?_
    congr 1 with x
    simp [Work.BoseFixR.latEquiv, add_comm]
  rw [hplus, ← negLab.tsum_eq
    (fun n : Fin 3 → ℤ =>
      ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (x + Work.BoseFixR.lat ℓ n)‖)]
  refine tsum_congr fun n => ?_
  rw [show (fun x : E3 => ENNReal.ofReal ‖W (x + Work.BoseFixR.lat ℓ (negLab n))‖)
      = (fun x : E3 => ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖) from by
    funext x
    simp only [negLab_apply n, lat_neg ℓ n, sub_eq_add_neg]]

/-- The pointwise domination of the periodisation by the periodised norm. -/
lemma enorm_period_le {ℓ : ℝ} {W : E3 → ℝ}
    (hper : ∀ x : E3, Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (x : E3) :
    ‖period W ℓ x‖ₑ
      ≤ ∑' n : Fin 3 → ℤ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖ := by
  have hsum : Summable fun n : Fin 3 → ℤ => ‖W (x - Work.BoseFixR.lat ℓ n)‖ := (hper x).norm
  calc ‖period W ℓ x‖ₑ
      = ENNReal.ofReal ‖period W ℓ x‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (∑' n : Fin 3 → ℤ, ‖W (x - Work.BoseFixR.lat ℓ n)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
    _ = ∑' n : Fin 3 → ℤ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hsum

theorem integrableOn_period {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n))) :
    MeasureTheory.IntegrableOn (Work.BoseFixR.LatGreen.period W ℓ)
      (Work.BoseFixR.cell ℓ) := by
  -- each summand is a.e. measurable on the half-open cell
  have hAEm : ∀ n : Fin 3 → ℤ,
      AEMeasurable (fun x : E3 => W (x - Work.BoseFixR.lat ℓ n))
        (volume.restrict (Work.BoseFixR.cellI ℓ)) := fun n =>
    ((hW.comp_sub_right (Work.BoseFixR.lat ℓ n)).aestronglyMeasurable.aemeasurable).restrict
  -- the periodisation is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (period W ℓ) (volume.restrict (Work.BoseFixR.cellI ℓ)) := by
    have h : AEMeasurable (period W ℓ) (volume.restrict (Work.BoseFixR.cellI ℓ)) :=
      AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
        (μ := volume.restrict (Work.BoseFixR.cellI ℓ))
        (f := fun n x => W (x - Work.BoseFixR.lat ℓ n)) hAEm
    exact h.aestronglyMeasurable
  -- finiteness of the whole-space lintegral of the norm
  have hWfin : ∫⁻ y, ENNReal.ofReal ‖W y‖ < ⊤ := by
    simpa only [MeasureTheory.HasFiniteIntegral, ← ofReal_norm] using hW.hasFiniteIntegral
  have htsum_fin :
      (∑' n : Fin 3 → ℤ,
        ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖) < ⊤ := by
    rw [← lintegral_period_eq hℓ W]
    exact hWfin
  -- the cell-lintegral of the dominating sum is finite
  have hmain : ∫⁻ x, ‖period W ℓ x‖ₑ ∂(volume.restrict (Work.BoseFixR.cellI ℓ))
      ≤ ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖ := by
    calc ∫⁻ x, ‖period W ℓ x‖ₑ ∂(volume.restrict (Work.BoseFixR.cellI ℓ))
        ≤ ∫⁻ x, (∑' n : Fin 3 → ℤ, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖)
            ∂(volume.restrict (Work.BoseFixR.cellI ℓ)) :=
          lintegral_mono_ae (Filter.Eventually.of_forall (fun x => enorm_period_le hper x))
      _ = ∑' n : Fin 3 → ℤ, ∫⁻ x, ENNReal.ofReal ‖W (x - Work.BoseFixR.lat ℓ n)‖
            ∂(volume.restrict (Work.BoseFixR.cellI ℓ)) :=
          lintegral_tsum (fun n => by
            have hf : AEMeasurable (fun x : E3 => W (x - Work.BoseFixR.lat ℓ n))
                (volume.restrict (Work.BoseFixR.cellI ℓ)) := hAEm n
            have hg : Measurable fun r : ℝ => ENNReal.ofReal ‖r‖ := by fun_prop
            exact hg.comp_aemeasurable hf)
  -- the periodisation is integrable on the half-open cell
  have hfin : HasFiniteIntegral (period W ℓ) (volume.restrict (Work.BoseFixR.cellI ℓ)) :=
    lt_of_le_of_lt hmain htsum_fin
  have hIntI : Integrable (period W ℓ) (volume.restrict (Work.BoseFixR.cellI ℓ)) :=
    ⟨hmeas, hfin⟩
  -- transfer from the half-open cell to the closed cell
  have hInt : Integrable (period W ℓ) (volume.restrict (Work.BoseFixR.cell ℓ)) := by
    rw [← Measure.restrict_congr_set (Work.BoseFixR.cellI_ae_eq_cell ℓ)]
    exact hIntI
  exact hInt

end Work.BoseFixR.LatGreen
