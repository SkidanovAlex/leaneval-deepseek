import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseFixB1S.integral_sq_sub_coordMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.aQ_aP_sq_le`

The pair `aQ ℓ j ∘ aP ℓ i` of centred-box slot operators is an `L²`-contraction on the
centred box:

    ∫_{abox n ℓ} (Qⱼ (Pᵢ Θ))² ≤ ∫_{abox n ℓ} Θ²        (Θ ∈ L²(abox n ℓ)),

where `Pᵢ Θ x = (1/ℓ³)∫_{y ∈ acube ℓ} Θ(x[i ↦ y])` is the corpus's condensate projection and
`Qᵢ = 1 − Pᵢ` its complement (`Submission.Q0Sector`).  Only `MemLp Θ 2` is assumed — the state is
*not* continuous, which is what makes this the `L²`-twin of the corpus's `Continuous`-state chain
(`Submission.BoseGases.aP_sq_le`, …).

## Proof

The centred box carries the product measure `π = Measure.pi (fun _ : Fin n => ν)` with the
one-particle measure `ν = volume ↾ acube ℓ` (`Submission.BoseGases.restrict_abox_eq_pi`), and under
that identification

* `Pᵢ` **is** the coordinate mean `Work.BoseFixB1S.coordMean ν i` of the product measure
  (`aP_eq_coordMean` below: purely definitional, the normalisation `ℓ³ = (ν univ).toReal` being
  `Submission.BoseGases.restrict_acube_univ`);
* the coordinate mean contracts `L²`
  (`Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le`, the fibre Cauchy–Schwarz);
* the **variance (Pythagoras) identity** `Work.BoseFixB1S.integral_sq_sub_coordMean` with `c = 0`,
  `∫ f² = ∫ (f − Eⱼ f)² + ∫ (Eⱼ f)²`, exhibits `1 − Eⱼ` as the orthogonal projection onto the
  mean-free part, so the fluctuation contracts: `∫ (f − Eⱼ f)² ≤ ∫ f²`.

Applying the last two to `f = Pᵢ Θ = Eᵢ Θ` gives the two-step chain
`∫ (Qⱼ Pᵢ Θ)² ≤ ∫ (Pᵢ Θ)² ≤ ∫ Θ²`.

The hypothesis `i ≠ j` is not needed: both contractions hold for every pair of slots, and no
commutation of `Pᵢ` and `Qⱼ` is used.  (The frozen statement is kept untouched.)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseBoxFock.PCFU

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`aP ℓ i` is the coordinate mean for the centred-box product measure.**  The one-particle
measure of the box is `ν = volume ↾ acube ℓ` (`Submission.BoseGases.restrict_abox_eq_pi`), and
`aP ℓ i` averages the `i`-th slot with the normalisation `ℓ³ = (ν univ).toReal`
(`Submission.BoseGases.restrict_acube_univ`), which is `Work.BoseFixB1S.coordMean ν i`. -/
private lemma aP_eq_coordMean {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) (Θ : X N → ℝ) :
    aP ℓ i Θ
      = Work.BoseFixB1S.coordMean ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (acube ℓ)) i Θ := by
  funext x
  simp only [Submission.BoseGases.aP, Work.BoseFixB1S.coordMean]
  rw [restrict_acube_univ ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]

theorem aQ_aP_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Θ : Submission.BoseGases.X n → ℝ}
    (hΘ : MeasureTheory.MemLp Θ 2 ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Θ x) ^ 2 := by
  cases n with
  | zero => exact i.elim0
  | succ k =>
    -- ## The one-particle and the product measure
    set ν : Measure (EuclideanSpace ℝ (Fin 3)) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ) with hνdef
    haveI hνfin : IsFiniteMeasure ν := by
      rw [hνdef]
      exact ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
    have hV : (ν Set.univ).toReal = ℓ ^ 3 := by
      rw [hνdef, restrict_acube_univ ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
    have hνpos : 0 < (ν Set.univ).toReal := by rw [hV]; positivity
    have hμ : (volume : Measure (X (k + 1))).restrict (abox (k + 1) ℓ)
        = Measure.pi (fun _ : Fin (k + 1) => ν) := by
      rw [hνdef]
      exact restrict_abox_eq_pi (k + 1) ℓ
    haveI hπfin : IsFiniteMeasure (Measure.pi (fun _ : Fin (k + 1) => ν)) := inferInstance
    -- rewrite the goal into the product measure
    rw [hμ]
    -- ## The state data
    have hΘmem : MemLp Θ 2 (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hμ]; exact hΘ
    have hΘsm : AEStronglyMeasurable Θ (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      hΘmem.aestronglyMeasurable
    have hΘ2 : Integrable (fun x : X (k + 1) => (Θ x) ^ 2)
        (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      (memLp_two_iff_integrable_sq hΘsm).mp hΘmem
    -- ## `Pᵢ` is the coordinate mean and contracts `L²`
    have haP : aP ℓ i Θ = Work.BoseFixB1S.coordMean ν i Θ := by
      rw [hνdef]
      exact aP_eq_coordMean hℓ i Θ
    have hPac := Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le ν hνpos i hΘsm hΘ2
    have hPsq : Integrable (fun x => (aP ℓ i Θ x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [haP]
      exact hPac.1
    have hP : (∫ x, (aP ℓ i Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        ≤ ∫ x, (Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [haP]
      exact hPac.2
    -- ## `Qⱼ` is a contraction: Pythagoras for the coordinate mean applied to `Pᵢ Θ`
    have hfsm : AEStronglyMeasurable (aP ℓ i Θ) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [haP]
      exact (Work.BoseFixB1S.aestronglyMeasurable_pi_coordMean ν i hΘsm).const_mul _
    have hfmem : MemLp (aP ℓ i Θ) 2 (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      (memLp_two_iff_integrable_sq hfsm).mpr hPsq
    have hf1 : Integrable (aP ℓ i Θ) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      hfmem.integrable (by norm_num)
    have hid := Work.BoseFixB1S.integral_sq_sub_coordMean ν hνpos j
      (f := aP ℓ i Θ) hfsm hf1 hPsq 0
    have haPj : aP ℓ j (aP ℓ i Θ) = Work.BoseFixB1S.coordMean ν j (aP ℓ i Θ) := by
      rw [hνdef]
      exact aP_eq_coordMean hℓ j (aP ℓ i Θ)
    have hsq : (∫ x, (aP ℓ i Θ x - 0) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ x, (aP ℓ i Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hsq' : (∫ x, (Work.BoseFixB1S.coordMean ν j (aP ℓ i Θ) x - 0) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ x, (Work.BoseFixB1S.coordMean ν j (aP ℓ i Θ) x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hnonneg : 0 ≤ ∫ x, (Work.BoseFixB1S.coordMean ν j (aP ℓ i Θ) x) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := integral_nonneg (fun x => sq_nonneg _)
    have hQ : (∫ x, (aP ℓ i Θ x - aP ℓ j (aP ℓ i Θ) x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        ≤ ∫ x, (aP ℓ i Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [haPj]
      rw [hsq, hsq'] at hid
      linarith [hid, hnonneg]
    -- ## Assembly
    calc (∫ x, (aQ ℓ j (aP ℓ i Θ) x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ x, (aP ℓ i Θ x - aP ℓ j (aP ℓ i Θ) x) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := rfl
      _ ≤ ∫ x, (aP ℓ i Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := hQ
      _ ≤ ∫ x, (Θ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := hP

end Work.BoseBoxFock.PCFU
