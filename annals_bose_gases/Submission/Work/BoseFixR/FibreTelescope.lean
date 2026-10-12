import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.KinSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FibreTelescope` — the fibre telescoping of `Φ²` and of the excited count

The two-block splitting of the state space (`Work.BoseFixR.blockME`,
`Submission/Work/BoseFixR/KinBlockDefs.lean`) turns the box `abox (k+j) ℓ` into the product
`abox k ℓ × abox j ℓ`, and the two block fibres `bfL Φ y` (`z ↦ Φ (z,y)`) / `bfR Φ z`
(`y ↦ Φ (z,y)`) of a `(k+j)`-particle state `Φ` into states of `k` resp. `j` particles.

This module proves the telescoping identities along that splitting:

* the mass telescope `∫_{abox k}∫_{abox j} Φ² = ∫_{abox (k+j)} Φ²` in both orders;
* the **excited-count telescope**

      `∫_{abox j ℓ} cnPlus ℓ (bfL Φ y) + ∫_{abox k ℓ} cnPlus ℓ (bfR Φ z) = cnPlus ℓ Φ`,

  i.e. the total excited-particle count `n₊ = Σᵢ ∫(QᵢΦ)²` of the glued state is the sum of the
  excited counts of the two block fibres: the `Fin k`-sum of the first fibre covers the slots
  `0,…,k−1` of the glued configuration and the `Fin j`-sum of the second fibre the slots
  `k,…,k+j−1` (the projection `Q` of a glued configuration in a slot of a block is the block
  projection of the fibre, `aQ_blockME_castAdd`/`aQ_blockME_natAdd`).

The route is Fubini along `blockME` (`Work.BoseFixR.abox_blockME_fubini` and its mirror
`abox_blockME_fubini_symm` from `KinSplit`), which needs `IntegrableOn (Φ)²` resp.
`IntegrableOn (aQ ℓ i Φ)²` on the box (both from continuity on the compact box), together with
the sum/integral exchange `MeasureTheory.integral_finsetSum`, whose integrability input on the
outer box comes from the Fubini measurability lemma `Integrable.integral_prod_right`
(recorded here as `integrableOn_inner_integral` / `integrableOn_inner_integral'`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The pointwise slot-fibre identities

The projection `Qᵢ` of the glued configuration `blockME k j (z,y)` in a slot of the first block
is the first-block projection of the fibre `bfL Φ y` (and dually for the second block and
`bfR Φ z`).  Both are pure statement bookkeeping: the mean over `acube ℓ` of the glued
configuration in the slot `castAdd j i` resp. `natAdd k i` is the mean over `acube ℓ` of the
fibre in the slot `i`, because `Function.update` commutes with `blockME`. -/

/-- **The slot projection of a glued configuration in a first-block slot is the first-block
projection of the fibre.** -/
lemma aQ_blockME_castAdd {k j : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X (k + j) → ℝ}
    (i : Fin k) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ (blockME k j (z, y))
      = Submission.BoseGases.aQ ℓ i (bfL Φ y) z := by
  unfold Submission.BoseGases.aQ Submission.BoseGases.aP
  simp only [bfL_eq_blockME, update_blockME_castAdd]

/-- **The slot projection of a glued configuration in a second-block slot is the second-block
projection of the fibre.** -/
lemma aQ_blockME_natAdd {k j : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X (k + j) → ℝ}
    (i : Fin j) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ (blockME k j (z, y))
      = Submission.BoseGases.aQ ℓ i (bfR Φ z) y := by
  unfold Submission.BoseGases.aQ Submission.BoseGases.aP
  simp only [bfR_eq_blockME, update_blockME_natAdd]

/-! ## 2. Fubini on the product box

If a function of a pair of configurations is integrable on the product of the two boxes, then
the inner integral over the first (resp. second) box is integrable over the other box.  This is
`Integrable.integral_prod_right` / `Integrable.integral_prod_left` after rewriting the restricted
product measure as the product of the restricted measures (`Measure.prod_restrict`). -/

/-- **Fubini: integrating out the first block is an integrable operation on the second box.** -/
lemma integrableOn_inner_integral {k j : ℕ} {ℓ : ℝ}
    {G : Submission.BoseGases.X k → Submission.BoseGases.X j → ℝ}
    (hG : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j => G p.1 p.2)
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)) :
    MeasureTheory.IntegrableOn
      (fun y : Submission.BoseGases.X j => ∫ z in Submission.BoseGases.abox k ℓ, G z y)
      (Submission.BoseGases.abox j ℓ) := by
  have hm : (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ)) := by
    rw [show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl]
    exact (Measure.prod_restrict _ _).symm
  exact (show Integrable (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j => G p.1 p.2)
      (((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ))) from by
    rw [← hm]; exact hG).integral_prod_right

/-- **Fubini: integrating out the second block is an integrable operation on the first box.** -/
lemma integrableOn_inner_integral' {k j : ℕ} {ℓ : ℝ}
    {G : Submission.BoseGases.X k → Submission.BoseGases.X j → ℝ}
    (hG : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j => G p.1 p.2)
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)) :
    MeasureTheory.IntegrableOn
      (fun z : Submission.BoseGases.X k => ∫ y in Submission.BoseGases.abox j ℓ, G z y)
      (Submission.BoseGases.abox k ℓ) := by
  have hm : (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ)) := by
    rw [show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl]
    exact (Measure.prod_restrict _ _).symm
  exact (show Integrable (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j => G p.1 p.2)
      (((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ))) from by
    rw [← hm]; exact hG).integral_prod_left

/-- The `i`-th slot integrand of the first block fibre is integrable over the second box (as a
function of the second block), i.e. the `y`-integral of the `i`-th slot energy is integrable. -/
lemma integrableOn_fibre_integral_L {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin k) :
    MeasureTheory.IntegrableOn (fun y : Submission.BoseGases.X j =>
      ∫ z in Submission.BoseGases.abox k ℓ, (Submission.BoseGases.aQ ℓ i (bfL Φ y) z) ^ 2)
      (Submission.BoseGases.abox j ℓ) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (k + j) => (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2)
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrableOn_sq_aQ hℓ (Fin.castAdd j i) hΦ.continuous
  have himg := (measurePreserving_blockME k j).integrableOn_image
      (MeasurableEquiv.measurableEmbedding (blockME k j))
      (f := fun x : Submission.BoseGases.X (k + j) =>
        (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2)
      (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
  rw [blockME_image_abox] at himg
  exact integrableOn_inner_integral ((himg.mp hbase).congr_fun
      (fun p _ => by simp only [Function.comp_apply]; rw [aQ_blockME_castAdd])
      ((abox_measurable k ℓ).prod (abox_measurable j ℓ)))

/-- The `i`-th slot integrand of the second block fibre is integrable over the first box (as a
function of the first block). -/
lemma integrableOn_fibre_integral_R {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin j) :
    MeasureTheory.IntegrableOn (fun z : Submission.BoseGases.X k =>
      ∫ y in Submission.BoseGases.abox j ℓ, (Submission.BoseGases.aQ ℓ i (bfR Φ z) y) ^ 2)
      (Submission.BoseGases.abox k ℓ) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (k + j) => (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2)
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrableOn_sq_aQ hℓ (Fin.natAdd k i) hΦ.continuous
  have himg := (measurePreserving_blockME k j).integrableOn_image
      (MeasurableEquiv.measurableEmbedding (blockME k j))
      (f := fun x : Submission.BoseGases.X (k + j) =>
        (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2)
      (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
  rw [blockME_image_abox] at himg
  exact integrableOn_inner_integral' ((himg.mp hbase).congr_fun
      (fun p _ => by simp only [Function.comp_apply]; rw [aQ_blockME_natAdd])
      ((abox_measurable k ℓ).prod (abox_measurable j ℓ)))

/-! ## 3. The excited-count telescope, one block at a time

`∫_{abox j} cnPlus(bfL Φ y)` is the sum over the slots `0,…,k−1` of the glued state of the slot
energy: unfold `cnPlus` (a finite sum of integrals over `abox k ℓ`), exchange the sum with the
`y`-integral (`Integrable.integral_prod_right`, via `integrableOn_fibre_integral_L`), and identify
each term with the corresponding slot of `abox (k+j) ℓ` by Fubini along `blockME`
(`abox_blockME_fubini` + `aQ_blockME_castAdd`). -/

/-- **The first-block excited count telescopes.** -/
lemma cnPlus_fibre_blockL {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ y in Submission.BoseGases.abox j ℓ, Submission.BoseGases.cnPlus ℓ (bfL Φ y))
      = ∑ i : Fin k, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
          (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2 := by
  have hterm : ∀ i : Fin k,
      (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        (Submission.BoseGases.aQ ℓ i (bfL Φ y) z) ^ 2)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ,
          (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2 := by
    intro i
    have hInt : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (k + j) =>
          (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2)
        (Submission.BoseGases.abox (k + j) ℓ) :=
      integrableOn_sq_aQ hℓ (Fin.castAdd j i) hΦ.continuous
    rw [abox_blockME_fubini hℓ (F := fun x : Submission.BoseGases.X (k + j) =>
      (Submission.BoseGases.aQ ℓ (Fin.castAdd j i) Φ x) ^ 2) hInt]
    simp only [aQ_blockME_castAdd]
  simp only [Submission.BoseGases.cnPlus]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => integrableOn_fibre_integral_L hℓ hΦ i)]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

/-- **The second-block excited count telescopes.** -/
lemma cnPlus_fibre_blockR {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ z in Submission.BoseGases.abox k ℓ, Submission.BoseGases.cnPlus ℓ (bfR Φ z))
      = ∑ i : Fin j, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
          (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2 := by
  have hterm : ∀ i : Fin j,
      (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        (Submission.BoseGases.aQ ℓ i (bfR Φ z) y) ^ 2)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ,
          (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2 := by
    intro i
    have hInt : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (k + j) =>
          (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2)
        (Submission.BoseGases.abox (k + j) ℓ) :=
      integrableOn_sq_aQ hℓ (Fin.natAdd k i) hΦ.continuous
    rw [abox_blockME_fubini_symm hℓ (F := fun x : Submission.BoseGases.X (k + j) =>
      (Submission.BoseGases.aQ ℓ (Fin.natAdd k i) Φ x) ^ 2) hInt]
    simp only [aQ_blockME_natAdd]
  simp only [Submission.BoseGases.cnPlus]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => integrableOn_fibre_integral_R hℓ hΦ i)]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

/-! ## 4. The fibre telescope -/

theorem FibreTelescope {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ((∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        (Work.BoseFixR.bfL Φ y z) ^ 2)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, (Φ x) ^ 2)
    ∧ ((∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        (Work.BoseFixR.bfR Φ z y) ^ 2)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, (Φ x) ^ 2)
    ∧ ((∫ y in Submission.BoseGases.abox j ℓ, Submission.BoseGases.cnPlus ℓ (Work.BoseFixR.bfL Φ y))
      + (∫ z in Submission.BoseGases.abox k ℓ, Submission.BoseGases.cnPlus ℓ (Work.BoseFixR.bfR Φ z))
      = Submission.BoseGases.cnPlus ℓ Φ) := by
  have hInt : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) => (Φ x) ^ 2)
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrableOn_abox_of_continuous hℓ (hΦ.continuous.pow 2)
  refine ⟨?_, ?_, ?_⟩
  · have h := abox_blockME_fubini hℓ
      (F := fun x : Submission.BoseGases.X (k + j) => (Φ x) ^ 2) hInt
    simp only [bfL_eq_blockME]
    rw [← h]
  · have h := abox_blockME_fubini_symm hℓ
      (F := fun x : Submission.BoseGases.X (k + j) => (Φ x) ^ 2) hInt
    simp only [bfR_eq_blockME]
    rw [← h]
  · rw [cnPlus_fibre_blockL hℓ hΦ, cnPlus_fibre_blockR hℓ hΦ]
    simp only [Submission.BoseGases.cnPlus, Fin.sum_univ_add]

end Work.BoseFixR
