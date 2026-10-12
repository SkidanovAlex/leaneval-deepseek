import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
import Submission.Work.BoseFixR.KinBlockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.KinSplit` — the two-block splitting of the box-restricted kinetic word

`kinFormB (k+j) ℓ d s εT b Φ = ∫_{abox j ℓ} kinFormB k ℓ d s εT b (bfL Φ y)
                            + ∫_{abox k ℓ} kinFormB j ℓ d s εT b (bfR Φ z)`.

Both sides carry the **same** box side `ℓ`: the left side is `ℓ⁻³` times the sum over the `k+j`
slots of the (box-restricted) slot energy of the `(k+j)`-particle state, and the right side
splits that sum into the `k` slots of the first block and the `j` slots of the second block,
each block being integrated over its own configuration box.

The proof is the Fubini splitting of `abox (k+j) ℓ = abox k ℓ × abox j ℓ` along the block
equivalence `Work.BoseFixR.blockME` (`Submission/Work/BoseFixR/KinBlockDefs.lean`), together with
the fact that the slot-`i` fibre of the concatenation is the slot-`i` fibre of the corresponding
block word (`fibre_blockME_castAdd`, `fibre_blockME_natAdd`).  The only analytic input is the
integrability of the slot integrand on the box, available for *merely smooth* (not necessarily
compactly supported) states through `Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`,
combined here with the pointwise identity `indU ℓ 0 (x i) = 1` on `abox n ℓ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open Submission.BoseGases
open Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The two elementary inputs -/

/-- The anchored window `indU ℓ 0` is `1` on the anchored cube `acube ℓ`. -/
lemma indU_zero_eq_one_of_mem_abox {n : ℕ} {ℓ : ℝ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) :
    Work.BoseKinLoc.indU ℓ 0 (x i) = 1 := by
  have h : x i ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hx i
  rw [show Work.BoseKinLoc.indU ℓ 0 (x i)
      = (Work.BoseKinLoc.lamBox ℓ 0).indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  exact Set.indicator_of_mem h 1

/-- **The slot integrand of the box-restricted kinetic word is integrable on the box**, for a
merely smooth state: the window factor `indU ℓ 0 (x i)` is `1` on the box, so the statement
follows from the windowed version `integrableOn_fsT_fibre_smooth`. -/
lemma integrableOn_fsT_fibre {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Ψ x))
      (Submission.BoseGases.abox n ℓ) := by
  refine (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
    (b := b) hℓ i hΨ).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
  intro x hx
  show Work.BoseKinLoc.indU ℓ 0 (x i)
      * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Ψ x)
    = Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Ψ x)
  rw [indU_zero_eq_one_of_mem_abox hx i, one_mul]

/-- The arithmetic of the volume factor: `ℓ⁻³ · ℓ³ = 1`. -/
lemma zpow_neg_three_mul_three {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ ^ (-3 : ℤ) * ℓ ^ (3 : ℤ) = 1 := by
  rw [← zpow_add₀ (ne_of_gt hℓ), show (-3 : ℤ) + 3 = 0 by norm_num, zpow_zero]

/-- The arithmetic of the volume factor: `ℓ³ · ℓ⁻³ = 1`. -/
lemma zpow_three_mul_neg_three {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ ^ (3 : ℤ) * ℓ ^ (-3 : ℤ) = 1 := by
  rw [← zpow_add₀ (ne_of_gt hℓ), show (3 : ℤ) + -3 = 0 by norm_num, zpow_zero]

/-- The arithmetic of the volume factor: `ℓ⁻³ · (ℓ³ · X) = X`. -/
lemma zpow_neg_three_mul_left {ℓ : ℝ} (hℓ : 0 < ℓ) (X : ℝ) :
    ℓ ^ (-3 : ℤ) * (ℓ ^ (3 : ℤ) * X) = X := by
  rw [← mul_assoc, zpow_neg_three_mul_three hℓ, one_mul]

/-- The arithmetic of the volume factor: `ℓ³ · (ℓ⁻³ · X) = X`. -/
lemma zpow_three_mul_left {ℓ : ℝ} (hℓ : 0 < ℓ) (X : ℝ) :
    ℓ ^ (3 : ℤ) * (ℓ ^ (-3 : ℤ) * X) = X := by
  rw [← mul_assoc, zpow_three_mul_neg_three hℓ, one_mul]

/-! ## 1. The Fubini splitting of the box integral -/

/-- **The box integral splits along the block equivalence** (the `y`-outer order). -/
theorem abox_blockME_fubini {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X (k + j) → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (k + j) ℓ)) :
    (∫ x in Submission.BoseGases.abox (k + j) ℓ, F x)
      = ∫ y in Submission.BoseGases.abox j ℓ,
          ∫ z in Submission.BoseGases.abox k ℓ, F (blockME k j (z, y)) := by
  have hstep : (∫ x in Submission.BoseGases.abox (k + j) ℓ, F x)
      = ∫ p in Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ,
          F (blockME k j p) := by
    have h := (measurePreserving_blockME k j).setIntegral_image_emb
      (MeasurableEquiv.measurableEmbedding (blockME k j)) F
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
    rwa [blockME_image_abox] at h
  rw [hstep]
  have hInt : MeasureTheory.IntegrableOn (fun p : Submission.BoseGases.X k ×
      Submission.BoseGases.X j => F (blockME k j p))
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) := by
    have h := (measurePreserving_blockME k j).integrableOn_image
      (MeasurableEquiv.measurableEmbedding (blockME k j)) (f := F)
      (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
    rw [blockME_image_abox] at h
    exact h.mp hF
  have hm : (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict
          (Submission.BoseGases.abox j ℓ)) := by
    rw [show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl]
    exact (Measure.prod_restrict _ _).symm
  rw [show (∫ p in Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ,
        F (blockME k j p))
      = ∫ p, F (blockME k j p) ∂
          (((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
            ((volume : Measure (Submission.BoseGases.X j)).restrict
              (Submission.BoseGases.abox j ℓ))) from by rw [hm]]
  exact integral_prod_symm _ (by rw [← hm]; exact hInt)

/-- **The box integral splits along the block equivalence** (the `z`-outer order). -/
theorem abox_blockME_fubini_symm {k j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X (k + j) → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (k + j) ℓ)) :
    (∫ x in Submission.BoseGases.abox (k + j) ℓ, F x)
      = ∫ z in Submission.BoseGases.abox k ℓ,
          ∫ y in Submission.BoseGases.abox j ℓ, F (blockME k j (z, y)) := by
  have hstep : (∫ x in Submission.BoseGases.abox (k + j) ℓ, F x)
      = ∫ p in Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ,
          F (blockME k j p) := by
    have h := (measurePreserving_blockME k j).setIntegral_image_emb
      (MeasurableEquiv.measurableEmbedding (blockME k j)) F
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
    rwa [blockME_image_abox] at h
  rw [hstep]
  have hInt : MeasureTheory.IntegrableOn (fun p : Submission.BoseGases.X k ×
      Submission.BoseGases.X j => F (blockME k j p))
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) := by
    have h := (measurePreserving_blockME k j).integrableOn_image
      (MeasurableEquiv.measurableEmbedding (blockME k j)) (f := F)
      (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
    rw [blockME_image_abox] at h
    exact h.mp hF
  have hm : (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict
          (Submission.BoseGases.abox j ℓ)) := by
    rw [show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl]
    exact (Measure.prod_restrict _ _).symm
  rw [show (∫ p in Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ,
        F (blockME k j p))
      = ∫ p, F (blockME k j p) ∂
          (((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)).prod
            ((volume : Measure (Submission.BoseGases.X j)).restrict
              (Submission.BoseGases.abox j ℓ))) from by rw [hm]]
  exact integral_prod _ (by rw [← hm]; exact hInt)

/-! ## 2. The inner integral over a block is the block word -/

/-- **The mean-free slot sum of the first block integrates to `ℓ³` times the first block word.** -/
lemma kinFormB_blockL {k j : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (y : Submission.BoseGases.X j) :
    (∫ z in Submission.BoseGases.abox k ℓ,
        ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z))
      = ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB k ℓ d s εT b (bfL Φ y) := by
  have hone : (∫ z in Submission.BoseGases.abox k ℓ,
        ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z))
      = ∑ i : Fin k, ∫ z in Submission.BoseGases.abox k ℓ,
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z) :=
    (integral_finsetSum Finset.univ (f := fun (i : Fin k) (z : Submission.BoseGases.X k) =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z))
      (fun i _ => integrableOn_fsT_fibre hℓ (contDiff_bfL hΦ y) i))
  have htwo : (∑ i : Fin k, ∫ z in Submission.BoseGases.abox k ℓ,
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z))
      = ∑ i : Fin k, ∫ z in Submission.BoseGases.abox k ℓ,
          Work.BoseKinLoc.indU ℓ 0 (z i)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre k i (bfL Φ y) z) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable k ℓ) (fun z hz => ?_)
    rw [indU_zero_eq_one_of_mem_abox hz i, one_mul]
  rw [hone, htwo, Work.BoseKinLoc.kinFormB]
  exact (zpow_three_mul_left hℓ _).symm

/-- **The mean-free slot sum of the second block integrates to `ℓ³` times the second block
word.** -/
lemma kinFormB_blockR {k j : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (z : Submission.BoseGases.X k) :
    (∫ y in Submission.BoseGases.abox j ℓ,
        ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y))
      = ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB j ℓ d s εT b (bfR Φ z) := by
  have hone : (∫ y in Submission.BoseGases.abox j ℓ,
        ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y))
      = ∑ i : Fin j, ∫ y in Submission.BoseGases.abox j ℓ,
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y) :=
    (integral_finsetSum Finset.univ (f := fun (i : Fin j) (y : Submission.BoseGases.X j) =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y))
      (fun i _ => integrableOn_fsT_fibre hℓ (contDiff_bfR hΦ z) i))
  have htwo : (∑ i : Fin j, ∫ y in Submission.BoseGases.abox j ℓ,
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y))
      = ∑ i : Fin j, ∫ y in Submission.BoseGases.abox j ℓ,
          Work.BoseKinLoc.indU ℓ 0 (y i)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre j i (bfR Φ z) y) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable j ℓ) (fun y hy => ?_)
    rw [indU_zero_eq_one_of_mem_abox hy i, one_mul]
  rw [hone, htwo, Work.BoseKinLoc.kinFormB]
  exact (zpow_three_mul_left hℓ _).symm

/-! ## 3. The splitting -/

theorem KinSplit {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseKinLoc.kinFormB (k + j) ℓ d s eT b Φ
      = (∫ y in Submission.BoseGases.abox j ℓ,
          Work.BoseKinLoc.kinFormB k ℓ d s eT b (Work.BoseFixR.bfL Φ y))
        + (∫ z in Submission.BoseGases.abox k ℓ,
          Work.BoseKinLoc.kinFormB j ℓ d s eT b (Work.BoseFixR.bfR Φ z)) := by
  have hIntN : ∀ i : Fin (k + j), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (k + j) =>
        Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre (k + j) i Φ x))
      (Submission.BoseGases.abox (k + j) ℓ) :=
    fun i => integrableOn_fsT_fibre hℓ hΦ i
  -- (0) unfold the word and drop the window on the box
  have h0 : Work.BoseKinLoc.kinFormB (k + j) ℓ d s eT b Φ
      = ℓ ^ (-3 : ℤ) * ∑ i : Fin (k + j),
          ∫ x in Submission.BoseGases.abox (k + j) ℓ,
            Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre (k + j) i Φ x) := by
    simp only [Work.BoseKinLoc.kinFormB]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable (k + j) ℓ)
      (fun x hx => ?_)
    rw [indU_zero_eq_one_of_mem_abox hx i, one_mul]
  -- (1) split the slot sum into the two blocks
  have h1 : (∑ i : Fin (k + j), ∫ x in Submission.BoseGases.abox (k + j) ℓ,
        Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre (k + j) i Φ x))
      = (∑ i : Fin k, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
            Work.BoseKinLoc.fsT ℓ d s eT b 0
              (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
        + (∑ i : Fin j, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
            Work.BoseKinLoc.fsT ℓ d s eT b 0
              (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x)) :=
    Fin.sum_univ_add _
  -- (2) the first block
  have h2a : (∑ i : Fin k, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, ∑ i : Fin k,
          Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x) :=
    (integral_finsetSum Finset.univ (f := fun (i : Fin k)
        (x : Submission.BoseGases.X (k + j)) =>
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
      (fun i _ => hIntN (Fin.castAdd j i))).symm
  have hIntL : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) => ∑ i : Fin k,
      Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrable_finsetSum Finset.univ (fun i _ => hIntN (Fin.castAdd j i))
  have h2b : (∫ x in Submission.BoseGases.abox (k + j) ℓ, ∑ i : Fin k,
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
      = ∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ (blockME k j (z, y))) :=
    abox_blockME_fubini hℓ hIntL
  have h2c : (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ (blockME k j (z, y))))
      = ∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre k i (bfL Φ y) z) := by
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable j ℓ) (fun y _ => ?_)
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable k ℓ) (fun z _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fibre_blockME_castAdd]
  have h2d : (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre k i (bfL Φ y) z))
      = ℓ ^ (3 : ℤ) * (∫ y in Submission.BoseGases.abox j ℓ,
          Work.BoseKinLoc.kinFormB k ℓ d s eT b (bfL Φ y)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable j ℓ) (fun y _ => ?_)
    exact kinFormB_blockL hℓ hΦ y
  -- (3) the second block
  have h3a : (∑ i : Fin j, ∫ x in Submission.BoseGases.abox (k + j) ℓ,
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, ∑ i : Fin j,
          Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x) :=
    (integral_finsetSum Finset.univ (f := fun (i : Fin j)
        (x : Submission.BoseGases.X (k + j)) =>
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
      (fun i _ => hIntN (Fin.natAdd k i))).symm
  have hIntR : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) => ∑ i : Fin j,
      Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrable_finsetSum Finset.univ (fun i _ => hIntN (Fin.natAdd k i))
  have h3b : (∫ x in Submission.BoseGases.abox (k + j) ℓ, ∑ i : Fin j,
        Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
      = ∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ (blockME k j (z, y))) :=
    abox_blockME_fubini_symm hℓ hIntR
  have h3c : (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ (blockME k j (z, y))))
      = ∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre j i (bfR Φ z) y) := by
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable k ℓ) (fun z _ => ?_)
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable j ℓ) (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fibre_blockME_natAdd]
  have h3d : (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre j i (bfR Φ z) y))
      = ℓ ^ (3 : ℤ) * (∫ z in Submission.BoseGases.abox k ℓ,
          Work.BoseKinLoc.kinFormB j ℓ d s eT b (bfR Φ z)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable k ℓ) (fun z _ => ?_)
    exact kinFormB_blockR hℓ hΦ z
  -- (4) assemble
  rw [h0, h1, h2a, h2b, h2c, h2d, h3a, h3b, h3c, h3d]
  rw [mul_add]
  exact congrArg₂ (· + ·) (zpow_neg_three_mul_left hℓ _) (zpow_neg_three_mul_left hℓ _)

end Work.BoseFixR
