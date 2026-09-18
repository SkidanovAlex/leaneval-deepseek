/-
# The Hausdorff measure of the Cantor set of the mass transference construction

This file proves the last step of the Beresnevich–Velani mass transference principle in `ℝ`
for the power dimension function `f(r) = r ^ d`: the Cantor set `cantor T` produced by the
construction has `d`-dimensional Hausdorff measure at least `η / 400`.

The mass distribution with the Frostman-type bound is `Tree.frostmanMeasure` (proved in
`Submission/Work/MassTransferenceAlt/Tree/frostmanMeasure.lean`, with the level masses and the
key estimate in `Submission/Work/MassTransferenceAlt/Tree/LevelMass.lean`); this file turns that
bound into a bound for the Hausdorff measure by `MeasureTheory.Measure.le_hausdorffMeasure`.
-/
import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.LevelMass
import Submission.Work.MassTransferenceAlt.Tree.frostmanMeasure

namespace Work.MassTransferenceAlt.Tree
open Work.MassTransferenceAlt MeasureTheory Set Metric
open scoped ENNReal NNReal
open Work.MassTransferenceAlt.Tree.Hausdorff

/-- The interval `Iv ((a+b)/2) ((b-a)/2)` is the interval `Icc a b`. -/
lemma iv_mid (a b : ℝ) : Iv ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext z
  rw [mem_Iv, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **The Cantor set of the construction has `d`-dimensional Hausdorff measure at least
`η / 400`.** -/
theorem cantorHausdorff (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) :
    ENNReal.ofReal (η / 400) ≤ MeasureTheory.Measure.hausdorffMeasure d
      (Work.MassTransferenceAlt.cantor T) := by
  classical
  obtain ⟨μ, hμuniv, hμK, hμbound⟩ := frostmanMeasure d hd0 hd1 c ρ η hη T
  have hηpos : (0:ℝ) < η := hη
  -- the measure `μ` has no atoms
  have hρmin : 0 < rmin0 d c ρ η T := rmin0_pos d c ρ η T
  have hatom : ∀ z : ℝ, μ ({z} : Set ℝ) = 0 := by
    intro z
    have hle : ∀ n : ℕ, μ ({z} : Set ℝ) ≤
        ENNReal.ofReal (400 * (2 * (rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)))) ^ d / η) := by
      intro n
      have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have hrpos : 0 < rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)) := by positivity
      have hrle : 2 * (rmin0 d c ρ η T / (8 * ((n:ℝ) + 1))) ≤ rmin0 d c ρ η T := by
        have h3 : 2 * (rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)))
            = 2 * rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)) := by ring
        rw [h3, div_le_iff₀ (by positivity : (0:ℝ) < 8 * ((n:ℝ) + 1))]
        nlinarith [hρmin, hn1]
      refine le_trans (measure_mono ?_) (hμbound z _ hrpos hrle)
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [mem_Iv]
      simpa using hrpos.le
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hεR : (0:ℝ) < (ε:ℝ) := NNReal.coe_pos.mpr hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        (400 * (2 * (rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)))) ^ d / η) ≤ (ε:ℝ) := by
      have h1 : 0 < (ε:ℝ) * η / 400 := by positivity
      obtain ⟨N, hN⟩ := exists_nat_gt ((2 * rmin0 d c ρ η T / 8) / ((ε:ℝ) * η / 400) ^ (1 / d))
      refine ⟨N, ?_⟩
      have hpos : 0 < ((ε:ℝ) * η / 400) ^ (1 / d) := Real.rpow_pos_of_pos h1 _
      have hN' : 2 * (rmin0 d c ρ η T / (8 * ((N:ℝ) + 1))) ≤ ((ε:ℝ) * η / 400) ^ (1 / d) := by
        have h2 : (0:ℝ) < (N : ℝ) + 1 := by positivity
        have h3 : 2 * (rmin0 d c ρ η T / (8 * ((N:ℝ) + 1)))
            = (2 * rmin0 d c ρ η T / 8) / ((N:ℝ) + 1) := by field_simp
        rw [h3, div_le_iff₀ h2]
        rw [div_lt_iff₀ hpos] at hN
        linarith
      have h4 : (2 * (rmin0 d c ρ η T / (8 * ((N:ℝ) + 1)))) ^ d ≤ (ε:ℝ) * η / 400 := by
        have h5 := Real.rpow_le_rpow (by positivity) hN' hd0.le
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (ε:ℝ) * η / 400),
          one_div_mul_cancel (ne_of_gt hd0), Real.rpow_one] at h5
        exact h5
      rw [div_le_iff₀ hηpos]
      nlinarith [h4]
    calc μ ({z} : Set ℝ) ≤
          ENNReal.ofReal (400 * (2 * (rmin0 d c ρ η T / (8 * ((n:ℝ) + 1)))) ^ d / η) := hle n
      _ ≤ ENNReal.ofReal (ε:ℝ) := ENNReal.ofReal_le_ofReal hn
      _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      _ = 0 + ε := (zero_add _).symm

  -- the scaled measure is bounded by the Hausdorff measure
  set ε₀ : ℝ := rmin0 d c ρ η T / 4 with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; linarith
  have hmain : ((ENNReal.ofReal (η / 400)) • μ) ≤ MeasureTheory.Measure.hausdorffMeasure d := by
    refine MeasureTheory.Measure.le_hausdorffMeasure d ((ENNReal.ofReal (η / 400)) • μ) (ENNReal.ofReal ε₀) (ENNReal.ofReal_pos.mpr hε₀pos) ?_
    intro s hs
    by_cases hsne : (s : Set ℝ).Nonempty
    · have hfin : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
      have hbdd : Bornology.IsBounded s := isBounded_iff_ediam_ne_top.mpr hfin
      obtain ⟨z, hz⟩ := hsne
      have hle_sInf : sInf s ≤ sSup s := by
        have h1 : sInf s ≤ z := csInf_le hbdd.bddBelow hz
        have h2 : z ≤ sSup s := le_csSup hbdd.bddAbove hz
        linarith
      set x : ℝ := (sInf s + sSup s) / 2 with hx
      set r : ℝ := (sSup s - sInf s) / 2 with hr
      have hsub : s ⊆ Iv x r := by
        have h1 : s ⊆ Set.Icc (sInf s) (sSup s) := hbdd.subset_Icc_sInf_sSup
        have h2 : Set.Icc (sInf s) (sSup s) = Iv x r := (iv_mid (sInf s) (sSup s)).symm
        rw [h2] at h1
        exact h1
      have hediam : Metric.ediam (Iv x r) = Metric.ediam s := by
        rw [iv_mid, Real.ediam_Icc, Real.ediam_eq hbdd]
      have h2r : 2 * r = (Metric.ediam s).toReal := by
        rw [hr]
        have := Real.ediam_eq hbdd
        rw [this, ENNReal.toReal_ofReal (by linarith)]
        ring
      have h2r_le : 2 * r ≤ rmin0 d c ρ η T := by
        have h1 : (Metric.ediam s).toReal ≤ (ENNReal.ofReal ε₀).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
        rw [ENNReal.toReal_ofReal hε₀pos.le, hε₀def] at h1
        rw [h2r]
        linarith
      by_cases hr0 : r = 0
      · have hzero : Metric.ediam s = 0 := by
          have h1 : (Metric.ediam s).toReal = 0 := by rw [← h2r, hr0]; ring
          have h2 : Metric.ediam s ≠ ⊤ := hfin
          calc Metric.ediam s = ENNReal.ofReal ((Metric.ediam s).toReal) :=
                (ENNReal.ofReal_toReal h2).symm
            _ = 0 := by rw [h1]; simp
        have hsingle : s ⊆ ({z} : Set ℝ) := by
          intro w hw
          have hzw : w = z := by
            by_contra hne
            have hpos : (0:ℝ) < |w - z| := abs_pos.mpr (sub_ne_zero.mpr hne)
            have hle : edist w z ≤ Metric.ediam s := edist_le_ediam_of_mem hw hz
            rw [edist_dist, Real.dist_eq, hzero] at hle
            have h0 : ENNReal.ofReal |w - z| = 0 := le_antisymm hle bot_le
            rw [ENNReal.ofReal_eq_zero] at h0
            linarith
          rw [Set.mem_singleton_iff]
          exact hzw
        rw [hzero, ENNReal.zero_rpow_of_pos hd0]
        refine le_trans (measure_mono hsingle) ?_
        rw [Measure.smul_apply, hatom z, smul_zero]
      · have hrpos : 0 < r := lt_of_le_of_ne (by positivity) (Ne.symm hr0)
        have hbdA : μ (Iv x r) ≤ ENNReal.ofReal (400 * (2 * r) ^ d / η) := hμbound x r hrpos h2r_le
        have h1 : ((ENNReal.ofReal (η / 400)) • μ) s ≤ ((ENNReal.ofReal (η / 400)) • μ) (Iv x r) := by
          rw [Measure.smul_apply, Measure.smul_apply]
          exact mul_le_mul_of_nonneg_left (measure_mono hsub) bot_le
        refine h1.trans ?_
        rw [Measure.smul_apply]
        refine (mul_le_mul_of_nonneg_left hbdA bot_le).trans ?_
        have h2 : ENNReal.ofReal (η / 400) * ENNReal.ofReal (400 * (2 * r) ^ d / η)
            = ENNReal.ofReal ((2 * r) ^ d) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        rw [h2]
        have h3 : ENNReal.ofReal ((2 * r) ^ d) = (Metric.ediam s) ^ d := by
          rw [h2r, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd0.le,
            ENNReal.ofReal_toReal hfin]
        rw [h3]
    · rw [Set.not_nonempty_iff_eq_empty] at hsne
      subst hsne
      rw [Measure.smul_apply, measure_empty, smul_zero, Metric.ediam_empty,
        ENNReal.zero_rpow_of_pos hd0]
  have hK : ((ENNReal.ofReal (η / 400)) • μ) (Work.MassTransferenceAlt.cantor T) = ENNReal.ofReal (η / 400) := by
    rw [Measure.smul_apply, hμK]
    exact mul_one _
  calc ENNReal.ofReal (η / 400)
      = ((ENNReal.ofReal (η / 400)) • μ) (Work.MassTransferenceAlt.cantor T) := hK.symm
    _ ≤ MeasureTheory.Measure.hausdorffMeasure d (Work.MassTransferenceAlt.cantor T) := hmain _

end Work.MassTransferenceAlt.Tree
