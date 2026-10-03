import Mathlib
import Submission.Work.FIArea3.JointCount.sharp_defs
import Submission.Work.FIArea3.JointCount.polarBand_volume
import Submission.Work.FIArea3.JointCount.angSector
import Submission.Work.FIArea3.JointCount.volume_convexHull_angSector_le_small
import Submission.Work.FIArea3.JointCount.volume_convexHull_angSector_le_large

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- `annSector` is an `angSector` with angular interval `(max φ (-π), min (φ+Δ) π]`. -/
lemma annSector_eq_angSector (a b φ Δ : ℝ) :
    annSector a b φ Δ
      = angSector a b (Set.Ioc (max φ (-Real.pi)) (min (φ + Δ) Real.pi)) := by
  ext z
  simp only [annSector, angSector, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, max_lt_iff.mpr ⟨h3, Complex.neg_pi_lt_arg z⟩,
      le_min_iff.mpr ⟨h4, Complex.arg_le_pi z⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨h3, -⟩ := max_lt_iff.mp h3
    obtain ⟨h4, -⟩ := le_min_iff.mp h4
    exact ⟨h1, h2, h3, h4⟩

/-- The area of an angular annulus sector with angular interval `(α, β] ⊆ (-π, π]`
equals `(b² - a²)/2 · (β - α)`. -/
lemma angSector_volume_toReal (a b α β : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hα : -Real.pi ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    (MeasureTheory.volume (angSector a b (Set.Ioc α β))).toReal
      = (b ^ 2 - a ^ 2) / 2 * (β - α) := by
  have hvol := polarBand_volume a b (Set.Ioc α β) (le_of_lt ha) hab measurableSet_Ioc
  have hco : MeasureTheory.volume (Set.Ioc α β ∩ Set.Ioo (-Real.pi) Real.pi)
      = ENNReal.ofReal (β - α) := by
    apply le_antisymm
    · calc MeasureTheory.volume (Set.Ioc α β ∩ Set.Ioo (-Real.pi) Real.pi)
          ≤ MeasureTheory.volume (Set.Ioc α β) := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (β - α) := Real.volume_Ioc
    · rw [← Real.volume_Ioo]
      apply measure_mono
      intro x hx
      rw [Set.mem_Ioo] at hx
      exact ⟨⟨hx.1, hx.2.le⟩, lt_of_le_of_lt hα hx.1, lt_of_lt_of_le hx.2 hβ⟩
  have hco2 : (MeasureTheory.volume (Set.Ioc α β ∩ Set.Ioo (-Real.pi) Real.pi)).toReal
      = β - α := by rw [hco, ENNReal.toReal_ofReal (sub_nonneg.mpr hαβ)]
  unfold angSector
  rw [hvol, hco2]
  rw [ENNReal.toReal_ofReal (by
    apply mul_nonneg
    · apply div_nonneg
      · exact sub_nonneg.mpr (pow_le_pow_left₀ ha.le hab 2)
      · norm_num
    · exact sub_nonneg.mpr hαβ)]

/-- `π + 2 ≤ π³/6`. -/
lemma pi_add_two_le_pi_cube_div_six : Real.pi + 2 ≤ Real.pi ^ 3 / 6 := by
  have h1 : (3.14:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
  have h2 : Real.pi ≤ (3.142:ℝ) := by linarith [Real.pi_lt_d20]
  have h3 : (3.14:ℝ) ^ 3 ≤ Real.pi ^ 3 := by gcongr
  nlinarith [h3, h2, h1]

/-- For `x ≥ π`, `x + 2 ≤ x³/6`. -/
lemma add_two_le_cube_div_six (x : ℝ) (hx : Real.pi ≤ x) : x + 2 ≤ x ^ 3 / 6 := by
  have hpi : Real.pi + 2 ≤ Real.pi ^ 3 / 6 := pi_add_two_le_pi_cube_div_six
  have hpi6 : 0 ≤ Real.pi ^ 3 - 6 * Real.pi - 12 := by nlinarith [hpi]
  have hsq : 0 ≤ x ^ 2 + x * Real.pi + Real.pi ^ 2 - 6 := by
    nlinarith [hx, Real.pi_gt_three]
  have hprod : 0 ≤ (x - Real.pi) * (x ^ 2 + x * Real.pi + Real.pi ^ 2 - 6) :=
    mul_nonneg (by linarith) hsq
  nlinarith [hprod, hpi6]

theorem convexHull_annSector_gap_le (a θ φ : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (MeasureTheory.volume (convexHull ℝ (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ)))).toReal
      ≤ (MeasureTheory.volume (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))).toReal
        + (a^2 / 2) * min ((2 * Real.pi * θ)^3 / 6) (2 * Real.pi * θ + 1 + θ) := by
  set b : ℝ := a * Real.sqrt (1 + θ) with hbdef
  set Δ : ℝ := 2 * Real.pi * θ with hΔdef
  set α : ℝ := max φ (-Real.pi) with hαdef
  set β : ℝ := min (φ + Δ) Real.pi with hβdef
  have hb_ge : a ≤ b := by
    rw [hbdef]
    have hs : (1:ℝ) ≤ Real.sqrt (1 + θ) := Real.one_le_sqrt.mpr (by linarith)
    nlinarith [ha.le, hs]
  have hbsq : b ^ 2 = a ^ 2 * (1 + θ) := by
    rw [hbdef, mul_pow, Real.sq_sqrt (by linarith)]
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; positivity
  have hset : Work.FIArea3.JointCount.annSector a b φ Δ = angSector a b (Set.Ioc α β) := by
    rw [hαdef, hβdef]; exact annSector_eq_angSector a b φ Δ
  rw [hset]
  rcases le_or_gt β α with hβα | hαβ
  · -- empty angular interval
    have hIoc : Set.Ioc α β = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_Ioc] at hx
      exact absurd hx.1 (not_lt_of_ge (le_trans hx.2 hβα))
    have hS : angSector a b (Set.Ioc α β) = ∅ := by rw [hIoc]; simp [angSector]
    rw [hS, convexHull_empty]
    have hmin : 0 ≤ (a ^ 2 / 2) * min (Δ ^ 3 / 6) (Δ + 1 + θ) := by
      have h1 : 0 ≤ Δ ^ 3 / 6 := div_nonneg (pow_nonneg hΔ0 3) (by norm_num)
      have h2 : 0 ≤ Δ + 1 + θ := by linarith
      exact mul_nonneg (by positivity) (le_min h1 h2)
    simpa using hmin
  · -- nonempty
    have hαge : -Real.pi ≤ α := by rw [hαdef]; exact le_max_right _ _
    have hβle : β ≤ Real.pi := by rw [hβdef]; exact min_le_right _ _
    have hφβ : β ≤ φ + Δ := by rw [hβdef]; exact min_le_left _ _
    have hφα : φ ≤ α := by rw [hαdef]; exact le_max_left _ _
    have hℓΔ : β - α ≤ Δ := by linarith
    have hvS := angSector_volume_toReal a b α β ha hb_ge hαge hαβ.le hβle
    rcases le_or_gt (β - α) Real.pi with hℓ | hℓ
    · -- thin sector: ℓ ≤ π
      have hsmall := volume_convexHull_angSector_le_small a b α β ha hb_ge hαge hβle hαβ.le hℓ
      have hkey : β - α - Real.sin (β - α) ≤ min (Δ ^ 3 / 6) (Δ + 1 + θ) := by
        apply le_min
        · have hs := Real.sin_ge_sub_cube (show 0 ≤ β - α by linarith)
          have hcube : (β - α) ^ 3 / 6 ≤ Δ ^ 3 / 6 :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) hℓΔ 3) (by norm_num)
          linarith
        · have hsin : -1 ≤ Real.sin (β - α) := Real.neg_one_le_sin _
          linarith [hℓΔ, hθ0]
      nlinarith [hsmall, hvS, hkey, hbsq, sq_nonneg a]
    · -- wide sector: ℓ ≥ π
      have hlarge := volume_convexHull_angSector_le_large a b α β ha hb_ge hαge hβle hαβ.le hℓ.le
      have hΔpi : Real.pi ≤ Δ := le_trans hℓ.le hℓΔ
      have hkey : 1 + θ + (β - α) ≤ min (Δ ^ 3 / 6) (Δ + 1 + θ) := by
        apply le_min
        · have h1 : 1 + θ + (β - α) ≤ Δ + 2 := by nlinarith [hℓΔ, hθ1]
          have h2 : Δ + 2 ≤ Δ ^ 3 / 6 := add_two_le_cube_div_six Δ hΔpi
          linarith
        · nlinarith [hℓΔ, hθ0]
      nlinarith [hlarge, hvS, hkey, hbsq, sq_nonneg a]

end

end Work.FIArea3.JointCount
