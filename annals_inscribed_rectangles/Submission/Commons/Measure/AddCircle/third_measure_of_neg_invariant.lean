import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Measure.RealEndgame.measureReal_smul_image

namespace Commons.Measure.AddCircle

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

/-- For a fixed `S`, the sets `S ∩ Ico a b` and `S ∩ Ioo a b` have the same Lebesgue measure
(they differ only by the endpoint `a`). -/
private lemma volume_inter_Ico_eq_Ioo (S : Set ℝ) (a b : ℝ) :
    volume (S ∩ Ico a b) = volume (S ∩ Ioo a b) := by
  refine le_antisymm ?_ ?_
  · have hsub : S ∩ Ico a b ⊆ (S ∩ Ioo a b) ∪ (S ∩ ({a} : Set ℝ)) := by
      rintro x ⟨hxS, hxI⟩
      rw [mem_Ico] at hxI
      rcases eq_or_lt_of_le hxI.1 with h | h
      · exact Or.inr ⟨hxS, h.symm⟩
      · exact Or.inl ⟨hxS, h, hxI.2⟩
    calc volume (S ∩ Ico a b)
        ≤ volume ((S ∩ Ioo a b) ∪ (S ∩ ({a} : Set ℝ))) := measure_mono hsub
      _ ≤ volume (S ∩ Ioo a b) + volume (S ∩ ({a} : Set ℝ)) := measure_union_le _ _
      _ ≤ volume (S ∩ Ioo a b) + volume ({a} : Set ℝ) := by
            gcongr; exact inter_subset_right
      _ = volume (S ∩ Ioo a b) + 0 := by rw [Real.volume_singleton]
      _ = volume (S ∩ Ioo a b) := add_zero _
  · exact measure_mono (inter_subset_inter_right S Ioo_subset_Ico_self)

/-- For a fixed `S`, the sets `S ∩ Ioc a b` and `S ∩ Ioo a b` have the same Lebesgue measure
(they differ only by the endpoint `b`). -/
private lemma volume_inter_Ioc_eq_Ioo (S : Set ℝ) (a b : ℝ) :
    volume (S ∩ Ioc a b) = volume (S ∩ Ioo a b) := by
  refine le_antisymm ?_ ?_
  · have hsub : S ∩ Ioc a b ⊆ (S ∩ Ioo a b) ∪ (S ∩ ({b} : Set ℝ)) := by
      rintro x ⟨hxS, hxI⟩
      rw [mem_Ioc] at hxI
      rcases eq_or_lt_of_le hxI.2 with h | h
      · exact Or.inr ⟨hxS, h⟩
      · exact Or.inl ⟨hxS, hxI.1, h⟩
    calc volume (S ∩ Ioc a b)
        ≤ volume ((S ∩ Ioo a b) ∪ (S ∩ ({b} : Set ℝ))) := measure_mono hsub
      _ ≤ volume (S ∩ Ioo a b) + volume (S ∩ ({b} : Set ℝ)) := measure_union_le _ _
      _ ≤ volume (S ∩ Ioo a b) + volume ({b} : Set ℝ) := by
            gcongr; exact inter_subset_right
      _ = volume (S ∩ Ioo a b) + 0 := by rw [Real.volume_singleton]
      _ = volume (S ∩ Ioo a b) := add_zero _
  · exact measure_mono (inter_subset_inter_right S Ioo_subset_Ioc_self)

/-- Corner-insensitivity: `S ∩ Ico a b` and `S ∩ Ioc a b` have the same Lebesgue measure. -/
private lemma volume_inter_Ico_eq_Ioc (S : Set ℝ) (a b : ℝ) :
    volume (S ∩ Ico a b) = volume (S ∩ Ioc a b) := by
  rw [volume_inter_Ico_eq_Ioo S a b, volume_inter_Ioc_eq_Ioo S a b]

/-- Corner-insensitivity: `S ∩ Icc a b` and `S ∩ Ioc a b` have the same Lebesgue measure. -/
private lemma volume_inter_Icc_eq_Ioc (S : Set ℝ) (a b : ℝ) :
    volume (S ∩ Icc a b) = volume (S ∩ Ioc a b) := by
  refine le_antisymm ?_ ?_
  · have hsub : S ∩ Icc a b ⊆ (S ∩ Ioc a b) ∪ (S ∩ ({a} : Set ℝ)) := by
      rintro x ⟨hxS, hxI⟩
      rw [mem_Icc] at hxI
      rcases eq_or_lt_of_le hxI.1 with h | h
      · exact Or.inr ⟨hxS, h.symm⟩
      · exact Or.inl ⟨hxS, h, hxI.2⟩
    calc volume (S ∩ Icc a b)
        ≤ volume ((S ∩ Ioc a b) ∪ (S ∩ ({a} : Set ℝ))) := measure_mono hsub
      _ ≤ volume (S ∩ Ioc a b) + volume (S ∩ ({a} : Set ℝ)) := measure_union_le _ _
      _ ≤ volume (S ∩ Ioc a b) + volume ({a} : Set ℝ) := by
            gcongr; exact inter_subset_right
      _ = volume (S ∩ Ioc a b) + 0 := by rw [Real.volume_singleton]
      _ = volume (S ∩ Ioc a b) := add_zero _
  · exact measure_mono (inter_subset_inter_right S Ioc_subset_Icc_self)

/-- **Assembly of the measure-theoretic endgame**: a measurable, negation-invariant subset of the
circle `ℝ/ℤ` of normalised measure at least `1/3` gives at least `1/3` of the parameters `r ∈ [0,1]`
whose half-angle point `e^{iπr}` lies in the set. -/
theorem third_measure_of_neg_invariant {X : Set UnitAddCircle} (hX : MeasurableSet X)
    (hneg : X = -X) (h : (1 / 3 : ℝ) ≤ volume.real X) :
    (1 / 3 : ℝ) ≤ volume.real
      {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ (((1 / (2 * Real.pi)) * (Real.pi * r) : ℝ) : UnitAddCircle) ∈ X} := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Negation identification: `mk (1 - x) = - mk x`.
  have hkey : ∀ x : ℝ, (((1 - x : ℝ)) : UnitAddCircle) ∈ X ↔ ((x : ℝ) : UnitAddCircle) ∈ X := by
    intro x
    have hcast : ((1 - x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
      rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_period 1, zero_add]
    rw [hcast, ← Set.mem_neg, ← hneg]
  -- The lifted set in `ℝ`.
  set P : Set ℝ := (↑) ⁻¹' X with hPdef
  have hPmeas : MeasurableSet P := by
    rw [hPdef]; exact hX.preimage AddCircle.measurable_mk'
  set L : Set ℝ := P ∩ Ioc (0 : ℝ) (1 / 2) with hLdef
  set R : Set ℝ := P ∩ Ico (1 / 2) (1 : ℝ) with hRdef
  set T : Set ℝ := P ∩ Icc (0 : ℝ) (1 / 2) with hTdef
  have hLmeas : MeasurableSet L := by rw [hLdef]; exact hPmeas.inter measurableSet_Ioc
  have hRmeas : MeasurableSet R := by rw [hRdef]; exact hPmeas.inter measurableSet_Ico
  have hTmeas : MeasurableSet T := by rw [hTdef]; exact hPmeas.inter measurableSet_Icc
  -- (1) circle measure equals the measure of the representative in `(0,1]`.
  have hproj : volume X = volume (P ∩ Ioc (0 : ℝ) 1) := by
    have hh := AddCircle.add_projection_respects_measure 1 0 hX
    rw [hPdef]
    simpa using hh
  -- (2) split `(0,1]` into `(0,1/2] ∪ [1/2,1)`.
  have hsplit : volume (P ∩ Ico (0 : ℝ) 1)
      = volume (P ∩ Ico (0 : ℝ) (1 / 2)) + volume (P ∩ Ico (1 / 2) (1 : ℝ)) := by
    have hunion : P ∩ Ico (0 : ℝ) 1
        = (P ∩ Ico (0 : ℝ) (1 / 2)) ∪ (P ∩ Ico (1 / 2) (1 : ℝ)) := by
      rw [← inter_union_distrib_left]
      congr 1
      ext x
      simp only [mem_Ico, mem_union]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_ge x (1 / 2) with hx | hx
        · exact Or.inl ⟨h0, hx⟩
        · exact Or.inr ⟨hx, h1⟩
      · rintro (⟨h0, hx⟩ | ⟨hx, h1⟩)
        · exact ⟨h0, by linarith⟩
        · exact ⟨by linarith, h1⟩
    have hdisj : Disjoint (P ∩ Ico (0 : ℝ) (1 / 2)) (P ∩ Ico (1 / 2) (1 : ℝ)) := by
      rw [disjoint_left]
      intro x hx1 hx2
      rw [mem_inter_iff, mem_Ico] at hx1 hx2
      linarith [hx1.2.2, hx2.2.1]
    rw [hunion]
    exact measure_union hdisj (hPmeas.inter measurableSet_Ico)
  -- (3) symmetry: `R` is the reflection of `L`.
  have hf : MeasurePreserving (fun x : ℝ => 1 - x) volume volume := by
    have h := (measurePreserving_add_left volume (1 : ℝ)).comp (Measure.measurePreserving_neg volume)
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hfL : (fun x : ℝ => 1 - x) ⁻¹' L = R := by
    rw [hLdef, hRdef, hPdef]
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨hxP, h0, hh⟩
      refine ⟨hkey x |>.mp hxP, by linarith, by linarith⟩
    · rintro ⟨hxP, hh1, hh2⟩
      refine ⟨hkey x |>.mpr hxP, by linarith, by linarith⟩
  have hRL : volume R = volume L := by
    have := hf.measure_preimage hLmeas.nullMeasurableSet
    rw [hfL] at this
    exact this
  -- (4) `T` has the same measure as `L`.
  have hTL : volume T = volume L := by
    rw [hTdef, hLdef]
    exact volume_inter_Icc_eq_Ioc P 0 (1 / 2)
  -- (5) `X` carries twice the measure of its left half `L`.
  have hX2L : volume X = 2 * volume L := by
    rw [hproj]
    rw [← volume_inter_Ico_eq_Ioc P 0 1]
    rw [hsplit]
    rw [← hRdef, volume_inter_Ico_eq_Ioc P 0 (1 / 2), ← hLdef]
    rw [hRL, two_mul]
  have hrealX : volume.real X = 2 * volume.real L := by
    rw [Measure.real_def, Measure.real_def, hX2L, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have hrealT : volume.real T = volume.real L := by
    rw [Measure.real_def, Measure.real_def, hTL]
  -- (6) the target set is the scaling preimage of `T`.
  set Aset : Set ℝ := (fun r : ℝ => (1 / 2) * r) ⁻¹' T with hAdef
  have hrealAset : volume.real Aset = 2 * volume.real T := by
    rw [hAdef]
    rw [Commons.Measure.RealEndgame.measureReal_smul_image (by norm_num : (1 / 2 : ℝ) ≠ 0) hTmeas]
    norm_num
  -- (7) identify the goal's set with `Aset`.
  have hgoal : {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧
      (((1 / (2 * Real.pi)) * (Real.pi * r) : ℝ) : UnitAddCircle) ∈ X} = Aset := by
    rw [hAdef, hTdef, hPdef]
    ext r
    simp only [Set.mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_Icc]
    have hcast : (((1 / (2 * Real.pi)) * (Real.pi * r) : ℝ) : UnitAddCircle)
        = (((1 / 2) * r : ℝ) : UnitAddCircle) := by
      congr 1
      field_simp
    constructor
    · rintro ⟨h0, h1, hx⟩
      exact ⟨by rw [← hcast]; exact hx, by linarith, by linarith⟩
    · rintro ⟨hx, h0, h1⟩
      exact ⟨by linarith, by linarith, by rw [hcast]; exact hx⟩
  rw [hgoal, hrealAset, hrealT, ← hrealX]
  exact h

end

end Commons.Measure.AddCircle