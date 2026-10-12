import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory ENNReal
open scoped ENNReal

namespace Commons.Measure.FinFunction

/-- The volume of a closed cube in `(Fin 3 → ℝ)` with side length `b - a`. -/
lemma volume_pi_Icc_const_fin3 {a b : ℝ} (hab : 0 ≤ b - a) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      (Set.univ.pi (fun _ : Fin 3 => Set.Icc a b)) = ENNReal.ofReal ((b - a) ^ 3) := by
  rw [Set.pi_univ_Icc (x := fun _ : Fin 3 => a) (y := fun _ : Fin 3 => b)]
  rw [Real.volume_Icc_pi (a := fun _ : Fin 3 => a) (b := fun _ : Fin 3 => b)]
  calc
    (∏ _i : Fin 3, ENNReal.ofReal (b - a)) = ENNReal.ofReal (b - a) ^ 3 := by
      simp [Finset.card_univ, Fintype.card_fin, Finset.prod_const]
    _ = ENNReal.ofReal ((b - a) ^ 3) := by
      rw [ENNReal.ofReal_pow hab 3]

/-- The volume of an open cube in `(Fin 3 → ℝ)` with side length `b - a`. -/
lemma volume_pi_Ioo_const_fin3 {a b : ℝ} (hab : 0 ≤ b - a) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      (Set.univ.pi (fun _ : Fin 3 => Set.Ioo a b)) = ENNReal.ofReal ((b - a) ^ 3) := by
  rw [Real.volume_pi_Ioo (a := fun _ : Fin 3 => a) (b := fun _ : Fin 3 => b)]
  calc
    (∏ _i : Fin 3, ENNReal.ofReal (b - a)) = ENNReal.ofReal (b - a) ^ 3 := by
      simp [Finset.card_univ, Fintype.card_fin, Finset.prod_const]
    _ = ENNReal.ofReal ((b - a) ^ 3) := by
      rw [ENNReal.ofReal_pow hab 3]

lemma cube_shell_volume_le {A δ : ℝ} (hA : 0 ≤ A) (hAδ : 0 ≤ A - δ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) {f : Fin 3 → ℝ | (∃ i : Fin 3, A - δ ≤ |f i|) ∧ (∀ i : Fin 3, |f i| ≤ A)}
      ≤ ENNReal.ofReal ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3) := by
  classical
  let C : Set (Fin 3 → ℝ) := {f | ∀ i : Fin 3, |f i| ≤ A}
  let B : Set (Fin 3 → ℝ) := {f | ∀ i : Fin 3, |f i| < A - δ}
  -- The shell is exactly the closed cube minus the open inner cube.
  have hCeq : ({f : Fin 3 → ℝ | (∃ i : Fin 3, A - δ ≤ |f i|) ∧ (∀ i : Fin 3, |f i| ≤ A)} : Set (Fin 3 → ℝ)) = C \ B := by
    ext f
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · exact hf.2
      · change ¬ (∀ i : Fin 3, |f i| < A - δ)
        rw [not_forall]
        rcases hf.1 with ⟨i, hi⟩
        exact ⟨i, not_lt.mpr hi⟩
    · intro hf
      have hfC : ∀ i : Fin 3, |f i| ≤ A := by simpa [C] using hf.1
      have hnotB : ¬ (∀ i : Fin 3, |f i| < A - δ) := by
        have h : f ∉ B := hf.2
        change ¬ (∀ i : Fin 3, |f i| < A - δ) at h
        exact h
      constructor
      · rw [not_forall] at hnotB
        rcases hnotB with ⟨i, hi⟩
        exact ⟨i, not_lt.mp hi⟩
      · exact hfC
  -- volume of the outer closed cube of side 2A
  have hvolC : (volume : Measure (Fin 3 → ℝ)) C = ENNReal.ofReal ((2 * A) ^ 3) := by
    have hCpi : C = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-A) A) := by
      ext f
      simp [C, Set.mem_Icc, abs_le, Pi.le_def, forall_and]
    rw [hCpi]
    have h2 : 0 ≤ A - (-A) := by linarith
    rw [volume_pi_Icc_const_fin3 (a := -A) (b := A) h2]
    congr 1
    ring
  -- volume of the open inner cube of side 2(A-δ)
  have hvolB : (volume : Measure (Fin 3 → ℝ)) B = ENNReal.ofReal ((2 * (A - δ)) ^ 3) := by
    have hBpi : B = Set.univ.pi (fun _ : Fin 3 => Set.Ioo (-(A - δ)) (A - δ)) := by
      ext f
      simp [B, Set.mem_Ioo, abs_lt, forall_and]
    rw [hBpi]
    have h2 : 0 ≤ (A - δ) - (-(A - δ)) := by linarith
    rw [volume_pi_Ioo_const_fin3 (a := -(A - δ)) (b := A - δ) h2]
    congr 1
    ring
  have hBmeas : MeasurableSet B := by
    have hBpi : B = Set.univ.pi (fun _ : Fin 3 => Set.Ioo (-(A - δ)) (A - δ)) := by
      ext f
      simp [B, Set.mem_Ioo, abs_lt, forall_and]
    rw [hBpi]
    exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3))) (t := fun _ : Fin 3 => Set.Ioo (-(A - δ)) (A - δ))
      Set.countable_univ (by intro i hi; exact measurableSet_Ioo)
  by_cases hδ : 0 ≤ δ
  · -- δ ≥ 0: inner cube is contained in the outer cube
    have hAδleA : A - δ ≤ A := by linarith
    have hBC : B ⊆ C := by
      intro f hf i
      exact le_trans (le_of_lt (by simpa [B] using hf i)) hAδleA
    have hBfin : (volume : Measure (Fin 3 → ℝ)) B ≠ ∞ := by
      rw [hvolB]
      exact ENNReal.ofReal_ne_top
    have hq : 0 ≤ (2 * (A - δ)) ^ 3 := by positivity
    calc
      (volume : Measure (Fin 3 → ℝ)) {f : Fin 3 → ℝ | (∃ i : Fin 3, A - δ ≤ |f i|) ∧ (∀ i : Fin 3, |f i| ≤ A)}
          = volume (C \ B) := by rw [hCeq]
      _ = volume C - volume B := MeasureTheory.measure_sdiff hBC hBmeas.nullMeasurableSet hBfin
      _ = ENNReal.ofReal ((2 * A) ^ 3) - ENNReal.ofReal ((2 * (A - δ)) ^ 3) := by
            rw [hvolC, hvolB]
      _ ≤ ENNReal.ofReal ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3) := by
            rw [← ENNReal.ofReal_sub ((2 * A) ^ 3) hq]
  · -- δ < 0: the shell is empty, since A - δ > A
    have hA_lt : A < A - δ := by linarith
    have hCsubB : C ⊆ B := by
      intro f hf i
      have hfi : |f i| ≤ A := by simpa [C] using hf i
      simpa [B] using lt_of_le_of_lt hfi hA_lt
    have hdiff : C \ B = ∅ := Set.sdiff_eq_empty.mpr hCsubB
    calc
      (volume : Measure (Fin 3 → ℝ)) {f : Fin 3 → ℝ | (∃ i : Fin 3, A - δ ≤ |f i|) ∧ (∀ i : Fin 3, |f i| ≤ A)}
          = volume (C \ B) := by rw [hCeq]
      _ = 0 := by rw [hdiff, MeasureTheory.measure_empty]
      _ ≤ ENNReal.ofReal ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3) := by
            exact (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3))

end Commons.Measure.FinFunction