import Mathlib
import Submission.Commons.Analysis.Measure.volume_dist_int_mul_Ico
import Submission.Commons.Analysis.Measure.measurePreserving_pi_comm

open MeasureTheory Set
open scoped ENNReal

namespace Commons.Analysis.Measure

/-- The set of `y : Fin ℓ → ℝ` whose linear form `∑ aᵢ yᵢ` is within `δ` of an integer and
which lies in the unit cube is measurable (for any `a`, `δ`). -/
private lemma measurableSet_linearForm_column {ℓ : ℕ} (a : Fin ℓ → ℤ) {δ : ℝ} :
    MeasurableSet {y : Fin ℓ → ℝ |
      (∃ b : ℤ, |(∑ i, (a i : ℝ) * y i) - (b : ℝ)| < δ) ∧ (∀ i, y i ∈ Set.Ico (0:ℝ) 1)} := by
  have hL : Continuous (fun y : Fin ℓ → ℝ => ∑ i, (a i : ℝ) * y i) := by fun_prop
  have hP : MeasurableSet {y : Fin ℓ → ℝ | ∃ b : ℤ,
      |(∑ i, (a i : ℝ) * y i) - (b : ℝ)| < δ} := by
    rw [show {y : Fin ℓ → ℝ | ∃ b : ℤ, |(∑ i, (a i : ℝ) * y i) - (b:ℝ)| < δ}
        = (fun y : Fin ℓ → ℝ => ∑ i, (a i : ℝ) * y i) ⁻¹'
            (⋃ b : ℤ, Set.Ioo ((b:ℝ) - δ) ((b:ℝ) + δ)) from by
      ext y; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_Ioo, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b, hb⟩; rw [abs_lt] at hb; exact ⟨b, by constructor <;> linarith [hb.1, hb.2]⟩
      · rintro ⟨b, hb⟩; exact ⟨b, by rw [abs_lt]; constructor <;> linarith [hb.1, hb.2]⟩]
    exact (isOpen_iUnion (fun b : ℤ => isOpen_Ioo)).measurableSet.preimage hL.measurable
  have hQ : MeasurableSet {y : Fin ℓ → ℝ | ∀ i, y i ∈ Set.Ico (0:ℝ) 1} := by
    rw [show {y : Fin ℓ → ℝ | ∀ i, y i ∈ Set.Ico (0:ℝ) 1}
        = Set.univ.pi (fun _ : Fin ℓ => Set.Ico (0:ℝ) 1) from by
      ext y; simp]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  exact hP.inter hQ

/-- The measure of the unit cube `[0,1)^n` is `1`. -/
private lemma volume_cube (n : ℕ) :
    MeasureTheory.volume (Set.univ.pi (fun _ : Fin n => Set.Ico (0:ℝ) 1)) = 1 := by
  rw [MeasureTheory.volume_pi_pi]
  simp [Real.volume_Ico]

/-- **Single column.**  For a non-zero integer vector `a`, the measure of the set of
`y ∈ [0,1)^ℓ` such that `∑ aᵢ yᵢ` is within `δ` of an integer equals `2δ`, for `δ ≤ 1/2`.
The proof splits off one coordinate whose coefficient is non-zero using `piFinSuccAbove` and
applies Fubini, the inner one-variable computation being `volume_dist_int_mul_Ico`. -/
private lemma volume_singleColumn {ℓ : ℕ} (a : Fin ℓ → ℤ) (ha : ∃ i, a i ≠ 0) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    MeasureTheory.volume {y : Fin ℓ → ℝ |
        (∃ b : ℤ, |(∑ i, (a i : ℝ) * y i) - (b : ℝ)| < δ) ∧
        (∀ i, y i ∈ Set.Ico (0:ℝ) 1)}
      = ENNReal.ofReal (2 * δ) := by
  obtain ⟨i0, hi0⟩ := ha
  have hℓ : 0 < ℓ := i0.pos
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hℓ)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i0 with he
  set C : Set (Fin n → ℝ) := Set.univ.pi (fun _ : Fin n => Set.Ico (0:ℝ) 1) with hC
  set φ : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => (a i0 : ℝ) * p.1 + ∑ j : Fin n, (a (i0.succAbove j) : ℝ) * p.2 j with hφ
  set A : Set (ℝ × (Fin n → ℝ)) :=
    {p | p.2 ∈ C ∧ p.1 ∈ Set.Ico (0:ℝ) 1 ∧ ∃ b : ℤ, |φ p - (b : ℝ)| < δ} with hA
  have hCmeas : MeasurableSet C := by
    rw [hC]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have hAmeas : MeasurableSet A := by
    rw [hA]
    refine (hCmeas.preimage measurable_snd).inter ?_
    refine (MeasurableSet.preimage (measurableSet_Ico (a := (0:ℝ)) (b := 1)) measurable_fst).inter ?_
    change MeasurableSet {p : ℝ × (Fin n → ℝ) | ∃ b : ℤ, |φ p - (b : ℝ)| < δ}
    rw [show {p : ℝ × (Fin n → ℝ) | ∃ b : ℤ, |φ p - (b : ℝ)| < δ}
        = φ ⁻¹' (⋃ b : ℤ, Set.Ioo ((b:ℝ) - δ) ((b:ℝ) + δ)) from by
      ext p; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_Ioo, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b, hb⟩; rw [abs_lt] at hb; exact ⟨b, by constructor <;> linarith [hb.1, hb.2]⟩
      · rintro ⟨b, hb⟩; exact ⟨b, by rw [abs_lt]; constructor <;> linarith [hb.1, hb.2]⟩]
    exact (isOpen_iUnion (fun b : ℤ => isOpen_Ioo)).measurableSet.preimage hφc.measurable
  have hS : {y : Fin (n + 1) → ℝ |
        (∃ b : ℤ, |(∑ i, (a i : ℝ) * y i) - (b : ℝ)| < δ) ∧
        (∀ i, y i ∈ Set.Ico (0:ℝ) 1)} = e ⁻¹' A := by
    ext y
    have hey : e y = (y i0, fun j : Fin n => y (i0.succAbove j)) := rfl
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hA, hC, hφ, Set.mem_univ_pi]
    rw [hey]
    simp only [Set.mem_Ico]
    rw [Fin.sum_univ_succAbove, Fin.forall_iff_succAbove]
    tauto
  rw [hS, (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i0).measure_preimage_equiv A]
  change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) A = ENNReal.ofReal (2 * δ)
  rw [Measure.prod_apply_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))) hAmeas]
  have hint : ∀ y : Fin n → ℝ,
      MeasureTheory.volume ((fun x : ℝ => (x, y)) ⁻¹' A)
        = C.indicator (fun _ => ENNReal.ofReal (2 * δ)) y := by
    intro y
    by_cases hy : y ∈ C
    · have hset : (fun x : ℝ => (x, y)) ⁻¹' A = {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧
          ∃ b : ℤ, |(a i0 : ℝ) * t + (∑ j : Fin n, (a (i0.succAbove j) : ℝ) * y j) - (b : ℝ)| < δ} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hA, hφ]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨hy, h1, h2⟩
      rw [hset, volume_dist_int_mul_Ico (a i0)
        (∑ j : Fin n, (a (i0.succAbove j) : ℝ) * y j) δ hi0 hδ0 hδ1,
        Set.indicator_of_mem hy]
    · have hset : (fun x : ℝ => (x, y)) ⁻¹' A = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ht
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hA, hφ] at ht
        exact hy ht.1
      rw [hset, MeasureTheory.measure_empty, Set.indicator_of_notMem hy]
  rw [MeasureTheory.lintegral_congr hint]
  rw [MeasureTheory.lintegral_indicator_const hCmeas]
  have hCvol : MeasureTheory.volume C = 1 := by
    rw [hC, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Ico]
  rw [hCvol, mul_one]

/-- **Main lemma.**  For a non-zero integer row vector `a`, the measure of the set of `ℓ × m`
matrices with entries in `[0,1)` such that every column satisfies the diophantine condition
`dist (∑ aᵢ xᵢⱼ , ℤ) < δ` equals `(2δ)^m`, for `δ ≤ 1/2`. -/
theorem volume_linearForm_cylinder {ℓ m : ℕ} {a : Fin ℓ → ℤ} (ha : ∃ i, a i ≠ 0) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    MeasureTheory.volume {x : Fin ℓ → Fin m → ℝ |
        (∀ j, ∃ b : ℤ, |(∑ i, (a i : ℝ) * x i j) - (b : ℝ)| < δ) ∧
        (∀ i j, x i j ∈ Set.Ico (0:ℝ) 1)}
      = ENNReal.ofReal ((2 * δ) ^ m) := by
  set A : Set (Fin ℓ → ℝ) := {y | (∃ b : ℤ, |(∑ i, (a i : ℝ) * y i) - (b : ℝ)| < δ) ∧
    (∀ i, y i ∈ Set.Ico (0:ℝ) 1)} with hA
  have hAvol : MeasureTheory.volume A = ENNReal.ofReal (2 * δ) :=
    volume_singleColumn a ha hδ0 hδ1
  have hAmeas : MeasurableSet A := measurableSet_linearForm_column a
  have hS : {x : Fin ℓ → Fin m → ℝ |
        (∀ j, ∃ b : ℤ, |(∑ i, (a i : ℝ) * x i j) - (b : ℝ)| < δ) ∧
        (∀ i j, x i j ∈ Set.Ico (0:ℝ) 1)}
      = (fun (f : Fin ℓ → Fin m → ℝ) (j : Fin m) (i : Fin ℓ) => f i j) ⁻¹'
          (Set.univ.pi (fun _ : Fin m => A)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi, hA]
    constructor
    · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, fun i => h2 i j⟩
    · intro h; exact ⟨fun j => (h j).1, fun i j => (h j).2 i⟩
  have hmp : MeasureTheory.MeasurePreserving
      (fun (f : Fin ℓ → Fin m → ℝ) (j : Fin m) (i : Fin ℓ) => f i j) volume volume :=
    measurePreserving_pi_comm (μ := (volume : Measure ℝ))
  rw [hS, hmp.measure_preimage
    (MeasurableSet.nullMeasurableSet (MeasurableSet.univ_pi (fun _ => hAmeas)))]
  rw [MeasureTheory.volume_pi_pi]
  rw [show (∏ _ : Fin m, MeasureTheory.volume A) = (MeasureTheory.volume A) ^ m from by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  rw [hAvol, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2 * δ)]

end Commons.Analysis.Measure
