import Mathlib
import Submission.Commons.Analysis.Measure.volume_linearForm_cylinder

namespace Commons.Analysis.Measure

open MeasureTheory Set ENNReal
open scoped ENNReal

/-- For `k : ℤ` and `A ≥ 0`, the condition `|k| ≤ A` is equivalent to membership of the integer
interval `[-⌊A⌋, ⌊A⌋]`. -/
private lemma mem_Icc_floor_iff {A : ℝ} (_hA : 0 ≤ A) (k : ℤ) :
    k ∈ Finset.Icc (-⌊A⌋) ⌊A⌋ ↔ |(k : ℝ)| ≤ A := by
  rw [Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h1' : ((-⌊A⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
      have hfl : ((-⌊A⌋ : ℤ) : ℝ) = -(⌊A⌋ : ℝ) := by push_cast; ring
      have := Int.floor_le A
      linarith
    · have h2' : (k : ℝ) ≤ (⌊A⌋ : ℝ) := by exact_mod_cast h2
      have := Int.floor_le A
      linarith
  · rintro ⟨h1, h2⟩
    have h2' : (k : ℝ) ≤ A := h2
    constructor
    · have : ((-k : ℤ) : ℝ) ≤ A := by push_cast; linarith
      have hk := (Int.le_floor (a := A) (z := -k)).mpr this
      linarith
    · exact (Int.le_floor (a := A) (z := k)).mpr h2'

/-- The integer interval `[-⌊A⌋, ⌊A⌋]` has at most `2 * A + 1` elements (for `A ≥ 0`). -/
private lemma card_Icc_abs_le {A : ℝ} (hA : 0 ≤ A) :
    ((Finset.Icc (-⌊A⌋) ⌊A⌋ : Finset ℤ).card : ℝ) ≤ 2 * A + 1 := by
  have hcard : (Finset.Icc (-⌊A⌋) ⌊A⌋ : Finset ℤ).card = (2 * ⌊A⌋ + 1).toNat := by
    rw [Int.card_Icc]; ring_nf
  rw [hcard]
  have h1 : ((2 * ⌊A⌋ + 1 : ℤ).toNat : ℝ) = 2 * (⌊A⌋ : ℝ) + 1 := by
    have hpos : (0:ℤ) ≤ 2 * ⌊A⌋ + 1 := by
      have hk : (0:ℤ) ≤ ⌊A⌋ := Int.floor_nonneg.mpr hA
      linarith
    have hz : ((2 * ⌊A⌋ + 1 : ℤ).toNat : ℤ) = 2 * ⌊A⌋ + 1 := Int.toNat_of_nonneg hpos
    have hzr : ((2 * ⌊A⌋ + 1 : ℤ).toNat : ℝ) = ((2 * ⌊A⌋ + 1 : ℤ) : ℝ) := by exact_mod_cast hz
    rw [hzr]; push_cast; ring
  rw [h1]
  have := Int.floor_le A
  linarith

/-- The number of integer vectors `a : Fin ℓ → ℤ` with `|a i| ≤ A` for all `i` is at most
`(2 * A + 1) ^ ℓ`. -/
private lemma card_piFinset_le {ℓ : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    ((Fintype.piFinset (fun _ : Fin ℓ => Finset.Icc (-⌊A⌋) ⌊A⌋)).card : ℝ) ≤ (2 * A + 1) ^ ℓ := by
  have hfac : ∀ _i : Fin ℓ, ((Finset.Icc (-⌊A⌋) ⌊A⌋ : Finset ℤ).card : ℝ) ≤ 2 * A + 1 :=
    fun _ => card_Icc_abs_le hA
  calc ((Fintype.piFinset (fun _ : Fin ℓ => Finset.Icc (-⌊A⌋) ⌊A⌋)).card : ℝ)
      = ∏ _i : Fin ℓ, ((Finset.Icc (-⌊A⌋) ⌊A⌋ : Finset ℤ).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ _i : Fin ℓ, (2 * A + 1) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact hfac i
    _ = (2 * A + 1) ^ ℓ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem volume_bad_union_le {ℓ m : ℕ} {A δ : ℝ} (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    MeasureTheory.volume {c : Fin ℓ → Fin m → ℝ |
        (∃ a : Fin ℓ → ℤ, (∃ i, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧
          ∃ b : Fin m → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ) ∧
        (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)}
      ≤ ENNReal.ofReal (((2 * A + 1) ^ ℓ) * ((2 * δ) ^ m)) := by
  classical
  -- The candidate set of coefficient vectors, restricted to those of length bound `A`.
  let G : (Fin ℓ → ℤ) → Set (Fin ℓ → Fin m → ℝ) := fun a =>
    {c : Fin ℓ → Fin m → ℝ |
      (∃ b : Fin m → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ) ∧
      (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)}
  set F : Finset (Fin ℓ → ℤ) := Fintype.piFinset (fun _ : Fin ℓ => Finset.Icc (-⌊A⌋) ⌊A⌋) with hF
  set F' : Finset (Fin ℓ → ℤ) := F.filter (fun a => ∃ i, a i ≠ 0) with hF'
  -- Cardinality of the surviving coefficient vectors.
  have hcardF' : (F'.card : ℝ) ≤ (2 * A + 1) ^ ℓ := by
    have h1 : (F'.card : ℝ) ≤ (F.card : ℝ) := by
      have := Finset.card_filter_le F (fun a : Fin ℓ → ℤ => ∃ i, a i ≠ 0)
      exact_mod_cast this
    have h2 : (F.card : ℝ) ≤ (2 * A + 1) ^ ℓ := by
      rw [hF]; exact card_piFinset_le hA
    linarith
  -- Each individual bad set has measure at most `(2δ)^m`.
  have hGA : ∀ a : Fin ℓ → ℤ, (∃ i, a i ≠ 0) → MeasureTheory.volume (G a)
      ≤ ENNReal.ofReal ((2 * δ) ^ m) := by
    intro a ha
    have hkey := volume_linearForm_cylinder (ℓ := ℓ) (m := m) ha hδ0 hδ1
    have hset : G a = {c : Fin ℓ → Fin m → ℝ |
        (∀ j, ∃ b : ℤ, |(∑ i, (a i : ℝ) * c i j) - (b : ℝ)| < δ) ∧
        (∀ i j, c i j ∈ Set.Ico (0 : ℝ) 1)} := by
      ext c
      simp only [G]
      constructor
      · rintro ⟨⟨b, hb⟩, hbox⟩; exact ⟨fun j => ⟨b j, hb j⟩, hbox⟩
      · rintro ⟨h, hbox⟩
        exact ⟨⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩, hbox⟩
    rw [hset]; exact le_of_eq hkey
  -- The bad set is contained in the finite union of the individual bad sets.
  have hSub : {c : Fin ℓ → Fin m → ℝ |
        (∃ a : Fin ℓ → ℤ, (∃ i, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧
          ∃ b : Fin m → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ) ∧
        (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)}
      ⊆ ⋃ a ∈ F', G a := by
    intro c hc
    obtain ⟨⟨a, hane, habnd, hb⟩, hbox⟩ := hc
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rw [hF']
      rw [Finset.mem_filter]
      refine ⟨?_, hane⟩
      rw [hF]
      rw [Fintype.mem_piFinset]
      intro i
      rw [mem_Icc_floor_iff hA]
      exact habnd i
    · exact ⟨hb, hbox⟩
  calc MeasureTheory.volume {c : Fin ℓ → Fin m → ℝ |
        (∃ a : Fin ℓ → ℤ, (∃ i, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧
          ∃ b : Fin m → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ) ∧
        (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)}
      ≤ MeasureTheory.volume (⋃ a ∈ F', G a) := measure_mono hSub
    _ ≤ ∑ a ∈ F', MeasureTheory.volume (G a) := MeasureTheory.measure_biUnion_finset_le F' G
    _ ≤ ∑ _a ∈ F', ENNReal.ofReal ((2 * δ) ^ m) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hGA a (Finset.mem_filter.mp ha).2
    _ = (F'.card : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((2 * A + 1) ^ ℓ) * ENNReal.ofReal ((2 * δ) ^ m) := by
        apply mul_le_mul_of_nonneg_right
        · rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hcardF'
        · positivity
    _ = ENNReal.ofReal (((2 * A + 1) ^ ℓ) * ((2 * δ) ^ m)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

end Commons.Analysis.Measure
