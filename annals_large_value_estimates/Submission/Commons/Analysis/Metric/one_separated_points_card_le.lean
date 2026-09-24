import Mathlib

namespace Commons.Analysis.Metric

open Filter
set_option autoImplicit false

/-- Two reals with equal integer parts are at distance strictly less than one. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : (⌊x⌋ : ℤ) = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · -- `-1 < x - y`, i.e. `y - x < 1`
    have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · -- `x - y < 1`
    have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

/-- Coercing a natural number to `ℝ` directly equals coercing it via `ℤ`. -/
private lemma cast_nat_int_real (n : ℕ) : (n : ℝ) = ((n : ℤ) : ℝ) := by
  norm_num

/-- At most `T + 1` points of an interval `[0, T]` (`0 ≤ T`) can be pairwise at distance ≥ 1.
Proof: the floors ⌊t i⌋ are pairwise distinct integers lying in {0, …, ⌊T⌋}. -/
theorem one_separated_points_card_le (T : ℝ) (hT : 0 ≤ T) (R : ℕ) (t : Fin R → ℝ)
    (hIcc : ∀ i, t i ∈ Set.Icc 0 T)
    (hsep : ∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) :
    (R : ℝ) ≤ T + 1 := by
  classical
  let M : ℕ := (⌊T⌋ : ℤ).toNat
  -- embed `i ↦ ⌊t i⌋.toNat` into `Fin (M+1)` (each floor is in `{0, …, ⌊T⌋}`)
  let φ : Fin R → Fin (M + 1) := fun i => ⟨(⌊t i⌋ : ℤ).toNat, by
    have hleT : (⌊t i⌋ : ℤ) ≤ ⌊T⌋ := Int.floor_mono (hIcc i).2
    have hleM : (⌊t i⌋ : ℤ).toNat ≤ M := by
      dsimp [M]
      exact Int.toNat_le_toNat hleT
    omega⟩
  have hφinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have hsep' : 1 ≤ |t i - t j| := hsep i j hne
    have hflooreq : (⌊t i⌋ : ℤ) = ⌊t j⌋ := by
      have htoNat : (⌊t i⌋ : ℤ).toNat = (⌊t j⌋ : ℤ).toNat := by
        simpa [φ] using congrArg Fin.val hij
      have hfi0 : 0 ≤ (⌊t i⌋ : ℤ) := (Int.floor_nonneg).2 (hIcc i).1
      have hfj0 : 0 ≤ (⌊t j⌋ : ℤ) := (Int.floor_nonneg).2 (hIcc j).1
      have hcast := congrArg (fun n : ℕ => (n : ℤ)) htoNat
      rwa [Int.toNat_of_nonneg hfi0, Int.toNat_of_nonneg hfj0] at hcast
    have hlt : |t i - t j| < 1 := abs_sub_lt_one_of_floor_eq hflooreq
    linarith
  have hcard_le : R ≤ M + 1 := by
    have h := Fintype.card_le_of_injective φ hφinj
    simpa using h
  have hRreal : (R : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast hcard_le
  have hMleT : (M : ℝ) ≤ T := by
    dsimp [M]
    have hfloorT0 : 0 ≤ (⌊T⌋ : ℤ) := (Int.floor_nonneg).2 hT
    have htoNatT : ((⌊T⌋ : ℤ).toNat : ℤ) = (⌊T⌋ : ℤ) := Int.toNat_of_nonneg hfloorT0
    calc
      (((⌊T⌋ : ℤ).toNat : ℕ) : ℝ) = (((⌊T⌋ : ℤ).toNat : ℤ) : ℝ) := by
        rw [cast_nat_int_real]
      _ = (⌊T⌋ : ℝ) := by rw [htoNatT]
      _ ≤ T := Int.floor_le T
  calc
    (R : ℝ) ≤ (M : ℝ) + 1 := hRreal
    _ ≤ T + 1 := by linarith

end Commons.Analysis.Metric
