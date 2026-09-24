import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card

namespace Commons.Analysis.Metric

set_option autoImplicit false

/-- Two reals with equal integer parts are at distance strictly less than one. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : (⌊x⌋ : ℤ) = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

/-- Coercing a natural number to `ℝ` directly equals coercing it via `ℤ`. -/
private lemma cast_nat_int_real (n : ℕ) : (n : ℝ) = ((n : ℤ) : ℝ) := by
  norm_num

/-- At most `T + 1` points of the interval `[0, T]` (`0 ≤ T`) can be pairwise at
distance at least `1`.  Proof: the floors `⌊x⌋` are pairwise distinct integers
lying in `{0, …, ⌊T⌋}`. -/
theorem one_separated_real_card_le (A : Finset ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hA : ∀ x ∈ A, 0 ≤ x ∧ x ≤ T)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) : (A.card : ℝ) ≤ T + 1 := by
  classical
  let M : ℕ := (⌊T⌋ : ℤ).toNat
  let f : ℝ → ℕ := fun x => (⌊x⌋ : ℤ).toNat
  have hinj : (A : Set ℝ).InjOn f := by
    intro x hx y hy hfxy
    by_contra hne
    have hsep' : 1 ≤ |x - y| := hsep x hx y hy hne
    have hfx0 : 0 ≤ (⌊x⌋ : ℤ) := (Int.floor_nonneg).2 (hA x hx).1
    have hfy0 : 0 ≤ (⌊y⌋ : ℤ) := (Int.floor_nonneg).2 (hA y hy).1
    have hflooreq : (⌊x⌋ : ℤ) = ⌊y⌋ := by
      have hcast := congrArg (fun n : ℕ => (n : ℤ)) hfxy
      rwa [Int.toNat_of_nonneg hfx0, Int.toNat_of_nonneg hfy0] at hcast
    have hlt : |x - y| < 1 := abs_sub_lt_one_of_floor_eq hflooreq
    linarith
  have himage_le : (A.image f).card ≤ M + 1 := by
    have hsubset : A.image f ⊆ Finset.range (M + 1) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
      simp only [f, Finset.mem_range]
      have hleT : (⌊x⌋ : ℤ) ≤ ⌊T⌋ := Int.floor_mono (hA x hx).2
      have hleM : (⌊x⌋ : ℤ).toNat ≤ M := by
        dsimp [M]
        exact Int.toNat_le_toNat hleT
      omega
    simpa using Finset.card_le_card hsubset
  have hcard : A.card ≤ M + 1 := by
    calc
      A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ M + 1 := himage_le
  have hRreal : (A.card : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast hcard
  have hMleT : (M : ℝ) ≤ T := by
    dsimp [M]
    calc
      (((⌊T⌋ : ℤ).toNat : ℕ) : ℝ) = (((⌊T⌋ : ℤ).toNat : ℤ) : ℝ) := by
        rw [cast_nat_int_real]
      _ = (⌊T⌋ : ℝ) := by
        have hfloorT0 : 0 ≤ (⌊T⌋ : ℤ) := (Int.floor_nonneg).2 hT
        rw [Int.toNat_of_nonneg hfloorT0]
      _ ≤ T := Int.floor_le T
  calc
    (A.card : ℝ) ≤ (M : ℝ) + 1 := hRreal
    _ ≤ T + 1 := by linarith

end Commons.Analysis.Metric