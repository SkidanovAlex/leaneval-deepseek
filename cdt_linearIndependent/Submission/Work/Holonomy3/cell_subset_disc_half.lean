import Mathlib
import Submission.Work.Holonomy3.lowdiscCells
import Submission.Work.Holonomy3.disc_shift_two

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- **Geometry of a grid cell around a real-normalised lattice point.**  With the grid denominator
`g = ⌊R⌋ + 1` (so that `R < g ≤ R + 1`) and a lattice point `k/R` whose coordinates satisfy
`k j ≤ ⌊R⌋`, every point `u` of the cell `cell d g k = ∏_j [k_j/g, (k_j+1)/g)` lies in `[0,1]^d`
and is within `1/R` of `k/R`.

The two one-sided bounds are
`u j - k j/R < (k j + 1)/g - k j/R = (R - k j (g - R))/(g R) ≤ R/(g R) = 1/g ≤ 1/R` and
`k j/R - u j ≤ k j/R - k j/g = k j (g - R)/(R g) ≤ ⌊R⌋ (g - R)/(R g) ≤ R/(R g) = 1/g ≤ 1/R`
(using `g - R ≤ 1`, `k j ≤ ⌊R⌋ ≤ R`). -/
lemma cell_dist_le_inv {d : ℕ} {R : ℝ} (hR : 1 ≤ R) {k : Fin d → ℕ}
    (hk : ∀ j, k j ≤ Nat.floor R) {u : Fin d → ℝ}
    (hu : u ∈ cell d (Nat.floor R + 1) k) :
    (∀ j, u j ∈ Set.Icc 0 1) ∧ (∀ j, |u j - (k j : ℝ) / R| ≤ R⁻¹) := by
  rw [mem_cell] at hu
  have hRpos : 0 < R := by linarith
  have hfl : ((Nat.floor R : ℕ) : ℝ) ≤ R := Nat.floor_le (le_of_lt hRpos)
  have hD : (((Nat.floor R + 1 : ℕ) : ℝ)) = (Nat.floor R : ℝ) + 1 := by push_cast; ring
  have hR_lt : R < (((Nat.floor R + 1 : ℕ) : ℝ)) := by
    rw [hD]; exact Nat.lt_floor_add_one R
  have hposD : (0 : ℝ) < (((Nat.floor R + 1 : ℕ) : ℝ)) := by linarith
  have h_inv : (((Nat.floor R + 1 : ℕ) : ℝ))⁻¹ ≤ R⁻¹ := by
    rw [inv_le_inv₀ hposD hRpos]; linarith
  have hdist : ∀ j, |u j - (k j : ℝ) / R| ≤ R⁻¹ := by
    intro j
    obtain ⟨hlo, hhi⟩ := hu j
    have hup : u j - ↑(k j) / R ≤ R⁻¹ := by
      have hstep : u j - ↑(k j) / R
          < (↑(k j) + 1) / ↑(⌊R⌋₊ + 1) - ↑(k j) / R := by linarith
      have heq : (↑(k j) + 1) / ↑(⌊R⌋₊ + 1) - ↑(k j) / R
          = (R - ↑(k j) * (↑(⌊R⌋₊ + 1) - R)) / (↑(⌊R⌋₊ + 1) * R) := by
        rw [div_sub_div (hb := hposD.ne') (hd := hRpos.ne')]
        congr 1
        ring
      rw [heq] at hstep
      have hle : (R - ↑(k j) * (↑(⌊R⌋₊ + 1) - R)) / (↑(⌊R⌋₊ + 1) * R) ≤ R⁻¹ := by
        have hnum : R - ↑(k j) * (↑(⌊R⌋₊ + 1) - R) ≤ R := by
          have : 0 ≤ ↑(k j) * (↑(⌊R⌋₊ + 1) - R) :=
            mul_nonneg (Nat.cast_nonneg _) (by linarith)
          linarith
        have hDR : 0 < ↑(⌊R⌋₊ + 1) * R := mul_pos hposD hRpos
        calc (R - ↑(k j) * (↑(⌊R⌋₊ + 1) - R)) / (↑(⌊R⌋₊ + 1) * R)
            ≤ R / (↑(⌊R⌋₊ + 1) * R) := div_le_div_of_nonneg_right hnum (le_of_lt hDR)
          _ = (↑(⌊R⌋₊ + 1))⁻¹ := by field_simp
          _ ≤ R⁻¹ := h_inv
      linarith
    have hdn : ↑(k j) / R - u j ≤ R⁻¹ := by
      have hle1 : ↑(⌊R⌋₊ + 1) - R ≤ 1 := by rw [hD]; linarith
      have hDmR : 0 ≤ ↑(⌊R⌋₊ + 1) - R := by linarith
      have hstep : ↑(k j) / R - u j ≤ ↑(k j) / R - ↑(k j) / ↑(⌊R⌋₊ + 1) := by linarith
      have heq : ↑(k j) / R - ↑(k j) / ↑(⌊R⌋₊ + 1)
          = ↑(k j) * (↑(⌊R⌋₊ + 1) - R) / (R * ↑(⌊R⌋₊ + 1)) := by
        rw [div_sub_div (hb := hRpos.ne') (hd := hposD.ne')]
        congr 1
        ring
      rw [heq] at hstep
      have hkjfl : (↑(k j) : ℝ) ≤ ↑⌊R⌋₊ := by exact_mod_cast hk j
      have hRD : 0 < R * ↑(⌊R⌋₊ + 1) := mul_pos hRpos hposD
      have hnum : ↑(k j) * (↑(⌊R⌋₊ + 1) - R) ≤ R * 1 := by
        calc ↑(k j) * (↑(⌊R⌋₊ + 1) - R) ≤ ↑⌊R⌋₊ * (↑(⌊R⌋₊ + 1) - R) :=
              mul_le_mul_of_nonneg_right hkjfl hDmR
          _ ≤ R * (↑(⌊R⌋₊ + 1) - R) := mul_le_mul_of_nonneg_right hfl hDmR
          _ ≤ R * 1 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hRpos)
      calc ↑(k j) / R - u j
          ≤ ↑(k j) * (↑(⌊R⌋₊ + 1) - R) / (R * ↑(⌊R⌋₊ + 1)) := hstep
        _ ≤ R * 1 / (R * ↑(⌊R⌋₊ + 1)) := div_le_div_of_nonneg_right hnum (le_of_lt hRD)
        _ = (↑(⌊R⌋₊ + 1))⁻¹ := by field_simp
        _ ≤ R⁻¹ := h_inv
    rw [abs_le]
    exact ⟨by linarith, hup⟩
  refine ⟨?_, hdist⟩
  intro j
  obtain ⟨hlo, hhi⟩ := hu j
  refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) (le_of_lt hposD)) hlo, ?_⟩
  have hk1 : ((k j : ℝ) + 1) ≤ (((Nat.floor R + 1 : ℕ) : ℝ)) := by
    have hN : k j + 1 ≤ Nat.floor R + 1 := by have := hk j; omega
    rw [hD]; push_cast; exact_mod_cast hN
  have h3 : ((k j : ℝ) + 1) / (((Nat.floor R + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one hposD]; exact hk1
  linarith

/-- **A grid cell around a high-discrepancy lattice point lies in the halved tail event.**
The grid denominator here is `g = ⌊R⌋ + 1` with `R` real, so `R < g`; the lattice point is the
real-normalised centre `k/R`.

For `k : Fin d → ℕ` with all `k j ≤ ⌊R⌋` the half-open cell
`cell d g k = ∏_j [k_j/g, (k_j+1)/g)` lies in `[0,1)^d` and every `u` in it satisfies
`|u j - k j / R| < 1/R`: indeed `u j - k j/R < 1/g < 1/R` (because `R < g`), while
`k j / R - u j ≤ k j (g - R) / (R g) ≤ ⌊R⌋ (g - R) / (R g) < 1/R` (because `g - R < 1`).  Hence by
`Work.Holonomy3.disc_shift_two` (shift estimate with constant `2`) applied with `η = 1/R`, every
`u` in the cell satisfies `disc u ≥ disc (k/R) - 2/R ≥ ε - 2/R - 1/d` (using
`Work.Holonomy3.disc_shift_lipschitz` if the extra `1/d` is convenient), and since
`hbig : 4 (1/R + 1/d) ≤ ε` gives `2/R + 1/d ≤ ε/2`, we get `disc u ≥ ε/2`.  So a high-discrepancy
lattice point `k/R` forces its cell into the halved tail event `{disc ≥ ε/2}`. -/
lemma cell_subset_disc_half {d : ℕ} (hd : 0 < d) {R ε : ℝ} (hR : 1 ≤ R)
    (hbig : 4 * (R⁻¹ + (d : ℝ)⁻¹) ≤ ε) {k : Fin d → ℕ}
    (hk : ∀ j, k j ≤ Nat.floor R)
    (hbad : ε ≤ Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / R)) :
    Work.Holonomy3.cell d (Nat.floor R + 1) k ⊆ {u : Fin d → ℝ | ε / 2 ≤ Submission.CDT.Discrepancy.disc u} := by
  intro u hu
  show ε / 2 ≤ disc u
  obtain ⟨huI, hdist⟩ := cell_dist_le_inv hR hk hu
  have hRpos : 0 < R := by linarith
  have htI : ∀ j : Fin d, (k j : ℝ) / R ∈ Set.Icc 0 1 := by
    intro j
    refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hRpos), ?_⟩
    rw [div_le_one hRpos]
    have hkj : (k j : ℝ) ≤ (Nat.floor R : ℝ) := by exact_mod_cast hk j
    have hfl : ((Nat.floor R : ℕ) : ℝ) ≤ R := Nat.floor_le (le_of_lt hRpos)
    linarith
  have hη : 0 ≤ R⁻¹ := inv_nonneg.mpr (le_of_lt hRpos)
  have h1 : disc u ≤ disc (fun j : Fin d => (k j : ℝ) / R) + 2 * R⁻¹ :=
    disc_le_disc_add _ _ htI huI hη hdist
  have h2 : disc (fun j : Fin d => (k j : ℝ) / R) ≤ disc u + 2 * R⁻¹ :=
    disc_le_disc_add _ _ huI htI hη (fun j => by rw [abs_sub_comm]; exact hdist j)
  have hnum : 2 * R⁻¹ ≤ ε / 2 := by
    have hd' : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    have : 4 * R⁻¹ ≤ 4 * (R⁻¹ + (d : ℝ)⁻¹) := by linarith
    linarith
  linarith

end Work.Holonomy3
