import Mathlib
import Submission.Work.HP.LsetAux.GridDefs
import Submission.Work.HP.LsetAux.abs_rNorm_sub_le
import Submission.Work.HP.LsetAux.rNorm_le_sqrt_card_mul

/-!
# The grid is a net on the unit sphere

For every unit vector `x : Fin (n+1) → ℝ` and every `N ≥ 2(n+1)` there is a nonzero integer
point `z` in the box `∏ᵢ [-N,N]` such that the rescaled grid point `gw n N z = gy n N z / ‖gy n N z‖`
is a unit vector within distance `2√(n+1)/N` of `x`.

This is the finite `(1/N)`-net used in the proof that `Lset` has measure zero: rounding each
coordinate of `x` to the nearest multiple of `1/N` gives `y = gy n N z` with `‖y - x‖ ≤ √(n+1)/(2N)`
and `‖y‖ ≥ 3/4`; normalising `y` then costs another `‖y‖ - 1 ≤ √(n+1)/(2N)`.
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP.LsetAux

/-- Coordinatewise rounding: for `|x i| ≤ 1`, the integer point
`z i = ⌊N * x i + 1/2⌋` lies in the box `gbox n N` and satisfies `|z i - N * x i| ≤ 1/2`,
i.e. `|z i / N - x i| ≤ 1/(2N)`. -/
lemma exists_grid_close_aux (n N : ℕ) {x : Fin (n + 1) → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ∃ z ∈ gbox n N, ∀ i, |(z i : ℝ) - (N : ℝ) * x i| ≤ 1 / 2 := by
  refine ⟨fun i => ⌊(N : ℝ) * x i + 1 / 2⌋, ?_, ?_⟩
  · rw [gbox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    constructor
    · change -(N : ℤ) ≤ ⌊(N : ℝ) * x i + 1 / 2⌋
      rw [Int.le_floor]
      have hxi : -(1 : ℝ) ≤ x i := by
        have := hx i; rw [abs_le] at this; linarith [this.1]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · change ⌊(N : ℝ) * x i + 1 / 2⌋ ≤ (N : ℤ)
      rw [Int.floor_le_iff]
      have hxi : x i ≤ 1 := by
        have := hx i; rw [abs_le] at this; exact this.2
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · intro i
    have h1 := Int.floor_le ((N : ℝ) * x i + 1 / 2)
    have h2 := Int.lt_floor_add_one ((N : ℝ) * x i + 1 / 2)
    rw [abs_le]
    constructor <;> linarith

theorem exists_grid_net (n N : ℕ) (hN : 2 * (n + 1) ≤ N) {x : Fin (n + 1) → ℝ}
    (hx : rNorm x = 1) :
    ∃ z ∈ gbox n N, z ≠ 0 ∧ rNorm (gw n N z) = 1 ∧
      rNorm (x - gw n N z) ≤ 2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ) := by
  have hNnz : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- a grid point whose coordinates are close to those of `x`
  obtain ⟨z, hzmem, hcoord⟩ := exists_grid_close_aux n N (fun i => by
    have := abs_apply_le_rNorm x i
    rw [hx] at this; exact this)
  -- consequently `gy n N z` itself is close to `x`
  have hcoordy : ∀ i, |(gy n N z - x) i| ≤ 1 / (2 * (N : ℝ)) := by
    intro i
    have hyi : (gy n N z - x) i = ((z i : ℝ) - (N : ℝ) * x i) / (N : ℝ) := by
      simp only [gy, Pi.sub_apply]
      field_simp
    rw [hyi, abs_div, abs_of_pos hNpos]
    rw [div_le_iff₀ hNpos]
    have hb : (1 / (2 * (N : ℝ))) * (N : ℝ) = 1 / 2 := by field_simp
    rw [hb]
    exact hcoord i
  have hclose : rNorm (gy n N z - x) ≤ Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) := by
    have ha : 0 ≤ 1 / (2 * (N : ℝ)) := by positivity
    have h := rNorm_le_sqrt_card_mul (u := gy n N z - x) (a := 1 / (2 * (N : ℝ))) ha hcoordy
    have hval : Real.sqrt (Fintype.card (Fin (n + 1)) : ℝ) * (1 / (2 * (N : ℝ)))
        = Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) := by
      rw [Fintype.card_fin]
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hc, mul_one_div]
    rwa [hval] at h
  -- `‖gy‖` is within `1/4` of `1`
  have hc1 : |rNorm (gy n N z) - 1| ≤ Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) := by
    have h := abs_rNorm_sub_le (gy n N z) x
    rw [hx] at h
    exact h.trans hclose
  have hquarter : Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
    have hNm : 2 * ((n : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsle : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩
    nlinarith [hNm, hsle]
  have hry_ge : (3 : ℝ) / 4 ≤ rNorm (gy n N z) := by
    have := (abs_le.mp hc1).1
    linarith
  have hry_pos : 0 < rNorm (gy n N z) := by linarith
  have hynz : gy n N z ≠ 0 := by
    intro h
    have : rNorm (gy n N z) = 0 := by rw [h]; simp [rNorm]
    linarith
  have hznz : z ≠ 0 := fun hz => hynz ((gy_eq_zero_iff hNnz z).mpr hz)
  -- normalising `gy n N z` costs at most `√(n+1)/(2N)` as well
  have hgw_sub : rNorm (gy n N z - gw n N z)
      ≤ Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) := by
    have hc : 0 < rNorm (gy n N z) := hry_pos
    have heq : gy n N z - gw n N z = (1 - 1 / rNorm (gy n N z)) • gy n N z := by
      rw [gw]; simp only [sub_smul, one_smul]
    rw [heq, rNorm_smul']
    have hstep : |1 - 1 / rNorm (gy n N z)| * rNorm (gy n N z)
        = |rNorm (gy n N z) - 1| := by
      have hmul : (1 - 1 / rNorm (gy n N z)) * rNorm (gy n N z)
          = rNorm (gy n N z) - 1 := by field_simp
      calc |1 - 1 / rNorm (gy n N z)| * rNorm (gy n N z)
          = |1 - 1 / rNorm (gy n N z)| * |rNorm (gy n N z)| := by rw [abs_of_pos hc]
        _ = |(1 - 1 / rNorm (gy n N z)) * rNorm (gy n N z)| := (abs_mul _ _).symm
        _ = |rNorm (gy n N z) - 1| := by rw [hmul]
    rw [hstep]
    exact hc1
  refine ⟨z, hzmem, hznz, rNorm_gw hNnz hznz, ?_⟩
  have hsplit : x - gw n N z = (x - gy n N z) + (gy n N z - gw n N z) := by abel
  rw [hsplit]
  have h1 : rNorm (x - gy n N z) ≤ Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) := by
    rw [rNorm_sub_comm]; exact hclose
  calc rNorm ((x - gy n N z) + (gy n N z - gw n N z))
      ≤ rNorm (x - gy n N z) + rNorm (gy n N z - gw n N z) := rNorm_add_le _ _
    _ ≤ Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) + Real.sqrt ((n : ℝ) + 1) / (2 * (N : ℝ)) :=
          add_le_add h1 hgw_sub
    _ = Real.sqrt ((n : ℝ) + 1) / (N : ℝ) := by field_simp; ring
    _ ≤ 2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ) := by
          have hnn : 0 ≤ Real.sqrt ((n : ℝ) + 1) / (N : ℝ) := by positivity
          rw [mul_div_assoc]
          linarith

end Work.HP.LsetAux
