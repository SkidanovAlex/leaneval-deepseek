import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

/-- Tail bound for the convergent `r`-power series from `X₀` onward: for `r > 1` and
`X₀ ≥ 2`, `∑'_{m} (X₀+m)^(-r) ≤ (2^(r-1)/(r-1)) · X₀^(1-r)`. -/
theorem tail_rpow_nat_le {r : ℝ} (hr : 1 < r) {X₀ : ℕ} (hX₀ : 2 ≤ X₀) :
    (∑' m : ℕ, ((X₀ + m : ℕ) : ℝ) ^ (-r)) ≤
      ((2 : ℝ) ^ (r - 1) / (r - 1)) * (X₀ : ℝ) ^ (1 - r) := by
  let f : ℝ → ℝ := fun x => x ^ (-r)
  let N : ℕ := X₀ - 1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    dsimp [N]
    exact_mod_cast (by omega : (0 : ℕ) < X₀ - 1)
  have hanti0 : AntitoneOn f (Set.Ioi (0 : ℝ)) := by
    dsimp [f]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -r) (by linarith : -r ≤ 0)
  have hanti : AntitoneOn f (Set.Ici (N : ℝ)) := hanti0.mono (by
    intro x hx
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hNpos (Set.mem_Ici.mp hx)))
  have hintegrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-r)) (Set.Ioi (N : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (a := -r) (by linarith : -r < -1) hNpos
  have hnonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ f t := by
    intro t ht
    dsimp [f]
    exact Real.rpow_nonneg (le_of_lt (lt_trans hNpos (Set.mem_Ioi.mp ht))) (-r)
  have hmain := AntitoneOn.tsum_comp_add_le_integral (f := f) (N := N) hanti hintegrable hnonneg
  have hInt : (∫ x in Set.Ioi (N : ℝ), f x) = (N : ℝ) ^ (1 - r) / (r - 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -r) (by linarith : -r < -1) (c := (N : ℝ)) hNpos
    dsimp [f] at h ⊢
    rw [h]
    rw [show -r + 1 = 1 - r by ring]
    rw [show 1 - r = -(r - 1) by ring]
    have hr_ne : r - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
    field_simp [hr_ne]
  have hX₀gt : (0 : ℝ) < (X₀ : ℝ) := by exact_mod_cast (by omega : 0 < X₀)
  have hXhalf_pos : (0 : ℝ) < (X₀ : ℝ) / 2 := div_pos hX₀gt (by norm_num)
  have hXhalf : (X₀ : ℝ) / 2 ≤ (N : ℝ) := by
    have h1leX : (1 : ℕ) ≤ X₀ := by omega
    rw [show (N : ℝ) = (X₀ : ℝ) - 1 by
      dsimp [N]
      rw [Nat.cast_sub h1leX]
      norm_num]
    have hX2 : (2 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX₀
    nlinarith
  have hpow_ineq : (N : ℝ) ^ (1 - r) ≤ ((X₀ : ℝ) / 2) ^ (1 - r) :=
    Real.rpow_le_rpow_of_nonpos hXhalf_pos hXhalf (by linarith : 1 - r ≤ 0)
  have hpow_eq : ((X₀ : ℝ) / 2) ^ (1 - r) = (2 : ℝ) ^ (r - 1) * (X₀ : ℝ) ^ (1 - r) := by
    have hx0 : (0 : ℝ) ≤ (X₀ : ℝ) := le_of_lt hX₀gt
    calc
      ((X₀ : ℝ) / 2) ^ (1 - r) = (X₀ : ℝ) ^ (1 - r) / (2 : ℝ) ^ (1 - r) := by
        exact Real.div_rpow hx0 (by norm_num : (0 : ℝ) ≤ 2) (1 - r)
      _ = (X₀ : ℝ) ^ (1 - r) * (2 : ℝ) ^ (r - 1) := by
        rw [div_eq_mul_inv]
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 - r)]
        rw [show -(1 - r) = r - 1 by ring]
      _ = (2 : ℝ) ^ (r - 1) * (X₀ : ℝ) ^ (1 - r) := by rw [mul_comm]
  calc
    (∑' m : ℕ, ((X₀ + m : ℕ) : ℝ) ^ (-r)) = ∑' m : ℕ, f ((X₀ + m : ℕ) : ℝ) := by rfl
    _ = ∑' n : ℕ, f (↑(n + N + 1)) := by
      apply tsum_congr
      intro m
      congr 1
      have hterm : (X₀ + m : ℕ) = (m + N + 1 : ℕ) := by
        dsimp [N]
        omega
      exact_mod_cast hterm
    _ ≤ ∫ x in Set.Ioi (N : ℝ), f x := hmain
    _ = (N : ℝ) ^ (1 - r) / (r - 1) := hInt
    _ ≤ ((2 : ℝ) ^ (r - 1) / (r - 1)) * (X₀ : ℝ) ^ (1 - r) := by
      have hrpos : 0 < r - 1 := sub_pos.mpr hr
      have hpow_ineq2 : (N : ℝ) ^ (1 - r) ≤ (2 : ℝ) ^ (r - 1) * (X₀ : ℝ) ^ (1 - r) :=
        hpow_ineq.trans hpow_eq.le
      calc
        (N : ℝ) ^ (1 - r) / (r - 1) ≤ (2 : ℝ) ^ (r - 1) * (X₀ : ℝ) ^ (1 - r) / (r - 1) :=
          div_le_div_of_nonneg_right hpow_ineq2 hrpos.le
        _ = ((2 : ℝ) ^ (r - 1) / (r - 1)) * (X₀ : ℝ) ^ (1 - r) := by
          rw [div_mul_eq_mul_div]



end Commons.Analysis.Asymptotics