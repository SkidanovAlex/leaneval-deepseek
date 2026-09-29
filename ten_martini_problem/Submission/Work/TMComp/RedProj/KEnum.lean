import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Basic
import Submission.Work.TMComp.RedProj.FourierAux
import Submission.Work.TMComp.RedProj.Extract

open MeasureTheory Filter Topology Set intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-! ## The enumeration `ℤ∖{0} = {1, -1, 2, -2, …}` -/

/-- The standard enumeration of the nonzero integers: `kEnum (2m) = m+1`,
`kEnum (2m+1) = -(m+1)`. -/
def kEnum (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 + 1 : ℕ) : ℤ) else -(((n / 2 + 1 : ℕ) : ℤ))

theorem kEnum_ne_zero (n : ℕ) : kEnum n ≠ 0 := by
  unfold kEnum
  split
  · exact Nat.cast_ne_zero.mpr (by omega)
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))

theorem natAbs_kEnum (n : ℕ) : (kEnum n).natAbs = n / 2 + 1 := by
  unfold kEnum
  split
  · rw [Int.natAbs_natCast]
  · rw [Int.natAbs_neg, Int.natAbs_natCast]

theorem kEnum_even (m : ℕ) : kEnum (2 * m) = ((m : ℤ) + 1) := by
  unfold kEnum
  rw [if_pos (by omega : (2 * m) % 2 = 0)]
  have h2 : (2 * m) / 2 + 1 = m + 1 := by omega
  rw [h2]
  push_cast
  ring

theorem kEnum_odd (m : ℕ) : kEnum (2 * m + 1) = -(((m : ℤ) + 1)) := by
  unfold kEnum
  rw [if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]
  have h2 : (2 * m + 1) / 2 + 1 = m + 1 := by omega
  rw [h2]
  push_cast
  ring

theorem kEnum_surj (k : ℤ) (hk : k ≠ 0) : ∃ n : ℕ, kEnum n = k := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · -- `k < 0`: `k = -((m : ℤ) + 1)` with `m = (-k - 1).toNat`
    refine ⟨2 * ((-k - 1).toNat) + 1, ?_⟩
    rw [kEnum_odd]
    have h1 : (((-k - 1).toNat : ℕ) : ℤ) + 1 = -k := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -k - 1)]
      ring
    rw [h1, neg_neg]
  · -- `k > 0`: `k = (m : ℤ) + 1` with `m = (k - 1).toNat`
    refine ⟨2 * ((k - 1).toNat), ?_⟩
    rw [kEnum_even]
    have h1 : (((k - 1).toNat : ℕ) : ℤ) + 1 = k := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 1)]
      ring
    rw [h1]

/-! ## Auxiliary estimates -/

/-- `DiophBelow α b` is unsatisfiable for `b ≤ 0` (the distance to the nearest integer is at
most `1/2`). -/
theorem pos_of_diophBelow (α b : ℝ) (h : DiophBelow α b) : 0 < b := by
  by_contra hb
  push_neg at hb
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  set k : ℕ := max N 1 with hkdef
  have hNk : N ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk := hN k hNk
  have hdist : Work.TMContract.fracDist ((k : ℝ) * α) ≤ 1 / 2 := by
    unfold Work.TMContract.fracDist
    rw [abs_sub_round_eq_min]
    have h1 : Int.fract ((k : ℝ) * α) ≤ 1 := (Int.fract_lt_one _).le
    have h2 : (0 : ℝ) ≤ Int.fract ((k : ℝ) * α) := Int.fract_nonneg _
    have h3 : min (Int.fract ((k : ℝ) * α)) (1 - Int.fract ((k : ℝ) * α)) ≤ 1 / 2 := by
      rcases le_total (Int.fract ((k : ℝ) * α)) (1 / 2) with h | h
      · exact le_trans (min_le_left _ _) h
      · exact le_trans (min_le_right _ _) (by linarith)
    linarith [h3]
  have hnonneg : (0 : ℝ) ≤ -(b * (k : ℝ)) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith
  have hexp : 1 ≤ Real.exp (-(b * (k : ℝ))) := by
    simpa using Real.one_le_exp_iff.mpr hnonneg
  linarith [hdist, hk]

/-- Absorb a constant into an exponential rate. -/
theorem eventually_const_mul_exp_le (A η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      A * Real.exp (-(η * ((n : ℝ) + 1))) ≤ Real.exp (-((η / 2) * ((n : ℝ) + 1))) := by
  rcases le_or_gt A 0 with hA | hA
  · filter_upwards with n
    have h1 : 0 < Real.exp (-(η * ((n : ℝ) + 1))) := Real.exp_pos _
    nlinarith [h1, Real.exp_pos (-((η / 2) * ((n : ℝ) + 1)))]
  · filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 * Real.log A / η) + 1)] with n hn
    have hlog : Real.log A ≤ (η / 2) * ((n : ℝ) + 1) := by
      have h3 : 2 * Real.log A / η ≤ (n : ℝ) + 1 := by
        have h4 : 2 * Real.log A / η ≤ (Nat.ceil (2 * Real.log A / η) : ℝ) := Nat.le_ceil _
        have h5 : ((Nat.ceil (2 * Real.log A / η) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hn
        push_cast at h5
        linarith
      rw [div_le_iff₀ hη] at h3
      linarith
    have h5 : A ≤ Real.exp ((η / 2) * ((n : ℝ) + 1)) := by
      have h6 := Real.log_le_iff_le_exp (x := A) (y := (η / 2) * ((n : ℝ) + 1)) hA
      exact h6.mp hlog
    calc A * Real.exp (-(η * ((n : ℝ) + 1)))
        ≤ Real.exp ((η / 2) * ((n : ℝ) + 1)) * Real.exp (-(η * ((n : ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = Real.exp (-((η / 2) * ((n : ℝ) + 1))) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- `|k|` for `k : ℤ`, as a real number. -/
theorem abs_intCast_eq (k : ℤ) : |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs k]
  norm_num


/-- `e ^ (2π i k α) ≠ 1` for `k ≠ 0` and irrational `α`. -/
theorem exp_two_pi_mul_I_mul_ne_one (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * (α : ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ) := by
    rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I) (m : ℂ), ← hm]
    push_cast
    ring
  have h3 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [Complex.mul_im, Complex.mul_re, Real.pi_pos.ne'] at this
  have h4 : (k : ℂ) * (α : ℂ) = (m : ℂ) := mul_left_cancel₀ h3 h2
  have h5 : (k : ℝ) * α = (m : ℝ) := by
    have := congrArg Complex.re h4
    simpa using this
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hq : (((m : ℚ) / (k : ℚ) : ℚ) : ℝ) = α := by
    push_cast
    rw [div_eq_iff hk']
    linarith [h5]
  exact hα ⟨_, hq⟩

/-- The two normalisations of the exponential factor agree. -/
theorem exp_factor_eq (α : ℝ) (k : ℤ) :
    Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) := by
  congr 1
  push_cast
  ring

end Work.TMComp.RedProj
