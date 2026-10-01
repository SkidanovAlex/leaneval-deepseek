import Mathlib
import Submission.Work.LinnikBurgess.bval_transfer
import Submission.Work.LinnikBurgess.lf_defs

namespace Work.LinnikBurgess.u8three

open scoped BigOperators
open Classical

/-! ### Scalar arithmetic of the levels at `p = 3`

`cubeLevel 3 e = (e + 2) / 3` (the branch `p = 2` is not taken) and
`capLevel 3 e = e - 2 * ((e + 2) / 3)`, so the two level inequalities used by the support transfer
hold for every `e` (in particular for `e ≥ 2`, where `bval_transfer` needs them for `p ≥ 5`). -/

theorem cubeLevel_three_formula (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num : ¬ (3 = 2))]

theorem capLevel_three_formula (e : ℕ) : capLevel 3 e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_three_formula]

theorem one_le_cubeLevel_three_low {e : ℕ} (he : 2 ≤ e) : 1 ≤ cubeLevel 3 e := by
  rw [cubeLevel_three_formula]; omega

theorem cubeLevel_add_capLevel_le_three_low (e : ℕ) : cubeLevel 3 e + capLevel 3 e ≤ e := by
  rw [cubeLevel_three_formula, capLevel_three_formula]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem cubeLevel_add_bval_le_three_low (e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) :
    cubeLevel 3 e + bval 3 e a b y ≤ e := by
  have hb : bval 3 e a b y ≤ capLevel 3 e := vcap_le 3 (capLevel 3 e) (defect2 3 e a b y).val
  have h := cubeLevel_add_capLevel_le_three_low e
  omega

/-- **The support transfer at `p = 3`.**  `Work.LinnikBurgess.bval_transfer` proves
`SuppTransfer p e a b` for every prime `p ≥ 5` (and `2 ≤ e`); this is the same statement for
`p = 3`, obtained by replacing the two arithmetic side conditions `cubeLevel_add_capLevel_le` and
`cubeLevel_add_bval_le` (which carry a `5 ≤ p` hypothesis) by their `p = 3` counterparts. -/
theorem transfer_three {e : ℕ} (he : 2 ≤ e) (a b : Fin 3 → ℕ) : SuppTransfer 3 e a b := by
  intro y hy
  obtain ⟨hunit, hsupp⟩ := hy
  have hp : Nat.Prime 3 := by norm_num
  have hm : 1 ≤ cubeLevel 3 e := one_le_cubeLevel_three_low he
  have hmT : cubeLevel 3 e + capLevel 3 e ≤ e := cubeLevel_add_capLevel_le_three_low e
  have hmb : cubeLevel 3 e + bval 3 e a b y ≤ e := cubeLevel_add_bval_le_three_low e a b y
  have hc1 := dvd_defect1_congr (p := 3) (e := e) a b hunit
  have hc2 := dvd_defect2_congr (p := 3) (e := e) a b hunit
  -- `U(y)` is coprime to `3`
  have hu : ¬ (((3 : ℕ) : ℤ)) ∣ (Uval y a b : ℤ) :=
    fun h => not_dvd_Uval hp hunit (Int.natCast_dvd_natCast.mp h)
  -- `3^(m+b_y) ∣ N(y)`
  have hN : ((((3 : ℕ) : ℤ)) ^ (cubeLevel 3 e + bval 3 e a b y)) ∣ (critN a b).eval (y : ℤ) := by
    have h1 : ((((3 : ℕ) : ℤ)) ^ (cubeLevel 3 e + bval 3 e a b y))
        ∣ (defect1 3 e a b y).val * (Uval y a b : ℤ) := by
      have h2 : ((((3 : ℕ) : ℤ)) ^ (cubeLevel 3 e + bval 3 e a b y))
          ∣ (((defect1 3 e a b y).val : ℕ) : ℤ) := by
        rw [← Nat.cast_pow]
        exact Int.natCast_dvd_natCast.mpr hsupp
      exact dvd_mul_of_dvd_left h2 _
    have h3 : ((((3 : ℕ) : ℤ)) ^ (cubeLevel 3 e + bval 3 e a b y)) ∣ ((((3 : ℕ) : ℤ)) ^ e) :=
      pow_dvd_pow _ hmb
    have h4 := dvd_trans h3 hc1
    have h5 := dvd_sub h1 h4
    have hkey : (critN a b).eval (y : ℤ)
        = (defect1 3 e a b y).val * (Uval y a b : ℤ)
          - ((defect1 3 e a b y).val * (Uval y a b : ℤ) - (critN a b).eval (y : ℤ)) := by ring
    rw [hkey]
    exact h5
  refine ⟨?_, ?_⟩
  · have hcore := transfer_core (p := 3) (e := e) (m := cubeLevel 3 e) (T := capLevel 3 e)
      (b := bval 3 e a b y) (d2 := (((defect2 3 e a b y).val : ℕ) : ℤ))
      (u := (Uval y a b : ℤ)) (w := (Wval y a b : ℤ))
      (nn := (critN a b).eval (y : ℤ)) (nn' := (critN a b).derivative.eval (y : ℤ))
      hm hmT (bval_eq a b y) hc2 hu hN
    rw [hcore, nval_eq]
  · rw [Nat.cast_pow]
    exact hN

end Work.LinnikBurgess.u8three
