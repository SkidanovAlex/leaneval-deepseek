import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs

namespace Work.BourgainPlan.Maximal

theorem mstQ_le_two_pow (s : ℕ) :
    (Work.BourgainPlan.Maximal.mstQ' s : ℝ)
      ≤ (2 : ℝ) ^ ((2 : ℕ) ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1))) := by
  rw [mstQ']
  set x : ℝ := ((s : ℝ) + 1) ^ (1 / 10 : ℝ) with hxdef
  set m : ℕ := ⌊x⌋₊ + 1 with hmdef
  have hxlt : x < (m : ℝ) := by
    have := Nat.lt_floor_add_one x
    rw [hmdef]
    push_cast
    linarith
  -- `⌈exp x⌉₊ ≤ ⌈exp m⌉₊ ≤ 2^(2m)`
  have hNleM : Nat.ceil (Real.exp x) ≤ Nat.ceil (Real.exp (m : ℝ)) :=
    Nat.ceil_le_ceil (Real.exp_le_exp.mpr hxlt.le)
  have hMle : Nat.ceil (Real.exp (m : ℝ)) ≤ 2 ^ (2 * m) := by
    rw [Nat.ceil_le]
    have hexp : Real.exp ((m : ℕ) : ℝ) = (Real.exp 1) ^ m := by
      simpa using (Real.exp_nat_mul (1 : ℝ) m)
    rw [hexp]
    have h4 : Real.exp 1 ≤ (2 : ℝ) ^ 2 := by
      have := Real.exp_one_lt_three
      norm_num
      linarith
    calc (Real.exp 1) ^ m ≤ ((2 : ℝ) ^ 2) ^ m := pow_le_pow_left₀ (Real.exp_pos 1).le h4 m
      _ = (2 : ℝ) ^ (2 * m) := by rw [← pow_mul]
      _ = ((2 ^ (2 * m) : ℕ) : ℝ) := by push_cast; ring
  have h2m : 2 * m ≤ 2 ^ (2 * m) :=
    (Nat.lt_pow_self (n := 2 * m) (a := 2) (by norm_num)).le
  have hfact : Nat.factorial (Nat.ceil (Real.exp x)) ≤ (2 : ℕ) ^ (2 ^ (5 * m)) := by
    have hNM : Nat.factorial (Nat.ceil (Real.exp x))
        ≤ Nat.factorial (Nat.ceil (Real.exp (m : ℝ))) := Nat.factorial_le hNleM
    have hM : Nat.factorial (Nat.ceil (Real.exp (m : ℝ))) ≤ (2 : ℕ) ^ (2 ^ (5 * m)) := by
      calc Nat.factorial (Nat.ceil (Real.exp (m : ℝ)))
          ≤ (Nat.ceil (Real.exp (m : ℝ))) ^ (Nat.ceil (Real.exp (m : ℝ))) :=
            Nat.factorial_le_pow _
        _ ≤ (2 ^ (2 * m)) ^ (Nat.ceil (Real.exp (m : ℝ))) := Nat.pow_le_pow_left hMle _
        _ ≤ (2 ^ (2 * m)) ^ (2 ^ (2 * m)) := Nat.pow_le_pow_right (n := 2 ^ (2 * m)) (by positivity) hMle
        _ = 2 ^ ((2 * m) * (2 ^ (2 * m))) := (pow_mul 2 (2 * m) (2 ^ (2 * m))).symm
        _ ≤ 2 ^ (2 ^ (5 * m)) := by
              apply Nat.pow_le_pow_right (n := 2) (by norm_num)
              calc (2 * m) * 2 ^ (2 * m) ≤ 2 ^ (2 * m) * 2 ^ (2 * m) :=
                    Nat.mul_le_mul_right _ h2m
                _ = 2 ^ (4 * m) := by rw [← pow_add]; ring_nf
                _ ≤ 2 ^ (5 * m) := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    exact hNM.trans hM
  exact_mod_cast hfact

end Work.BourgainPlan.Maximal
