import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `s ≥ 0`, `exp s - 1 ≤ s * exp s`. -/
lemma exp_sub_one_le_mul_exp (s : ℝ) (_hs : 0 ≤ s) :
    Real.exp s - 1 ≤ s * Real.exp s := by
  have h1 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 - Real.exp (-s) ≤ s := by
    have := Real.add_one_le_exp (-s); linarith
  calc Real.exp s - 1 = Real.exp s * (1 - Real.exp (-s)) := by rw [mul_sub, mul_one, h1]
    _ ≤ Real.exp s * s := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg s)
    _ = s * Real.exp s := by ring

lemma exp_two_lt_nine : Real.exp 2 < 9 := by
  have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by simpa using Real.exp_nat_mul (1:ℝ) 2
  rw [hsq]; nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

lemma exp_half_lt_two : Real.exp (1/2) < 2 := by
  have hsq : Real.exp (1/2)^2 = Real.exp 1 := by
    simpa using (Real.exp_nat_mul (1/2) 2).symm
  have hlt : Real.exp (1/2)^2 < 4 := by rw [hsq]; linarith [Real.exp_one_lt_three]
  have := Real.exp_pos (1/2); nlinarith [hlt, this]

/-- The function `t ↦ t*M - exp t` is increasing on `[1/2, 2]` when `9 ≤ M`. -/
lemma half_le_of_mem (M t : ℝ) (hM : 9 ≤ M) (h1 : 1/2 ≤ t) (h2 : t ≤ 2) :
    (1/2) * M - Real.exp (1/2) ≤ t * M - Real.exp t := by
  set s : ℝ := t - 1/2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have ht : t = 1/2 + s := by rw [hs]; ring
  have hexp : Real.exp t = Real.exp (1/2) * Real.exp s := by rw [ht, Real.exp_add]
  have hMs : Real.exp t < M := by
    have hle : Real.exp t ≤ Real.exp 2 := Real.exp_le_exp_of_le h2
    linarith [exp_two_lt_nine]
  have hkey := exp_sub_one_le_mul_exp s hs0
  have hstep : Real.exp t - Real.exp (1/2) ≤ s * M := by
    calc Real.exp t - Real.exp (1/2)
        = Real.exp (1/2) * (Real.exp s - 1) := by rw [hexp]; ring
      _ ≤ Real.exp (1/2) * (s * Real.exp s) :=
            mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg (1/2))
      _ = s * Real.exp t := by rw [hexp]; ring
      _ ≤ s * M := mul_le_mul_of_nonneg_left hMs.le hs0
  nlinarith [hstep, ht]

/--
Given positive naturals `n ≤ D`, there is a prime `p` such that for every
`1 ≤ k ≤ n`, `n * exp(1/(9 D^2))^(k p) + n * exp(1/(9 D^2))^k < p`.
-/
theorem exists_prime_house_condition (D n : ℕ) (hD : 0 < D) (hn : 0 < n) (hnD : n ≤ D) :
    ∃ p : ℕ, Nat.Prime p ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (n : ℝ) * (Real.exp (1 / (9 * (D : ℝ) ^ 2))) ^ (k * p)
        + (n : ℝ) * (Real.exp (1 / (9 * (D : ℝ) ^ 2))) ^ k < (p : ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hnD' : (n:ℝ) ≤ D := by exact_mod_cast hnD
  set a : ℝ := 1 / (9 * (D:ℝ)^2) with ha
  set L : ℝ := (n:ℝ) / (9 * (D:ℝ)^2) with hL
  set p0 : ℝ := 9 * (D:ℝ)^2 / (n:ℝ) with hp0
  set X : ℝ := p0 / 2 with hX
  set m : ℕ := Nat.ceil X with hm
  -- p0 ≥ 9, hence X ≥ 1 and m ≥ 1
  have hp0_ge9 : 9 ≤ p0 := by
    rw [hp0, le_div_iff₀ hn0]
    have hnn : (n:ℝ) ≤ (D:ℝ)^2 := by nlinarith [hnD', hD1]
    nlinarith
  have hp0_pos : 0 < p0 := by linarith
  have hX_ge1 : (1:ℝ) ≤ X := by rw [hX]; linarith
  have hm_ge1 : (1:ℝ) ≤ (m:ℝ) := by rw [hm]; exact le_trans hX_ge1 (Nat.le_ceil X)
  have hm0 : m ≠ 0 := by
    have : (0:ℕ) < m := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hm_ge1
    omega
  -- Bertrand's postulate: a prime strictly above `m` and at most `2m`
  obtain ⟨p, hprime, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m hm0
  refine ⟨p, hprime, ?_⟩
  set M : ℝ := 9 * (D:ℝ)^2 / (n:ℝ)^2 with hM
  set u : ℝ := L * (p:ℝ) with hu
  -- `u = p/p0`
  have hu_eq : u = (p:ℝ) / p0 := by
    rw [hu, hL, hp0]; field_simp
  have hM9 : 9 ≤ M := by
    rw [hM, le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2)]
    have : (n:ℝ)^2 ≤ (D:ℝ)^2 := by nlinarith [hnD', hn0]
    nlinarith
  -- bounds on `u`
  have hp_gt_halfp0 : p0 / 2 < (p:ℝ) := by
    have hmc := Nat.le_ceil X
    have : X < (p:ℝ) := lt_of_le_of_lt hmc (by exact_mod_cast hmp)
    rwa [hX] at this
  have hp_lt_2p0 : (p:ℝ) < 2 * p0 := by
    have hm_lt : (m:ℝ) < X + 1 := by
      rw [hm]; exact Nat.ceil_lt_add_one (by rw [hX]; linarith)
    have hp2 : (p:ℝ) ≤ 2 * (m:ℝ) := by exact_mod_cast hp2m
    calc (p:ℝ) ≤ 2*(m:ℝ) := hp2
      _ < 2*(X+1) := by linarith
      _ = p0 + 2 := by rw [hX]; ring
      _ ≤ 2*p0 := by linarith
  have hu_ge : 1/2 ≤ u := by
    rw [hu_eq, le_div_iff₀ hp0_pos]; linarith
  have hu_le : u ≤ 2 := by
    rw [hu_eq, div_le_iff₀ hp0_pos]; linarith [hp_lt_2p0.le]
  -- `L ≤ 1/2`, so `exp L < 2`
  have hLle : L ≤ 1/2 := by
    rw [hL, div_le_iff₀ (by positivity : (0:ℝ) < 9*(D:ℝ)^2)]
    nlinarith [hnD', hD1]
  have hExpL : Real.exp L < 2 := lt_of_le_of_lt (Real.exp_le_exp_of_le hLle) exp_half_lt_two
  -- core estimate  exp u + exp L < u * M
  have hF : (1/2) * M - Real.exp (1/2) ≤ u * M - Real.exp u :=
    half_le_of_mem M u hM9 hu_ge hu_le
  have hBig : (5/2:ℝ) < u * M - Real.exp u := by
    have hb : (5/2:ℝ) < (1/2)*M - Real.exp (1/2) := by linarith [hM9, exp_half_lt_two]
    linarith
  have hexpineq : Real.exp u + Real.exp L < u * M := by linarith
  have huM : u * M = (p:ℝ)/(n:ℝ) := by
    rw [hu_eq, hM, hp0]; field_simp
  have hexpineq' : Real.exp u + Real.exp L < (p:ℝ)/(n:ℝ) := by rw [← huM]; exact hexpineq
  have hfinal : (n:ℝ) * Real.exp u + (n:ℝ) * Real.exp L < (p:ℝ) := by
    have := mul_lt_mul_of_pos_left hexpineq' hn0
    rw [mul_add] at this
    rwa [mul_div_cancel₀ _ (ne_of_gt hn0)] at this
  -- transfer to arbitrary `k`
  intro k _hk_pos hk_le
  have hkn : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk_le
  have hk1b : (Real.exp a)^(k*p) ≤ Real.exp u := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp, hu, hL, ha]
    push_cast
    have hpos : (0:ℝ) ≤ (p:ℝ) * (1/(9*(D:ℝ)^2)) := by positivity
    calc ((k:ℝ) * (p:ℝ)) * (1/(9*(D:ℝ)^2))
        = (k:ℝ) * ((p:ℝ) * (1/(9*(D:ℝ)^2))) := by ring
      _ ≤ (n:ℝ) * ((p:ℝ) * (1/(9*(D:ℝ)^2))) := mul_le_mul_of_nonneg_right hkn hpos
      _ = ((n:ℝ)/(9*(D:ℝ)^2)) * (p:ℝ) := by ring
  have hk2b : (Real.exp a)^k ≤ Real.exp L := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp, hL, ha]
    have hpos : (0:ℝ) ≤ 1/(9*(D:ℝ)^2) := by positivity
    calc (k:ℝ) * (1/(9*(D:ℝ)^2)) ≤ (n:ℝ) * (1/(9*(D:ℝ)^2)) :=
          mul_le_mul_of_nonneg_right hkn hpos
      _ = (n:ℝ)/(9*(D:ℝ)^2) := by ring
  calc (n:ℝ) * (Real.exp a)^(k*p) + (n:ℝ)*(Real.exp a)^k
      ≤ (n:ℝ) * Real.exp u + (n:ℝ) * Real.exp L := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hk1b (by positivity)
        · exact mul_le_mul_of_nonneg_left hk2b (by positivity)
    _ < (p:ℝ) := hfinal

end Work.BW
