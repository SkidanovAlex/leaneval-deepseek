import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum.NatFactorial

noncomputable section

namespace Commons.Analysis.InfiniteSum

/-- `6 * (n+3 choose 3) = (n+1)(n+2)(n+3)` in `ℝ`. -/
private lemma choose_three_mul (n : ℕ) :
    (6 : ℝ) * ((n + 3).choose 3 : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
  have h1 := Nat.ascFactorial_eq_factorial_mul_choose (n := n) (k := 3)
  norm_num at h1
  have asc3 : (n + 1).ascFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp [Nat.ascFactorial]
    ring
  calc
    (6 : ℝ) * ((n + 3).choose 3 : ℝ) = ((n + 1).ascFactorial 3 : ℝ) := by
      exact_mod_cast h1.symm
    _ = (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℝ) := by rw [asc3]
    _ = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by norm_num

/-- `2 * (n+2 choose 2) = (n+1)(n+2)` in `ℝ`. -/
private lemma choose_two_mul (n : ℕ) :
    (2 : ℝ) * ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
  have h1 := Nat.ascFactorial_eq_factorial_mul_choose (n := n) (k := 2)
  norm_num at h1
  have asc2 : (n + 1).ascFactorial 2 = (n + 1) * (n + 2) := by
    simp [Nat.ascFactorial]
    ring
  calc
    (2 : ℝ) * ((n + 2).choose 2 : ℝ) = ((n + 1).ascFactorial 2 : ℝ) := by
      exact_mod_cast h1.symm
    _ = (((n + 1) * (n + 2) : ℕ) : ℝ) := by rw [asc2]
    _ = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by norm_num

private lemma choose_one_cast (n : ℕ) : ((n + 1).choose 1 : ℝ) = (n : ℝ) + 1 := by
  norm_num [Nat.choose_one_right]

/-- The third power of `n` as an integer-linear combination of binomial coefficients. -/
private lemma cube_comb (n : ℕ) :
    (6 : ℝ) * ((n + 3).choose 3 : ℝ) - 12 * ((n + 2).choose 2 : ℝ)
      + 7 * ((n + 1).choose 1 : ℝ) - 1 = (n : ℝ) ^ 3 := by
  rw [show (12 : ℝ) * ((n + 2).choose 2 : ℝ) = 6 * (2 * ((n + 2).choose 2 : ℝ)) by ring]
  rw [choose_three_mul, choose_two_mul]
  rw [show (7 : ℝ) * ((n + 1).choose 1 : ℝ) = 7 * (1 * ((n + 1).choose 1 : ℝ)) by ring]
  rw [choose_one_cast]
  norm_num
  ring

/-- `Σₙ n³·Xⁿ = X(1+4X+X²)/(1−X)⁴` for real `‖X‖ < 1` (third moment of the geometric series). -/
lemma nat_cube_geom_hasSum {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * X ^ n) (X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4) := by
  have hXne : (1 - X : ℝ) ≠ 0 := by
    have hXlt : X < 1 := (abs_lt.mp (by simpa using hX)).2
    exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hXlt))
  let C3 : ℕ → ℝ := fun n => ((n + 3).choose 3 : ℝ)
  let C2 : ℕ → ℝ := fun n => ((n + 2).choose 2 : ℝ)
  let C1 : ℕ → ℝ := fun n => ((n + 1).choose 1 : ℝ)
  let F3 : ℕ → ℝ := fun n => 6 * (C3 n * X ^ n)
  let F2 : ℕ → ℝ := fun n => 12 * (C2 n * X ^ n)
  let F1 : ℕ → ℝ := fun n => 7 * (C1 n * X ^ n)
  let FG : ℕ → ℝ := fun n => X ^ n
  -- tsum values of the binomial series
  have t3 : (∑' n : ℕ, C3 n * X ^ n) = 1 / (1 - X) ^ (3 + 1) := by
    simpa [C3] using (tsum_choose_mul_geometric_of_norm_lt_one 3 (𝕜 := ℝ) hX)
  have t2 : (∑' n : ℕ, C2 n * X ^ n) = 1 / (1 - X) ^ (2 + 1) := by
    simpa [C2] using (tsum_choose_mul_geometric_of_norm_lt_one 2 (𝕜 := ℝ) hX)
  have t1 : (∑' n : ℕ, C1 n * X ^ n) = 1 / (1 - X) ^ (1 + 1) := by
    simpa [C1] using (tsum_choose_mul_geometric_of_norm_lt_one 1 (𝕜 := ℝ) hX)
  have tG : (∑' n : ℕ, X ^ n) = (1 - X)⁻¹ := tsum_geometric_of_norm_lt_one hX
  -- summability
  have hs3 : Summable (fun n : ℕ => C3 n * X ^ n) := by
    simpa [C3] using (summable_choose_mul_geometric_of_norm_lt_one 3 (r := X) hX)
  have hs2 : Summable (fun n : ℕ => C2 n * X ^ n) := by
    simpa [C2] using (summable_choose_mul_geometric_of_norm_lt_one 2 (r := X) hX)
  have hs1 : Summable (fun n : ℕ => C1 n * X ^ n) := by
    simpa [C1] using (summable_choose_mul_geometric_of_norm_lt_one 1 (r := X) hX)
  have hsG : Summable (fun n : ℕ => X ^ n) := summable_geometric_of_norm_lt_one hX
  have hsF3 : Summable F3 := by simpa [F3] using hs3.mul_left (6 : ℝ)
  have hsF2 : Summable F2 := by simpa [F2] using hs2.mul_left (12 : ℝ)
  have hsF1 : Summable F1 := by simpa [F1] using hs1.mul_left (7 : ℝ)
  -- the cubic term decomposes
  have hdecomp : (fun n : ℕ => (n : ℝ) ^ 3 * X ^ n) = fun n : ℕ =>
      F3 n - F2 n + F1 n - FG n := by
    funext n
    dsimp [F3, F2, F1, FG, C3, C2, C1]
    rw [← cube_comb n]
    ring
  -- linearity of the infinite sum
  have hlin : (∑' n : ℕ, (F3 n - F2 n + F1 n - FG n))
      = 6 * (∑' n : ℕ, C3 n * X ^ n)
        - 12 * (∑' n : ℕ, C2 n * X ^ n)
        + 7 * (∑' n : ℕ, C1 n * X ^ n)
        - (∑' n : ℕ, X ^ n) := by
    have hsplit : (fun n : ℕ => F3 n - F2 n + F1 n - FG n)
        = fun n : ℕ => (F3 n - F2 n) + (F1 n - FG n) := by
      funext n
      ring
    calc
      (∑' n : ℕ, (F3 n - F2 n + F1 n - FG n))
        = (∑' n : ℕ, ((F3 n - F2 n) + (F1 n - FG n))) := by
            exact congrArg tsum hsplit
      _ = (∑' n : ℕ, (F3 n - F2 n)) + (∑' n : ℕ, (F1 n - FG n)) := by
            rw [Summable.tsum_add (hsF3.sub hsF2) (hsF1.sub hsG)]
      _ = (∑' n : ℕ, F3 n) - (∑' n : ℕ, F2 n) + (∑' n : ℕ, F1 n) - (∑' n : ℕ, FG n) := by
            dsimp [FG]
            rw [Summable.tsum_sub hsF3 hsF2, Summable.tsum_sub hsF1 hsG]
            ring
      _ = 6 * (∑' n : ℕ, C3 n * X ^ n) - 12 * (∑' n : ℕ, C2 n * X ^ n)
            + 7 * (∑' n : ℕ, C1 n * X ^ n) - (∑' n : ℕ, X ^ n) := by
            dsimp [F3, F2, F1, FG, C3, C2, C1]
            rw [Summable.tsum_mul_left (6 : ℝ) hs3, Summable.tsum_mul_left (12 : ℝ) hs2,
              Summable.tsum_mul_left (7 : ℝ) hs1]
  -- value algebra
  have hval : 6 * (1 / (1 - X) ^ (3 + 1)) - 12 * (1 / (1 - X) ^ (2 + 1))
        + 7 * (1 / (1 - X) ^ (1 + 1)) - (1 - X)⁻¹
      = X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4 := by
    norm_num
    field_simp [hXne]
    ring
  -- tsum value
  have htsum : (∑' n : ℕ, (n : ℝ) ^ 3 * X ^ n) = X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4 := by
    calc
      (∑' n : ℕ, (n : ℝ) ^ 3 * X ^ n)
        = (∑' n : ℕ, (F3 n - F2 n + F1 n - FG n)) := by
            exact congrArg tsum hdecomp
      _ = 6 * (∑' n : ℕ, C3 n * X ^ n) - 12 * (∑' n : ℕ, C2 n * X ^ n)
            + 7 * (∑' n : ℕ, C1 n * X ^ n) - (∑' n : ℕ, X ^ n) := hlin
      _ = 6 * (1 / (1 - X) ^ (3 + 1)) - 12 * (1 / (1 - X) ^ (2 + 1))
            + 7 * (1 / (1 - X) ^ (1 + 1)) - (1 - X)⁻¹ := by
            rw [t3, t2, t1, tG]
      _ = X * (1 + 4 * X + X ^ 2) / (1 - X) ^ 4 := hval
  -- convert tsum identity to HasSum
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 3 * X ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 3 (r := X) hX)
  simpa [htsum] using hs.hasSum

end Commons.Analysis.InfiniteSum