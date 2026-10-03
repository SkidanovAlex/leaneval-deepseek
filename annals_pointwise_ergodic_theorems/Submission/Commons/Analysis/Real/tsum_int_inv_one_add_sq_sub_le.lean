import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Real.tsum_int_one_div_sq_sep_le

namespace Commons.Analysis.Real

open scoped Topology

/-- Monotonicity of `x ↦ (1+x²)⁻¹` on `[0,∞)`. -/
private lemma inv_one_add_sq_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1 + y ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  exact (inv_le_inv₀ h1 h2).mpr (by linarith)

/-- The series `∑ₙ 1/(1+n²)` (over the naturals) converges. -/
private lemma summable_inv_one_add_sq_nat :
    Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Summable.mul_left 2 summable_one_div_sq_add_one)
  have h1 : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 / 2 := by positivity
  have hge : ((n : ℝ) + 1) ^ 2 / 2 ≤ 1 + (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have h := (inv_le_inv₀ h1 h2).mpr hge
  have heq : (((n : ℝ) + 1) ^ 2 / 2)⁻¹ = 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    rw [one_div, inv_div, div_eq_mul_inv]
  rwa [heq] at h

/-- `∑' n : ℕ, 1/(1+n²) ≤ 3`. -/
private lemma tsum_inv_one_add_sq_nat_le_three :
    (∑' n : ℕ, (1 + (n : ℝ) ^ 2)⁻¹) ≤ 3 := by
  have hg := summable_inv_one_add_sq_nat
  rw [hg.tsum_eq_zero_add]
  have htail : (∑' n : ℕ, (1 + (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)⁻¹)
      ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    refine Summable.tsum_le_tsum (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hg) summable_one_div_sq_add_one
    have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, one_div]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (by linarith [sq_nonneg ((n : ℝ) + 1)])
  have h0 : (1 + ((0 : ℕ) : ℝ) ^ 2)⁻¹ = 1 := by norm_num
  rw [h0]
  have h2 := tsum_one_div_sq_add_one_le_two
  linarith

theorem tsum_int_inv_one_add_sq_sub_le :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, (∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹) ≤ B := by
  refine ⟨7, by norm_num, ?_⟩
  intro t
  -- write `t = n + a` with `n = ⌊t⌋ ∈ ℤ` and `a ∈ [0,1)`
  obtain ⟨n, hn_le, hn_lt⟩ : ∃ n : ℤ, (n : ℝ) ≤ t ∧ t < (n : ℝ) + 1 :=
    ⟨⌊t⌋, Int.floor_le t, Int.lt_floor_add_one t⟩
  set a : ℝ := t - (n : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  -- reindex the `ℤ`-sum by the unit shift `n`
  have hshift : (∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹)
      = ∑' k : ℤ, (1 + ((k : ℝ) - a) ^ 2)⁻¹ := by
    have h := Equiv.tsum_eq (Equiv.addRight n) (fun k : ℤ => (1 + ((k : ℝ) - t) ^ 2)⁻¹)
    rw [← h]
    refine tsum_congr (fun k => ?_)
    have h1 : (((Equiv.addRight n) k : ℤ) : ℝ) = (k : ℝ) + (n : ℝ) := by simp
    rw [h1, show (k : ℝ) + (n : ℝ) - t = (k : ℝ) - a by rw [ha]; ring]
  rw [hshift]
  -- the dominating series `∑ 1/(1+m²)`
  have hg : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2)⁻¹) := summable_inv_one_add_sq_nat
  have hGle : (∑' m : ℕ, (1 + (m : ℝ) ^ 2)⁻¹) ≤ 3 := tsum_inv_one_add_sq_nat_le_three
  -- the shifted positive half is summable, dominated termwise by `1/(1+m²)`
  have hPshift : Summable (fun m : ℕ => (1 + (((m + 1 : ℕ) : ℝ) - a) ^ 2)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hg
    have hgoal : (1 + ((m : ℝ) + 1 - a) ^ 2)⁻¹ ≤ (1 + (m : ℝ) ^ 2)⁻¹ :=
      inv_one_add_sq_antitone (x := (m : ℝ)) (y := (m : ℝ) + 1 - a)
        (Nat.cast_nonneg m) (by linarith [ha1])
    simpa only [Nat.cast_add, Nat.cast_one] using hgoal
  have hPsum_nat : Summable (fun m : ℕ => (1 + ((m : ℝ) - a) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mp hPshift
  have hQsum_nat : Summable (fun m : ℕ => (1 + ((m : ℝ) + 1 + a) ^ 2)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hg
    exact inv_one_add_sq_antitone (x := (m : ℝ)) (y := (m : ℝ) + 1 + a)
      (Nat.cast_nonneg m) (by linarith [ha0])
  -- the two halves of the `ℤ`-sum, in the shape `tsum_of_nat_of_neg_add_one` expects
  have hPsum : Summable (fun m : ℕ => (1 + (((m : ℤ) : ℝ) - a) ^ 2)⁻¹) :=
    hPsum_nat.congr (fun m => by simp)
  have hQsum : Summable (fun m : ℕ => (1 + (((-(↑m + 1) : ℤ) : ℝ) - a) ^ 2)⁻¹) :=
    hQsum_nat.congr (fun m => by
      congr 1
      push_cast
      ring)
  rw [tsum_of_nat_of_neg_add_one
    (f := fun k : ℤ => (1 + ((k : ℝ) - a) ^ 2)⁻¹) hPsum hQsum]
  -- bound the positive half
  have hP : (∑' n : ℕ, (1 + (((n : ℤ) : ℝ) - a) ^ 2)⁻¹) ≤ 4 := by
    have heq : (∑' n : ℕ, (1 + (((n : ℤ) : ℝ) - a) ^ 2)⁻¹)
        = (∑' n : ℕ, (1 + ((n : ℝ) - a) ^ 2)⁻¹) :=
      tsum_congr (fun n => by simp)
    rw [heq, hPsum_nat.tsum_eq_zero_add]
    have h0 : (1 + (((0 : ℕ) : ℝ) - a) ^ 2)⁻¹ ≤ 1 := by
      have hsimp : (1 + (((0 : ℕ) : ℝ) - a) ^ 2)⁻¹ = (1 + a ^ 2)⁻¹ := by
        congr 1
        push_cast
        ring
      rw [hsimp]
      have h1 : (0 : ℝ) < 1 + a ^ 2 := by positivity
      have h2 : (1 + a ^ 2)⁻¹ ≤ (1 : ℝ)⁻¹ :=
        (inv_le_inv₀ h1 (by norm_num)).mpr (by linarith [sq_nonneg a])
      simpa using h2
    have htail : (∑' m : ℕ, (1 + (((m + 1 : ℕ) : ℝ) - a) ^ 2)⁻¹)
        ≤ ∑' m : ℕ, (1 + (m : ℝ) ^ 2)⁻¹ := by
      refine Summable.tsum_le_tsum (fun m => ?_) hPshift hg
      have hgoal : (1 + ((m : ℝ) + 1 - a) ^ 2)⁻¹ ≤ (1 + (m : ℝ) ^ 2)⁻¹ :=
        inv_one_add_sq_antitone (x := (m : ℝ)) (y := (m : ℝ) + 1 - a)
          (Nat.cast_nonneg m) (by linarith [ha1])
      simpa only [Nat.cast_add, Nat.cast_one] using hgoal
    linarith [h0, htail, hGle]
  -- bound the negative half
  have hQ : (∑' n : ℕ, (1 + (((-(↑n + 1) : ℤ) : ℝ) - a) ^ 2)⁻¹) ≤ 3 := by
    have heq : (∑' n : ℕ, (1 + (((-(↑n + 1) : ℤ) : ℝ) - a) ^ 2)⁻¹)
        = (∑' n : ℕ, (1 + ((n : ℝ) + 1 + a) ^ 2)⁻¹) :=
      tsum_congr (fun n => by
        congr 1
        push_cast
        ring)
    rw [heq]
    calc (∑' n : ℕ, (1 + ((n : ℝ) + 1 + a) ^ 2)⁻¹)
        ≤ ∑' n : ℕ, (1 + (n : ℝ) ^ 2)⁻¹ := by
          refine Summable.tsum_le_tsum (fun m => ?_) hQsum_nat hg
          exact inv_one_add_sq_antitone (x := (m : ℝ)) (y := (m : ℝ) + 1 + a)
            (Nat.cast_nonneg m) (by linarith [ha0])
      _ ≤ 3 := hGle
  linarith [hP, hQ]

end Commons.Analysis.Real