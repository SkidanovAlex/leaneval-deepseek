import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic

namespace Commons.Analysis.IntegerGaussianSum

open scoped BigOperators

/-- For `x ≥ 1` we have `x ≤ x^2`. -/
private lemma sq_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hxm : 0 ≤ x * (x - 1) := mul_nonneg hx0 (sub_nonneg.mpr hx)
  nlinarith

/-- `exp (-c x²) ≤ exp (-c x)` for `c ≥ 0` and `x ≥ 1`. -/
private lemma exp_decay {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) :
    Real.exp (-c * x ^ 2) ≤ Real.exp (-c * x) := by
  rw [Real.exp_le_exp]
  have hx2 : x ≤ x ^ 2 := sq_le_self_of_one_le hx
  have hcprod : c * x ≤ c * x ^ 2 := mul_le_mul_of_nonneg_left hx2 hc
  nlinarith

/-- `exp (-c * n) = exp (-c)^n` for `n : ℕ`. -/
private lemma exp_neg_mul_nat_eq_pow (c : ℝ) (n : ℕ) :
    Real.exp (-c * ((n : ℕ) : ℝ)) = Real.exp (-c) ^ n := by
  calc
    Real.exp (-c * ((n : ℕ) : ℝ)) = Real.exp ((n : ℝ) * -c) := by congr 1; ring
    _ = Real.exp (-c) ^ n := by rw [Real.exp_nat_mul (-c) n]

/-- The geometric series `∑ n, exp (-c * n)` over `ℕ` converges to `(1 - exp(-c))⁻¹`. -/
private lemma hasSum_exp_neg_mul_nat (c : ℝ) (hc : 0 < c) :
    HasSum (fun n : ℕ => Real.exp (-c * ((n : ℕ) : ℝ))) ((1 - Real.exp (-c))⁻¹) := by
  let q : ℝ := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos (-c)).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact (Real.exp_lt_exp).mpr (by linarith)
  have hgeo : HasSum (fun n : ℕ => q ^ n) ((1 - q)⁻¹) :=
    hasSum_geometric_of_lt_one hq0 hq1
  convert hgeo using 1
  funext n
  dsimp [q]
  exact exp_neg_mul_nat_eq_pow c n

private lemma tsum_exp_neg_mul_nat (c : ℝ) (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * ((n : ℕ) : ℝ))) = (1 - Real.exp (-c))⁻¹ :=
  (hasSum_exp_neg_mul_nat c hc).tsum_eq

private lemma exp_neg_mul_nat_succ (c : ℝ) (n : ℕ) :
    Real.exp (-c * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (-c) * Real.exp (-c * ((n : ℕ) : ℝ)) := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hcast]
  rw [mul_add]
  have hone : -c * (1 : ℝ) = -c := by ring
  rw [hone]
  rw [Real.exp_add]
  ring

/-- The shifted geometric series `∑ n, exp (-c * (n+1))` over `ℕ`. -/
private lemma tsum_exp_neg_mul_nat_shift (c : ℝ) (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ))) =
      Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by
  calc
    (∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ)))
        = ∑' n : ℕ, (Real.exp (-c) * Real.exp (-c * ((n : ℕ) : ℝ))) := by
          apply tsum_congr
          intro n
          exact exp_neg_mul_nat_succ c n
    _ = Real.exp (-c) * (∑' n : ℕ, Real.exp (-c * ((n : ℕ) : ℝ))) := by
          rw [tsum_mul_left]
    _ = Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by rw [tsum_exp_neg_mul_nat c hc]

/-- The sequence `n ↦ exp (-c n²)` on `ℕ` is summable. -/
private lemma summable_exp_neg_mul_sq_nat (c : ℝ) (hc0 : 0 ≤ c) (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * ((n : ℕ) : ℝ) ^ 2)) := by
  have hb : Summable (fun n : ℕ => Real.exp (-c * ((n : ℕ) : ℝ))) :=
    (hasSum_exp_neg_mul_nat c hc).summable
  refine Summable.of_nonneg_of_le ?_ ?_ hb
  · intro n
    exact (Real.exp_pos _).le
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ (n : ℝ) := by
        have hn1n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        exact_mod_cast hn1n
      exact exp_decay hc0 hn1

/-- Bound the Gaussian sum over positive integers by `1/4` for `c ≥ 4`:
`∑' n : ℕ+, exp (-c n²) ≤ 1/4`. -/
private lemma tsum_exp_neg_mul_sq_pnat_le (c : ℝ) (hc0 : 0 ≤ c) (hc : 0 < c) (hc4 : 4 ≤ c) :
    (∑' n : ℕ+, Real.exp (-c * ((((n : ℕ+) : ℕ) : ℝ) ^ 2))) ≤ 1 / 4 := by
  let a : ℕ → ℝ := fun n => Real.exp (-c * ((n : ℕ) : ℝ) ^ 2)
  have hsumA : Summable a := by
    simpa [a] using summable_exp_neg_mul_sq_nat c hc0 hc
  have hsumAt : Summable (fun n : ℕ => a (n + 1)) := by
    change Summable (a ∘ fun n : ℕ => n + 1)
    exact (hsumA.comp_injective (add_left_injective 1))
  have hsumBt : Summable (fun n : ℕ => Real.exp (-c * ((n + 1 : ℕ) : ℝ))) := by
    change Summable ((fun n : ℕ => Real.exp (-c * ((n : ℕ) : ℝ))) ∘ fun n : ℕ => n + 1)
    exact ((hasSum_exp_neg_mul_nat c hc).summable.comp_injective (add_left_injective 1))
  have hle : ∀ n : ℕ,
      Real.exp (-c * (((n + 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ)) := by
    intro n
    exact exp_decay hc0 (by norm_num : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  have hmain :
      (∑' n : ℕ, Real.exp (-c * (((n + 1 : ℕ) : ℝ) ^ 2)))
        ≤ Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by
    have hcmp := Summable.tsum_le_tsum hle hsumAt hsumBt
    calc
      (∑' n : ℕ, Real.exp (-c * (((n + 1 : ℕ) : ℝ) ^ 2)))
          ≤ ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ)) := hcmp
      _ = Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := tsum_exp_neg_mul_nat_shift c hc
  -- q := exp (-c) ≤ 1/5, so q / (1 - q) ≤ 1/4
  let q : ℝ := Real.exp (-c)
  have hq_le : q ≤ (1 : ℝ) / 5 := by
    have hc5 : (5 : ℝ) ≤ Real.exp c := by
      calc
        (5 : ℝ) ≤ c + 1 := by linarith
        _ ≤ Real.exp c := Real.add_one_le_exp c
    have h5 : (0 : ℝ) < 5 := by norm_num
    dsimp [q]
    rw [Real.exp_neg]
    simpa using (one_div_le_one_div_of_le h5 hc5)
  have hq_mid : q * (1 - q)⁻¹ ≤ (1 : ℝ) / 4 := by
    have h1q : 0 < 1 - q := by nlinarith
    have hmain4 : (4 : ℝ) * q ≤ 1 - q := by nlinarith
    have hmul : 4 * q * (1 - q)⁻¹ ≤ (1 - q) * (1 - q)⁻¹ :=
      mul_le_mul_of_nonneg_right hmain4 (inv_nonneg.mpr h1q.le)
    calc
      q * (1 - q)⁻¹ = (4 * q * (1 - q)⁻¹) / 4 := by field_simp
      _ ≤ ((1 - q) * (1 - q)⁻¹) / 4 := by
        simpa [div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4))
      _ = (1 : ℝ) / 4 := by field_simp [h1q.ne']
  calc
    (∑' n : ℕ+, Real.exp (-c * ((((n : ℕ+) : ℕ) : ℝ) ^ 2)))
        = ∑' n : ℕ, Real.exp (-c * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [tsum_pnat_eq_tsum_succ (f := a)]
    _ ≤ Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := hmain
    _ ≤ 1 / 4 := by
      simpa [q] using hq_mid

lemma zsum_exp_neg_mul_sq_le (c : ℝ) (hc : 1200 ≤ c) :
    (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2)) ≤ 3 / 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hcpos : 0 < c := by linarith
  have hc4 : 4 ≤ c := by linarith
  let f : ℤ → ℝ := fun k => Real.exp (-c * ((k : ℤ) : ℝ) ^ 2)
  have hfeven : Function.Even f := by
    intro k
    dsimp [f]
    congr 1
    rw [Int.cast_neg]
    ring
  have hsumf : Summable f := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · show Summable (fun n : ℕ => f ((n : ℕ) : ℤ))
      simpa [f] using (summable_exp_neg_mul_sq_nat c hc0 hcpos)
    · have hpos : Summable (fun n : ℕ => f ((n : ℕ) : ℤ)) := by
        simpa [f] using (summable_exp_neg_mul_sq_nat c hc0 hcpos)
      refine Summable.congr hpos ?_
      intro n
      exact (hfeven (((n : ℕ) : ℤ))).symm
  have htsum : (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2)) =
      f 0 + 2 • (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) := by
    simpa [f] using (tsum_int_eq_zero_add_two_mul_tsum_pnat (f := f) hfeven hsumf)
  have hsum0 : f 0 = 1 := by
    dsimp [f]
    simp
  have hp : (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) ≤ 1 / 4 := by
    have hb := tsum_exp_neg_mul_sq_pnat_le c hc0 hcpos hc4
    simpa [f] using hb
  calc
    (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2)) = f 0 + 2 • (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) := htsum
    _ ≤ 3 / 2 := by
      rw [hsum0]
      have hsmul : 2 • (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) =
          2 * (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) := by norm_num
      rw [hsmul]
      have hmul : 2 * (∑' n : ℕ+, f (((n : ℕ+) : ℤ))) ≤ (1 : ℝ) / 2 := by
        nlinarith [hp]
      nlinarith

end Commons.Analysis.IntegerGaussianSum