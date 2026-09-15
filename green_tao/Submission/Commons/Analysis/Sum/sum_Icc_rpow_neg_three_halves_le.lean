import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Sum

/-- Auxiliary: the reciprocal-square-root midpoint bound. -/
lemma inv_sqrt_mid_le (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : x = (a + b) / 2) (hab : b = a + 1) :
    1 / (x * Real.sqrt x) ≤ 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) := by
  have hx0 : 0 < x := by rw [hx]; linarith
  have h1 : Real.sqrt a * Real.sqrt b ≤ x := by
    have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
    rw [sub_sq, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le] at h
    nlinarith [h, hx]
  have h2 : Real.sqrt a + Real.sqrt b ≤ 2 * Real.sqrt x := by
    have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := by
      rw [add_sq, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, mul_pow, Real.sq_sqrt hx0.le]
      nlinarith [h1, hx]
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
    exact h
  have hqp : Real.sqrt b - Real.sqrt a = 1 / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff (by positivity : (Real.sqrt a + Real.sqrt b) ≠ 0)]
    have hsq : (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 = 1 := by
      rw [Real.sq_sqrt hb.le, Real.sq_sqrt ha.le]; linarith
    nlinarith [hsq]
  have h3 : Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) ≤ 2 * x * Real.sqrt x := by
    calc Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b)
        ≤ x * (2 * Real.sqrt x) := by
          exact mul_le_mul h1 h2 (by positivity) hx0.le
      _ = 2 * x * Real.sqrt x := by ring
  have hsq_ba : (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 = 1 := by
    rw [Real.sq_sqrt hb.le, Real.sq_sqrt ha.le]; linarith
  have hdiff : (1 / Real.sqrt a - 1 / Real.sqrt b) * (Real.sqrt a * Real.sqrt b)
      = Real.sqrt b - Real.sqrt a := by
    field_simp
  have hsq2 : (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b) = 1 := by
    nlinarith [hsq_ba]
  have hdiff2 : (1 / Real.sqrt a - 1 / Real.sqrt b) * ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b)) = 1 := by
    rw [mul_comm (Real.sqrt a + Real.sqrt b) (Real.sqrt a * Real.sqrt b), ← mul_assoc, hdiff]
    exact hsq2
  have hD : 0 < (Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b) := by positivity
  have hkey : 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) * (x * Real.sqrt x)
      = (2 * x * Real.sqrt x) / ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b)) := by
    rw [eq_div_iff hD.ne']
    have h : 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) * (x * Real.sqrt x)
        * ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b))
        = 2 * (x * Real.sqrt x) * ((1 / Real.sqrt a - 1 / Real.sqrt b) * ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b))) := by
      ring
    rw [h, hdiff2, mul_one]
    ring
  rw [div_le_iff₀ (by positivity : (0:ℝ) < x * Real.sqrt x)]
  rw [hkey, le_div_iff₀ hD]
  nlinarith [h3]

/-- Auxiliary: the per-term bound. -/
lemma rpow_neg_three_halves_le (x : ℝ) (hx : 1 ≤ x) :
    x ^ (-(3:ℝ)/2) ≤ 2 * ((x - 1/2) ^ (-(1:ℝ)/2) - (x + 1/2) ^ (-(1:ℝ)/2)) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < x - 1/2 := by linarith
  have hb : 0 < x + 1/2 := by linarith
  rw [show (-(3:ℝ)/2) = -(3/2 : ℝ) by ring,
      show (-(1:ℝ)/2) = -(1/2 : ℝ) by ring]
  rw [Real.rpow_neg hx0.le (3/2), show (3:ℝ)/2 = 1 + 1/2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow x,
      Real.rpow_neg ha.le (1/2), ← Real.sqrt_eq_rpow (x - 1/2),
      Real.rpow_neg hb.le (1/2), ← Real.sqrt_eq_rpow (x + 1/2)]
  simp only [inv_eq_one_div]
  exact inv_sqrt_mid_le (x - 1/2) (x + 1/2) x ha hb (by ring) (by ring)

/-- Auxiliary: telescoping of a difference over `Icc 1 K`. -/
lemma sum_Icc_telescope (g : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, (g j - g (j + 1)) = g 1 - g (K + 1) := by
  induction K with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      ring

lemma sum_Icc_rpow_neg_three_halves_le (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, (j : ℝ) ^ (-(3:ℝ)/2)) ≤ 3 := by
  have hg1' : (((1:ℕ):ℝ) - 1/2) ^ (-(1:ℝ)/2) = Real.sqrt 2 := by
    have h : ((1:ℕ):ℝ) - 1/2 = (2:ℝ)⁻¹ := by norm_num
    rw [h, show (-(1:ℝ)/2) = -(1/2 : ℝ) by ring,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (1/2),
        ← Real.sqrt_eq_rpow, Real.sqrt_inv]
    simp
  set g : ℕ → ℝ := fun j => ((j:ℝ) - 1/2) ^ (-(1:ℝ)/2) with hg_def
  have hg1_eq : g 1 = Real.sqrt 2 := by simpa only [hg_def] using hg1'
  have hterm : ∀ j ∈ Finset.Icc 1 K, (j:ℝ) ^ (-(3:ℝ)/2) ≤ 2 * (g j - g (j + 1)) := by
    intro j hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by
      have : (1:ℕ) ≤ j := (Finset.mem_Icc.mp hj).1
      exact_mod_cast this
    have h := rpow_neg_three_halves_le (j:ℝ) hj1
    have hgj : g j = ((j:ℝ) - 1/2) ^ (-(1:ℝ)/2) := by simp only [hg_def]
    have hgj1 : g (j + 1) = ((j:ℝ) + 1/2) ^ (-(1:ℝ)/2) := by
      simp only [hg_def]
      have : (((j+1:ℕ)):ℝ) - 1/2 = (j:ℝ) + 1/2 := by push_cast; ring
      rw [this]
    rw [hgj, hgj1]
    exact h
  have hpos : 0 ≤ g (K + 1) := by
    rw [hg_def]
    have hK : (0:ℝ) ≤ (((K + 1 : ℕ)):ℝ) - 1/2 := by
      have h1 : (1:ℝ) ≤ (((K+1:ℕ)):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
      linarith
    exact Real.rpow_nonneg hK _
  have hmain : ∑ j ∈ Finset.Icc 1 K, (j:ℝ) ^ (-(3:ℝ)/2) ≤ 2 * (Real.sqrt 2 - g (K + 1)) := by
    calc ∑ j ∈ Finset.Icc 1 K, (j:ℝ) ^ (-(3:ℝ)/2)
        ≤ ∑ j ∈ Finset.Icc 1 K, 2 * (g j - g (j + 1)) := Finset.sum_le_sum hterm
      _ = 2 * ∑ j ∈ Finset.Icc 1 K, (g j - g (j + 1)) := (Finset.mul_sum _ _ _).symm
      _ = 2 * (g 1 - g (K + 1)) := by rw [sum_Icc_telescope]
      _ = 2 * (Real.sqrt 2 - g (K + 1)) := by rw [hg1_eq]
  have h2 : 2 * Real.sqrt 2 ≤ 3 := by
    have hlt : Real.sqrt 2 < 3/2 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3/2)]
      norm_num
    linarith
  linarith [hmain, hpos, h2]

end Commons.Analysis.Sum