import Mathlib

namespace Work.ZeroFreeTables

/-- Auxiliary polynomial-type sum.  With `z = x⁻¹`,
`Q x k u = ∑_{j=0}^{k} (-1)^j (k!/(k-j)!) u^{k-j} z^{j+1}`.
It is the antiderivative coefficient of `u^k · exp(x·u)`:
`d/du (exp(x·u) · Q x k u) = u^k · exp(x·u)`. -/
noncomputable def Q (x : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (-1:ℝ)^j * ((k.factorial:ℝ)/((k-j).factorial:ℝ)) * u^(k-j) * (x⁻¹)^(j+1)

/-- The recursion satisfied by `Q`: `Q (k+1) = u^{k+1}/x - ((k+1)/x) Q k`. -/
theorem Q_succ (x : ℝ) (k : ℕ) (u : ℝ) :
    Q x (k+1) u = u^(k+1) * x⁻¹ - ((k+1:ℝ) * x⁻¹) * Q x k u := by
  unfold Q
  rw [Finset.sum_range_succ']
  have hf0 : (-1:ℝ)^0 * (((k+1).factorial:ℝ)/((k+1-0).factorial:ℝ)) * u^(k+1-0) * (x⁻¹)^(0+1)
      = u^(k+1) * x⁻¹ := by
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.zero_add, pow_one]
    rw [div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k+1)))]
    ring
  rw [hf0]
  have hsum : (∑ i ∈ Finset.range (k+1),
        (-1:ℝ)^(i+1) * (((k+1).factorial:ℝ)/(((k+1)-(i+1)).factorial:ℝ)) * u^((k+1)-(i+1)) * (x⁻¹)^((i+1)+1))
      = -(((k+1:ℝ)*x⁻¹) * ∑ j ∈ Finset.range (k+1),
        (-1:ℝ)^j * ((k.factorial:ℝ)/((k-j).factorial:ℝ)) * u^(k-j) * (x⁻¹)^(j+1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.succ_sub_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  rw [hsum]
  ring

/-- Value of `Q` at `u = 0`. -/
theorem Q_zero (x : ℝ) (k : ℕ) : Q x k 0 = (-1:ℝ)^k * (k.factorial:ℝ) * (x⁻¹)^(k+1) := by
  unfold Q
  rw [Finset.sum_eq_single k]
  · simp only [pow_zero, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
    ring
  · intro b hb hbk
    simp only [Finset.mem_range] at hb
    rw [zero_pow (by omega : k - b ≠ 0)]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h

/-- `Q` at `k = 0` is the constant `1/x`. -/
theorem Q_zero_len (x u : ℝ) : Q x 0 u = x⁻¹ := by
  unfold Q
  rw [Finset.sum_range_one]
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.zero_add, pow_one]

/-- Value of `Q` at `u = 2`, matching the shape in the target statement. -/
theorem Q_two (x : ℝ) (k : ℕ) :
    Q x k 2 = ∑ j ∈ Finset.range (k+1),
      (-1:ℝ)^j * ((k.factorial:ℝ)/((k-j).factorial:ℝ)) * (2:ℝ)^(k-j) / x^(j+1) := by
  unfold Q
  apply Finset.sum_congr rfl
  intro j hj
  rw [inv_pow]
  ring

/-- Value of `Q` at `u = 0`, in the shape used by the target statement. -/
theorem Q_zero' (x : ℝ) (k : ℕ) : Q x k 0 = (-1:ℝ)^k * (k.factorial:ℝ) / x^(k+1) := by
  rw [Q_zero, inv_pow]
  ring

/-- Derivative of `u ↦ exp (x·u)`. -/
theorem hasDerivAt_exp_mul (x : ℝ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (x*v)) (Real.exp (x*u)*x) u := by
  have h : HasDerivAt (fun v : ℝ => x * v) x u := by
    simpa using (hasDerivAt_id u).const_mul x
  exact h.exp

/-- `u ↦ exp(x·u) · Q x k u` is an antiderivative of `u ↦ u^k · exp(x·u)`. -/
theorem hasDerivAt_exp_mul_Q {x : ℝ} (hx : x ≠ 0) (k : ℕ) (u : ℝ) :
    HasDerivAt (fun v => Real.exp (x * v) * Q x k v) (u ^ k * Real.exp (x * u)) u := by
  induction k generalizing u with
  | zero =>
    have hQ : Q x 0 = fun _ => x⁻¹ := funext fun v => Q_zero_len x v
    rw [hQ]
    have hm : HasDerivAt (fun v : ℝ => Real.exp (x*v) * x⁻¹) ((Real.exp (x*u)*x) * x⁻¹) u :=
      (hasDerivAt_exp_mul x u).mul_const x⁻¹
    convert hm using 1
    rw [pow_zero, one_mul, mul_assoc, mul_inv_cancel₀ hx, mul_one]
  | succ k ih =>
    have hf : (fun v => Real.exp (x * v) * Q x (k+1) v)
        = (fun v => Real.exp (x*v) * v^(k+1) * x⁻¹ - ((k+1:ℝ)*x⁻¹) * (Real.exp (x*v) * Q x k v)) := by
      funext v; rw [Q_succ]; ring
    rw [hf]
    have h1 : HasDerivAt (fun v : ℝ => Real.exp (x*v) * v^(k+1) * x⁻¹)
        ((Real.exp (x*u)*x * u^(k+1) + Real.exp (x*u) * ((k+1:ℝ) * u^((k+1)-1))) * x⁻¹) u := by
      have hp : HasDerivAt (fun v : ℝ => v^(k+1)) ((k+1:ℝ) * u^((k+1)-1)) u := by
        simpa using hasDerivAt_pow (k+1) u
      exact ((hasDerivAt_exp_mul x u).mul hp).mul_const x⁻¹
    have h2 : HasDerivAt (fun v : ℝ => ((k+1:ℝ)*x⁻¹) * (Real.exp (x*v) * Q x k v))
        (((k+1:ℝ)*x⁻¹) * (u^k * Real.exp (x*u))) u := (ih u).const_mul ((k+1:ℝ)*x⁻¹)
    have hd : (Real.exp (x*u)*x * u^(k+1) + Real.exp (x*u) * ((k+1:ℝ) * u^((k+1)-1))) * x⁻¹
        - ((k+1:ℝ)*x⁻¹) * (u^k * Real.exp (x*u)) = u^(k+1) * Real.exp (x*u) := by
      rw [Nat.add_sub_cancel]
      calc (Real.exp (x*u)*x * u^(k+1) + Real.exp (x*u) * ((k+1:ℝ) * u^k)) * x⁻¹
              - ((k+1:ℝ)*x⁻¹) * (u^k * Real.exp (x*u))
            = Real.exp (x*u) * u^(k+1) * (x * x⁻¹) := by ring
        _ = Real.exp (x*u) * u^(k+1) := by rw [mul_inv_cancel₀ hx, mul_one]
        _ = u^(k+1) * Real.exp (x*u) := by ring
    rw [← hd]
    exact h1.sub h2

theorem integral_pow_mul_exp (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (∫ u in (0:ℝ)..2, u ^ k * Real.exp (x * u))
      = Real.exp (2 * x) * (∑ j ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ j * ((k.factorial : ℝ) / ((k - j).factorial : ℝ)) * (2 : ℝ) ^ (k - j) / x ^ (j + 1))
        - (-1 : ℝ) ^ k * (k.factorial : ℝ) / x ^ (k + 1) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) 2,
      HasDerivAt (fun v => Real.exp (x * v) * Q x k v) (u ^ k * Real.exp (x * u)) u :=
    fun u _ => hasDerivAt_exp_mul_Q hx k u
  have hint : IntervalIntegrable (fun u : ℝ => u^k * Real.exp (x*u)) MeasureTheory.volume 0 2 :=
    (by fun_prop : Continuous (fun u : ℝ => u^k * Real.exp (x*u))).intervalIntegrable 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hx2 : x * 2 = 2 * x := by ring
  rw [hx2, mul_zero, Real.exp_zero, one_mul]
  rw [Q_zero', Q_two]

end Work.ZeroFreeTables
