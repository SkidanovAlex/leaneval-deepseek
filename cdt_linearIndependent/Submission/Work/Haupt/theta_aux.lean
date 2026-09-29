import Mathlib
import Submission.Work.Haupt.defs

/-!
# Theta duplication formulas (`Area M`)

With the nome-variable theta series of `Submission.Work.Haupt.defs`,

* `T3 x = θ₃(x) = ∑' n : ℤ, x ^ (n^2)`,
* `T4 x = θ₄(x) = ∑' n : ℤ, (-1)^n x ^ (n^2)`,
* `T2 x = θ₂(x)/x^{1/4} = ∑' n : ℤ, x ^ (n(n+1))`,

we prove the three *duplication* identities (`x ↦ x^2`):

* `T3 x ^ 2 = T3 (x^2)^2 + x * T2 (x^2)^2`,
* `T4 x ^ 2 = T3 (x^2)^2 - x * T2 (x^2)^2`,
* `T2 x ^ 2 = 2 * T2 (x^2) * T3 (x^2)`.

The proofs are the classical combinatorial ones: expand the square into a double
`tsum` over `ℤ × ℤ`, split the index set according to the parity of `m + n`, and use the
involutions `(m,n) = (a+b, a-b)` (even) resp. `(m,n) = (a+b, a-b-1)` (odd).
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-! ### Summability of the model series

We first record absolute convergence of the two basic one-variable series, in the form
needed by `tsum_mul_tsum_of_summable_norm`. -/

/-- `∑'_{n:ℤ} R^{n²}` converges for `0 ≤ R < 1`. -/
lemma summable_int_pow_sq (R : ℝ) (h0 : 0 ≤ R) (h1 : R < 1) :
    Summable (fun n : ℤ => R ^ (n ^ 2)) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · have hle : ∀ n : ℕ, R ^ (n ^ 2) ≤ R ^ n := fun n =>
      pow_le_pow_of_le_one h0 h1.le (Nat.le_self_pow (by norm_num) n)
    have h1' : (fun n : ℕ => R ^ ((n : ℤ) ^ 2)) = fun n : ℕ => R ^ (n ^ 2) := by
      funext n; rw [← Nat.cast_pow, zpow_natCast]
    rw [h1']
    exact Summable.of_nonneg_of_le (fun n => by positivity) hle (summable_geometric_of_lt_one h0 h1)
  · have hle : ∀ n : ℕ, R ^ ((n+1) ^ 2) ≤ R ^ n := fun n =>
      pow_le_pow_of_le_one h0 h1.le (by nlinarith)
    have h1' : (fun n : ℕ => R ^ ((-((n : ℤ) + 1)) ^ 2)) = fun n : ℕ => R ^ ((n+1) ^ 2) := by
      funext n
      have harg : (-((n : ℤ) + 1)) ^ 2 = ((n+1)^2 : ℕ) := by push_cast; ring
      rw [harg, zpow_natCast]
    rw [h1']
    exact Summable.of_nonneg_of_le (fun n => by positivity) hle (summable_geometric_of_lt_one h0 h1)

/-- `∑'_{n:ℤ} R^{n(n+1)}` converges for `0 ≤ R < 1`. -/
lemma summable_int_pow_mul_succ (R : ℝ) (h0 : 0 ≤ R) (h1 : R < 1) :
    Summable (fun n : ℤ => R ^ (n * (n + 1))) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · have hle : ∀ n : ℕ, R ^ (n * (n+1)) ≤ R ^ n := fun n =>
      pow_le_pow_of_le_one h0 h1.le (by nlinarith)
    have h1' : (fun n : ℕ => R ^ ((n : ℤ) * ((n : ℤ) + 1))) = fun n : ℕ => R ^ (n * (n+1)) := by
      funext n
      have harg : (n:ℤ) * ((n:ℤ)+1) = ((n * (n+1) : ℕ) : ℤ) := by push_cast; ring
      rw [harg, zpow_natCast]
    rw [h1']
    exact Summable.of_nonneg_of_le (fun n => by positivity) hle (summable_geometric_of_lt_one h0 h1)
  · have hle : ∀ n : ℕ, R ^ (n * (n+1)) ≤ R ^ n := fun n =>
      pow_le_pow_of_le_one h0 h1.le (by nlinarith)
    have h1' : (fun n : ℕ => R ^ ((-((n:ℤ)+1)) * ((-((n:ℤ)+1))+1))) = fun n : ℕ => R ^ (n*(n+1)) := by
      funext n
      have harg : (-((n:ℤ)+1)) * ((-((n:ℤ)+1))+1) = ((n*(n+1) : ℕ) : ℤ) := by push_cast; ring
      rw [harg, zpow_natCast]
    rw [h1']
    exact Summable.of_nonneg_of_le (fun n => by positivity) hle (summable_geometric_of_lt_one h0 h1)

/-- Norm summability of the `θ₃` summand. -/
lemma summable_norm_pow_sq (y : ℂ) (hy : ‖y‖ < 1) :
    Summable (fun n : ℤ => ‖y ^ (n ^ 2)‖) := by
  have h : (fun n : ℤ => ‖y ^ (n^2)‖) = fun n : ℤ => ‖y‖ ^ (n^2) := by
    funext n; rw [norm_zpow]
  rw [h]
  exact summable_int_pow_sq ‖y‖ (norm_nonneg y) hy

/-- Norm summability of the `θ₂` summand. -/
lemma summable_norm_pow_mul_succ (y : ℂ) (hy : ‖y‖ < 1) :
    Summable (fun n : ℤ => ‖y ^ (n * (n + 1))‖) := by
  have h : (fun n : ℤ => ‖y ^ (n*(n+1))‖) = fun n : ℤ => ‖y‖ ^ (n*(n+1)) := by
    funext n; rw [norm_zpow]
  rw [h]
  exact summable_int_pow_mul_succ ‖y‖ (norm_nonneg y) hy

/-- Norm summability of the `θ₄` summand. -/
lemma summable_norm_pow_sq_mul (y : ℂ) (hy : ‖y‖ < 1) :
    Summable (fun n : ℤ => ‖(-1 : ℂ)^n * y ^ (n ^ 2)‖) := by
  refine Summable.congr (summable_norm_pow_sq y hy) (fun n => ?_)
  rw [norm_mul, norm_zpow]
  norm_num

/-! ### Integer power algebra

`zpow` is total on `ℂ` (with `x^0 = 1` even for `x = 0`), and the usual `zpow_add`/`zpow_mul`
fail at `x = 0` with negative exponents. On the non-negative exponents that occur here both
laws hold, and we record them. -/

/-- `x^{a+b} = x^a x^b` for non-negative `a, b` (valid also for `x = 0`). -/
lemma zpow_add_nn (x : ℂ) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ^ (a + b) = x ^ a * x ^ b := by
  rw [show a = (a.toNat : ℤ) from (Int.toNat_of_nonneg ha).symm,
      show b = (b.toNat : ℤ) from (Int.toNat_of_nonneg hb).symm]
  rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

/-- `x^{a b} = (x^a)^b` for non-negative `a, b` (valid also for `x = 0`). -/
lemma zpow_mul_nn (x : ℂ) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ^ (a * b) = (x ^ a) ^ b := by
  rw [show a = (a.toNat : ℤ) from (Int.toNat_of_nonneg ha).symm,
      show b = (b.toNat : ℤ) from (Int.toNat_of_nonneg hb).symm]
  rw [← Nat.cast_mul, zpow_natCast, zpow_natCast, zpow_natCast, pow_mul]

/-- `x^{2b} = (x^2)^b` for `b ≥ 0`. -/
lemma zpow_two_mul (x : ℂ) {b : ℤ} (hb : 0 ≤ b) : x ^ (2 * b) = (x ^ 2) ^ b := by
  simpa using zpow_mul_nn x (by norm_num : (0:ℤ) ≤ 2) hb

/-- `a(a-1) ≥ 0` for integers. -/
lemma sq_sub_self_nonneg (a : ℤ) : 0 ≤ a * (a - 1) := by
  rcases le_or_gt a 0 with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- `a(a+1) ≥ 0` for integers. -/
lemma mul_self_add_self_nonneg (b : ℤ) : 0 ≤ b * (b + 1) := by
  rcases lt_or_ge b 0 with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg h (by omega)

/-! ### The parity splitting of a double sum over `ℤ × ℤ`

The map `(m,n) = (a+b, a-b)` parameterises the `m + n` even pairs and `(m,n) = (a+b, a-b-1)`
the odd ones; together they give a bijection `(ℤ×ℤ) ⊕ (ℤ×ℤ) ≃ ℤ×ℤ`. -/

/-- `(a,b) ↦ (a+b, a-b)` on the left summand and `(a,b) ↦ (a+b, a-b-1)` on the right summand. -/
def dupeMap : (ℤ × ℤ) ⊕ (ℤ × ℤ) → ℤ × ℤ
  | Sum.inl p => (p.1 + p.2, p.1 - p.2)
  | Sum.inr p => (p.1 + p.2, p.1 - p.2 - 1)

lemma dupeMap_inj : Function.Injective dupeMap := by
  rintro (⟨a,b⟩ | ⟨a,b⟩) (⟨a',b'⟩ | ⟨a',b'⟩) h <;>
    simp only [dupeMap, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h ⊢ <;> omega

lemma dupeMap_surj : Function.Surjective dupeMap := by
  rintro ⟨m, n⟩
  rcases Int.even_or_odd (m + n) with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨Sum.inl (k, k - n), ?_⟩
    simp only [dupeMap, Prod.mk.injEq]; omega
  · refine ⟨Sum.inr (k+1, k - n), ?_⟩
    simp only [dupeMap, Prod.mk.injEq]; omega

/- **Parity splitting of a double sum over `ℤ×ℤ`.** -/
set_option maxHeartbeats 4000000 in
lemma tsum_int_sq_split (f : ℤ × ℤ → ℂ) (hf : Summable f) :
    ∑' p : ℤ × ℤ, f p
      = (∑' q : ℤ × ℤ, f (q.1 + q.2, q.1 - q.2))
        + (∑' q : ℤ × ℤ, f (q.1 + q.2, q.1 - q.2 - 1)) := by
  let e : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ := Equiv.ofBijective dupeMap ⟨dupeMap_inj, dupeMap_surj⟩
  have hsum : Summable (fun s : (ℤ × ℤ) ⊕ (ℤ × ℤ) => f (e s)) := (Equiv.summable_iff e).mpr hf
  have hl : Summable (fun a : ℤ × ℤ => f (e (Sum.inl a))) := hsum.comp_injective Sum.inl_injective
  have hr : Summable (fun a : ℤ × ℤ => f (e (Sum.inr a))) := hsum.comp_injective Sum.inr_injective
  have h1 : (fun i : ℤ × ℤ => f (e (Sum.inl i))) = fun i => f (i.1 + i.2, i.1 - i.2) := by
    funext i; rfl
  have h2 : (fun i : ℤ × ℤ => f (e (Sum.inr i))) = fun i => f (i.1 + i.2, i.1 - i.2 - 1) := by
    funext i; rfl
  rw [← e.tsum_eq f, Summable.tsum_sum hl hr, h1, h2]

/-! ### Pointwise exponent identities

For the even parameterisation: -/

lemma dup_even (x : ℂ) (a b : ℤ) :
    x ^ ((a+b)^2 + (a-b)^2) = (x^2)^(a^2) * (x^2)^(b^2) := by
  have h1 : (a+b)^2 + (a-b)^2 = 2*(a^2) + 2*(b^2) := by ring
  rw [h1, zpow_add_nn x (by positivity) (by positivity)]
  rw [zpow_two_mul x (sq_nonneg a), zpow_two_mul x (sq_nonneg b)]

lemma dup_even2 (x : ℂ) (a b : ℤ) :
    x ^ ((a+b)*(a+b+1) + (a-b)*(a-b+1)) = (x^2)^(a*(a+1)) * (x^2)^(b^2) := by
  have h1 : (a+b)*(a+b+1) + (a-b)*(a-b+1) = 2*(a*(a+1)) + 2*(b^2) := by ring
  rw [h1, zpow_add_nn x (by have := mul_self_add_self_nonneg a; linarith) (by positivity)]
  rw [zpow_two_mul x (mul_self_add_self_nonneg a), zpow_two_mul x (sq_nonneg b)]

lemma dup_even4 (x : ℂ) (a b : ℤ) :
    ((-1 : ℂ)^(a+b) * x^((a+b)^2)) * ((-1)^(a-b) * x^((a-b)^2))
      = (x^2)^(a^2) * (x^2)^(b^2) := by
  have h1 : ((-1 : ℂ)^(a+b) * x^((a+b)^2)) * ((-1)^(a-b) * x^((a-b)^2))
      = ((-1)^(a+b) * (-1)^(a-b)) * (x^((a+b)^2) * x^((a-b)^2)) := by ring
  rw [h1, ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0) (a+b) (a-b),
      Even.neg_one_zpow (show Even ((a+b) + (a-b)) from ⟨a, by ring⟩),
      one_mul, ← zpow_add_nn x (sq_nonneg (a+b)) (sq_nonneg (a-b))]
  exact dup_even x a b

/-- For the odd parameterisation: -/

lemma dup_odd (x : ℂ) (a b : ℤ) :
    x ^ ((a+b)^2 + (a-b-1)^2) = x * ((x^2)^(a*(a-1)) * (x^2)^(b*(b+1))) := by
  have h1 : (a+b)^2 + (a-b-1)^2 = 2*(a*(a-1)) + (2*(b*(b+1)) + 1) := by ring
  rw [h1]
  rw [zpow_add_nn x (by have := sq_sub_self_nonneg a; linarith)
        (by have := mul_self_add_self_nonneg b; linarith)]
  rw [zpow_add_nn x (by have := mul_self_add_self_nonneg b; linarith) (by norm_num), zpow_one]
  rw [zpow_two_mul x (sq_sub_self_nonneg a), zpow_two_mul x (mul_self_add_self_nonneg b)]
  ring

lemma dup_odd2 (x : ℂ) (a b : ℤ) :
    x ^ ((a+b)*(a+b+1) + (a-b-1)*((a-b-1)+1)) = (x^2)^(a^2) * (x^2)^(b*(b+1)) := by
  have h1 : (a+b)*(a+b+1) + (a-b-1)*((a-b-1)+1) = 2*(a^2) + 2*(b*(b+1)) := by ring
  rw [h1, zpow_add_nn x (by positivity) (by have := mul_self_add_self_nonneg b; linarith)]
  rw [zpow_two_mul x (sq_nonneg a), zpow_two_mul x (mul_self_add_self_nonneg b)]

lemma dup_odd4 (x : ℂ) (a b : ℤ) :
    ((-1 : ℂ)^(a+b) * x^((a+b)^2)) * ((-1)^(a-b-1) * x^((a-b-1)^2))
      = - (x * ((x^2)^(a*(a-1)) * (x^2)^(b*(b+1)))) := by
  have h1 : ((-1 : ℂ)^(a+b) * x^((a+b)^2)) * ((-1)^(a-b-1) * x^((a-b-1)^2))
      = ((-1)^(a+b) * (-1)^(a-b-1)) * (x^((a+b)^2) * x^((a-b-1)^2)) := by ring
  rw [h1, ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0) (a+b) (a-b-1),
      Odd.neg_one_zpow (show Odd ((a+b) + (a-b-1)) from ⟨a-1, by ring⟩),
      neg_one_mul, ← zpow_add_nn x (sq_nonneg (a+b)) (sq_nonneg (a-b-1))]
  exact congrArg Neg.neg (dup_odd x a b)

/-! ### Identifying the pieces as products of theta series -/

lemma sq_sum_eq (y : ℂ) (hy : ‖y‖ < 1) :
    (∑' q : ℤ×ℤ, y^(q.1^2) * y^(q.2^2)) = T3 y ^ 2 := by
  rw [← tsum_mul_tsum_of_summable_norm (summable_norm_pow_sq y hy) (summable_norm_pow_sq y hy)]
  rw [show T3 y ^ 2 = T3 y * T3 y from by ring]
  simp only [T3]

lemma succ_sum_eq (y : ℂ) (hy : ‖y‖ < 1) :
    (∑' q : ℤ×ℤ, y^(q.1*(q.1+1)) * y^(q.2*(q.2+1))) = T2 y ^ 2 := by
  rw [← tsum_mul_tsum_of_summable_norm (summable_norm_pow_mul_succ y hy)
        (summable_norm_pow_mul_succ y hy)]
  rw [show T2 y ^ 2 = T2 y * T2 y from by ring]
  simp only [T2]

lemma odd_sum_eq (y : ℂ) (hy : ‖y‖ < 1) :
    (∑' q : ℤ×ℤ, y^(q.1*(q.1-1)) * y^(q.2*(q.2+1))) = T2 y ^ 2 := by
  have hsn : Summable (fun a : ℤ => ‖y^(a*(a-1))‖) := by
    refine Summable.congr ((Equiv.summable_iff (Equiv.neg ℤ)).mpr
      (summable_norm_pow_mul_succ y hy)) (fun a => ?_)
    simp only [Function.comp_apply, Equiv.neg_apply]
    rw [show -a * (-a + 1) = a * (a - 1) from by ring]
  rw [← tsum_mul_tsum_of_summable_norm hsn (summable_norm_pow_mul_succ y hy)]
  have hA : (∑' a : ℤ, y^(a*(a-1))) = (∑' b : ℤ, y^(b*(b+1))) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => y^(n*(n+1)))]
    apply tsum_congr; intro n
    simp only [Equiv.neg_apply]
    rw [show -n * (-n + 1) = n * (n - 1) from by ring]
  rw [hA, show T2 y ^ 2 = T2 y * T2 y from by ring]
  simp only [T2]

lemma mixed_sum_eq (y : ℂ) (hy : ‖y‖ < 1) :
    (∑' q : ℤ×ℤ, y^(q.1*(q.1+1)) * y^(q.2^2)) = T2 y * T3 y := by
  rw [← tsum_mul_tsum_of_summable_norm (summable_norm_pow_mul_succ y hy)
        (summable_norm_pow_sq y hy)]
  simp only [T2, T3]

lemma mixed_sum_eq' (y : ℂ) (hy : ‖y‖ < 1) :
    (∑' q : ℤ×ℤ, y^(q.1^2) * y^(q.2*(q.2+1))) = T3 y * T2 y := by
  rw [← tsum_mul_tsum_of_summable_norm (summable_norm_pow_sq y hy)
        (summable_norm_pow_mul_succ y hy)]
  simp only [T3, T2]


end

end Work.Haupt
