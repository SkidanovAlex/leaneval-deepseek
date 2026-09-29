import Mathlib

/-!
# Summing a coefficient recurrence against a geometric weight

`tsum_ode_of_rec` turns the term-wise recurrence

`4 n c n - (n-1) c (n-1) = 2 c n - [n=0 ? 0 : c (n-1)] + (4 b n - [n=0 ? 0 : b (n-1)])
   - [n=1] 8 + [n=2] 2`

into the ODE identity for the generating functions
`F z = Σ c n z^n`, `G z = Σ b n z^n`:

`y (4 - y) F'(y) = (2 - y) F(y) + (4 - y) G(y) - 2 y (4 - y)`.

The proof multiplies the recurrence by `y^n`, sums over `n` (using the given summability
hypotheses and the given expression for `F'(y)`) and evaluates the six resulting series by
the elementary closed forms `Σ c (n-1) y^n = y F(y)`, `Σ n c n y^n = y F'(y)`, etc.
-/

namespace Work.CPull

/-- The `(0,1)`-shifted series `Σ (if n = 0 then 0 else f (n-1)) y^n` is summable whenever
`Σ f n y^n` is. -/
private lemma summable_ite_zero_shift (f : ℕ → ℂ) (y : ℂ)
    (hf : Summable fun n : ℕ => f n * y ^ n) :
    Summable fun n : ℕ => (if n = 0 then 0 else f (n - 1)) * y ^ n := by
  apply (summable_nat_add_iff 1).mp
  refine (hf.mul_right y).congr fun n => ?_
  rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  ring

/-- `Σ (if n = 0 then 0 else f (n-1)) y^n = y Σ f n y^n`. -/
private lemma tsum_ite_zero_shift (f : ℕ → ℂ) (y : ℂ)
    (hf : Summable fun n : ℕ => f n * y ^ n) :
    ∑' n : ℕ, (if n = 0 then 0 else f (n - 1)) * y ^ n = y * ∑' n : ℕ, f n * y ^ n := by
  have hF := summable_ite_zero_shift f y hf
  rw [Summable.tsum_eq_zero_add hF]
  simp only [if_true, zero_mul, zero_add]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by
    rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]; ring

/-- `Σ n f n y^n = y Σ (n+1) f (n+1) y^n`: the derivative-series reindexing. -/
private lemma tsum_nat_mul_pow_eq (f : ℕ → ℂ) (y : ℂ)
    (hf : Summable fun n : ℕ => (n : ℂ) * f n * y ^ n) :
    ∑' n : ℕ, (n : ℂ) * f n * y ^ n
      = y * ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * f (n + 1) * y ^ n := by
  rw [Summable.tsum_eq_zero_add hf]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by rw [pow_succ]; ring

/-- `Σ (n-1) f (n-1) y^n = y Σ n f n y^n`. -/
private lemma tsum_pred_mul_pow_eq (f : ℕ → ℂ) (y : ℂ)
    (hf : Summable fun n : ℕ => (n : ℂ) * f n * y ^ n) :
    ∑' n : ℕ, ((((n - 1 : ℕ) : ℂ)) * f (n - 1)) * y ^ n
      = y * ∑' n : ℕ, (n : ℂ) * f n * y ^ n := by
  have hF : Summable fun m : ℕ => (((m - 1 : ℕ) : ℂ) * f (m - 1)) * y ^ m := by
    apply (summable_nat_add_iff 1).mp
    refine (hf.mul_right y).congr fun n => ?_
    simp only [Nat.add_sub_cancel]
    ring
  rw [Summable.tsum_eq_zero_add hF]
  simp only [Nat.zero_sub, Nat.cast_zero, zero_mul, zero_add, pow_zero, mul_one]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring

/-- `Σ (if n = 1 then 8 else 0) y^n` is summable (finite support). -/
private lemma summable_ite_eq_one (y : ℂ) :
    Summable fun n : ℕ => (if n = 1 then 8 else 0) * y ^ n := by
  refine summable_of_ne_finset_zero (s := ({1} : Finset ℕ)) ?_
  intro b hb
  rw [Finset.mem_singleton] at hb
  rw [if_neg hb, zero_mul]

/-- `Σ (if n = 2 then 2 else 0) y^n` is summable (finite support). -/
private lemma summable_ite_eq_two (y : ℂ) :
    Summable fun n : ℕ => (if n = 2 then 2 else 0) * y ^ n := by
  refine summable_of_ne_finset_zero (s := ({2} : Finset ℕ)) ?_
  intro b hb
  rw [Finset.mem_singleton] at hb
  rw [if_neg hb, zero_mul]

/-- `Σ (if n = 1 then 8 else 0) y^n = 8 y`. -/
private lemma tsum_ite_eq_one (y : ℂ) :
    (∑' n : ℕ, (if n = 1 then 8 else 0) * y ^ n) = 8 * y := by
  rw [tsum_eq_single 1 (fun b hb => by rw [if_neg hb, zero_mul])]
  norm_num

/-- `Σ (if n = 2 then 2 else 0) y^n = 2 y ^ 2`. -/
private lemma tsum_ite_eq_two (y : ℂ) :
    (∑' n : ℕ, (if n = 2 then 2 else 0) * y ^ n) = 2 * y ^ 2 := by
  rw [tsum_eq_single 2 (fun b hb => by rw [if_neg hb, zero_mul])]
  norm_num

theorem tsum_ode_of_rec (c b : ℕ → ℂ) (y : ℂ)
    (hrec : ∀ n : ℕ, 4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))
      = 2 * c n - (if n = 0 then 0 else c (n - 1))
        + (4 * b n - (if n = 0 then 0 else b (n - 1)))
        - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0))
    (hS : Summable fun n : ℕ => c n * y ^ n)
    (hS2 : Summable fun n : ℕ => ((n : ℂ)) * c n * y ^ n)
    (hS3 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
    (hT : Summable fun n : ℕ => b n * y ^ n)
    (hderiv : deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) :
    y * (4 - y) * deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = (2 - y) * (∑' n : ℕ, c n * y ^ n) + (4 - y) * (∑' n : ℕ, b n * y ^ n)
        - 2 * y * (4 - y) := by
  have _hS3 := hS3
  -- The two basic reindexings of the derivative series.
  have hA := tsum_nat_mul_pow_eq c y hS2
  have hB := tsum_pred_mul_pow_eq c y hS2
  -- Summabilities of the individual terms of the left-hand side.
  have hf1 : Summable fun n : ℕ => 4 * ((n : ℂ) * c n * y ^ n) := hS2.mul_left 4
  have hf2 : Summable fun n : ℕ => ((((n - 1 : ℕ) : ℂ)) * c (n - 1)) * y ^ n := by
    apply (summable_nat_add_iff 1).mp
    refine (hS2.mul_right y).congr fun n => ?_
    simp only [Nat.add_sub_cancel]
    ring
  -- Value of the summed left-hand side.
  have hLval :
      (∑' n : ℕ, (4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
        = y * (4 - y) * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) := by
    have e1 :
        (∑' n : ℕ, (4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
          = ∑' n : ℕ,
              (4 * ((n : ℂ) * c n * y ^ n) - ((((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n)) :=
      tsum_congr fun n => by ring
    rw [e1, Summable.tsum_sub hf1 hf2]
    rw [Summable.tsum_mul_left 4 hS2]
    rw [hB, hA]
    ring
  -- Value of the summed right-hand side.
  have hRval :
      (∑' n : ℕ, (2 * c n - (if n = 0 then 0 else c (n - 1))
          + (4 * b n - (if n = 0 then 0 else b (n - 1)))
          - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0)) * y ^ n)
        = (2 - y) * (∑' n : ℕ, c n * y ^ n) + (4 - y) * (∑' n : ℕ, b n * y ^ n)
          - 2 * y * (4 - y) := by
    have hFc : Summable fun m : ℕ => (if m = 0 then 0 else c (m - 1)) * y ^ m :=
      summable_ite_zero_shift c y hS
    have hFb : Summable fun m : ℕ => (if m = 0 then 0 else b (m - 1)) * y ^ m :=
      summable_ite_zero_shift b y hT
    have s1 : Summable fun n : ℕ => 2 * (c n * y ^ n) := hS.mul_left 2
    have s3 : Summable fun n : ℕ => 4 * (b n * y ^ n) := hT.mul_left 4
    have s5 : Summable fun n : ℕ => (if n = 1 then 8 else 0) * y ^ n := summable_ite_eq_one y
    have s6 : Summable fun n : ℕ => (if n = 2 then 2 else 0) * y ^ n := summable_ite_eq_two y
    have t1 : Summable fun n : ℕ =>
        2 * (c n * y ^ n) - (if n = 0 then 0 else c (n - 1)) * y ^ n := s1.sub hFc
    have t2 : Summable fun n : ℕ =>
        2 * (c n * y ^ n) - (if n = 0 then 0 else c (n - 1)) * y ^ n + 4 * (b n * y ^ n) :=
      t1.add s3
    have t3 : Summable fun n : ℕ =>
        2 * (c n * y ^ n) - (if n = 0 then 0 else c (n - 1)) * y ^ n + 4 * (b n * y ^ n)
          - (if n = 0 then 0 else b (n - 1)) * y ^ n := t2.sub hFb
    have t4 : Summable fun n : ℕ =>
        2 * (c n * y ^ n) - (if n = 0 then 0 else c (n - 1)) * y ^ n + 4 * (b n * y ^ n)
          - (if n = 0 then 0 else b (n - 1)) * y ^ n - (if n = 1 then 8 else 0) * y ^ n :=
      t3.sub s5
    have eR :
        (∑' n : ℕ, (2 * c n - (if n = 0 then 0 else c (n - 1))
            + (4 * b n - (if n = 0 then 0 else b (n - 1)))
            - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0)) * y ^ n)
          = ∑' n : ℕ,
              (2 * (c n * y ^ n) - (if n = 0 then 0 else c (n - 1)) * y ^ n
                + 4 * (b n * y ^ n) - (if n = 0 then 0 else b (n - 1)) * y ^ n
                - (if n = 1 then 8 else 0) * y ^ n + (if n = 2 then 2 else 0) * y ^ n) :=
      tsum_congr fun n => by ring
    rw [eR]
    rw [Summable.tsum_add t4 s6]
    rw [Summable.tsum_sub t3 s5]
    rw [Summable.tsum_sub t2 hFb]
    rw [Summable.tsum_add t1 s3]
    rw [Summable.tsum_sub s1 hFc]
    rw [Summable.tsum_mul_left 2 hS, Summable.tsum_mul_left 4 hT]
    rw [tsum_ite_zero_shift c y hS, tsum_ite_zero_shift b y hT, tsum_ite_eq_one, tsum_ite_eq_two]
    ring
  -- Summing the recurrence.
  have key :
      (∑' n : ℕ, (4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
        = ∑' n : ℕ, (2 * c n - (if n = 0 then 0 else c (n - 1))
            + (4 * b n - (if n = 0 then 0 else b (n - 1)))
            - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0)) * y ^ n :=
    tsum_congr fun n => by rw [hrec n]
  rw [hderiv, ← hLval, key, hRval]

end Work.CPull
