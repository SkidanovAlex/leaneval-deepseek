import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- The elementary-symmetric recursion for `powersetCard`: adding a new element `a ∉ s`,
the `(n+1)`-element subsets of `insert a s` split into those contained in `s` and those
of the form `insert a B` with `B ⊆ s` of size `n`. -/
theorem sum_powersetCard_insert_succ {ι : Type*} [DecidableEq ι] (s : Finset ι) {a : ι}
    (ha : a ∉ s) (x : ι → ℝ) (n : ℕ) :
    ∑ B ∈ (insert a s).powersetCard (n + 1), ∏ i ∈ B, x i
      = ∑ B ∈ s.powersetCard (n + 1), ∏ i ∈ B, x i
        + x a * ∑ B ∈ s.powersetCard n, ∏ i ∈ B, x i := by
  have hrec := Finset.powersetCard_succ_insert ha n
  rw [hrec]
  have hdisj : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    rw [Finset.mem_image] at hB2
    obtain ⟨B', _, rfl⟩ := hB2
    exact ha ((Finset.mem_powersetCard.mp hB1).1 (Finset.mem_insert_self a B'))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [Finset.prod_insert (fun h => ha ((Finset.mem_powersetCard.mp hB).1 h))]
  · intro B hB B' hB' h
    have haB : a ∉ B := fun hh => ha ((Finset.mem_powersetCard.mp hB).1 hh)
    have haB' : a ∉ B' := fun hh => ha ((Finset.mem_powersetCard.mp hB').1 hh)
    have := congrArg (fun C : Finset ι => C.erase a) h
    rwa [Finset.erase_insert haB, Finset.erase_insert haB'] at this

/-- The binomial lower bound: for `S, y ≥ 0` and `n : ℕ` the sum of the first two terms of
`(y + S)^{n+1}` is at most `(y + S)^{n+1}`. -/
theorem binom_pow_lower_bound (S y : ℝ) (hS : 0 ≤ S) (hy : 0 ≤ y) (n : ℕ) :
    S ^ (n + 1) + ((n : ℝ) + 1) * y * S ^ n ≤ (y + S) ^ (n + 1) := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 2) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> simp
  have hkey : (y + S) ^ (n + 1)
      = ∑ m ∈ Finset.range (n + 2), y ^ m * S ^ (n + 1 - m) * ((n + 1).choose m : ℝ) := by
    rw [add_pow]
  rw [hkey]
  calc S ^ (n + 1) + ((n : ℝ) + 1) * y * S ^ n
      = ∑ m ∈ ({0, 1} : Finset ℕ), y ^ m * S ^ (n + 1 - m) * ((n + 1).choose m : ℝ) := by
        rw [Finset.sum_insert (by simp), Finset.sum_singleton]
        simp [Nat.choose_one_right]
        ring
    _ ≤ ∑ m ∈ Finset.range (n + 2), y ^ m * S ^ (n + 1 - m) * ((n + 1).choose m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro m _ _; positivity)

/-- **Factorial times the `b`-th elementary symmetric sum.**  For finitely many nonnegative
reals `x`, the `b`-th elementary symmetric sum is at most `(∑ x)^b / b!`.  Equivalently,
`b! * e_b(x) ≤ (∑ x)^b`.  (This is the elementary-symmetric-function form of the
multinomial inequality; it is the `b!`-weighted "extract the injective terms" bound used in
the Ionescu–Wainger analysis.) -/
theorem factorial_mul_powersetCard_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (b : ℕ) :
    (b.factorial : ℝ) * ∑ B ∈ s.powersetCard b, ∏ i ∈ B, x i ≤ (∑ i ∈ s, x i) ^ b := by
  classical
  have key : ∀ (s : Finset ι), (∀ i ∈ s, 0 ≤ x i) →
      ∀ b, (b.factorial : ℝ) * ∑ B ∈ s.powersetCard b, ∏ i ∈ B, x i ≤ (∑ i ∈ s, x i) ^ b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ b
      cases b with
      | zero => simp
      | succ k =>
        rw [Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < k + 1)]
        simp
    | insert a s ha ih =>
      intro hx b
      have ha0 : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∑ i ∈ s, x i :=
        Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      cases b with
      | zero => simp
      | succ k =>
        rw [sum_powersetCard_insert_succ s ha x k, Finset.sum_insert ha]
        have hF := ih hxs (k + 1)
        have hG := ih hxs k
        have hstep : ((k + 1).factorial : ℝ) *
              ((∑ B ∈ s.powersetCard (k + 1), ∏ i ∈ B, x i)
                + x a * ∑ B ∈ s.powersetCard k, ∏ i ∈ B, x i)
            ≤ (∑ i ∈ s, x i) ^ (k + 1)
              + ((k : ℝ) + 1) * x a * (∑ i ∈ s, x i) ^ k := by
          have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          rw [mul_add]
          refine add_le_add hF ?_
          rw [hfac]
          have hrw : ((k : ℝ) + 1) * (k.factorial : ℝ)
                * (x a * ∑ B ∈ s.powersetCard k, ∏ i ∈ B, x i)
              = ((k : ℝ) + 1) * x a
                * ((k.factorial : ℝ) * ∑ B ∈ s.powersetCard k, ∏ i ∈ B, x i) := by ring
          rw [hrw]
          exact mul_le_mul_of_nonneg_left hG (mul_nonneg (by positivity) ha0)
        calc ((k + 1).factorial : ℝ) *
              ((∑ B ∈ s.powersetCard (k + 1), ∏ i ∈ B, x i)
                + x a * ∑ B ∈ s.powersetCard k, ∏ i ∈ B, x i)
            ≤ (∑ i ∈ s, x i) ^ (k + 1)
              + ((k : ℝ) + 1) * x a * (∑ i ∈ s, x i) ^ k := hstep
          _ ≤ (x a + ∑ i ∈ s, x i) ^ (k + 1) := binom_pow_lower_bound _ _ hs0 ha0 k
  exact key s hx b

end Work.BourgainPlan.IonescuWainger
