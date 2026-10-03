import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs

open Set Finset

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- A perfect square of an integer is the cast of a natural square. -/
private lemma int_sq_eq (a : ℤ) : a ^ 2 = ((a.natAbs ^ 2 : ℕ) : ℤ) := by
  rw [← Int.natAbs_sq a, Nat.cast_pow]

/-- A fourth power of an integer is the cast of a natural fourth power. -/
private lemma int_pow_four_eq (b : ℤ) : b ^ 4 = ((b.natAbs ^ 4 : ℕ) : ℤ) := by
  rw [← Int.natAbs_of_nonneg (show (0 : ℤ) ≤ b ^ 4 by positivity), Int.natAbs_pow, Nat.cast_pow]

private lemma int_sq_add_pow_four_eq (a b : ℤ) :
    a ^ 2 + b ^ 4 = ((a.natAbs ^ 2 + b.natAbs ^ 4 : ℕ) : ℤ) := by
  rw [int_sq_eq, int_pow_four_eq, ← Nat.cast_add]

/-- Membership of an integer in a symmetric interval `[-n, n]` is equivalent to
its absolute value being at most `n`. -/
private lemma int_mem_Icc_iff (a : ℤ) (n : ℕ) :
    a ∈ Finset.Icc (-(n:ℤ)) n ↔ a.natAbs ≤ n := by
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |a| ≤ (n:ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |a| ≤ (n:ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h
    exact abs_le.mp h'

private lemma natAbs_le_sqrt_of_sq_le {a : ℤ} {x : ℕ} (h : a ^ 2 ≤ (x : ℤ)) :
    a.natAbs ≤ Nat.sqrt x := by
  rw [Nat.le_sqrt']
  have h' : ((a.natAbs ^ 2 : ℕ) : ℤ) ≤ (x : ℤ) := by
    rw [Nat.cast_pow, Int.natAbs_sq a]; exact h
  exact_mod_cast h'

private lemma natAbs_le_sqrt_sqrt_of_pow_four_le {b : ℤ} {x : ℕ} (h : b ^ 4 ≤ (x : ℤ)) :
    b.natAbs ≤ Nat.sqrt (Nat.sqrt x) := by
  have h' : b.natAbs ^ 4 ≤ x := by
    have : ((b.natAbs ^ 4 : ℕ) : ℤ) ≤ (x : ℤ) := by
      rw [← int_pow_four_eq b]; exact h
    exact_mod_cast this
  exact Nat.lt_succ_iff.mp (pow_four_le_iff_lt_sqrt_sqrt_succ.mp h')

private lemma natAbs_eq_iff_eq_or_eq_neg {a : ℤ} {c : ℕ} :
    a.natAbs = c ↔ a = (c : ℤ) ∨ a = -(c : ℤ) := by
  constructor
  · intro h
    rcases Int.natAbs_eq a with h' | h'
    · exact Or.inl (by rw [h', h])
    · exact Or.inr (by rw [h', h])
  · rintro (h | h) <;> · rw [h]; simp

/-- The set of integers with a prescribed absolute value has `1` element if the
value is `0` and `2` elements otherwise. -/
private lemma ncard_natAbs_eq (c : ℕ) :
    ({a : ℤ | a.natAbs = c}).ncard = if c = 0 then 1 else 2 := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    have hset : ({a : ℤ | a.natAbs = 0} : Set ℤ) = {0} := by
      ext a; rw [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact Int.natAbs_eq_zero
    rw [hset, if_pos rfl, Set.ncard_singleton]
  · have hset : ({a : ℤ | a.natAbs = c} : Set ℤ) = insert (c:ℤ) {-(c:ℤ)} := by
      ext a
      rw [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
          natAbs_eq_iff_eq_or_eq_neg]
    rw [hset, if_neg hc]
    rw [Set.ncard_insert_of_notMem (s := {-(c:ℤ)})
      (by
        rw [Set.mem_singleton_iff]
        intro h
        have h2 : (c:ℤ) = 0 := by omega
        exact hc (by exact_mod_cast h2))]
    simp

/-- The number of integer pairs `(a, b)` with prescribed absolute values is the
product of the two one-dimensional counts. -/
private lemma ncard_fiber_intpairs (q : ℕ × ℕ) :
    ({p : ℤ × ℤ | p.1.natAbs = q.1 ∧ p.2.natAbs = q.2}).ncard =
      (if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2) := by
  have hset : ({p : ℤ × ℤ | p.1.natAbs = q.1 ∧ p.2.natAbs = q.2} : Set (ℤ × ℤ)) =
      {a : ℤ | a.natAbs = q.1} ×ˢ {b : ℤ | b.natAbs = q.2} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_prod]
  rw [hset, Set.ncard_prod, ncard_natAbs_eq, ncard_natAbs_eq]

/-- A prime is not a perfect square. -/
private lemma nat_sq_ne_prime {p x : ℕ} (hp : p.Prime) (h : x ^ 2 = p) : False := by
  have hdvd : x ∣ p := ⟨x, by rw [← h]; ring⟩
  rcases hp.eq_one_or_self_of_dvd x hdvd with hx | hx
  · have hp1 : p = 1 := by rw [hx] at h; simpa using h.symm
    exact hp.ne_one hp1
  · have h2 : p * p = p := by
      rw [← hx] at h ⊢
      simpa [pow_two] using h
    exact hp.ne_one (Nat.mul_left_cancel hp.pos (by rw [h2, Nat.mul_one]))

/-- A prime is not a perfect fourth power. -/
private lemma nat_pow_four_ne_prime {p y : ℕ} (hp : p.Prime) (h : y ^ 4 = p) : False :=
  nat_sq_ne_prime hp (x := y ^ 2) (by rw [show (y ^ 2) ^ 2 = y ^ 4 by ring, h])

theorem ncard_int_pow_two_add_pow_four_prime {p : ℕ} (hp : p.Prime) :
    ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = (p : ℤ)}).ncard =
      4 * ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}).ncard := by
  classical
  let SZf : Finset (ℤ × ℤ) :=
    (((Finset.Icc (-(Nat.sqrt p : ℤ)) (Nat.sqrt p)) ×ˢ
      (Finset.Icc (-(Nat.sqrt (Nat.sqrt p) : ℤ)) (Nat.sqrt (Nat.sqrt p)))).filter
        (fun x => x.1 ^ 2 + x.2 ^ 4 = (p : ℤ)))
  let SNf : Finset (ℕ × ℕ) :=
    (((Finset.range (Nat.sqrt p + 1)) ×ˢ (Finset.range (Nat.sqrt (Nat.sqrt p) + 1))).filter
        (fun q => q.1 ^ 2 + q.2 ^ 4 = p))
  have hmemSZf : ∀ x : ℤ × ℤ, x ∈ SZf ↔ x.1 ^ 2 + x.2 ^ 4 = (p : ℤ) := by
    intro x
    simp only [SZf, Finset.mem_filter, Finset.mem_product]
    rw [int_mem_Icc_iff, int_mem_Icc_iff]
    constructor
    · rintro ⟨_, h3⟩; exact h3
    · intro h3
      have hx2 : x.1 ^ 2 ≤ (p : ℤ) := by
        have : (0 : ℤ) ≤ x.2 ^ 4 := by positivity
        linarith
      have hx4 : x.2 ^ 4 ≤ (p : ℤ) := by
        have : (0 : ℤ) ≤ x.1 ^ 2 := by positivity
        linarith
      exact ⟨⟨natAbs_le_sqrt_of_sq_le hx2, natAbs_le_sqrt_sqrt_of_pow_four_le hx4⟩, h3⟩
  have hmemSNf : ∀ q : ℕ × ℕ, q ∈ SNf ↔ 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := by
    intro q
    simp only [SNf, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨_, h3⟩
      have hq1 : q.1 ≠ 0 := by
        rintro h0
        exact nat_pow_four_ne_prime hp (by have := h3; rw [h0] at this; simpa using this)
      have hq2 : q.2 ≠ 0 := by
        rintro h0
        exact nat_sq_ne_prime hp (by have := h3; rw [h0] at this; simpa using this)
      exact ⟨Nat.one_le_iff_ne_zero.mpr hq1, Nat.one_le_iff_ne_zero.mpr hq2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hq1 : q.1 ^ 2 ≤ p := by omega
      have hq2 : q.2 ^ 4 ≤ p := by omega
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hq1),
        pow_four_le_iff_lt_sqrt_sqrt_succ.mp hq2⟩, h3⟩
  have hSZf : ((SZf : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = (p : ℤ)} := by
    ext x; simp only [Finset.mem_coe, Set.mem_setOf_eq]; exact hmemSZf x
  have hSNf : ((SNf : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) =
      {q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p} := by
    ext q; simp only [Finset.mem_coe, Set.mem_setOf_eq]; exact hmemSNf q
  have hmaps : Set.MapsTo (fun x : ℤ × ℤ => (x.1.natAbs, x.2.natAbs))
      (↑SZf : Set (ℤ × ℤ)) (↑SNf : Set (ℕ × ℕ)) := by
    intro x hx
    have hx' : x.1 ^ 2 + x.2 ^ 4 = (p : ℤ) := (hmemSZf x).mp hx
    have hnat : x.1.natAbs ^ 2 + x.2.natAbs ^ 4 = p := by
      have : ((x.1.natAbs ^ 2 + x.2.natAbs ^ 4 : ℕ) : ℤ) = (p : ℤ) := by
        rw [← int_sq_add_pow_four_eq]; exact hx'
      exact_mod_cast this
    have ha : 1 ≤ x.1.natAbs := by
      rw [Nat.one_le_iff_ne_zero]
      rintro h0
      exact nat_pow_four_ne_prime hp (by have := hnat; rw [h0] at this; simpa using this)
    have hb : 1 ≤ x.2.natAbs := by
      rw [Nat.one_le_iff_ne_zero]
      rintro h0
      exact nat_sq_ne_prime hp (by have := hnat; rw [h0] at this; simpa using this)
    exact (hmemSNf (x.1.natAbs, x.2.natAbs)).mpr ⟨ha, hb, hnat⟩
  have hfibsum : SZf.card =
      ∑ q ∈ SNf, (SZf.filter (fun x => (x.1.natAbs, x.2.natAbs) = q)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hterm : ∀ q ∈ SNf,
      (SZf.filter (fun x => (x.1.natAbs, x.2.natAbs) = q)).card = 4 := by
    intro q hq
    have hqT : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := (hmemSNf q).mp hq
    have hset_eq : ((SZf.filter (fun x => (x.1.natAbs, x.2.natAbs) = q) : Finset (ℤ × ℤ)) :
        Set (ℤ × ℤ)) = {x : ℤ × ℤ | x.1.natAbs = q.1 ∧ x.2.natAbs = q.2} := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨_, hxq⟩; exact Prod.ext_iff.mp hxq
      · rintro ⟨h1, h2⟩
        refine ⟨?_, Prod.ext_iff.mpr ⟨h1, h2⟩⟩
        rw [hmemSZf x, int_sq_add_pow_four_eq]
        have : x.1.natAbs ^ 2 + x.2.natAbs ^ 4 = p := by rw [h1, h2]; exact hqT.2.2
        rw [this]
    rw [← Set.ncard_coe_finset, hset_eq, ncard_fiber_intpairs]
    have hq1 : q.1 ≠ 0 := by
      rintro h0
      exact nat_pow_four_ne_prime hp (by have := hqT.2.2; rw [h0] at this; simpa using this)
    have hq2 : q.2 ≠ 0 := by
      rintro h0
      exact nat_sq_ne_prime hp (by have := hqT.2.2; rw [h0] at this; simpa using this)
    rw [if_neg hq1, if_neg hq2]
  have hsum4 : (∑ q ∈ SNf, (SZf.filter (fun x => (x.1.natAbs, x.2.natAbs) = q)).card)
      = ∑ q ∈ SNf, 4 := Finset.sum_congr rfl hterm
  have hSZcard : SZf.card = 4 * SNf.card := by
    rw [hfibsum, hsum4]
    rw [Finset.sum_const_nat (s := SNf) (m := 4) (f := fun _ => (4 : ℕ)) (fun _ _ => rfl)]
    exact Nat.mul_comm _ _
  have hScard : ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = (p : ℤ)}).ncard = SZf.card := by
    rw [← hSZf, Set.ncard_coe_finset]
  have hTcard : ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}).ncard
      = SNf.card := by
    rw [← hSNf, Set.ncard_coe_finset]
  rw [hScard, hTcard]
  exact hSZcard

end Commons.NumberTheory.FriedlanderIwaniec
