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

/-- The condition `a ^ 2 + b ^ 4 ≤ x` for integers is the condition on the
absolute values: `|a| ^ 2 + |b| ^ 4 ≤ x`. -/
private lemma natAbs_pair_le_iff (a b : ℤ) {x : ℕ} :
    a.natAbs ^ 2 + b.natAbs ^ 4 ≤ x ↔ a ^ 2 + b ^ 4 ≤ (x : ℤ) := by
  rw [int_sq_add_pow_four_eq a b, Nat.cast_le]

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

/-- The number of integer pairs `(a, b)` with `a.natAbs = q.1` and
`b.natAbs = q.2` is the product of the two one-dimensional counts. -/
private lemma ncard_fiber (q : ℕ × ℕ) :
    ({p : ℤ × ℤ | p.1.natAbs = q.1 ∧ p.2.natAbs = q.2}).ncard =
      (if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2) := by
  have hset : ({p : ℤ × ℤ | p.1.natAbs = q.1 ∧ p.2.natAbs = q.2} : Set (ℤ × ℤ)) =
      {a : ℤ | a.natAbs = q.1} ×ˢ {b : ℤ | b.natAbs = q.2} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_prod]
  rw [hset, Set.ncard_prod, ncard_natAbs_eq, ncard_natAbs_eq]

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

/-- **Integer versus natural point count for `X² + Y⁴`.**

The integer solutions of `a ^ 2 + b ^ 4 ≤ x` are obtained from the natural
solutions `(c, d)` with `c ^ 2 + d ^ 4 ≤ x` by independently choosing signs of
the two coordinates.  A coordinate equal to `0` contributes only one sign, so
four copies of the natural count are overcounted: for each of the `Nat.sqrt x`
positive `c` in a pair `(c, 0)` and each of the `Nat.sqrt (Nat.sqrt x)`
positive `d` in a pair `(0, d)` two extra sign choices were counted, and the
single pair `(0, 0)` was counted four times instead of once.  Undoing this
overcount gives the stated correction. -/
lemma card_intpairs_eq_four_mul_natpairs_sub {x : ℕ} :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard) =
      4 * ({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard) -
        2 * Nat.sqrt x - 2 * Nat.sqrt (Nat.sqrt x) - 3 := by
  classical
  set SZ : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)} with hSZdef
  set SN : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x} with hSNdef
  have hmemSZ : ∀ p : ℤ × ℤ, p ∈ SZ ↔ p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := by
    intro p; rw [hSZdef]; rfl
  have hmemSN : ∀ q : ℕ × ℕ, q ∈ SN ↔ q.1 ^ 2 + q.2 ^ 4 ≤ x := by
    intro q; rw [hSNdef]; rfl
  let SZf : Finset (ℤ × ℤ) :=
    (((Finset.Icc (-(Nat.sqrt x : ℤ)) (Nat.sqrt x)) ×ˢ
      (Finset.Icc (-(Nat.sqrt (Nat.sqrt x) : ℤ)) (Nat.sqrt (Nat.sqrt x)))).filter
        (fun p => p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)))
  let SNf : Finset (ℕ × ℕ) :=
    (((Finset.range (Nat.sqrt x + 1)) ×ˢ (Finset.range (Nat.sqrt (Nat.sqrt x) + 1))).filter
        (fun p => p.1 ^ 2 + p.2 ^ 4 ≤ x))
  have hSNf : ((SNf : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) = SN := by
    ext q
    simp only [SNf, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, SN, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact h3
    · intro h3
      refine ⟨⟨?_, ?_⟩, h3⟩
      · have h : q.1 ^ 2 ≤ x := Nat.le_trans (Nat.le_add_right _ _) h3
        exact Nat.lt_succ_iff.mpr (Nat.le_sqrt'.mpr h)
      · have h : q.2 ^ 4 ≤ x := Nat.le_trans (Nat.le_add_left _ _) h3
        exact Nat.lt_succ_iff.mpr (Nat.lt_succ_iff.mp (pow_four_le_iff_lt_sqrt_sqrt_succ.mp h))
  have hSZf : ((SZf : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = SZ := by
    ext p
    simp only [SZf, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      SZ, Set.mem_setOf_eq]
    rw [int_mem_Icc_iff, int_mem_Icc_iff]
    constructor
    · rintro ⟨⟨_, _⟩, h3⟩; exact h3
    · intro h3
      have hp2 : p.1 ^ 2 ≤ (x : ℤ) := by
        have : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
        linarith
      have hp4 : p.2 ^ 4 ≤ (x : ℤ) := by
        have : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
        linarith
      exact ⟨⟨natAbs_le_sqrt_of_sq_le hp2, natAbs_le_sqrt_sqrt_of_pow_four_le hp4⟩, h3⟩
  have hmaps : Set.MapsTo (fun p : ℤ × ℤ => (p.1.natAbs, p.2.natAbs))
      (↑SZf : Set (ℤ × ℤ)) (↑SNf : Set (ℕ × ℕ)) := by
    intro p hp
    rw [hSZf] at hp
    rw [hSNf]
    exact (natAbs_pair_le_iff p.1 p.2).mpr hp
  have hfibsum : SZf.card =
      ∑ q ∈ SNf, (SZf.filter (fun p => (p.1.natAbs, p.2.natAbs) = q)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hterm : ∀ q ∈ SNf, (SZf.filter (fun p => (p.1.natAbs, p.2.natAbs) = q)).card =
      (if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2) := by
    intro q hq
    have hqSN : q.1 ^ 2 + q.2 ^ 4 ≤ x := (hmemSN q).mp (by rw [← hSNf]; exact hq)
    have hset_eq : ((SZf.filter (fun p => (p.1.natAbs, p.2.natAbs) = q) : Finset (ℤ × ℤ)) :
        Set (ℤ × ℤ)) = {p : ℤ × ℤ | p.1.natAbs = q.1 ∧ p.2.natAbs = q.2} := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨_, hpq⟩; exact Prod.ext_iff.mp hpq
      · rintro ⟨h1, h2⟩
        refine ⟨?_, Prod.ext_iff.mpr ⟨h1, h2⟩⟩
        rw [← Finset.mem_coe, hSZf, hmemSZ p]
        exact (natAbs_pair_le_iff p.1 p.2).mp (by rw [h1, h2]; exact hqSN)
    rw [← Set.ncard_coe_finset, hset_eq, ncard_fiber]
  have hsum : SZf.card =
      ∑ q ∈ SNf, ((if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2)) := by
    rw [hfibsum]; exact Finset.sum_congr rfl hterm
  have hA : (SNf.filter (fun q => q.1 = 0)).card = Nat.sqrt (Nat.sqrt x) + 1 := by
    have himg : SNf.filter (fun q => q.1 = 0) =
        (Finset.range (Nat.sqrt (Nat.sqrt x) + 1)).image (fun d => (0, d)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hq, hq1⟩
        have h4 : q.2 ^ 4 ≤ x := by
          have h := (hmemSN q).mp (by rw [← hSNf]; exact hq)
          rw [hq1] at h; simpa using h
        refine ⟨q.2, ?_, ?_⟩
        · exact Nat.lt_succ_iff.mpr (Nat.lt_succ_iff.mp (pow_four_le_iff_lt_sqrt_sqrt_succ.mp h4))
        · exact Prod.ext hq1.symm rfl
      · rintro ⟨d, hd, hdq⟩
        subst hdq
        exact ⟨by rw [← Finset.mem_coe, hSNf, hmemSN]; simpa using pow_four_le_iff_lt_sqrt_sqrt_succ.mpr hd, rfl⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h), Finset.card_range]
  have hB : (SNf.filter (fun q => q.2 = 0)).card = Nat.sqrt x + 1 := by
    have himg : SNf.filter (fun q => q.2 = 0) =
        (Finset.range (Nat.sqrt x + 1)).image (fun d => (d, 0)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hq, hq2⟩
        have h2 : q.1 ^ 2 ≤ x := by
          have h := (hmemSN q).mp (by rw [← hSNf]; exact hq)
          rw [hq2] at h; simpa using h
        refine ⟨q.1, ?_, ?_⟩
        · exact Nat.lt_succ_iff.mpr (Nat.le_sqrt'.mpr h2)
        · exact Prod.ext rfl hq2.symm
      · rintro ⟨d, hd, hdq⟩
        subst hdq
        exact ⟨by rw [← Finset.mem_coe, hSNf, hmemSN]; simpa using Nat.le_sqrt'.mp (Nat.lt_succ_iff.mp hd), rfl⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h), Finset.card_range]
  have hC : (SNf.filter (fun q => q.1 = 0 ∧ q.2 = 0)).card = 1 := by
    have hone : SNf.filter (fun q => q.1 = 0 ∧ q.2 = 0) = ({(0, 0)} : Finset (ℕ × ℕ)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h1, h2⟩; exact Prod.ext h1 h2
      · rintro hq
        subst hq
        exact ⟨by rw [← Finset.mem_coe, hSNf, hmemSN]; simp, rfl, rfl⟩
    rw [hone]; simp
  have hsumZ : (SZf.card : ℤ) =
      4 * (SNf.card : ℤ) - 2 * ((SNf.filter (fun q => q.1 = 0)).card : ℤ)
        - 2 * ((SNf.filter (fun q => q.2 = 0)).card : ℤ)
        + ((SNf.filter (fun q => q.1 = 0 ∧ q.2 = 0)).card : ℤ) := by
    have hcast : (SZf.card : ℤ) =
        ∑ q ∈ SNf, (((if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2) : ℕ) : ℤ) := by
      rw [hsum]; push_cast; rfl
    rw [hcast]
    have hm : ∀ q ∈ SNf,
        (((if q.1 = 0 then 1 else 2) * (if q.2 = 0 then 1 else 2) : ℕ) : ℤ)
        = 4 - 2 * (if q.1 = 0 then (1:ℤ) else 0) - 2 * (if q.2 = 0 then (1:ℤ) else 0)
          + (if q.1 = 0 then (1:ℤ) else 0) * (if q.2 = 0 then (1:ℤ) else 0) := by
      intro q _
      by_cases h1 : q.1 = 0 <;> by_cases h2 : q.2 = 0 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl hm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_boole, Finset.sum_boole]
    have hab : ∀ q ∈ SNf, (if q.1 = 0 then (1:ℤ) else 0) * (if q.2 = 0 then (1:ℤ) else 0)
        = (if q.1 = 0 ∧ q.2 = 0 then (1:ℤ) else 0) := by
      intro q _
      by_cases h1 : q.1 = 0 <;> by_cases h2 : q.2 = 0 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl hab, Finset.sum_boole]
    ring
  have hcard : (SZf.card : ℤ) = 4 * (SNf.card : ℤ) - 2 * (Nat.sqrt x : ℤ)
      - 2 * (Nat.sqrt (Nat.sqrt x) : ℤ) - 3 := by
    rw [hsumZ, hA, hB, hC]
    push_cast
    ring
  have hSZcard : SZ.ncard = SZf.card := by rw [← hSZf, Set.ncard_coe_finset]
  have hSNcard : SN.ncard = SNf.card := by rw [← hSNf, Set.ncard_coe_finset]
  rw [hSZcard, hSNcard]
  have hnat : SZf.card + (2 * Nat.sqrt x + 2 * Nat.sqrt (Nat.sqrt x) + 3) = 4 * SNf.card := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    linarith [hcard]
  omega

end Commons.NumberTheory.FriedlanderIwaniec
