import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

/-!
# Support definitions for `Work.CORE3.Case1bEightNine`

Bender 1981 §3, pp. 223–224.  The whole section is a study of the cosets of `Ĥ = B.Hhat` and
their involutions.  This file fixes the notation used by the leaf `Case1bEightNine` and by the
lemmas it delegates.

Throughout `Hh` is a subgroup of `G` and `y` is an involution of `G`.

* `invSetIn Hh y` — Bender's `I_Ĥ(y) = {x ∈ Ĥ | y x y = x⁻¹}`.  For an involution `y ∉ Hh` the
  map `x ↦ y * x` is a bijection onto `cosetInvolSet Hh y`, so both sets have the same number
  `cosetInvCount Hh y` of elements; that number is the index of the coset.
* `cosetInvolSet Hh y` — the involutions of the left coset `y Hh`; Bender's `Ĥy ∩ J`.
* `cosetPairCount Hh y` — the number of *ordered* pairs `(z,z')` of distinct commuting
  involutions of the coset `y Hh`; twice the number of unordered commuting pairs in `y Hh`.
* `commutingInvolsIn Hh z` — Bender's `|I_Ĥ(z) ∩ J|`, the involutions of `Hh` commuting with
  the involution `z`.

The intended facts about these numbers (Bender's (6), (7) and the count (8)) are:

* `cosetInvCount Hh y ≤ 4` for an involution `y ∉ Hh` (Bender (6), (7));  this is the only
  deep input for the leaf `Case1bEightNine`;
* `cosetInvCount Hh y = 4 → cosetPairCount Hh y = 6` (the commuting graph on the four
  involutions of a `b₄`-coset is a star `K_{1,3}`);
* `cosetInvCount Hh y = 2 → cosetPairCount Hh y = 2` (elementary);
* `cosetInvCount Hh y = 3 → cosetPairCount Hh y = 0` (elementary, Bender (6) for `n ≤ 3`).
-/

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G]

/-- Bender's `I_Ĥ(y) = {x ∈ Ĥ | y x y = x⁻¹}`: the elements of `Hh` inverted by `y`.  For an
involution `y`, the map `x ↦ y * x` sends this set onto the involutions of the coset `y Hh`,
and `invSetIn Hh y = invSet Hh y` (the definition of `Work.GW2.invSet`). -/
def invSetIn (Hh : Subgroup G) (y : G) : Set G := {x : G | x ∈ Hh ∧ y * x * y = x⁻¹}

/-- The involutions of the left coset `y Hh` (Bender's `Ĥy ∩ J`). -/
def cosetInvolSet (Hh : Subgroup G) (y : G) : Set G :=
  {x : G | orderOf x = 2 ∧ y⁻¹ * x ∈ Hh}

/-- The number of ordered pairs `(z,z')` of distinct commuting involutions of the coset
`y Hh`; twice the number of unordered such pairs. -/
noncomputable def cosetPairCount (Hh : Subgroup G) (y : G) : ℕ :=
  {p : G × G | p.1 ∈ cosetInvolSet Hh y ∧ p.2 ∈ cosetInvolSet Hh y ∧
    p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1}.ncard

/-- Bender's `|I_Ĥ(z) ∩ J|`: the involutions of `Hh` commuting with the involution `z`.  This
is the number of `s ∈ Ĥ` for which `(z,s)` is a pair of commuting involutions. -/
noncomputable def commutingInvolsIn (Hh : Subgroup G) (z : G) : ℕ :=
  (involutionSet Hh ∩ {x : G | z * x = x * z}).ncard

@[simp] theorem mem_cosetInvolSet {Hh : Subgroup G} {y x : G} :
    x ∈ cosetInvolSet Hh y ↔ orderOf x = 2 ∧ y⁻¹ * x ∈ Hh := Iff.rfl

@[simp] theorem mem_invSetIn {Hh : Subgroup G} {y x : G} :
    x ∈ invSetIn Hh y ↔ x ∈ Hh ∧ y * x * y = x⁻¹ := Iff.rfl

/-- Every element of `invSetIn Hh y` lies in `Hh`. -/
theorem invSetIn_subset (Hh : Subgroup G) (y : G) : invSetIn Hh y ⊆ Hh := fun _ hx => hx.1

section Basic

variable {Hh : Subgroup G} {y x : G}

theorem inv_eq_of_sq_eq_one (hy : y * y = 1) : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy

/-- For an involution `y`, `invSetIn Hh y` is `Work.GW2.invSet Hh y` (Bender's notation). -/
theorem invSetIn_eq_invSet (hy : y * y = 1) : invSetIn Hh y = invSet Hh y := by
  ext x
  simp only [mem_invSetIn, Set.mem_setOf_eq, invSet]
  rw [inv_eq_of_sq_eq_one hy]

theorem one_mem_invSetIn (hy : y * y = 1) : (1 : G) ∈ invSetIn Hh y := by
  refine ⟨Hh.one_mem, ?_⟩
  rw [mul_one, inv_one]
  exact hy

/-- `orderOf x = 2` is `x * x = 1` together with `x ≠ 1`. -/
theorem orderOf_eq_two_iff_mul_self (x : G) : orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← h]
      exact pow_orderOf_eq_one x
    · rintro rfl
      simp at h
  · rintro ⟨h2, h1⟩
    rw [← pow_two] at h2
    exact orderOf_eq_prime h2 h1

end Basic

section Dictionary

variable {Hh : Subgroup G} {y x : G}

/-- For an involution `y`, the condition `(y * x) * (y * x) = 1` is exactly Bender's
condition `y * x * y = x⁻¹` of `invSetIn`. -/
theorem mul_self_mul_eq_one_iff (hy : y * y = 1) :
    (y * x) * (y * x) = 1 ↔ y * x * y = x⁻¹ := by
  constructor
  · intro h
    have h1 : (y * x * y) * x = x⁻¹ * x := by
      calc (y * x * y) * x = (y * x) * (y * x) := by group
        _ = 1 := h
        _ = x⁻¹ * x := by rw [inv_mul_cancel]
    exact mul_right_cancel h1
  · intro h
    calc (y * x) * (y * x) = (y * x * y) * x := by group
      _ = x⁻¹ * x := by rw [h]
      _ = 1 := inv_mul_cancel x

/-- The elementwise dictionary: for an involution `y ∉ Hh`, the elements `x ∈ Hh` for which
`y * x` is an involution of the coset `y Hh` are exactly the elements of `invSetIn Hh y`. -/
theorem mul_mem_cosetInvolSet_iff (hy : y * y = 1) (hyH : y ∉ Hh) :
    y * x ∈ cosetInvolSet Hh y ↔ x ∈ invSetIn Hh y := by
  constructor
  · intro h
    rw [mem_cosetInvolSet] at h
    obtain ⟨hord, hmem⟩ := h
    have h0 : y⁻¹ * (y * x) = x := by group
    have hx : x ∈ Hh := by
      rw [← h0]
      exact hmem
    exact ⟨hx,
      (mul_self_mul_eq_one_iff hy).mp ((orderOf_eq_two_iff_mul_self (y * x)).mp hord).1⟩
  · rintro ⟨hx, hxy⟩
    rw [mem_cosetInvolSet]
    have hself : (y * x) * (y * x) = 1 := (mul_self_mul_eq_one_iff hy).mpr hxy
    have hne : y * x ≠ 1 := by
      intro h1
      have h2 : x = y⁻¹ := by
        calc x = y⁻¹ * (y * x) := by group
          _ = y⁻¹ * 1 := by rw [h1]
          _ = y⁻¹ := by rw [mul_one]
      exact hyH (by rw [← inv_eq_of_sq_eq_one hy, ← h2]; exact hx)
    refine ⟨(orderOf_eq_two_iff_mul_self (y * x)).mpr ⟨hself, hne⟩, ?_⟩
    rw [show y⁻¹ * (y * x) = x by group]
    exact hx

/-- The coset-involution count of Bender §3 is the cardinality of the inverted set. -/
theorem ncard_invSetIn_eq_cosetInvCount (Hh : Subgroup G) (y : G) (hy : y * y = 1)
    (hyH : y ∉ Hh) :
    (invSetIn Hh y).ncard = cosetInvCount Hh y := by
  change (invSetIn Hh y).ncard = (cosetInvolSet Hh y).ncard
  refine Set.ncard_congr (fun x _ => y * x) ?_ ?_ ?_
  · intro x hx
    exact (mul_mem_cosetInvolSet_iff hy hyH).mpr hx
  · intro a b _ _ hab
    exact mul_left_cancel hab
  · intro b hb
    refine ⟨y⁻¹ * b, ?_, ?_⟩
    · rw [← mul_mem_cosetInvolSet_iff hy hyH]
      rw [show y * (y⁻¹ * b) = b by group]
      exact hb
    · rw [show y * (y⁻¹ * b) = b by group]

end Dictionary

end Work.CORE3

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G]
variable {Hh : Subgroup G} {y x x' : G}

section PairCounting

/-- In a group, `u * u = 1` says exactly that `u` is its own inverse. -/
theorem mul_self_eq_one_iff_eq_inv (u : G) : u * u = 1 ↔ u = u⁻¹ :=
  mul_eq_one_iff_eq_inv

/-- The pair set inside `invSetIn Hh y` corresponding to the commuting pairs of the coset
`y Hh`: the pairs of distinct elements `x, x'` with `(x⁻¹ x')² = 1`. -/
def invSetPairSet (Hh : Subgroup G) (y : G) : Set (G × G) :=
  {p : G × G | p.1 ∈ invSetIn Hh y ∧ p.2 ∈ invSetIn Hh y ∧ p.1 ≠ p.2 ∧
    (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}

/-- Elements of the inverted set stay in it under inverses. -/
theorem inv_mem_invSetIn (hy : y * y = 1) (hx : x ∈ invSetIn Hh y) :
    x⁻¹ ∈ invSetIn Hh y := by
  obtain ⟨hxH, hxy⟩ := hx
  refine ⟨Hh.inv_mem hxH, ?_⟩
  have h1 : y * x⁻¹ * y = (y * x * y)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev]
    simp only [inv_eq_of_sq_eq_one hy]
    group
  rw [h1, hxy, inv_inv]

/-- Conjugation by `y` is multiplicative on the middle of `y * _ * y`. -/
theorem mul_conj_mul (hy : y * y = 1) (a b : G) :
    (y * a * y) * (y * b * y) = y * (a * b) * y := by
  have key : (y * a * y) * (y * b * y) = y * a * (y * y) * b * y := by group
  rw [key, hy]
  group

/-- Conjugating powers: `y * x^n * y = (x⁻¹)^n` for an involution `y` inverting `x`. -/
theorem conj_pow_of_inv (hy : y * y = 1) (hxy : y * x * y = x⁻¹) (n : ℕ) :
    y * x ^ n * y = (x⁻¹) ^ n := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
      rw [pow_succ, pow_succ, ← mul_conj_mul hy (x ^ n) x, ih, hxy]

/-- Elements of the inverted set stay in it under natural powers. -/
theorem pow_mem_invSetIn (hy : y * y = 1) (hx : x ∈ invSetIn Hh y) (n : ℕ) :
    x ^ n ∈ invSetIn Hh y := by
  obtain ⟨hxH, hxy⟩ := hx
  refine ⟨Hh.pow_mem hxH n, ?_⟩
  rw [conj_pow_of_inv hy hxy n, inv_pow]

/-- For an involution `y` and `x, x' ∈ invSetIn Hh y`, the involutions `y x`, `y x'` of the
coset commute exactly when `x⁻¹ x'` is an involution. -/
theorem mul_comm_mul_iff (hy : y * y = 1) (hx : x ∈ invSetIn Hh y) (hx' : x' ∈ invSetIn Hh y) :
    (y * x) * (y * x') = (y * x') * (y * x) ↔ (x⁻¹ * x') * (x⁻¹ * x') = 1 := by
  obtain ⟨-, hxy⟩ := hx
  obtain ⟨-, hxy'⟩ := hx'
  have h1 : (y * x) * (y * x') = x⁻¹ * x' := by
    rw [← mul_assoc (y * x) y x', hxy]
  have h2 : (y * x') * (y * x) = x'⁻¹ * x := by
    rw [← mul_assoc (y * x') y x, hxy']
  rw [h1, h2, mul_self_eq_one_iff_eq_inv]
  simp only [mul_inv_rev, inv_inv]

end PairCounting

end Work.CORE3

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G]
variable {Hh : Subgroup G} {y x x' : G}

section PairCountingTwo

/-- The coset pair count is the pair count inside the inverted set. -/
theorem cosetPairCount_eq_ncard_invSetPairSet (Hh : Subgroup G) (y : G) (hy : y * y = 1)
    (hyH : y ∉ Hh) : cosetPairCount Hh y = (invSetPairSet Hh y).ncard := by
  change {p : G × G | p.1 ∈ cosetInvolSet Hh y ∧ p.2 ∈ cosetInvolSet Hh y ∧
      p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1}.ncard = (invSetPairSet Hh y).ncard
  refine Set.ncard_congr (fun p _ => (y⁻¹ * p.1, y⁻¹ * p.2)) ?_ ?_ ?_
  · rintro ⟨p1, p2⟩ hp
    simp only [Set.mem_setOf_eq, invSetPairSet] at hp ⊢
    obtain ⟨hp1, hp2, hne, hcomm⟩ := hp
    have hm1 : y⁻¹ * p1 ∈ invSetIn Hh y :=
      (mul_mem_cosetInvolSet_iff hy hyH).mp (by rw [show y * (y⁻¹ * p1) = p1 by group]; exact hp1)
    have hm2 : y⁻¹ * p2 ∈ invSetIn Hh y :=
      (mul_mem_cosetInvolSet_iff hy hyH).mp (by rw [show y * (y⁻¹ * p2) = p2 by group]; exact hp2)
    refine ⟨hm1, hm2, ?_, ?_⟩
    · intro hh
      exact hne (by simpa using congrArg (fun z : G => y * z) hh)
    · refine (mul_comm_mul_iff hy hm1 hm2).mp ?_
      rw [show y * (y⁻¹ * p1) = p1 by group, show y * (y⁻¹ * p2) = p2 by group]
      exact hcomm
  · rintro ⟨p1, p2⟩ ⟨q1, q2⟩ _ _ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨mul_left_cancel h.1, mul_left_cancel h.2⟩
  · rintro ⟨q1, q2⟩ hq
    simp only [invSetPairSet, Set.mem_setOf_eq] at hq
    obtain ⟨hq1, hq2, hne, hsq⟩ := hq
    refine ⟨(y * q1, y * q2), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      refine ⟨(mul_mem_cosetInvolSet_iff hy hyH).mpr hq1,
        (mul_mem_cosetInvolSet_iff hy hyH).mpr hq2, ?_, ?_⟩
      · intro hh
        exact hne (mul_left_cancel hh)
      · exact (mul_comm_mul_iff hy hq1 hq2).mpr hsq
    · simp only [Prod.mk.injEq]
      exact ⟨by group, by group⟩

/-- Multiplication inside the inverted set: if two of its elements commute, their product is
again in it. -/
theorem mul_mem_invSetIn (hy : y * y = 1) (hx : x ∈ invSetIn Hh y) (hx' : x' ∈ invSetIn Hh y)
    (hc : x * x' = x' * x) : x * x' ∈ invSetIn Hh y := by
  obtain ⟨hxH, hxy⟩ := hx
  obtain ⟨hx'H, hxy'⟩ := hx'
  refine ⟨Hh.mul_mem hxH hx'H, ?_⟩
  rw [← mul_conj_mul hy x x', hxy, hxy']
  have hc' : x'⁻¹ * x⁻¹ = x⁻¹ * x'⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hc]
  rw [mul_inv_rev, hc']

/-- Conjugation inside the inverted set: `x x' x` is again in it. -/
theorem mul_mem_invSetIn_conj (hy : y * y = 1) (hx : x ∈ invSetIn Hh y)
    (hx' : x' ∈ invSetIn Hh y) : x * x' * x ∈ invSetIn Hh y := by
  obtain ⟨hxH, hxy⟩ := hx
  obtain ⟨hx'H, hxy'⟩ := hx'
  refine ⟨Hh.mul_mem (Hh.mul_mem hxH hx'H) hxH, ?_⟩
  have h1 : y * (x * x' * x) * y = (y * x * y) * (y * x' * y) * (y * x * y) := by
    rw [← mul_conj_mul hy (x * x') x, ← mul_conj_mul hy x x']
  rw [h1, hxy, hxy', mul_inv_rev, mul_inv_rev, mul_assoc]

/-- The inverted set of a coset with exactly two involutions is `{1, b}` with `b` an
involution. -/
theorem invSetIn_eq_pair_of_ncard_two (hy : y * y = 1) (h2 : (invSetIn Hh y).ncard = 2) :
    ∃ b : G, b ≠ 1 ∧ b * b = 1 ∧ invSetIn Hh y = {1, b} := by
  obtain ⟨x, x', hne, hset⟩ := Set.ncard_eq_two.mp h2
  have h1mem : (1 : G) ∈ invSetIn Hh y := one_mem_invSetIn (Hh := Hh) hy
  rw [hset] at h1mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1mem
  rcases h1mem with h | h
  · -- `1 = x`, hence `I = {1, x'}`
    refine ⟨x', fun hc => hne (h.symm.trans hc.symm), ?_, ?_⟩
    · have hmem : x' ∈ invSetIn Hh y := by rw [hset]; simp
      have hinv : x'⁻¹ ∈ invSetIn Hh y := inv_mem_invSetIn (Hh := Hh) hy hmem
      rw [← h] at hset
      rw [hset] at hinv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hinv
      rcases hinv with h' | h'
      · exact absurd (inv_eq_one.mp h') (fun hc => hne (h.symm.trans hc.symm))
      · exact (mul_self_eq_one_iff_eq_inv x').mpr h'.symm
    · rw [← h] at hset
      exact hset
  · -- `1 = x'`, hence `I = {1, x}`
    refine ⟨x, fun hc => hne (hc.trans h), ?_, ?_⟩
    · have hmem : x ∈ invSetIn Hh y := by rw [hset]; simp
      have hinv : x⁻¹ ∈ invSetIn Hh y := inv_mem_invSetIn (Hh := Hh) hy hmem
      rw [← h] at hset
      rw [hset] at hinv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hinv
      rcases hinv with h' | h'
      · exact (mul_self_eq_one_iff_eq_inv x).mpr h'.symm
      · exact absurd (inv_eq_one.mp h') (fun hc => hne (hc.trans h))
    · refine hset.trans ?_
      rw [Set.pair_comm, ← h]

/-- A coset with exactly two involutions has ordered pair count `2` (the two involutions
commute). -/
theorem cosetPairCount_eq_two_of_ncard_two (hy : y * y = 1) (hyH : y ∉ Hh)
    (h2 : (invSetIn Hh y).ncard = 2) : cosetPairCount Hh y = 2 := by
  obtain ⟨b, hb1, hbsq, hset⟩ := invSetIn_eq_pair_of_ncard_two (Hh := Hh) hy h2
  have hpairs : invSetPairSet Hh y = {((1 : G), b), (b, (1 : G))} := by
    ext p
    obtain ⟨p1, p2⟩ := p
    simp only [invSetPairSet, Set.mem_setOf_eq, hset, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, hne, -⟩
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨Or.inl rfl, Or.inr rfl, ?_, ?_⟩
        · intro hh; exact hb1 hh.symm
        · rw [inv_one, one_mul]; exact hbsq
      · refine ⟨Or.inr rfl, Or.inl rfl, hb1, ?_⟩
        rw [inv_eq_of_sq_eq_one hbsq, mul_one]; exact hbsq
  rw [cosetPairCount_eq_ncard_invSetPairSet Hh y hy hyH, hpairs]
  exact Set.ncard_pair (by simp [hb1])

end PairCountingTwo

end Work.CORE3

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G]
variable {Hh : Subgroup G} {y x : G}

section PairCountingThree

/-- Decomposition of a three-element inverted set: `I_Ĥ(y) = {1, p, q}`. -/
theorem eq_insert_one_pair_of_ncard_three (hy : y * y = 1) (h3 : (invSetIn Hh y).ncard = 3) :
    ∃ p q : G, p ∈ invSetIn Hh y ∧ q ∈ invSetIn Hh y ∧ p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q ∧
      invSetIn Hh y = {1, p, q} ∧ invSetIn Hh y \ {1} = {p, q} := by
  have h1mem : (1 : G) ∈ invSetIn Hh y := one_mem_invSetIn (Hh := Hh) hy
  have h2 : (invSetIn Hh y \ {1}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem h1mem, h3]
  obtain ⟨p, q, hpq, hset⟩ := Set.ncard_eq_two.mp h2
  have hp : p ∈ invSetIn Hh y \ {1} := by rw [hset]; simp
  have hq : q ∈ invSetIn Hh y \ {1} := by rw [hset]; simp
  have hI : invSetIn Hh y = {1, p, q} := by
    calc invSetIn Hh y = insert (1 : G) (invSetIn Hh y) := (Set.insert_eq_self.mpr h1mem).symm
      _ = insert (1 : G) (invSetIn Hh y \ {1}) := by rw [Set.insert_sdiff_singleton]
      _ = insert (1 : G) ({p, q} : Set G) := by rw [hset]
      _ = {1, p, q} := rfl
  exact ⟨p, q, hp.1, hq.1, hp.2, hq.2, hpq, hI, hset⟩

/-- If `x ∈ I_Ĥ(y)` is different from `1` and `|I_Ĥ(y)| = 3`, then `I_Ĥ(y) = {1, x, r}` for a
companion `r`. -/
theorem eq_insert_one_pair_of_mem (hy : y * y = 1) (h3 : (invSetIn Hh y).ncard = 3)
    (hx : x ∈ invSetIn Hh y) (hx1 : x ≠ 1) :
    ∃ r : G, r ∈ invSetIn Hh y ∧ r ≠ 1 ∧ r ≠ x ∧ invSetIn Hh y = {1, x, r} := by
  obtain ⟨p, q, hp, hq, hp1, hq1, hpq, hI, hsdiff⟩ := eq_insert_one_pair_of_ncard_three (Hh := Hh) hy h3
  have hxp : x ∈ ({p, q} : Set G) := by
    have hxs : x ∈ invSetIn Hh y \ {1} := ⟨hx, by simpa using hx1⟩
    rwa [hsdiff] at hxs
  have hxp' : x = p ∨ x = q := by simpa using hxp
  rcases hxp' with h | h
  · refine ⟨q, hq, hq1, ?_, ?_⟩
    · intro hh; exact hpq (h.symm.trans hh.symm)
    · rw [hI, h]
  · refine ⟨p, hp, hp1, ?_, ?_⟩
    · intro hh; exact hpq (hh.trans h)
    · rw [hI, h]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- Bender §3 (6) for `n = 3`: the only involution of `I_Ĥ(y)` is `1`. -/
theorem eq_one_of_sq_eq_one_of_ncard_three (hy : y * y = 1) (h3 : (invSetIn Hh y).ncard = 3)
    (hx : x ∈ invSetIn Hh y) (hxsq : x * x = 1) : x = 1 := by
  by_contra hx1
  obtain ⟨r, hr, hr1, hrx, hI⟩ := eq_insert_one_pair_of_mem (Hh := Hh) hy h3 hx hx1
  have hcases : ∀ z ∈ invSetIn Hh y, z = 1 ∨ z = x ∨ z = r := by
    intro z hz
    rw [hI] at hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
  have hxinv : x⁻¹ = x := inv_eq_of_sq_eq_one hxsq
  by_cases hcomm : x * r = r * x
  · have hm : x * r ∈ invSetIn Hh y := mul_mem_invSetIn hy hx hr hcomm
    rcases hcases (x * r) hm with h | h | h
    · have hres : r = x := by
        have h2 : x * (x * r) = x * 1 := by rw [h]
        simpa only [← mul_assoc, hxsq, one_mul, mul_one] using h2
      exact hrx hres
    · have hres : r = 1 := mul_left_cancel (by rw [h, mul_one] : x * r = x * 1)
      exact hr1 hres
    · have hres : x = 1 := by
        have h2 : x * r * r⁻¹ = r * r⁻¹ := by rw [h]
        simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using h2
      exact hx1 hres
  · have hm : x * r * x ∈ invSetIn Hh y := mul_mem_invSetIn_conj hy hx hr
    rcases hcases (x * r * x) hm with h | h | h
    · have hres : r = 1 := by
        have h2 : x * (x * r * x) = x * 1 := by rw [h]
        have h2' : (x * x) * r * x = x := by
          have h3 : x * (x * r * x) = (x * x) * r * x := by group
          rw [h3, mul_one] at h2
          exact h2
        have h2'' : r * x = x := by simpa only [hxsq, one_mul] using h2'
        have h3 := congrArg (fun z : G => z * x⁻¹) h2''
        simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using h3
      exact hr1 hres
    · have hres : r = x := by
        have h2 : x * (x * r * x) = x * x := by rw [h]
        have h2' : (x * x) * r * x = x * x := by
          have h3 : x * (x * r * x) = (x * x) * r * x := by group
          rw [h3] at h2
          exact h2
        have h2'' : r * x = 1 := by simpa only [hxsq, one_mul] using h2'
        have h3 : r * x * x⁻¹ = 1 * x⁻¹ := by rw [h2'']
        rw [mul_assoc, mul_inv_cancel, mul_one, one_mul] at h3
        rw [hxinv] at h3
        exact h3
      exact hrx hres
    · have hres : x * r = r * x := by
        have h2 : x * (x * r * x) = x * r := by rw [h]
        have h2' : (x * x) * r * x = x * r := by
          have h3 : x * (x * r * x) = (x * x) * r * x := by group
          rw [h3] at h2
          exact h2
        have h2'' : r * x = x * r := by simpa only [hxsq, one_mul] using h2'
        exact h2''.symm
      exact hcomm hres

/-- Bender §3 (6), case `n = 3`: the inverted set is `{1, a, a * a}` with `a` of order three. -/
theorem invSetIn_eq_three_of_ncard_three (hy : y * y = 1) (h3 : (invSetIn Hh y).ncard = 3) :
    ∃ a : G, a ≠ 1 ∧ a * a * a = 1 ∧ invSetIn Hh y = {1, a, a * a} := by
  obtain ⟨p, q, hp, hq, hp1, hq1, hpq, hI, -⟩ :=
    eq_insert_one_pair_of_ncard_three (Hh := Hh) hy h3
  have hcases : ∀ z ∈ invSetIn Hh y, z = 1 ∨ z = p ∨ z = q := by
    intro z hz
    rw [hI] at hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
  have hp2mem : p * p ∈ invSetIn Hh y := by
    have h := pow_mem_invSetIn (Hh := Hh) hy hp 2
    simpa [pow_two] using h
  have hp2ne : p * p ≠ 1 :=
    fun h => hp1 (eq_one_of_sq_eq_one_of_ncard_three (Hh := Hh) hy h3 hp h)
  have hpp : p * p ≠ p := fun h => hp1 (by
    have h2 : p⁻¹ * (p * p) = 1 := by rw [h]; exact inv_mul_cancel p
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h2)
  have hp2 : p * p = q := by
    rcases hcases (p * p) hp2mem with h | h | h
    · exact absurd h hp2ne
    · exact absurd h hpp
    · exact h
  have hp3mem : p * p * p ∈ invSetIn Hh y := by
    have h := pow_mem_invSetIn (Hh := Hh) hy hp 3
    simpa [pow_succ, pow_two, mul_assoc] using h
  have hp3 : p * p * p = 1 := by
    rcases hcases (p * p * p) hp3mem with h | h | h
    · exact h
    · have h2 : p⁻¹ * (p * p * p) = p⁻¹ * p := by rw [h]
      have h3 : p * p = 1 := by
        rw [show p⁻¹ * (p * p * p) = p * p by group,
          show p⁻¹ * p = 1 by rw [inv_mul_cancel]] at h2
        exact h2
      exact absurd h3 hp2ne
    · rw [← hp2] at h
      have h2 : p⁻¹ * (p * p * p) = p⁻¹ * (p * p) := by rw [h]
      have h3 : p * p = p := by
        rw [show p⁻¹ * (p * p * p) = p * p by group,
          show p⁻¹ * (p * p) = p by group] at h2
        exact h2
      exact absurd h3 hpp
  refine ⟨p, hp1, hp3, ?_⟩
  rw [hI, ← hp2]

/-- A coset with exactly three involutions has ordered pair count `0`: the three involutions
of `I_Ĥ(y) = {1, a, a * a}` pairwise fail to commute. -/
theorem cosetPairCount_eq_zero_of_ncard_three (hy : y * y = 1) (hyH : y ∉ Hh)
    (h3 : (invSetIn Hh y).ncard = 3) : cosetPairCount Hh y = 0 := by
  obtain ⟨a, ha1, ha3, hI⟩ := invSetIn_eq_three_of_ncard_three (Hh := Hh) hy h3
  have ha_inv : a⁻¹ = a * a := by
    have h : a * (a * a) = 1 := by rw [← ha3]; group
    have h2 : a = (a * a)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h3 : a⁻¹ = ((a * a)⁻¹)⁻¹ := congrArg Inv.inv h2
    rwa [inv_inv] at h3
  have hsq_aa : a * a * (a * a) = a := by
    rw [show a * a * (a * a) = a * (a * a * a) by group, ha3, mul_one]
  have hinv_aa : (a * a)⁻¹ = a := by
    rw [show (a * a)⁻¹ = a⁻¹ * a⁻¹ by rw [mul_inv_rev], ha_inv, hsq_aa]
  rw [cosetPairCount_eq_ncard_invSetPairSet Hh y hy hyH]
  have hempty : invSetPairSet Hh y = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ hu
    rw [invSetPairSet, Set.mem_setOf_eq] at hu
    obtain ⟨hu1, hu2, hne, hsq⟩ := hu
    rw [hI] at hu1 hu2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu1 hu2
    have h1mem : (1 : G) ∈ invSetIn Hh y := one_mem_invSetIn (Hh := Hh) hy
    have hamem : a ∈ invSetIn Hh y := by rw [hI]; simp
    have ha2mem : a * a ∈ invSetIn Hh y := by rw [hI]; simp
    have hmem : u⁻¹ * v ∈ invSetIn Hh y := by
      rcases hu1 with h1 | h1 | h1 <;> rcases hu2 with h2 | h2 | h2 <;> rw [h1, h2]
      · rw [inv_one, one_mul]; exact h1mem
      · rw [inv_one, one_mul]; exact hamem
      · rw [inv_one, one_mul]; exact ha2mem
      · rw [ha_inv, mul_one]; exact ha2mem
      · rw [inv_mul_cancel]; exact h1mem
      · rw [ha_inv, hsq_aa]; exact hamem
      · rw [hinv_aa, mul_one]; exact hamem
      · rw [hinv_aa]; exact ha2mem
      · rw [inv_mul_cancel]; exact h1mem
    have h1v : u⁻¹ * v = 1 := eq_one_of_sq_eq_one_of_ncard_three (Hh := Hh) hy h3 hmem hsq
    have huv : v = u := by
      have h2 : u * (u⁻¹ * v) = u * 1 := by rw [h1v]
      rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
    exact hne huv.symm
  rw [hempty, Set.ncard_empty]

end PairCountingThree

end Work.CORE3

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G] [Finite G]

section Bookkeeping

/-- The left coset `g Hh` as a set. -/
def leftCoset (Hh : Subgroup G) (g : G) : Set G := {z : G | g⁻¹ * z ∈ Hh}

theorem mem_leftCoset {Hh : Subgroup G} {g z : G} :
    z ∈ leftCoset Hh g ↔ g⁻¹ * z ∈ Hh := Iff.rfl

theorem leftCoset_eq_iff {Hh : Subgroup G} {x y : G} :
    leftCoset Hh x = leftCoset Hh y ↔ x⁻¹ * y ∈ Hh := by
  constructor
  · intro h
    have hy : y ∈ leftCoset Hh x := by
      rw [h]
      exact mem_leftCoset.mpr (by rw [inv_mul_cancel]; exact Hh.one_mem)
    rwa [mem_leftCoset] at hy
  · intro h
    ext z
    rw [mem_leftCoset, mem_leftCoset]
    constructor
    · intro hz
      have h2 : y⁻¹ * z = (x⁻¹ * y)⁻¹ * (x⁻¹ * z) := by group
      rw [h2]
      exact Hh.mul_mem (Hh.inv_mem h) hz
    · intro hz
      have h2 : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
      rw [h2]
      exact Hh.mul_mem h hz

/-- `cosetInvCount Hh g` counts the involutions of the left coset `g Hh`. -/
theorem cosetInvCount_eq_of_leftCoset_eq {Hh : Subgroup G} {x y : G}
    (h : leftCoset Hh x = leftCoset Hh y) : cosetInvCount Hh x = cosetInvCount Hh y := by
  unfold cosetInvCount
  congr 1
  ext z
  simp only [Set.mem_setOf_eq]
  rw [← mem_leftCoset (Hh := Hh) (g := x) (z := z),
    ← mem_leftCoset (Hh := Hh) (g := y) (z := z), h]

theorem quotient_mk_eq_iff_mem_leftCoset {Hh : Subgroup G} [Hh.Normal] (c : G ⧸ Hh) (z : G) :
    QuotientGroup.mk z = c ↔ z ∈ leftCoset Hh (Quotient.out c) := by
  conv_lhs => rw [← Quotient.out_eq c]
  rw [QuotientGroup.eq, mem_leftCoset]
  constructor
  · intro h
    have h2 : (Quotient.out c)⁻¹ * z = (z⁻¹ * Quotient.out c)⁻¹ := by group
    rw [h2]
    exact Hh.inv_mem h
  · intro h
    have h2 : z⁻¹ * Quotient.out c = ((Quotient.out c)⁻¹ * z)⁻¹ := by group
    rw [h2]
    exact Hh.inv_mem h

/-- For `c ≠ 1` in `G ⧸ Hh`, the chosen representative `Quotient.out c` does not lie in `Hh`.
(`Hh` need not be normal: the quotient is the left-coset quotient.) -/
theorem quotient_out_notMem {Hh : Subgroup G} {c : G ⧸ Hh} (hc : c ≠ ((1 : G) : G ⧸ Hh)) :
    Quotient.out c ∉ Hh := by
  intro h
  apply hc
  rw [← Quotient.out_eq c]
  apply Quotient.sound
  show QuotientGroup.leftRel Hh (Quotient.out c) 1
  rw [QuotientGroup.leftRel_apply]
  simpa using Hh.inv_mem h

/-- **Bookkeeping for `bCount`.**  If every involution outside `Hh` lies in a coset with at
most four involutions, then `bCount Hh n = 0` for `n ≥ 5`.  (`Hh` need not be normal: `bCount`
is defined through the left-coset quotient, which exists for every subgroup.) -/
theorem bCount_eq_zero_of_involution_bound (Hh : Subgroup G)
    (hbound : ∀ y : G, orderOf y = 2 → y ∉ Hh → cosetInvCount Hh y ≤ 4) :
    ∀ n : ℕ, 5 ≤ n → bCount Hh n = 0 := by
  have hle : ∀ c : G ⧸ Hh, c ≠ ((1 : G) : G ⧸ Hh) → cosetInvCount Hh (Quotient.out c) ≤ 4 := by
    intro c hc
    by_cases hinv : ∃ y : G, orderOf y = 2 ∧ y ∈ leftCoset Hh (Quotient.out c)
    · obtain ⟨y, hy2, hy⟩ := hinv
      have hyH : y ∉ Hh := by
        intro hyh
        refine quotient_out_notMem (Hh := Hh) hc ?_
        have hk : (Quotient.out c)⁻¹ * y ∈ Hh := mem_leftCoset.mp hy
        have h2 : Quotient.out c = y * ((Quotient.out c)⁻¹ * y)⁻¹ := by group
        rw [h2]
        exact Hh.mul_mem hyh (Hh.inv_mem hk)
      have hsmul : leftCoset Hh (Quotient.out c) = leftCoset Hh y := by
        rw [leftCoset_eq_iff]
        exact mem_leftCoset.mp hy
      rw [cosetInvCount_eq_of_leftCoset_eq hsmul]
      exact hbound y hy2 hyH
    · push_neg at hinv
      have hzero : cosetInvCount Hh (Quotient.out c) = 0 := by
        have hempty : {x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ Hh} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨hz2, hzmem⟩
          exact hinv z hz2 (mem_leftCoset.mpr hzmem)
        unfold cosetInvCount
        rw [hempty, Set.ncard_empty]
      omega
  intro n hn
  unfold bCount
  have hempty : {c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧
      cosetInvCount Hh (Quotient.out c) = n} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro c ⟨hc, hcount⟩
    have h4 := hle c hc
    omega
  rw [hempty, Set.ncard_empty]

end Bookkeeping

end Work.CORE3

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G] [Finite G]

section PairTally

/-- The involutions of `G` lying outside `Ĥ` (Bender's `J ∖ Ĥ`). -/
def involsOutsideHat (B : BenderSetup G) : Set G := {z : G | orderOf z = 2 ∧ z ∉ B.Hhat}

/-- The involutions of `Ĥ` (Bender's `Ĥ ∩ J`). -/
def involsInHat (B : BenderSetup G) : Set G := involutionSet B.Hhat

/-- Bender §3 (8): the set of pairs `(z,s)` of commuting involutions with `z ∉ Ĥ` and `s ∈ Ĥ`.
Its cardinality is the number counted twice in the proof of `3b₄ + b₂ = 6k²`. -/
def commutingPairsOutsideHat (B : BenderSetup G) : Set (G × G) :=
  {p : G × G | p.1 ∈ involsOutsideHat B ∧ p.2 ∈ involsInHat B ∧ p.1 * p.2 = p.2 * p.1}

@[simp] theorem mem_involsOutsideHat {B : BenderSetup G} {z : G} :
    z ∈ involsOutsideHat B ↔ orderOf z = 2 ∧ z ∉ B.Hhat := Iff.rfl

@[simp] theorem mem_involsInHat {B : BenderSetup G} {s : G} :
    s ∈ involsInHat B ↔ s ∈ B.Hhat ∧ orderOf s = 2 := Iff.rfl

theorem involsOutsideHat_eq (B : BenderSetup G) :
    involsOutsideHat B = {z : G | orderOf z = 2} \ B.Hhat := by
  ext z; simp [involsOutsideHat, and_comm]

theorem involsInHat_eq (B : BenderSetup G) :
    involsInHat B = involutionSet B.Hhat := rfl

end PairTally

end Work.CORE3
