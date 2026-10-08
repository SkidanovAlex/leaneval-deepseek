/-
# Automorphisms of odd order of a dihedral 2-group are trivial

`DihedralGroup (2^j)` (`j ≥ 2`) is the dihedral group of order `2^(j+1)`.  Its automorphism
group is `Hol(Z/2^j)` of order `2^j · 2^(j-1) = 2^(2j-1)`, which is a 2-group; consequently
every automorphism of `DihedralGroup (2^j)` of *odd* order is the identity.

The proof below is self-contained and deliberately avoids computing `Aut(D_{2^j})`:

* `zmod_two_pow_pow_eq_one_of_odd` : in `ZMod (2^j)` (`j ≥ 1`) the group of units is a
  2-group, hence an element of odd multiplicative order is `1`;
* the rotation part: writing `β (r 1) = r i`, one shows `i ^ orderOf β = 1`, so `i = 1` and
  `β` fixes the rotation subgroup `⟨r⟩` pointwise;
* the reflection part: `β (sr 0) = sr c`, and iterating `β` on the reflections forces
  `(orderOf β) · c = 0`; as `orderOf β` is odd (a unit mod `2^j`) this gives `c = 0`.
-/
import Mathlib

namespace Work.FUS.AutFacts

open DihedralGroup

/-- In `ZMod (2^j)` with `j ≥ 1`, an element of odd multiplicative order is `1`.

Equivalently: the group of units of `ZMod (2^j)` is a 2-group (`ZMod.card_units_eq_totient`
together with `Nat.totient_prime_pow`). -/
lemma zmod_two_pow_pow_eq_one_of_odd {j m : ℕ} (hj : 1 ≤ j) (hm : Odd m)
    {x : ZMod (2 ^ j)} (h : x ^ m = 1) : x = 1 := by
  have hm1 : 1 ≤ m := by obtain ⟨k, hk⟩ := hm; omega
  -- `x` is a unit, with inverse `x ^ (m - 1)`.
  have hxu : IsUnit x := by
    have h' : x * x ^ (m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hm1]; exact h
    exact ⟨⟨x, x ^ (m - 1), h', by rw [mul_comm]; exact h'⟩, rfl⟩
  have hcard : Fintype.card (ZMod (2 ^ j))ˣ = 2 ^ (j - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
      show (2 : ℕ) - 1 = 1 from rfl, mul_one]
  -- Hence `x ^ 2^(j-1) = 1`.
  have h2 : x ^ 2 ^ (j - 1) = 1 := by
    rcases hxu with ⟨u, rfl⟩
    rw [← hcard, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]
  have hd1 : orderOf x ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
  have hd2 : orderOf x ∣ 2 ^ (j - 1) := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hcop : Nat.Coprime m (2 ^ (j - 1)) := hm.coprime_two_right.pow_right (j - 1)
  have hd : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/-- Every element of a dihedral group is a rotation `r i` or a reflection `sr i`. -/
private lemma dihedralGroup_eq_r_or_sr {n : ℕ} (x : DihedralGroup n) :
    (∃ i : ZMod n, x = r i) ∨ (∃ i : ZMod n, x = sr i) := by
  cases x with
  | r i => exact Or.inl ⟨i, rfl⟩
  | sr i => exact Or.inr ⟨i, rfl⟩

theorem mulAut_dihedral_eq_one_of_odd (j : ℕ) (hj : 2 ≤ j) (β : DihedralGroup (2 ^ j) ≃* DihedralGroup (2 ^ j))
    (hodd : Odd (orderOf β)) : β = 1 := by
  have hj1 : 1 ≤ j := by omega
  have h2j : (2 : ℕ) < 2 ^ j := by
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  -- `β (r 1)` has order `2 ^ j`, so it is a rotation `r i`.
  have horder : orderOf (β (r 1)) = 2 ^ j := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨i, hi⟩ : ∃ i : ZMod (2 ^ j), β (r 1) = r i := by
    rcases dihedralGroup_eq_r_or_sr (β (r 1)) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    · exfalso
      rw [ha, DihedralGroup.orderOf_sr] at horder
      omega
  -- The action on the rotation subgroup: `β (r a) = r (i * a)`.
  have hβr : ∀ a : ZMod (2 ^ j), β (r a) = r (i * a) := by
    intro a
    have ha : ((a.val : ℕ) : ZMod (2 ^ j)) = a := ZMod.natCast_zmod_val a
    rw [← ha, ← DihedralGroup.r_one_pow a.val, map_pow, hi, DihedralGroup.r_pow]
  -- Iterating: `β ^ k (r a) = r (i ^ k * a)`.
  have hpow1 : ∀ k : ℕ, ∀ a : ZMod (2 ^ j), (β ^ k) (r a) = r (i ^ k * a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
        intro a
        rw [pow_succ]
        show (β ^ k) (β (r a)) = r (i ^ (k + 1) * a)
        rw [hβr a, ih (i * a), pow_succ, mul_assoc]
  have him : i ^ orderOf β = 1 := by
    have h1 : (β ^ orderOf β) (r 1) = r 1 := by rw [pow_orderOf_eq_one]; rfl
    have h2 := hpow1 (orderOf β) 1
    rw [h1] at h2
    simpa using (DihedralGroup.r.inj h2).symm
  -- Number theory: `i` has odd order, hence `i = 1`.
  have hi1 : i = 1 := zmod_two_pow_pow_eq_one_of_odd hj1 hodd him
  -- So `β` fixes the rotation subgroup pointwise (and `β⁻¹` too).
  have hβfixr : ∀ a : ZMod (2 ^ j), β (r a) = r a := by
    intro a
    rw [hβr, hi1, one_mul]
  have hβinv_fixr : ∀ a : ZMod (2 ^ j), β.symm (r a) = r a := by
    intro a
    apply β.injective
    rw [MulEquiv.apply_symm_apply, hβfixr]
  -- `β (sr 0)` cannot be a rotation, so it is a reflection `sr c`.
  obtain ⟨c, hc⟩ : ∃ c : ZMod (2 ^ j), β (sr 0) = sr c := by
    rcases dihedralGroup_eq_r_or_sr (β (sr 0)) with ⟨a, ha⟩ | ⟨c, hc⟩
    · exfalso
      have hs : (sr (0 : ZMod (2 ^ j)) : DihedralGroup (2 ^ j)) = r a := by
        rw [← MulEquiv.symm_apply_apply β (sr 0), ha, hβinv_fixr]
      exact (show ¬ ((sr (0 : ZMod (2 ^ j)) : DihedralGroup (2 ^ j)) = r a) from
        by intro hh; injection hh) hs
    · exact ⟨c, hc⟩
  -- Consequent action on reflections: `β (sr x) = sr (x + c)`.
  have hsr : ∀ x : ZMod (2 ^ j), β (sr x) = sr (x + c) := by
    intro x
    have hx : (sr x : DihedralGroup (2 ^ j)) = r (-x) * sr 0 := by
      rw [DihedralGroup.r_mul_sr]; congr 1; ring
    rw [hx, map_mul, hβfixr, hc, DihedralGroup.r_mul_sr]
    congr 1
    ring
  have hpow2 : ∀ k : ℕ, ∀ x : ZMod (2 ^ j),
      (β ^ k) (sr x) = sr (x + (k : ZMod (2 ^ j)) * c) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ]
        show (β ^ k) (β (sr x)) = sr (x + ((k + 1 : ℕ) : ZMod (2 ^ j)) * c)
        rw [hsr x, ih (x + c)]
        congr 1
        push_cast
        ring
  -- Evaluating at `k = orderOf β` gives `(orderOf β) * c = 0`.
  have hmc : ((orderOf β : ℕ) : ZMod (2 ^ j)) * c = 0 := by
    have h1 : (β ^ orderOf β) (sr 0) = sr 0 := by rw [pow_orderOf_eq_one]; rfl
    have h2 := hpow2 (orderOf β) 0
    rw [h1] at h2
    simpa using (DihedralGroup.sr.inj h2).symm
  -- As `orderOf β` is odd it is a unit mod `2 ^ j`, so `c = 0`.
  have hc0 : c = 0 := by
    have hunit : IsUnit ((orderOf β : ℕ) : ZMod (2 ^ j)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact hodd.coprime_two_right.pow_right j
    rw [mul_comm] at hmc
    exact (IsUnit.mul_left_eq_zero hunit).mp hmc
  apply MulEquiv.ext
  intro x
  cases x with
  | r a => simp [hβfixr]
  | sr a => simp [hsr, hc0]

end Work.FUS.AutFacts
