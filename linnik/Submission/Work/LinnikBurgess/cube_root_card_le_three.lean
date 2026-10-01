import Mathlib
set_option linter.style.haveILetI false

namespace Work.LinnikBurgess

/-! A unit of `ZMod (p ^ k)` has at most three cube roots.

The argument has three independent layers.

* Every cube root `r` of a unit `a` is itself a unit, so the ring-level
  counting can be pushed to the group of units; there the fibre of the cubing
  map over `a` is (when nonempty) a translate of the kernel, hence no larger
  than the number of cube roots of unity.
* For `p = 2` the group of units of `ZMod (2 ^ k)` has order a power of two,
  hence no element of order `3`, so the only cube root of unity is `1`.
* For odd `p` the group of units of the prime power `ZMod (p ^ k)` is cyclic
  (`ZMod.isCyclic_units_of_prime_pow`), and a cyclic group has at most `n`
  solutions to `x ^ n = 1` (`IsCyclic.card_pow_eq_one_le`). -/

/-- If `r ^ 3 = a` and `a` is a unit, then `r` is a unit.  Explicitly, `r` has
inverse `r ^ 2 * a⁻¹`. -/
lemma isUnit_of_cube_eq_unit {R : Type*} [CommSemiring R] {r a : R} (hr : r^3 = a)
    (ha : IsUnit a) : IsUnit r := by
  obtain ⟨u, hu⟩ := ha
  refine ⟨⟨r, r^2 * (↑(u⁻¹) : R), ?_, ?_⟩, rfl⟩
  · have h1 : r * (r^2 * ↑(u⁻¹)) = r^3 * ↑(u⁻¹) := by ring
    rw [h1, hr, ← hu]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · have h2 : (r^2 * ↑(u⁻¹)) * r = r^3 * ↑(u⁻¹) := by ring
    rw [h2, hr, ← hu]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- Cube roots of a unit `a` in a finite commutative ring inject into the cube
roots of `ha.unit` in the unit group: `x ↦ IsUnit.unit` of `x`. -/
lemma card_ring_le_card_units_kernel {R : Type*} [CommSemiring R] [Fintype R] [DecidableEq R]
    (a : R) (ha : IsUnit a) :
    Fintype.card {x : R // x^3 = a} ≤ Fintype.card {u : Rˣ // u^3 = ha.unit} := by
  apply Fintype.card_le_of_injective
    (fun x : {x : R // x^3 = a} =>
      ⟨(isUnit_of_cube_eq_unit x.2 ha).unit, by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, x.2, IsUnit.unit_spec]⟩)
  intro x y hxy
  have hv : (isUnit_of_cube_eq_unit x.2 ha).unit = (isUnit_of_cube_eq_unit y.2 ha).unit :=
    congrArg Subtype.val hxy
  apply Subtype.ext
  have hc := congrArg (fun u : Rˣ => (u : R)) hv
  rw [IsUnit.unit_spec, IsUnit.unit_spec] at hc
  exact hc

/-- In a finite commutative group the fibre of `x ↦ x ^ 3` over `a` is no larger
than the kernel of `x ↦ x ^ 3` (the two are equal when the fibre is nonempty,
via the bijection `u ↦ u * s⁻¹`). -/
lemma card_fiber_le_kernel {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (a : G) :
    Fintype.card {u : G // u^3 = a} ≤ Fintype.card {v : G // v^3 = 1} := by
  by_cases h : ∃ s : G, s^3 = a
  · obtain ⟨s, hs⟩ := h
    have key : ∀ u : G, u^3 = a → (u * s⁻¹)^3 = 1 := by
      intro u hu
      rw [mul_pow, hu, inv_pow, hs, mul_inv_cancel]
    let e : {u : G // u^3 = a} ≃ {v : G // v^3 = 1} :=
      { toFun := fun u => ⟨u.1 * s⁻¹, key u.1 u.2⟩
        invFun := fun v => ⟨v.1 * s, by rw [mul_pow, v.2, hs, one_mul]⟩
        left_inv := fun u => by ext; simp [mul_assoc]
        right_inv := fun v => by ext; simp [mul_assoc] }
    exact Fintype.card_le_of_injective e.toFun e.injective
  · have hempty : ∀ u : G, ¬ (u^3 = a) := by intro u hu; exact h ⟨u, hu⟩
    have hzero : Fintype.card {u : G // u^3 = a} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun x => hempty x.1 x.2⟩
    rw [hzero]; exact Nat.zero_le _

/-- The only cube root of unity among the units of `ZMod (2 ^ k)` is `1`: the
group of units has order `φ (2 ^ k) = 2 ^ (k-1)`, which is coprime to `3`, so an
element of order dividing `3` is trivial. -/
lemma units_two_pow_cube_eq_one {k : ℕ} (u : (ZMod (2^k))ˣ) (hu : u^3 = 1) : u = 1 := by
  haveI : NeZero (2^k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hdvd3 : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hu
  have hcard : Nat.card ((ZMod (2^k))ˣ) = (2^k).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hdvd : orderOf u ∣ (2^k).totient := by rw [← hcard]; exact orderOf_dvd_natCard u
  have htot : ¬ 3 ∣ (2^k).totient := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simp only [Nat.reduceSub, mul_one]
      exact fun h => (by have := Nat.prime_three.dvd_of_dvd_pow h; norm_num at this)
  have hcop : Nat.Coprime 3 ((2^k).totient) := (Nat.prime_three.coprime_iff_not_dvd).mpr htot
  have hgcd : orderOf u ∣ Nat.gcd 3 ((2^k).totient) := Nat.dvd_gcd hdvd3 hdvd
  rw [hcop.gcd_eq_one] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hgcd)

/-- The kernel of cubing on the units of `ZMod (p ^ k)` has at most `3` elements,
for every prime `p`. -/
lemma units_cube_kernel_card_le (p k : ℕ) [Fact p.Prime] :
    Fintype.card {u : (ZMod (p^k))ˣ // u^3 = 1} ≤ 3 := by
  rcases eq_or_ne p 2 with hp | hp2
  · subst hp
    have hsub : Subsingleton {u : (ZMod (2^k))ˣ // u^3 = 1} :=
      ⟨fun a b => by
        apply Subtype.ext
        rw [units_two_pow_cube_eq_one a.1 a.2, units_two_pow_cube_eq_one b.1 b.2]⟩
    calc Fintype.card {u : (ZMod (2^k))ˣ // u^3 = 1} ≤ 1 :=
          (Fintype.card_le_one_iff_subsingleton).mpr hsub
      _ ≤ 3 := by norm_num
  · haveI : IsCyclic (ZMod (p^k))ˣ := ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 k
    have h := IsCyclic.card_pow_eq_one_le (α := (ZMod (p^k))ˣ) (n := 3) (by norm_num)
    rw [Fintype.card_subtype]
    exact h

/-- A unit of `ZMod (p^k)` has at most three cube roots in the same ring.  (For odd `p` the group of units modulo a prime power is cyclic, so the kernel of `x ↦ x^3` has order `gcd(3, φ(p^k)) ≤ 3`; for `p = 2` cubing is an automorphism of the odd units.) -/
theorem cube_root_card_le_three (p k : ℕ) [Fact p.Prime] (a : ZMod (p ^ k)) (ha : IsUnit a) :
    ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun x => x ^ 3 = a)).card ≤ 3 := by
  classical
  rw [← Fintype.card_subtype (fun x : ZMod (p^k) => x^3 = a)]
  calc Fintype.card {x : ZMod (p^k) // x^3 = a}
      ≤ Fintype.card {u : (ZMod (p^k))ˣ // u^3 = ha.unit} :=
        card_ring_le_card_units_kernel a ha
    _ ≤ Fintype.card {v : (ZMod (p^k))ˣ // v^3 = 1} :=
        card_fiber_le_kernel ha.unit
    _ ≤ 3 := units_cube_kernel_card_le p k

end Work.LinnikBurgess
