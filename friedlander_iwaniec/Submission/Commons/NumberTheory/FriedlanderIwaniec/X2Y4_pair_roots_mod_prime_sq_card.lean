import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_pow_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The set of units of `ZMod n` has the same cardinality as the unit group. -/
lemma ncard_isUnit_zmod (n : ℕ) :
    ({u : ZMod n | IsUnit u}.ncard) = Nat.card (ZMod n)ˣ := by
  have hinj : Function.Injective (fun u : (ZMod n)ˣ => (u : ZMod n)) := Units.val_injective
  have himg : (fun u : (ZMod n)ˣ => (u : ZMod n)) '' Set.univ = {u : ZMod n | IsUnit u} := by
    ext u
    constructor
    · rintro ⟨v, -, rfl⟩
      exact v.isUnit
    · intro hu
      exact ⟨hu.unit, Set.mem_univ _, hu.unit_spec⟩
  rw [← himg, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]

/-- The number of units in `ZMod (p ^ 2)` is `p ^ 2 - p`. -/
lemma ncard_isUnit_zmod_prime_sq {p : ℕ} (hp : p.Prime) :
    ({u : ZMod (p ^ 2) | IsUnit u}.ncard) = p ^ 2 - p := by
  haveI : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  rw [ncard_isUnit_zmod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
  rw [show 2 - 1 = 1 by norm_num, pow_one]
  rw [Nat.mul_sub_left_distrib, mul_one, pow_two]

/-- The number of non-units in `ZMod (p ^ 2)` is `p`. -/
lemma ncard_not_isUnit_zmod_prime_sq {p : ℕ} (hp : p.Prime) :
    ({u : ZMod (p ^ 2) | ¬ IsUnit u}.ncard) = p := by
  classical
  haveI : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  rw [ncard_zmod_eq_range (n := p ^ 2) (ψ := fun u : ZMod (p ^ 2) => ¬ IsUnit u)]
  have hfilter : ((Finset.range (p ^ 2)).filter
        (fun r : ℕ => ¬ IsUnit ((r : ℕ) : ZMod (p ^ 2))))
      = ((Finset.range (p ^ 2)).filter (fun r : ℕ => p ∣ r)) := by
    apply Finset.filter_congr
    intro r _
    constructor
    · intro h
      by_contra hpr
      exact h ((ZMod.isUnit_iff_coprime r (p ^ 2)).mpr
        ((Nat.coprime_pow_right_iff (by norm_num : 0 < 2) r p).mpr
          (Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpr))))
    · intro hd hu
      have hc : r.Coprime (p ^ 2) := (ZMod.isUnit_iff_coprime r (p ^ 2)).mp hu
      have hcp : r.Coprime p := (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) r p).mp hc
      have hpc : p.Coprime r := Nat.coprime_comm.mp hcp
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hpc hd
  rw [hfilter, card_filter_range_dvd (p ^ 2) p hp.pos (dvd_pow_self p (by norm_num : 2 ≠ 0))]
  rw [pow_two, Nat.mul_div_right p hp.pos]

/-- The number of square roots of `0` in `ZMod (p ^ 2)` is `p`. -/
lemma ncard_sq_eq_zero_zmod_prime_sq {p : ℕ} (hp : p.Prime) :
    ({a : ZMod (p ^ 2) | a ^ 2 = 0}.ncard) = p := by
  classical
  haveI : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  rw [ncard_zmod_eq_range (n := p ^ 2) (ψ := fun a : ZMod (p ^ 2) => a ^ 2 = 0)]
  have hfilter : ((Finset.range (p ^ 2)).filter
        (fun r : ℕ => ((r : ℕ) : ZMod (p ^ 2)) ^ 2 = 0))
      = ((Finset.range (p ^ 2)).filter (fun r : ℕ => p ^ 2 ∣ r ^ 2)) := by
    apply Finset.filter_congr
    intro r _
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [hfilter, card_filter_range_sq_dvd_prime_pow p 2 hp (by norm_num : 1 ≤ 2)]
  rw [show 2 / 2 = 1 by norm_num, pow_one]

/-- A non-unit `y` of `ZMod (p ^ 2)` satisfies `y ^ 4 = 0` (in fact `y ^ 2 = 0`). -/
lemma pow_four_eq_zero_of_not_isUnit_zmod_prime_sq {p : ℕ} (hp : p.Prime)
    {y : ZMod (p ^ 2)} (hy : ¬ IsUnit y) : y ^ 4 = 0 := by
  haveI : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  have hpdvd : p ∣ y.val := by
    have h : ¬ IsUnit ((y.val : ℕ) : ZMod (p ^ 2)) := by rwa [ZMod.natCast_zmod_val]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by norm_num : 0 < 2)] at h
    by_contra hnd
    exact h (Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
  have hsq : y ^ 2 = 0 := by
    have h2 : ((y.val ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      obtain ⟨k, hk⟩ := hpdvd
      exact ⟨k ^ 2, by rw [hk]; ring⟩
    calc y ^ 2 = ((y.val : ZMod (p ^ 2))) ^ 2 := by rw [ZMod.natCast_zmod_val]
      _ = ((y.val ^ 2 : ℕ) : ZMod (p ^ 2)) := by rw [Nat.cast_pow]
      _ = 0 := h2
  calc y ^ 4 = (y ^ 2) ^ 2 := by ring
    _ = 0 := by rw [hsq]; ring

/-- The number of pairs `(x, y)` with `y` a unit and `x ^ 2 + y ^ 4 = 0`, in
`ZMod n × ZMod n`, is the number of square roots of `-1` times the number of
units. -/
lemma X2Y4_pair_count_isUnit_snd {n : ℕ} :
    ({x : ZMod n × ZMod n | IsUnit x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      ({γ : ZMod n | γ ^ 2 = -1}.ncard) * ({u : ZMod n | IsUnit u}.ncard) := by
  classical
  let B : Set (ZMod n × ZMod n) := {x | IsUnit x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}
  let T : Set (ZMod n × ZMod n) := {x | x.1 ^ 2 = -1 ∧ IsUnit x.2}
  let Φ : (ZMod n × ZMod n) → (ZMod n × ZMod n) := fun z => (z.1 * (z.2 ^ 2)⁻¹, z.2)
  let Ψ : (ZMod n × ZMod n) → (ZMod n × ZMod n) := fun w => (w.1 * w.2 ^ 2, w.2)
  have hΦ_mem : ∀ z, z ∈ B → Φ z ∈ T := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h2u : IsUnit (z.2 ^ 2) := hz1.pow 2
    have hinv : z.2 ^ 2 * (z.2 ^ 2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
    refine ⟨?_, hz1⟩
    change (z.1 * (z.2 ^ 2)⁻¹) ^ 2 = -1
    calc (z.1 * (z.2 ^ 2)⁻¹) ^ 2
        = z.1 ^ 2 * ((z.2 ^ 2)⁻¹) ^ 2 := by ring
      _ = -(z.2 ^ 2) ^ 2 * ((z.2 ^ 2)⁻¹) ^ 2 := by
            rw [eq_neg_of_add_eq_zero_left hz2, show z.2 ^ 4 = (z.2 ^ 2) ^ 2 by ring]
      _ = -((z.2 ^ 2) * (z.2 ^ 2)⁻¹) ^ 2 := by ring
      _ = -1 := by rw [hinv]; ring
  have hΨ_mem : ∀ w, w ∈ T → Ψ w ∈ B := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · change IsUnit w.2
      exact hw2
    · change (w.1 * w.2 ^ 2) ^ 2 + w.2 ^ 4 = 0
      calc (w.1 * w.2 ^ 2) ^ 2 + w.2 ^ 4
          = w.1 ^ 2 * (w.2 ^ 2) ^ 2 + w.2 ^ 4 := by ring
        _ = w.1 ^ 2 * w.2 ^ 4 + w.2 ^ 4 := by ring
        _ = (-1) * w.2 ^ 4 + w.2 ^ 4 := by rw [hw1]
        _ = 0 := by ring
  have hΨΦ : ∀ z, z ∈ B → Ψ (Φ z) = z := by
    intro z hz
    obtain ⟨hz1, -⟩ := hz
    have h2u : IsUnit (z.2 ^ 2) := hz1.pow 2
    apply Prod.ext
    · change (z.1 * (z.2 ^ 2)⁻¹) * z.2 ^ 2 = z.1
      rw [mul_assoc, ZMod.inv_mul_of_unit _ h2u, mul_one]
    · rfl
  have hΦΨ : ∀ w, w ∈ T → Φ (Ψ w) = w := by
    intro w hw
    obtain ⟨-, hw2⟩ := hw
    have h2u : IsUnit (w.2 ^ 2) := hw2.pow 2
    apply Prod.ext
    · change (w.1 * w.2 ^ 2) * (w.2 ^ 2)⁻¹ = w.1
      rw [mul_assoc, ZMod.mul_inv_of_unit _ h2u, mul_one]
    · rfl
  have hImg : Φ '' B = T := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hΦ_mem z hz
    · intro hw
      exact ⟨Ψ w, hΨ_mem w hw, hΦΨ w hw⟩
  have hInj : Set.InjOn Φ B := by
    intro z hz w hw heq
    calc z = Ψ (Φ z) := (hΨΦ z hz).symm
      _ = Ψ (Φ w) := congrArg Ψ heq
      _ = w := hΨΦ w hw
  have hB : B.ncard = T.ncard := by
    rw [← hImg, Set.InjOn.ncard_image hInj]
  have hT : T = ({γ : ZMod n | γ ^ 2 = -1} ×ˢ {u : ZMod n | IsUnit u}) := by
    ext w
    simp [T]
  calc ({x : ZMod n × ZMod n | IsUnit x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard)
      = B.ncard := rfl
    _ = T.ncard := hB
    _ = ({γ : ZMod n | γ ^ 2 = -1} ×ˢ {u : ZMod n | IsUnit u}).ncard := by rw [hT]
    _ = ({γ : ZMod n | γ ^ 2 = -1}.ncard) * ({u : ZMod n | IsUnit u}.ncard) := by
          rw [Set.ncard_prod]

theorem X2Y4_pair_roots_mod_prime_sq_card {p : ℕ} (hp : p.Prime) :
    ({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      if p = 2 then 4 else if p % 4 = 1 then 3 * p ^ 2 - 2 * p else p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  let S : Set (ZMod (p ^ 2) × ZMod (p ^ 2)) := {x | x.1 ^ 2 + x.2 ^ 4 = 0}
  let A : Set (ZMod (p ^ 2) × ZMod (p ^ 2)) := {x | IsUnit x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}
  let B : Set (ZMod (p ^ 2) × ZMod (p ^ 2)) := {x | ¬ IsUnit x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}
  have hsplit : S = A ∪ B := by
    ext x
    simp only [S, A, B, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hu : IsUnit x.2
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hxB.1 hxA.1
  have hSU : S.ncard = A.ncard + B.ncard := by
    rw [hsplit, Set.ncard_union_eq hdisj]
  have hA : A.ncard = ({γ : ZMod (p ^ 2) | γ ^ 2 = -1}.ncard) * (p ^ 2 - p) := by
    have h1 := X2Y4_pair_count_isUnit_snd (n := p ^ 2)
    rw [ncard_isUnit_zmod_prime_sq hp] at h1
    exact h1
  have hB : B.ncard = p ^ 2 := by
    have hEq : B = ({a : ZMod (p ^ 2) | a ^ 2 = 0} ×ˢ {y : ZMod (p ^ 2) | ¬ IsUnit y}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hx1, hx2⟩ := hx
        have h4 : x.2 ^ 4 = 0 := pow_four_eq_zero_of_not_isUnit_zmod_prime_sq hp hx1
        refine ⟨?_, hx1⟩
        rw [h4, add_zero] at hx2
        exact hx2
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have h4 : x.2 ^ 4 = 0 := pow_four_eq_zero_of_not_isUnit_zmod_prime_sq hp h2
        rw [h1, h4, add_zero]
    rw [hEq, Set.ncard_prod, ncard_sq_eq_zero_zmod_prime_sq hp,
        ncard_not_isUnit_zmod_prime_sq hp, ← pow_two]
  have hmain : S.ncard = ({γ : ZMod (p ^ 2) | γ ^ 2 = -1}.ncard) * (p ^ 2 - p) + p ^ 2 := by
    rw [hSU, hA, hB]
  have hR2 : p = 2 → ({γ : ZMod (p ^ 2) | γ ^ 2 = -1}.ncard) = 0 := by
    intro h2
    rw [h2]
    exact sq_roots_neg_one_mod_two_pow_eq_zero (by norm_num : 2 ≤ 2)
  have hR1 : p % 4 = 1 → ({γ : ZMod (p ^ 2) | γ ^ 2 = -1}.ncard) = 2 := by
    intro h
    exact sq_roots_neg_one_mod_prime_pow_eq_two hp h (by norm_num : 1 ≤ 2)
  have hR3 : p % 4 = 3 → ({γ : ZMod (p ^ 2) | γ ^ 2 = -1}.ncard) = 0 := by
    intro h
    exact sq_roots_neg_one_mod_prime_pow_eq_zero hp h (by norm_num : 1 ≤ 2)
  rw [hmain]
  by_cases h2 : p = 2
  · rw [if_pos h2, hR2 h2, h2]
    norm_num
  · rw [if_neg h2]
    have hp2 : 2 ≤ p := hp.two_le
    by_cases h41 : p % 4 = 1
    · rw [if_pos h41, hR1 h41]
      have h1 : 2 * (p ^ 2 - p) = 2 * p ^ 2 - 2 * p := by
        rw [Nat.mul_sub_left_distrib]
      rw [h1]
      have h2' : 2 * p ≤ 2 * p ^ 2 := by nlinarith
      rw [← Nat.sub_add_comm h2']
      have h3 : 2 * p ^ 2 + p ^ 2 = 3 * p ^ 2 := by ring
      rw [h3]
    · rw [if_neg h41]
      have h43 : p % 4 = 3 := by
        have hpodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left h2
        have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        have hmod2 : (p % 4) % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]
          exact hpodd
        interval_cases p % 4 <;> omega
      rw [hR3 h43, zero_mul, zero_add]

end Commons.NumberTheory.FriedlanderIwaniec
