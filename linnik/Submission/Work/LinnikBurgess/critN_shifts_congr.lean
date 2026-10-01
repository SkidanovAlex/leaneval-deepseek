import Mathlib
import Submission.Work.LinnikBurgess.critN_shifts

/-!
# Proportionality of the shifted symmetric functions at a double-critical level

`critN_shifts.lean` evaluates the Wronskian `critN a b` and its derivative at the shift `y`
as the two "cross" expressions

* `critN a b (y) = sh2 y a · sh3 y b − sh3 y a · sh2 y b`,
* `derivative (critN a b) (y) = 2 · (sh1 y a · sh3 y b − sh3 y a · sh1 y b)`

in terms of the shifted elementary symmetric functions `sh1, sh2, sh3` of the triples
`y + a l` and `y + b l`.

The present lemma extracts the *consequence* of the two congruences `p^k ∣ N(y)` and
`p^k ∣ N'(y)`: whenever none of the `y + a l`, `y + b l` is divisible by `p` (so that the
products `sh3 y a`, `sh3 y b` are units), the two triples are proportional modulo
`p ^ (k − v_p(2))` by a unit.  The exponent `k − v_p 2` is exactly the loss needed to
remove the factor `2` in the second congruence: for odd `p` it costs nothing, while for
`p = 2` it is the shift from `2^k` to `2^(k-1)`.
-/

namespace Work.LinnikBurgess

/-- Removing a factor of `2` from a `p`-adic divisibility: if `p^a ∣ 2 * D` then
`p ^ (a - padicValNat p 2) ∣ D`.  For odd `p` this just says `p^a ∣ D`; for `p = 2` it
loses one power of `2`. -/
private theorem int_dvd_of_two_mul_dvd {p a : ℕ} [Fact p.Prime] (D : ℤ)
    (h : ((p ^ a : ℕ) : ℤ) ∣ 2 * D) :
    ((p ^ (a - padicValNat p 2) : ℕ) : ℤ) ∣ D := by
  by_cases hD : D = 0
  · subst hD; exact dvd_zero _
  · have hn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
    have h2 : p ^ a ∣ 2 * D.natAbs := by
      have hh := (Int.natAbs_dvd_natAbs).mpr h
      simpa [Int.natAbs_mul] using hh
    have h3 : a ≤ padicValNat p (2 * D.natAbs) :=
      (padicValNat_dvd_iff_le (mul_ne_zero (by norm_num) hn)).mp h2
    have h4 : padicValNat p (2 * D.natAbs) = padicValNat p 2 + padicValNat p D.natAbs :=
      padicValNat.mul (by norm_num) hn
    have h5 : a - padicValNat p 2 ≤ padicValNat p D.natAbs := by omega
    have h6 : p ^ (a - padicValNat p 2) ∣ D.natAbs :=
      (padicValNat_dvd_iff_le hn).mpr h5
    exact (Int.natAbs_dvd_natAbs).mp (by simpa [Int.natAbs_natCast] using h6)

/-- Abstract proportionality step: two triples `s` and `t` over a commutative ring whose
`sh3`-entries are units and which satisfy the two cross relations `s₂t₃ = s₃t₂` and
`s₁t₃ = s₃t₁` are proportional by the unit `s₃ / t₃`. -/
private theorem zmod_unit_proportional {R : Type*} [CommRing R] {s1 s2 s3 t1 t2 t3 : R}
    (hs3 : IsUnit s3) (ht3 : IsUnit t3)
    (h23 : s2 * t3 = s3 * t2) (h13 : s1 * t3 = s3 * t1) :
    ∃ c : R, IsUnit c ∧ s1 = c * t1 ∧ s2 = c * t2 ∧ s3 = c * t3 := by
  obtain ⟨u, hu⟩ := ht3
  refine ⟨s3 * ↑u⁻¹, IsUnit.mul hs3 (Units.isUnit u⁻¹), ?_, ?_, ?_⟩
  · have h := congrArg (fun z : R => z * (↑u⁻¹ : R)) h13
    rw [← hu] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  · have h := congrArg (fun z : R => z * (↑u⁻¹ : R)) h23
    rw [← hu] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  · rw [mul_assoc, ← hu, Units.inv_mul, mul_one]

/-- If `p ∤ m` then `m` is a unit modulo `p ^ e`. -/
private theorem isUnit_natCast_zmod_of_not_dvd {p e m : ℕ} [Fact p.Prime] (h : ¬ p ∣ m) :
    IsUnit ((m : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (Fact.out : p.Prime).coprime_pow_of_not_dvd h

/-- **Proportionality of the shifts at a double-critical level.**  If `critN a b` and its
derivative both vanish at `y` modulo `p^k`, and none of the `y + a l`, `y + b l` is divisible
by `p`, then the shifted symmetric-function triples `(sh1, sh2, sh3)` of `a` and `b` are
proportional modulo `p ^ (k - padicValNat p 2)` by a unit. -/
theorem critN_shifts_congr {p k : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt p y a b)
    (hN : ((p ^ k : ℕ) : ℤ) ∣ (sh2 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh2 y b : ℤ))
    (hN' : ((p ^ k : ℕ) : ℤ)
      ∣ 2 * ((sh1 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh1 y b : ℤ))) :
    ∃ c : ZMod (p ^ (k - padicValNat p 2)), IsUnit c ∧
      (sh1 y a : ZMod (p ^ (k - padicValNat p 2)))
        = c * (sh1 y b : ZMod (p ^ (k - padicValNat p 2))) ∧
      (sh2 y a : ZMod (p ^ (k - padicValNat p 2)))
        = c * (sh2 y b : ZMod (p ^ (k - padicValNat p 2))) ∧
      (sh3 y a : ZMod (p ^ (k - padicValNat p 2)))
        = c * (sh3 y b : ZMod (p ^ (k - padicValNat p 2))) := by
  have hp : p.Prime := Fact.out
  set e := k - padicValNat p 2 with he
  have hes : e ≤ k := by rw [he]; exact Nat.sub_le _ _
  have hpe : ((p ^ e : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hes)
  -- first cross congruence, reduced to the modulus `p ^ e`
  have hE2 : (sh2 y a : ZMod (p ^ e)) * (sh3 y b : ZMod (p ^ e))
      - (sh3 y a : ZMod (p ^ e)) * (sh2 y b : ZMod (p ^ e)) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((sh2 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh2 y b : ℤ)) (p ^ e)).mpr
      (dvd_trans hpe hN)
    push_cast at h
    exact h
  have hE2' : (sh2 y a : ZMod (p ^ e)) * (sh3 y b : ZMod (p ^ e))
      = (sh3 y a : ZMod (p ^ e)) * (sh2 y b : ZMod (p ^ e)) := sub_eq_zero.mp hE2
  -- second cross congruence: remove the factor `2` (this is where `k - v_p 2` appears)
  have hE1 : (sh1 y a : ZMod (p ^ e)) * (sh3 y b : ZMod (p ^ e))
      - (sh3 y a : ZMod (p ^ e)) * (sh1 y b : ZMod (p ^ e)) = 0 := by
    have hdiv : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣
        (sh1 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh1 y b : ℤ) :=
      int_dvd_of_two_mul_dvd
        ((sh1 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh1 y b : ℤ)) hN'
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((sh1 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh1 y b : ℤ)) (p ^ e)).mpr hdiv
    push_cast at h
    exact h
  have hE1' : (sh1 y a : ZMod (p ^ e)) * (sh3 y b : ZMod (p ^ e))
      = (sh3 y a : ZMod (p ^ e)) * (sh1 y b : ZMod (p ^ e)) := sub_eq_zero.mp hE1
  -- the products `sh3` are units because `p` does not divide any of the shifts
  have hnd_a : ¬ p ∣ sh3 y a := by
    intro hd
    rw [sh3] at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact (hy 0).1 hd
      · exact (hy 1).1 hd
    · exact (hy 2).1 hd
  have hnd_b : ¬ p ∣ sh3 y b := by
    intro hd
    rw [sh3] at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact (hy 0).2 hd
      · exact (hy 1).2 hd
    · exact (hy 2).2 hd
  have hun_a : IsUnit ((sh3 y a : ℕ) : ZMod (p ^ e)) :=
    isUnit_natCast_zmod_of_not_dvd hnd_a
  have hun_b : IsUnit ((sh3 y b : ℕ) : ZMod (p ^ e)) :=
    isUnit_natCast_zmod_of_not_dvd hnd_b
  exact zmod_unit_proportional hun_a hun_b hE2' hE1'

end Work.LinnikBurgess
