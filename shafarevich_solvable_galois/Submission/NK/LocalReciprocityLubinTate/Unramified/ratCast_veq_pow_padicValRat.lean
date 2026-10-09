import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The valuation of a rational, in an abstract valued field of characteristic zero

Let `F` be a field of characteristic zero carrying a valuative relation `≤ᵥ` in the sense of
`ValuativeRel` (i.e. an equivalence class of valuations), and let `p` be a rational prime whose
image in `F` satisfies `(p : F) <ᵥ 1`, so that `p` is not a unit of the valuation ring of `F`.

The main result, `ratCast_veq_pow_padicValRat`, says that for every nonzero rational `q` with
`padicValRat p q ≥ 0`, the image of `q` in `F` has the same value as `(p : F) ^ padicValRat p q`.

The mathematical content is that the restricted valuation on `ℚ ⊆ F` is the `p`-adic one: a
valuation of `ℚ` has at most one rational prime of value `< 1`, because for coprime integers
`a` and `b` (here `p` and a prime `ℓ ≠ p`) one has a Bézout relation `u * a + v * b = 1`; all
integers have value `≤ 1`, so `1 = v (u * a + v * b) ≤ max (v a) (v b) < 1` is a contradiction as
soon as both `a` and `b` have value `< 1`.  Since `p` has value `< 1`, every integer coprime to `p`
is a unit, and the decomposition `q = p ^ padicValRat p q * u` with `u` a unit gives the claim.

## Main result

* `ratCast_veq_pow_padicValRat`
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NK.LocalReciprocityLubinTate.Unramified

open ValuativeRel

section Aux

variable {F : Type*} [Field F] [ValuativeRel F]

/-- **Every natural number has value `≤ 1`**, i.e. is integral for the valuation: `n = (n-1) + 1`
and addition of two elements of value `≤ 1` again has value `≤ 1`. -/
lemma ratCast_vle_one_natCast (n : ℕ) : ((n : F) ≤ᵥ (1 : F)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact vle_add ih vle_rfl

/-- Negation preserves the value. -/
lemma ratCast_neg_veq (x : F) : (-x) =ᵥ x :=
  (Valuation.veq_iff_eq (v := ValuativeRel.valuation F)).mpr (Valuation.map_neg _ x)

/-- **Every integer has value `≤ 1`.** -/
lemma ratCast_vle_one_intCast (n : ℤ) : ((n : F) ≤ᵥ (1 : F)) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  · rw [hm]; push_cast; exact ratCast_vle_one_natCast m
  · rw [hm]; push_cast
    exact vle_of_veq_of_vle (ratCast_neg_veq (x := (m : F))) (ratCast_vle_one_natCast m)

/-- The value relation is compatible with powers. -/
lemma ratCast_veq_pow {x y : F} (h : x =ᵥ y) (n : ℕ) : x ^ n =ᵥ y ^ n := by
  induction n with
  | zero => simpa using veq_refl (1 : F)
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_veq_mul ih h

/-- **An integer coprime to `p` has value `1`.**

Indeed, `m.Coprime p` gives integers `u`, `v` with `u * m + v * p = 1`.  All integers have value
`≤ 1`, so `1 = v (u * m + v * p) ≤ max (v m) (v p) < 1` unless `v m = 1`, since `v p < 1`. -/
lemma ratCast_veq_one_natCast_of_not_dvd {p : ℕ} (hp : p.Prime) (hlt : (p : F) <ᵥ 1) {m : ℕ}
    (hm : ¬ p ∣ m) : ((m : F) =ᵥ (1 : F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hγ : ValuativeRel.valuation F (p : F) < 1 := by
    have := (Valuation.vlt_iff_lt (ValuativeRel.valuation F)).mp hlt
    simpa using this
  have hmle : ValuativeRel.valuation F (m : F) ≤ 1 :=
    (Valuation.vle_iff_le (ValuativeRel.valuation F)).mp (ratCast_vle_one_natCast (F := F) m)
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd).mpr hm |>.symm
  have hbez : (m : ℤ) * (m.gcdA p) + (p : ℤ) * (m.gcdB p) = 1 := by
    have h := Nat.gcd_eq_gcd_ab m p
    rw [hcop.gcd_eq_one] at h
    norm_num at h
    exact h.symm
  have hbezF : (m : F) * ((m.gcdA p : ℤ) : F) + (p : F) * ((m.gcdB p : ℤ) : F) = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) hbez
    push_cast at this
    simpa using this
  have hgA : ValuativeRel.valuation F (((m.gcdA p : ℤ)) : F) ≤ 1 :=
    (Valuation.vle_iff_le (ValuativeRel.valuation F)).mp
      (ratCast_vle_one_intCast (F := F) (m.gcdA p))
  have hgB : ValuativeRel.valuation F (((m.gcdB p : ℤ)) : F) ≤ 1 :=
    (Valuation.vle_iff_le (ValuativeRel.valuation F)).mp
      (ratCast_vle_one_intCast (F := F) (m.gcdB p))
  have hkey : (1 : ValuativeRel.ValueGroupWithZero F)
      ≤ max (ValuativeRel.valuation F (m : F)) (ValuativeRel.valuation F (p : F)) := by
    calc (1 : ValuativeRel.ValueGroupWithZero F) = ValuativeRel.valuation F (1 : F) := by
            rw [Valuation.map_one]
      _ = ValuativeRel.valuation F ((m : F) * ((m.gcdA p : ℤ) : F)
            + (p : F) * ((m.gcdB p : ℤ) : F)) := by rw [hbezF]
      _ ≤ max (ValuativeRel.valuation F ((m : F) * ((m.gcdA p : ℤ) : F)))
            (ValuativeRel.valuation F ((p : F) * ((m.gcdB p : ℤ) : F))) :=
          Valuation.map_add _ _ _
      _ = max (ValuativeRel.valuation F (m : F) *
              ValuativeRel.valuation F (((m.gcdA p : ℤ)) : F))
            (ValuativeRel.valuation F (p : F) *
              ValuativeRel.valuation F (((m.gcdB p : ℤ)) : F)) := by
          rw [Valuation.map_mul, Valuation.map_mul]
      _ ≤ max (ValuativeRel.valuation F (m : F)) (ValuativeRel.valuation F (p : F)) :=
          max_le_max (mul_le_of_le_one_right' hgA) (mul_le_of_le_one_right' hgB)
  have hone : (1 : ValuativeRel.ValueGroupWithZero F) ≤ ValuativeRel.valuation F (m : F) := by
    by_contra h
    rw [not_le] at h
    exact absurd hkey (not_le.mpr (max_lt h hγ))
  exact (Valuation.veq_iff_eq (v := ValuativeRel.valuation F)).mpr (le_antisymm hmle hone)

/-- The image of an integer has the same value as the image of its absolute value. -/
lemma ratCast_veq_natAbs (a : ℤ) : ((a : F) =ᵥ (a.natAbs : F)) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg a
  · rw [hm]; push_cast; rw [Int.natAbs_natCast]
  · rw [hm]; push_cast; rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact ratCast_neg_veq (x := (m : F))

/-- **An integer coprime to `p` has value `1`** (integer form of
`ratCast_veq_one_natCast_of_not_dvd`). -/
lemma ratCast_veq_one_intCast_of_not_dvd {p : ℕ} (hp : p.Prime) (hlt : (p : F) <ᵥ 1) {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) : ((a : F) =ᵥ (1 : F)) := by
  have hna : ¬ p ∣ a.natAbs := fun h => ha (Int.ofNat_dvd_left.mpr h)
  exact veq_trans (ratCast_veq_natAbs a)
    (ratCast_veq_one_natCast_of_not_dvd (F := F) hp hlt hna)

/-- **The value of a natural number is the `p`-adic valuation of that number**: writing
`n = p ^ padicValNat p n * m` with `p ∤ m`, the factor `m` has value `1`. -/
lemma ratCast_veq_pow_padicValNat {p : ℕ} (hp : p.Prime) (hlt : (p : F) <ᵥ 1) {n : ℕ}
    (hn : n ≠ 0) : ((n : F) =ᵥ (p : F) ^ padicValNat p n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := p) (n := n)
  have hnotdvd : ¬ p ∣ m := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    refine pow_succ_padicValNat_not_dvd (p := p) hn ?_
    refine ⟨c, ?_⟩
    conv_lhs => rw [hm]
    rw [hc, pow_succ]
    ring
  have h1 : ((n : F)) = ((p ^ padicValNat p n * m : ℕ) : F) := by
    conv_lhs => rw [hm]
  rw [h1]
  push_cast
  have key := mul_veq_mul (veq_refl ((p : F) ^ padicValNat p n))
    (ratCast_veq_one_natCast_of_not_dvd (F := F) hp hlt hnotdvd)
  simpa using key

/-- **The value of an integer is the `p`-adic valuation of that integer** (integer form of
`ratCast_veq_pow_padicValNat`). -/
lemma ratCast_veq_pow_padicValInt {p : ℕ} (hp : p.Prime) (hlt : (p : F) <ᵥ 1) {a : ℤ}
    (ha : a ≠ 0) : ((a : F) =ᵥ (p : F) ^ padicValInt p a) := by
  have hna : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  exact veq_trans (ratCast_veq_natAbs a)
    (ratCast_veq_pow_padicValNat (F := F) hp hlt hna)

end Aux

theorem ratCast_veq_pow_padicValRat (F : Type*) [Field F] [CharZero F] [ValuativeRel F] {p : ℕ} (hp : Nat.Prime p) (hlt : (p : F) <ᵥ 1) {q : ℚ} (hq0 : q ≠ 0) (hq : 0 ≤ padicValRat p q) : ((q : F) =ᵥ (p : F) ^ (padicValRat p q).toNat) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hnum : ValuativeRel.valuation F (q.num : F)
      = ValuativeRel.valuation F (p : F) ^ padicValNat p q.num.natAbs := by
    have h := (Valuation.veq_iff_eq (v := ValuativeRel.valuation F)).mp
      (ratCast_veq_pow_padicValInt (F := F) hp hlt hnum0)
    rw [Valuation.map_pow] at h
    simpa [padicValInt] using h
  have hden : ValuativeRel.valuation F (q.den : F)
      = ValuativeRel.valuation F (p : F) ^ padicValNat p q.den := by
    have h := (Valuation.veq_iff_eq (v := ValuativeRel.valuation F)).mp
      (ratCast_veq_pow_padicValNat (F := F) hp hlt (Rat.den_ne_zero q))
    rwa [Valuation.map_pow] at h
  have hA : padicValRat p q
      = (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) := by
    simp [padicValRat_def, padicValInt]
  have hBA : padicValNat p q.den ≤ padicValNat p q.num.natAbs := by
    have h2 : ((padicValNat p q.den : ℤ)) ≤ (padicValNat p q.num.natAbs : ℤ) := by
      have := hq; rw [hA] at this; linarith
    exact_mod_cast h2
  have hk : (padicValRat p q).toNat
      = padicValNat p q.num.natAbs - padicValNat p q.den := by
    have h3 : ((padicValNat p q.den : ℤ)) ≤ (padicValNat p q.num.natAbs : ℤ) := by
      exact_mod_cast hBA
    apply Nat.cast_injective (R := ℤ)
    rw [hA, Int.toNat_sub_of_le h3, Nat.cast_sub hBA]
  have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hγpos : 0 < ValuativeRel.valuation F (p : F) :=
    (Valuation.vlt_iff_lt (ValuativeRel.valuation F)).mp
      (ValuativeRel.zero_vlt_iff.mpr hpF)
  have hγ0 : ValuativeRel.valuation F (p : F) ≠ 0 := ne_of_gt hγpos
  rw [Valuation.veq_iff_eq (v := ValuativeRel.valuation F), Rat.cast_def, Valuation.map_div,
    hnum, hden, div_eq_mul_inv, ← pow_sub₀ (ValuativeRel.valuation F (p : F)) hγ0 hBA,
    ← hk, Valuation.map_pow]

end NK.LocalReciprocityLubinTate.Unramified
