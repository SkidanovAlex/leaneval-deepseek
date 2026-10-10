import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.QuadraticLocalGlobal.GrunwaldPrelim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

noncomputable section

open scoped Classical

/-! ## Auxiliary lemmas about `unitPart`, coercions and congruence arithmetic -/

/-- The `p`-adic unit part of an inverse is the inverse of the unit part. -/
theorem unitPart_inv (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    unitPart p a⁻¹ = (unitPart p a)⁻¹ := by
  have h : unitPart p a * unitPart p a⁻¹ = 1 := by
    have h2 := unitPart_mul p a a⁻¹
    rw [mul_inv_cancel, unitPart_one] at h2
    exact h2.symm
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- The `p`-adic unit part of a quotient. -/
theorem unitPart_div (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    unitPart p (a / b) = unitPart p a * (unitPart p b)⁻¹ := by
  rw [div_eq_mul_inv, unitPart_mul, unitPart_inv]

/-- The coercion `ℚˣ → ℚ_[p]` respects division. -/
theorem ratUnits_coe_div {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    ((a / b : ℚˣ) : ℚ_[p]) = (a : ℚ_[p]) / (b : ℚ_[p]) := by
  have h1 : ((a / b : ℚˣ) : ℚ) = (a : ℚ) / (b : ℚ) := Units.val_div_eq_div_val a b
  rw [show ((a / b : ℚˣ) : ℚ_[p]) = (((a / b : ℚˣ) : ℚ) : ℚ_[p]) from rfl, h1,
    show (a : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) from rfl,
    show (b : ℚ_[p]) = ((b : ℚ) : ℚ_[p]) from rfl, Rat.cast_div]

/-- The coercion of `intUnit m` to `ℚ_[p]` is the integer `m`. -/
theorem intUnit_coe_padic (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ((intUnit m hm : ℚˣ) : ℚ_[p]) = (m : ℚ_[p]) := by
  rw [intUnit_coe]
  push_cast
  ring

/-- A prime does not divide `k * a * b` when `k` is a unit of `ℤ` and `a`, `b` are natural
numbers not divisible by the prime. -/
theorem prime_not_dvd_units_mul_nat {p : ℕ} (hp : p.Prime) {k : ℤˣ} {a b : ℕ}
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ (p : ℤ) ∣ (k : ℤ) * (a : ℤ) * (b : ℤ) := by
  intro hd
  have h1 : p ∣ ((k : ℤ) * (a : ℤ) * (b : ℤ)).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  have h2 : ((k : ℤ) * (a : ℤ) * (b : ℤ)).natAbs = a * b := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have hk : (k : ℤ).natAbs = 1 := by
      rcases Int.units_eq_one_or k with h | h <;> simp [h]
    rw [hk, one_mul]
  rw [h2] at h1
  rcases hp.dvd_mul.mp h1 with h | h
  · exact ha h
  · exact hb h

/-- The same statement with an integral last factor. -/
theorem prime_not_dvd_units_mul_int {p : ℕ} (hp : p.Prime) {k : ℤˣ} {a : ℕ} {b : ℤ}
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b.natAbs) : ¬ (p : ℤ) ∣ (k : ℤ) * (a : ℤ) * b := by
  intro hd
  have h1 : p ∣ ((k : ℤ) * (a : ℤ) * b).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  have h2 : ((k : ℤ) * (a : ℤ) * b).natAbs = a * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have hk : (k : ℤ).natAbs = 1 := by
      rcases Int.units_eq_one_or k with h | h <;> simp [h]
    rw [hk, one_mul]
  rw [h2] at h1
  rcases hp.dvd_mul.mp h1 with h | h
  · exact ha h
  · exact hb h

/-- Congruent integers are divisible by the same numbers. -/
theorem not_dvd_of_modEq_of_not_dvd {p : ℕ} {m r : ℤ} (h : m ≡ r [ZMOD (p : ℤ)])
    (hr : ¬ (p : ℤ) ∣ r) : ¬ (p : ℤ) ∣ m := by
  intro hm
  exact hr (by
    have hd : (p : ℤ) ∣ r - m := Int.modEq_iff_dvd.mp h
    have := dvd_add hd hm
    rwa [sub_add_cancel] at this)

/-- The square of an odd integer is `1` modulo `8`. -/
theorem sq_modEq_one_eight {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) : m * m ≡ 1 [ZMOD 8] := by
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩
  · rw [hk] at hm
    exact absurd ⟨k, by ring⟩ hm
  · have hkey : (2 : ℤ) ∣ k * (k + 1) := by
      rcases Int.even_or_odd' k with ⟨j, hj | hj⟩
      · exact ⟨j * (2 * j + 1), by rw [hj]; ring⟩
      · exact ⟨(2 * j + 1) * (j + 1), by rw [hj]; ring⟩
    obtain ⟨t, ht⟩ := hkey
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [hk, show (1 : ℤ) - (2 * k + 1) * (2 * k + 1) = -4 * (k * (k + 1)) by ring, ht]
    ring

/-! ## The two local square criteria in the form needed here -/

/-- A quotient `a / b` of odd integers with `a ≡ b (mod 8)` is a square in `ℚ_[2]`. -/
theorem isSquare_padic_two_intUnit_div_of_modEq {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha2 : ¬ (2 : ℤ) ∣ a) (hb2 : ¬ (2 : ℤ) ∣ b) (h : a ≡ b [ZMOD 8]) :
    IsSquare (((intUnit a ha) / (intUnit b hb) : ℚˣ) : ℚ_[2]) := by
  rw [isSquare_padic_two_rat_iff']
  constructor
  · rw [padicVal_div, padicVal_intUnit ha ha2, padicVal_intUnit hb hb2]
    norm_num
  · let f : ℤ_[2] →* ZMod (2 ^ 3) := (PadicInt.toZModPow (p := 2) 3)
    have hup : unitPart 2 ((intUnit a ha) / (intUnit b hb)) =
        unitPart 2 (intUnit a ha) * (unitPart 2 (intUnit b hb))⁻¹ :=
      unitPart_div 2 _ _
    have hae : (Units.map f (unitPart 2 (intUnit a ha)) : ZMod (2 ^ 3)) = (a : ZMod 8) := by
      rw [Units.coe_map]
      exact toZModPow_three_unitPart_two_intUnit ha ha2
    have hbe : (Units.map f (unitPart 2 (intUnit b hb)) : ZMod (2 ^ 3)) = (b : ZMod 8) := by
      rw [Units.coe_map]
      exact toZModPow_three_unitPart_two_intUnit hb hb2
    have hunit : Units.map f (unitPart 2 (intUnit a ha)) =
        Units.map f (unitPart 2 (intUnit b hb)) := by
      apply Units.ext
      rw [hae, hbe]
      exact (ZMod.intCast_eq_intCast_iff a b 8).mpr h
    have key : ((Units.map f (unitPart 2 ((intUnit a ha) / (intUnit b hb))) :
        (ZMod (2 ^ 3))ˣ) : ZMod (2 ^ 3)) = 1 := by
      rw [hup, map_mul, map_inv, hunit, mul_inv_cancel]
      rfl
    rwa [Units.coe_map] at key

/-- The `2`-adic criterion transported to a prime `p` known to be `2`. -/
theorem isSquare_padic_two_intUnit_div_of_modEq' {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha2 : ¬ (2 : ℤ) ∣ a) (hb2 : ¬ (2 : ℤ) ∣ b) (h : a ≡ b [ZMOD 8]) :
    IsSquare (((intUnit a ha) / (intUnit b hb) : ℚˣ) : ℚ_[p]) := by
  subst hp
  exact isSquare_padic_two_intUnit_div_of_modEq ha hb ha2 hb2 h

/-- For an odd prime `p`, a quotient `A / B` of integers coprime to `p` with
`B ≡ A * s ^ 2 (mod p)` is a square in `ℚ_[p]`. -/
theorem isSquare_padic_odd_intUnit_div_of_modEq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {A B s : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hAp : ¬ (p : ℤ) ∣ A) (hBp : ¬ (p : ℤ) ∣ B)
    (hs : (s : ZMod p) ≠ 0) (h : B ≡ A * s ^ 2 [ZMOD p]) :
    IsSquare (((intUnit A hA) / (intUnit B hB) : ℚˣ) : ℚ_[p]) := by
  rw [isSquare_padic_rat_iff hp]
  constructor
  · rw [padicVal_div, padicVal_intUnit hA hAp, padicVal_intUnit hB hBp]
    norm_num
  · rw [legendreOf_div, legendreOf_intUnit hA hAp, legendreOf_intUnit hB hBp]
    have hsym : legendreSym p B = legendreSym p A := by
      have hcast : (B : ZMod p) = ((A * s ^ 2 : ℤ) : ZMod p) :=
        (ZMod.intCast_eq_intCast_iff B (A * s ^ 2) p).mpr h
      have hs2 : legendreSym p (s ^ 2) = legendreSym p s ^ 2 := by
        rw [sq, legendreSym.mul, sq]
      calc legendreSym p B = legendreSym p (A * s ^ 2) := by
              rw [legendreSym, legendreSym, hcast]
        _ = legendreSym p A * legendreSym p (s ^ 2) := legendreSym.mul p A (s ^ 2)
        _ = legendreSym p A * legendreSym p s ^ 2 := by rw [hs2]
        _ = legendreSym p A := by rw [legendreSym.sq_one p hs, mul_one]
    rw [hsym, intUnitOf_mul_self_grunwald]

/-! ## The main construction -/

/-- Grünwald construction in degree two, local-data form: given finitely many distinct primes
`q i`, parities `e i ≤ 1`, positive integers `n i` coprime to `q i`, and a sign `σ : ℤˣ`, there is
a rational unit `d` whose sign times `σ` is positive and which has, at each `q i`, the same square
class as `(q i) ^ (e i) * n i`.

Construction: put `m i := if q i = 2 then 8 else q i`, `R i := ∏ j ∈ univ.erase i, (q j) ^ (e j)`
and `Q := ∏ i, (q i) ^ (e i)`.  The moduli `m i` are pairwise coprime, so
`Work.QuadraticLocalGlobal.exists_pos_int_modEq_finset` (in `GrunwaldPrelim`) applied to the
residues `r i := (σ : ℤ) * (R i : ℤ) * (n i : ℤ)` gives `g : ℤ` with `0 < g` and
`g ≡ r i [ZMOD m i]` for all `i`.  Set `d := intUnit (σ : ℤ) * Q * intUnit g` (all in `ℚˣ`).

Verification at `i`: `(q i) ^ (e i) * n i / d = σ * (R i)⁻¹ * n i * g⁻¹`, a rational unit with
`v_{q i} = 0`.  For odd `q i`, `legendreOf (q i)` of that unit is `1` because
`legendreOf (q i) (intUnit g) = legendreOf (q i) (intUnit (σ * R i * n i))` (residues agree mod
`q i`, use `legendreOf_intUnit_eq_of_modEq`).  For `q i = 2`, reduce the unit part mod `8` with
`toZModPow_three_unitPart_two_intUnit` and use
`Work.QuadraticLocalGlobal.isSquare_padic_two_rat_iff'`.  In both cases conclude with
`Work.QuadraticLocalGlobal.isSquare_padic_rat_iff` / `isSquare_padic_two_rat_iff'` and
`sameSquare_iff_isSquare_div`. -/
theorem exists_rat_unit_sameSquare_of_local_data {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime] (hq : Function.Injective q)
    (e : ι → ℕ) (he : ∀ i, e i ≤ 1) (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (hnc : ∀ i, (n i).Coprime (q i)) (σ : ℤˣ) :
    ∃ d : ℚˣ, (0 < (d : ℚ) * ((σ : ℤ) : ℚ)) ∧
      ∀ i, Work.QuadraticLocalGlobal.SameSquare ((d : ℚ_[q i]))
        (((q i : ℚ_[q i]) ^ (e i)) * (n i : ℚ_[q i])) := by
  classical
  -- ### The auxiliary data
  set R : ι → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, (q j) ^ (e j) with hRdef
  set Q : ℕ := ∏ i, (q i) ^ (e i) with hQdef
  set mm : ι → ℕ := fun i => if q i = 2 then 8 else q i with hmmdef
  set rr : ι → ℤ := fun i => (σ : ℤ) * (R i : ℤ) * (n i : ℤ) with hrrdef
  have hQne : Q ≠ 0 := by
    rw [hQdef]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (Fact.out : (q i).Prime).ne_zero)
  have hRQ : ∀ i, (R i : ℚ) * (q i : ℚ) ^ (e i) = (Q : ℚ) := by
    intro i
    have h := Finset.prod_erase_mul Finset.univ (fun j => (q j) ^ (e j)) (Finset.mem_univ i)
    have h' : R i * q i ^ e i = Q := by
      have : R i * q i ^ e i = (∏ x ∈ Finset.univ, q x ^ e x) := by
        rw [hRdef]
        exact h
      rw [this, hQdef]
    exact_mod_cast h'
  have hmm1 : ∀ i, 1 < mm i := by
    intro i
    by_cases h : q i = 2
    · rw [hmmdef]; simp [h]
    · rw [hmmdef]; simp only [h, if_false]
      exact (Fact.out : (q i).Prime).one_lt
  have hmmcop : ∀ i j, i ≠ j → (mm i).Coprime (mm j) := by
    intro i j hij
    have hqij : q i ≠ q j := fun h => hij (hq h)
    simp only [hmmdef]
    by_cases hi : q i = 2 <;> by_cases hj : q j = 2
    · exact absurd (hi.trans hj.symm) hqij
    · rw [if_pos hi, if_neg hj]
      refine (Nat.coprime_pow_left_iff (n := 3) (by norm_num) 2 (q j)).mpr
        ((Nat.prime_two.coprime_iff_not_dvd).mpr ?_)
      intro h2
      exact hj ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : (q j).Prime)).mp h2).symm
    · rw [if_neg hi, if_pos hj]
      refine (Nat.coprime_pow_right_iff (n := 3) (by norm_num) (q i) 2).mpr
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : (q i).Prime)).mpr ?_)
      intro h2
      exact hi ((Nat.prime_dvd_prime_iff_eq (Fact.out : (q i).Prime) Nat.prime_two).mp h2)
    · rw [if_neg hi, if_neg hj]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : (q i).Prime)).mpr
        (fun hdvd => hqij
          ((Nat.prime_dvd_prime_iff_eq (Fact.out : (q i).Prime) (Fact.out : (q j).Prime)).mp hdvd))
  -- ### The Chinese remainder theorem
  obtain ⟨g, hgpos, hgmod⟩ := exists_pos_int_modEq_finset mm hmm1 hmmcop rr
  have hgne : g ≠ 0 := by omega
  -- ### The candidate
  set D : ℤ := (σ : ℤ) * (Q : ℤ) * g with hDdef
  have hDne : D ≠ 0 := by
    rw [hDdef]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hgne
    · simpa using Units.ne_zero σ
    · exact_mod_cast hQne
  refine ⟨intUnit D hDne, ?_, ?_⟩
  · -- ### Positivity of `d * σ`
    have hdval : ((intUnit D hDne : ℚˣ) : ℚ) = ((σ : ℤ) : ℚ) * (Q : ℚ) * (g : ℚ) := by
      rw [intUnit_coe, hDdef]
      push_cast
      ring
    rw [hdval]
    have hσsq : ((σ : ℤ) : ℚ) * ((σ : ℤ) : ℚ) = 1 := by
      rcases Int.units_eq_one_or σ with h | h <;> (rw [h]; norm_num)
    calc ((σ : ℤ) : ℚ) * (Q : ℚ) * (g : ℚ) * ((σ : ℤ) : ℚ)
        = (((σ : ℤ) : ℚ) * ((σ : ℤ) : ℚ)) * (Q : ℚ) * (g : ℚ) := by ring
      _ = (Q : ℚ) * (g : ℚ) := by rw [hσsq, one_mul]
      _ > 0 := by
          have hQpos : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hQne
          have hgposQ : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hgpos
          positivity
  · -- ### The local verification
    intro i
    have hqp : (q i).Prime := Fact.out
    have hni0 : (n i : ℤ) ≠ 0 := by exact_mod_cast hn i
    have hRne : R i ≠ 0 := by
      rw [hRdef]
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (Fact.out : (q j).Prime).ne_zero)
    have hRcop : (q i).Coprime (R i) := by
      rw [hRdef]
      refine Nat.Coprime.prod_right (fun j hj => ?_)
      refine Nat.Coprime.pow_right _ ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      exact (Nat.Prime.coprime_iff_not_dvd hqp).mpr
        (fun hdvd =>
          hji (hq ((Nat.prime_dvd_prime_iff_eq hqp (Fact.out : (q j).Prime)).mp hdvd)).symm)
    have hRnotdvd : ¬ q i ∣ R i := fun h => hqp.ne_one (Nat.Coprime.eq_one_of_dvd hRcop h)
    have hRnotdvd_int : ¬ (q i : ℤ) ∣ (R i : ℤ) := fun h => hRnotdvd (by exact_mod_cast h)
    have hnnotdvd : ¬ q i ∣ n i :=
      fun h => hqp.ne_one (Nat.Coprime.eq_one_of_dvd (hnc i).symm h)
    have hnnotdvd_int : ¬ (q i : ℤ) ∣ (n i : ℤ) := fun h => hnnotdvd (by exact_mod_cast h)
    have hnotRR : ¬ (q i : ℤ) ∣ (σ : ℤ) * (R i : ℤ) * (n i : ℤ) :=
      prime_not_dvd_units_mul_nat hqp hRnotdvd hnnotdvd
    have hmmdvd : (q i : ℤ) ∣ (mm i : ℤ) := by
      by_cases h2 : q i = 2
      · rw [hmmdef]; simp only [h2, if_pos]; norm_num
      · rw [hmmdef]; simp only [h2, if_false]
        exact dvd_rfl
    have hcong_q : g ≡ rr i [ZMOD (q i : ℤ)] := Int.ModEq.of_dvd hmmdvd (hgmod i)
    have hgndvd_int : ¬ (q i : ℤ) ∣ g :=
      not_dvd_of_modEq_of_not_dvd hcong_q (by rw [hrrdef]; exact hnotRR)
    have hgndvd : ¬ q i ∣ g.natAbs := by
      intro h
      apply hgndvd_int
      have h' : ((q i : ℤ)).natAbs ∣ g.natAbs := by simpa using h
      exact Int.natAbs_dvd_natAbs.mp h'
    -- the two rational units
    set Ai : ℤ := (q i : ℤ) ^ (e i) * (n i : ℤ) with hAi
    have hAi0 : Ai ≠ 0 := by
      rw [hAi]
      exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hqp.ne_zero)) hni0
    set T : ℤ := (σ : ℤ) * (R i : ℤ) * g with hT
    have hT0 : T ≠ 0 := by
      rw [hT]
      exact mul_ne_zero (mul_ne_zero (by simpa using Units.ne_zero σ)
        (by exact_mod_cast hRne)) hgne
    set u : ℚˣ := intUnit (n i : ℤ) hni0 / intUnit T hT0 with hu
    have hunits : (intUnit Ai hAi0 / intUnit D hDne : ℚˣ) = u := by
      rw [hu]
      apply Units.ext
      simp only [Units.val_div_eq_div_val, intUnit_coe]
      rw [hAi, hT, hDdef]
      push_cast
      rw [← hRQ i]
      have hq0 : (q i : ℚ) ^ (e i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hqp.ne_zero)
      have hσ0 : ((σ : ℤ) : ℚ) ≠ 0 := by
        rcases Int.units_eq_one_or σ with h | h <;> simp [h]
      have hR0 : (R i : ℚ) ≠ 0 := by exact_mod_cast hRne
      have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hgne
      field_simp
    have hci_eq : ((intUnit Ai hAi0 : ℚˣ) : ℚ_[q i]) =
        (q i : ℚ_[q i]) ^ (e i) * (n i : ℚ_[q i]) := by
      rw [intUnit_coe_padic, hAi]
      push_cast
      ring
    have hdneq : ((intUnit D hDne : ℚˣ) : ℚ_[q i]) ≠ 0 := ratCast_ne_zero _
    refine (show SameSquare ((intUnit D hDne : ℚˣ) : ℚ_[q i])
      ((q i : ℚ_[q i]) ^ (e i) * (n i : ℚ_[q i])) from ?_)
    rw [← hci_eq, sameSquare_iff_isSquare_div hdneq]
    have hq_eq : ((intUnit Ai hAi0 : ℚˣ) : ℚ_[q i]) / ((intUnit D hDne : ℚˣ) : ℚ_[q i])
        = ((u : ℚˣ) : ℚ_[q i]) := by
      rw [← ratUnits_coe_div (p := q i) (a := intUnit Ai hAi0) (b := intUnit D hDne), hunits]
    rw [hq_eq]
    by_cases h2 : q i = 2
    · -- the `2`-adic prime
      have hn2 : ¬ (2 : ℕ) ∣ n i := by
        intro h
        have hcop : (2 : ℕ).Coprime (n i) := by rw [← h2]; exact (hnc i).symm
        exact (by norm_num : (2 : ℕ) ≠ 1) (Nat.Coprime.eq_one_of_dvd hcop h)
      have hAodd : ¬ (2 : ℤ) ∣ (n i : ℤ) := fun h => hn2 (by exact_mod_cast h)
      have hRodd_nat : ¬ (2 : ℕ) ∣ R i := fun h => hRnotdvd (by rw [h2]; exact h)
      have hBodd : ¬ (2 : ℤ) ∣ T := by
        rw [hT]
        exact prime_not_dvd_units_mul_int Nat.prime_two hRodd_nat
          (by rw [← h2]; exact hgndvd)
      have hcong2 : (n i : ℤ) ≡ T [ZMOD 8] := by
        have hmm8 : mm i = 8 := by rw [hmmdef]; simp [h2]
        have hg8 : g ≡ rr i [ZMOD (8 : ℤ)] := by
          have h := hgmod i
          rwa [show (mm i : ℤ) = (8 : ℤ) by exact_mod_cast hmm8] at h
        have hmul8 : (σ : ℤ) * (R i : ℤ) * g ≡ (σ : ℤ) * (R i : ℤ) * rr i [ZMOD 8] :=
          (Int.ModEq.refl ((σ : ℤ) * (R i : ℤ))).mul hg8
        rw [hrrdef] at hmul8
        have hstep : (σ : ℤ) * (R i : ℤ) * ((σ : ℤ) * (R i : ℤ) * (n i : ℤ))
            ≡ (n i : ℤ) [ZMOD 8] := by
          have hσsq : (σ : ℤ) * (σ : ℤ) = 1 := by
            rcases Int.units_eq_one_or σ with h | h <;> simp [h]
          have hR2 : (R i : ℤ) * (R i : ℤ) ≡ 1 [ZMOD 8] :=
            sq_modEq_one_eight (fun h => hRodd_nat (by exact_mod_cast h))
          have heq : (σ : ℤ) * (R i : ℤ) * ((σ : ℤ) * (R i : ℤ) * (n i : ℤ))
              = ((σ : ℤ) * (σ : ℤ)) * ((R i : ℤ) * (R i : ℤ)) * (n i : ℤ) := by ring
          rw [heq, hσsq, one_mul]
          simpa using hR2.mul (Int.ModEq.refl (n i : ℤ))
        have hT8 : T ≡ (n i : ℤ) [ZMOD 8] := by
          have h := hmul8.trans hstep
          rwa [← hT] at h
        exact hT8.symm
      rw [hu]
      exact isSquare_padic_two_intUnit_div_of_modEq' h2 hni0 hT0 hAodd hBodd hcong2
    · -- an odd prime
      have hsed : ((R i : ℤ) : ZMod (q i)) ≠ 0 := by
        intro h
        exact hRnotdvd_int ((ZMod.intCast_zmod_eq_zero_iff_dvd (R i) (q i)).mp h)
      have hBp : ¬ (q i : ℤ) ∣ T := by
        rw [hT]
        exact prime_not_dvd_units_mul_int hqp hRnotdvd hgndvd
      have hcongodd : T ≡ (n i : ℤ) * (R i : ℤ) ^ 2 [ZMOD (q i : ℤ)] := by
        have hmul : (σ : ℤ) * (R i : ℤ) * g ≡ (σ : ℤ) * (R i : ℤ) * rr i [ZMOD (q i : ℤ)] :=
          (Int.ModEq.refl ((σ : ℤ) * (R i : ℤ))).mul hcong_q
        rw [hrrdef] at hmul
        have hstep : (σ : ℤ) * (R i : ℤ) * ((σ : ℤ) * (R i : ℤ) * (n i : ℤ))
            ≡ (n i : ℤ) * (R i : ℤ) ^ 2 [ZMOD (q i : ℤ)] := by
          have hσsq : (σ : ℤ) * (σ : ℤ) = 1 := by
            rcases Int.units_eq_one_or σ with h | h <;> simp [h]
          have heq : (σ : ℤ) * (R i : ℤ) * ((σ : ℤ) * (R i : ℤ) * (n i : ℤ))
              = ((σ : ℤ) * (σ : ℤ)) * ((n i : ℤ) * (R i : ℤ) ^ 2) := by ring
          rw [heq, hσsq, one_mul]
        have h := hmul.trans hstep
        rwa [← hT] at h
      rw [hu]
      exact isSquare_padic_odd_intUnit_div_of_modEq h2 hni0 hT0 hnnotdvd_int hBp hsed hcongodd

end

end Work.QuadraticLocalGlobal
