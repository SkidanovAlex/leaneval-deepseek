import Mathlib
import Submission.Work.FIArea2.TsumDefs2
import Submission.Work.FIArea2.Tsum_odd_defs
import Submission.Work.FIArea2.congAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Elementary modular arithmetic -/

/-- `(a*b).val ≡ a.val * b.val (mod n)`: the difference is divisible by `n`. -/
lemma dvd_val_sub_mul {n : ℕ} [NeZero n] (a b : ZMod n) :
    (n : ℤ) ∣ ((a * b).val : ℤ) - (a.val : ℤ) * (b.val : ℤ) := by
  rw [ZMod.val_mul]
  have h := Nat.mod_add_div (a.val * b.val) n
  have hcast : ((a.val * b.val % n : ℕ) : ℤ)
      + (n : ℤ) * ((a.val * b.val / n : ℕ) : ℤ) = ((a.val * b.val : ℕ) : ℤ) := by
    exact_mod_cast h
  refine ⟨-((a.val * b.val / n : ℕ) : ℤ), ?_⟩
  push_cast at hcast ⊢
  linarith [hcast]

/-- `((p:ℤ)^ν) ∣ (p:ℤ)^2 * K ↔ ((p:ℤ)^(ν-2)) ∣ K` for `p ≠ 0`, `ν ≥ 2`. -/
lemma pow_dvd_sq_mul_iff {p ν : ℕ} (hp : p ≠ 0) (hν : 2 ≤ ν) (K : ℤ) :
    ((p : ℤ) ^ ν) ∣ (p : ℤ) ^ 2 * K ↔ ((p : ℤ) ^ (ν - 2)) ∣ K := by
  have hpow : (p : ℤ) ^ ν = (p : ℤ) ^ 2 * (p : ℤ) ^ (ν - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  exact mul_dvd_mul_iff_left (pow_ne_zero 2 (by exact_mod_cast hp))

/-- If `p ∣ x.val` and `y² = a x²` in `ZMod (p^ν)` with `a` a unit and `ν ≥ 2`, then `p ∣ y.val`. -/
lemma dvd_y_of_dvd_x {p ν : ℕ} (hp : p.Prime) (hν : 2 ≤ ν) (a : ℤ)
    (ha : IsUnit (a : ZMod (p ^ ν))) {x y : ZMod (p ^ ν)}
    (h : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2) (hx : p ∣ x.val) : p ∣ y.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ ν) := inferInstance
  have hdvd : ((p ^ ν : ℕ) : ℤ) ∣ (y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2 :=
    (zmod_cond_iff (p ^ ν) a x y).mpr h
  have hp2 : ((p : ℤ) ^ 2) ∣ ((p ^ ν : ℕ) : ℤ) := by
    rw [Nat.cast_pow]; exact pow_dvd_pow (p : ℤ) hν
  have h2 : (p : ℤ) ^ 2 ∣ (y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2 := dvd_trans hp2 hdvd
  have hx2 : (p : ℤ) ^ 2 ∣ (x.val : ℤ) ^ 2 := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨(k : ℤ) ^ 2, ?_⟩
    rw [hk]; push_cast; ring
  have hax2 : (p : ℤ) ^ 2 ∣ a * (x.val : ℤ) ^ 2 := dvd_mul_of_dvd_right hx2 a
  have hy2 : (p : ℤ) ^ 2 ∣ (y.val : ℤ) ^ 2 := by
    have := dvd_add h2 hax2
    simpa using this
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpy : (p : ℤ) ∣ (y.val : ℤ) := by
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ 2 := by
      simpa using pow_dvd_pow (p : ℤ) (by norm_num : 1 ≤ 2)
    exact hpprime.dvd_of_dvd_pow (dvd_trans h1 hy2)
  exact_mod_cast hpy

/-- The sum over the units of `ZMod n` of the additive character equals the Ramanujan sum. -/
lemma ram_eq_sum_units (n : ℕ) [NeZero n] (hn : 2 ≤ n) (m : ℤ) :
    (∑ x : ZMod n, (if IsUnit x then
        E (((m * (x.val : ℤ) : ℤ) : ℝ) / (n : ℝ)) else 0)) = ram n m := by
  rw [← Finset.sum_filter]
  unfold ram
  refine Finset.sum_bij' (fun x _ => x.val) (fun η _ => (η : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hxne : x.val ≠ 0 := by
      intro h0
      have hx0 : x = 0 := (ZMod.val_eq_zero x).mp h0
      obtain ⟨u, hu⟩ := hx
      have h1 : (1 : ZMod n) = 0 := by
        have hu0 : (↑u : ZMod n) = 0 := by rw [hu, hx0]
        rw [← Units.mul_inv u, hu0, zero_mul]
      have hdvd : (n : ℤ) ∣ 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) n).mp (by simpa using h1)
      have hdvdn : n ∣ 1 := by exact_mod_cast hdvd
      have hn1 : n = 1 := Nat.dvd_one.mp hdvdn
      omega
    refine ⟨⟨by omega, le_of_lt (ZMod.val_lt x)⟩, ?_⟩
    rw [← ZMod.isUnit_iff_coprime x.val n, ZMod.natCast_zmod_val]
    exact hx
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_filter, Finset.mem_Icc] at hη
    exact (ZMod.isUnit_iff_coprime η n).mpr hη.2
  · intro x hx
    exact ZMod.natCast_zmod_val x
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_Icc] at hη
    have hηn : η < n := by
      rcases lt_or_eq_of_le hη.1.2 with h | h
      · exact h
      · exfalso
        rw [h] at hη
        have := (Nat.coprime_self n).mp hη.2
        omega
    rw [ZMod.val_natCast_of_lt hηn]
  · intro x hx
    rfl

/-- For a unit `x`, the inner sum over the solutions `y² = a x²` reindexes over the square
roots `ρ` of `a` via `y = ρ x`. -/
lemma unit_inner (N : ℕ) [NeZero N] (a h1 h2 : ℤ) (x : ZMod N) (hx : IsUnit x) :
    (∑ y : ZMod N, (if y ^ 2 = (a : ZMod N) * x ^ 2 then
        E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / (N : ℝ)) else 0))
      = ∑ ρ : ZMod N, (if ρ ^ 2 = (a : ZMod N) then
        E ((((x.val : ℤ) * (h1 + (ρ.val : ℤ) * h2) : ℤ) : ℝ) / (N : ℝ)) else 0) := by
  obtain ⟨u, hu⟩ := hx
  have hxu : x * ↑u⁻¹ = 1 := by rw [← hu, Units.mul_inv]
  have hy_eq : ∀ y : ZMod N, y = x * (y * ↑u⁻¹) := by
    intro y
    rw [← hu, ← mul_assoc, mul_comm (↑u) y, mul_assoc, Units.mul_inv, mul_one]
  refine Finset.sum_bij' (fun y _ => y * ↑u⁻¹) (fun ρ _ => ρ * x) ?_ ?_ ?_ ?_ ?_
  · intro y _; exact Finset.mem_univ _
  · intro ρ _; exact Finset.mem_univ _
  · intro y _
    show (y * ↑u⁻¹) * x = y
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  · intro ρ _
    show (ρ * x) * ↑u⁻¹ = ρ
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  · intro y _
    by_cases hy : y ^ 2 = (a : ZMod N) * x ^ 2
    · have hpow : (y * ↑u⁻¹) ^ 2 = (a : ZMod N) := by
        rw [mul_pow, hy]
        rw [show (a : ZMod N) * x ^ 2 * ↑u⁻¹ ^ 2 = (a : ZMod N) * (x * ↑u⁻¹) ^ 2 by
              rw [mul_pow]; ring]
        rw [hxu, one_pow, mul_one]
      rw [if_pos hy, if_pos hpow]
      apply E_period
      have hd : (N : ℤ) ∣ ((x * (y * ↑u⁻¹)).val : ℤ)
          - (x.val : ℤ) * ((y * ↑u⁻¹).val : ℤ) := dvd_val_sub_mul x (y * ↑u⁻¹)
      rw [← hy_eq y] at hd
      have heq : ((x.val : ℤ) * h1 + (y.val : ℤ) * h2)
            - ((x.val : ℤ) * (h1 + ((y * ↑u⁻¹).val : ℤ) * h2))
          = h2 * ((y.val : ℤ) - (x.val : ℤ) * ((y * ↑u⁻¹).val : ℤ)) := by ring
      rw [heq]
      exact dvd_mul_of_dvd_right hd h2
    · have hρ : (y * ↑u⁻¹) ^ 2 ≠ (a : ZMod N) := by
        intro hc
        apply hy
        rw [hy_eq y, mul_pow, hc, mul_comm (x ^ 2) a]
      rw [if_neg hy, if_neg hρ]

/-- The congruence defining the non-unit stratum transports to the smaller modulus. -/
lemma iota_sq_cond {p ν : ℕ} (hp : p.Prime) (hν : 2 ≤ ν) (a : ℤ)
    (x' y' : ZMod (p ^ (ν - 1))) :
    (iota p ν 1 y') ^ 2 = (a : ZMod (p ^ ν)) * (iota p ν 1 x') ^ 2
      ↔ ((p ^ (ν - 2) : ℕ) : ℤ) ∣ (y'.val : ℤ) ^ 2 - a * (x'.val : ℤ) ^ 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ ν) := inferInstance
  haveI : NeZero (p ^ (ν - 1)) := inferInstance
  have h1ν : 1 ≤ ν := by omega
  rw [← zmod_cond_iff (p ^ ν) a (iota p ν 1 x') (iota p ν 1 y')]
  have key : ((iota p ν 1 y').val : ℤ) ^ 2 - a * ((iota p ν 1 x').val : ℤ) ^ 2
      = (p : ℤ) ^ 2 * ((y'.val : ℤ) ^ 2 - a * (x'.val : ℤ) ^ 2) := by
    rw [iota_val hp h1ν, iota_val hp h1ν]
    push_cast
    ring
  rw [key, Nat.cast_pow, Nat.cast_pow]
  exact pow_dvd_sq_mul_iff hp.ne_zero hν _

/-- The additive character argument is unchanged by the reindexing `iota`. -/
lemma iota_E_arg {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) (h1 h2 : ℤ)
    (x' y' : ZMod (p ^ (ν - 1))) :
    E (((((iota p ν 1 x').val : ℤ) * h1 + ((iota p ν 1 y').val : ℤ) * h2 : ℤ) : ℝ)
        / ((p ^ ν : ℕ) : ℝ))
      = E ((((x'.val : ℤ) * h1 + (y'.val : ℤ) * h2 : ℤ) : ℝ)
        / ((p ^ (ν - 1) : ℕ) : ℝ)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ ν) := inferInstance
  haveI : NeZero (p ^ (ν - 1)) := inferInstance
  rw [iota_val hp hν, iota_val hp hν]
  congr 1
  have hN : ((p ^ ν : ℕ) : ℝ) = (p : ℝ) * ((p ^ (ν - 1) : ℕ) : ℝ) := by
    have hpν : p ^ ν = p * p ^ (ν - 1) := by
      conv_lhs => rw [show ν = (ν - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpν, Nat.cast_mul]
  rw [hN]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hM0 : (p : ℝ) ^ (ν - 1) ≠ 0 := pow_ne_zero _ hp0
  rw [div_eq_div_iff (mul_ne_zero hp0 hM0) hM0]
  ring

/-- `sum_dvd_val` in the special case `i = 1`, with `p^1` simplified to `p`. -/
lemma sum_dvd_val_one {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    [NeZero (p ^ (ν - 1))] (f : ZMod (p ^ ν) → ℂ) :
    (∑ u : ZMod (p ^ ν), if p ∣ u.val then f u else 0)
      = ∑ z : ZMod (p ^ (ν - 1)), f (iota p ν 1 z) := by
  simpa using sum_dvd_val (p := p) (ν := ν) (i := 1) hp hν f

theorem TsumD_recursion (p ν : ℕ) (hp : p.Prime) [NeZero p] (hν : 2 ≤ ν) (a h1 h2 : ℤ)
    (ha : IsUnit (a : ZMod (p ^ ν))) :
    TsumD p ν ν a h1 h2 = Tup p ν a h1 h2 + TsumD p (ν - 1) (ν - 2) a h1 h2 := by
  haveI : NeZero (p ^ ν) := inferInstance
  haveI : NeZero (p ^ (ν - 1)) := inferInstance
  have hν1 : 1 ≤ ν := by omega
  have hp2ν : 2 ≤ p ^ ν := le_trans hp.two_le (Nat.le_self_pow (by omega : ν ≠ 0) p)
  rw [TsumD_self]
  set g : ZMod (p ^ ν) → ℂ := fun x => ∑ y : ZMod (p ^ ν),
      (if y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 then
        E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / ((p ^ ν : ℕ) : ℝ)) else 0)
      with hg
  set F : ZMod (p ^ ν) → ZMod (p ^ ν) → ℂ := fun x ρ =>
      E ((((x.val : ℤ) * (h1 + (ρ.val : ℤ) * h2) : ℤ) : ℝ) / ((p ^ ν : ℕ) : ℝ)) with hF
  have hT : Tsum (p ^ ν) a h1 h2 = ∑ x, g x := by
    unfold Tsum; simp only [hg]
  have hsplit : (∑ x, g x)
      = (∑ x : ZMod (p ^ ν), (if p ∣ x.val then 0 else g x))
        + (∑ x : ZMod (p ^ ν), (if p ∣ x.val then g x else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases h : p ∣ x.val <;> simp [h]
  have hU : (∑ x : ZMod (p ^ ν), (if p ∣ x.val then 0 else g x)) = Tup p ν a h1 h2 := by
    have step1 : (∑ x : ZMod (p ^ ν), (if p ∣ x.val then 0 else g x))
        = ∑ x : ZMod (p ^ ν), (if IsUnit x then
            ∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then F x ρ else 0)
            else 0) := by
      apply Finset.sum_congr rfl; intro x _
      by_cases hpx : p ∣ x.val
      · have hnu : ¬ IsUnit x := fun hiu =>
          ((isUnit_iff_not_dvd_val hp (by omega : 0 < ν) x).mp hiu) hpx
        rw [if_pos hpx, if_neg hnu]
      · have hu : IsUnit x := (isUnit_iff_not_dvd_val hp (by omega : 0 < ν) x).mpr hpx
        rw [if_neg hpx, if_pos hu]
        simp only [hg, hF]
        exact unit_inner (p ^ ν) a h1 h2 x hu
    have step2 : (∑ x : ZMod (p ^ ν), (if IsUnit x then
            ∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then F x ρ else 0)
            else 0))
        = ∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then
            ∑ x : ZMod (p ^ ν), (if IsUnit x then F x ρ else 0) else 0) := by
      have hA : (∑ x : ZMod (p ^ ν), (if IsUnit x then
            ∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then F x ρ else 0) else 0))
          = ∑ x : ZMod (p ^ ν), ∑ ρ : ZMod (p ^ ν),
              (if ρ ^ 2 = (a : ZMod (p ^ ν)) then
                (if IsUnit x then F x ρ else 0) else 0) := by
        apply Finset.sum_congr rfl; intro x _
        by_cases hx : IsUnit x
        · rw [if_pos hx]
          apply Finset.sum_congr rfl; intro ρ _
          by_cases hρ : ρ ^ 2 = (a : ZMod (p ^ ν)) <;> simp [hρ, hx]
        · rw [if_neg hx]; simp [hx]
      rw [hA, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro ρ _
      by_cases hρ : ρ ^ 2 = (a : ZMod (p ^ ν)) <;> simp [hρ]
    have step3 : (∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then
            ∑ x : ZMod (p ^ ν), (if IsUnit x then F x ρ else 0) else 0))
        = Tup p ν a h1 h2 := by
      have hTup : Tup p ν a h1 h2
          = ∑ ρ : ZMod (p ^ ν), (if ρ ^ 2 = (a : ZMod (p ^ ν)) then
              ram (p ^ ν) (h1 + (ρ.val : ℤ) * h2) else 0) := by
        rw [Tup, Finset.sum_filter]
      rw [hTup]
      apply Finset.sum_congr rfl; intro ρ _
      by_cases hρ : ρ ^ 2 = (a : ZMod (p ^ ν))
      · rw [if_pos hρ, if_pos hρ]
        rw [← ram_eq_sum_units (p ^ ν) hp2ν (h1 + (ρ.val : ℤ) * h2)]
        apply Finset.sum_congr rfl; intro x _
        by_cases hx : IsUnit x
        · rw [if_pos hx, if_pos hx]
          simp only [hF]
          congr 1; push_cast; ring
        · rw [if_neg hx, if_neg hx]
      · rw [if_neg hρ, if_neg hρ]
    rw [step1, step2, step3]
  have hV : (∑ x : ZMod (p ^ ν), (if p ∣ x.val then g x else 0))
      = TsumD p (ν - 1) (ν - 2) a h1 h2 := by
    have step1 : (∑ x : ZMod (p ^ ν), (if p ∣ x.val then g x else 0))
        = ∑ x : ZMod (p ^ ν), (if p ∣ x.val then
            ∑ y : ZMod (p ^ ν), (if p ∣ y.val then
              (if y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 then
                E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                  / ((p ^ ν : ℕ) : ℝ)) else 0) else 0)
            else 0) := by
      apply Finset.sum_congr rfl; intro x _
      by_cases hpx : p ∣ x.val
      · rw [if_pos hpx, if_pos hpx]
        simp only [hg]
        apply Finset.sum_congr rfl; intro y _
        by_cases hy : p ∣ y.val
        · rw [if_pos hy]
        · rw [if_neg hy]
          by_cases hcond : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2
          · exact absurd (dvd_y_of_dvd_x hp hν a ha hcond hpx) hy
          · rw [if_neg hcond]
      · rw [if_neg hpx, if_neg hpx]
    have step2 : (∑ x : ZMod (p ^ ν), (if p ∣ x.val then
            ∑ y : ZMod (p ^ ν), (if p ∣ y.val then
              (if y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 then
                E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                  / ((p ^ ν : ℕ) : ℝ)) else 0) else 0)
            else 0))
        = ∑ x' : ZMod (p ^ (ν - 1)), (∑ y : ZMod (p ^ ν), (if p ∣ y.val then
              (if y ^ 2 = (a : ZMod (p ^ ν)) * (iota p ν 1 x') ^ 2 then
                E (((((iota p ν 1 x').val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                  / ((p ^ ν : ℕ) : ℝ)) else 0) else 0)) := by
      rw [sum_dvd_val_one hp hν1]
    have step3 : (∑ x' : ZMod (p ^ (ν - 1)), (∑ y : ZMod (p ^ ν), (if p ∣ y.val then
              (if y ^ 2 = (a : ZMod (p ^ ν)) * (iota p ν 1 x') ^ 2 then
                E (((((iota p ν 1 x').val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                  / ((p ^ ν : ℕ) : ℝ)) else 0) else 0)))
        = ∑ x' : ZMod (p ^ (ν - 1)), ∑ y' : ZMod (p ^ (ν - 1)),
            (if (iota p ν 1 y') ^ 2 = (a : ZMod (p ^ ν)) * (iota p ν 1 x') ^ 2 then
              E (((((iota p ν 1 x').val : ℤ) * h1 + ((iota p ν 1 y').val : ℤ) * h2 : ℤ) : ℝ)
                / ((p ^ ν : ℕ) : ℝ)) else 0) := by
      apply Finset.sum_congr rfl; intro x' _
      rw [sum_dvd_val_one hp hν1]
    have step4 : (∑ x' : ZMod (p ^ (ν - 1)), ∑ y' : ZMod (p ^ (ν - 1)),
            (if (iota p ν 1 y') ^ 2 = (a : ZMod (p ^ ν)) * (iota p ν 1 x') ^ 2 then
              E (((((iota p ν 1 x').val : ℤ) * h1 + ((iota p ν 1 y').val : ℤ) * h2 : ℤ) : ℝ)
                / ((p ^ ν : ℕ) : ℝ)) else 0))
        = TsumD p (ν - 1) (ν - 2) a h1 h2 := by
      rw [TsumD]
      apply Finset.sum_congr rfl; intro x' _
      apply Finset.sum_congr rfl; intro y' _
      by_cases hc : ((p ^ (ν - 2) : ℕ) : ℤ) ∣ (y'.val : ℤ) ^ 2 - a * (x'.val : ℤ) ^ 2
      · rw [if_pos ((iota_sq_cond hp hν a x' y').mpr hc), if_pos hc]
        exact iota_E_arg hp hν1 h1 h2 x' y'
      · rw [if_neg (fun h1' => hc ((iota_sq_cond hp hν a x' y').mp h1')), if_neg hc]
    rw [step1, step2, step3, step4]
  rw [hT, hsplit, hU, hV]

end

end Work.FIArea2
