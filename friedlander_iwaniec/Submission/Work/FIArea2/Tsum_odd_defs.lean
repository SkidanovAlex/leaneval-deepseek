/-
Shared definitions and basic lemmas for the odd-prime case of the local estimate of
*FI* Lemma 8.1 (`Work.FIArea2.Tsum_prime_pow_odd`).

* `Phi N z = E (z.val / N)` is the standard additive character of `ZMod N`, where
  `E x = exp (2 * π * I * x)` (`Work.FIArea2.E`).
* `iota p ν i : ZMod (p^(ν-i)) → ZMod (p^ν)` identifies `ZMod (p^(ν-i))` with the multiples of
  `p^i` in `ZMod (p^ν)`; for `i ≤ ν` its image is exactly `A_i = {u : p^i ∣ u.val}`.
* `cval p ν x` is the `p`-adic valuation of `x : ℕ` capped at `ν` (with `cval p ν 0 = ν`), and
  `ordv p ν z = cval p ν z.val` the same for `z : ZMod (p^ν)`; `p^j ∣ z.val ↔ j ≤ ordv p ν z`
  for `j ≤ ν`, `ordv` is additive (capped at `ν`), and `Nat.gcd (p^ν) x = p ^ cval p ν x`.
-/
import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.ramanujan_primepow
import Submission.Work.FIArea2.sqRoots_card
import Submission.Work.FIArea2.congAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The additive character `Φ` of `ZMod N` -/

/-- The standard additive character of `ZMod N`: `Φ N z = E (z.val / N)`. -/
def Phi (N : ℕ) (z : ZMod N) : ℂ := E ((z.val : ℝ) / (N : ℝ))

@[simp] lemma Phi_zero (N : ℕ) : Phi N 0 = 1 := by
  simp [Phi, E]

lemma Phi_norm (N : ℕ) (z : ZMod N) : ‖Phi N z‖ = 1 := by
  rw [Phi, E_norm]

/-- `E` is trivial at integer multiples of the modulus. -/
lemma E_intCast_div {N : ℕ} [NeZero N] (m : ℤ) (h : (N : ℤ) ∣ m) :
    E ((m : ℝ) / (N : ℝ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [show (((N : ℤ) * k : ℤ) : ℝ) / (N : ℝ) = (k : ℝ) by
        push_cast
        field_simp]
  exact E_int k

/-- `E (· / N)` depends only on the residue modulo `N`. -/
lemma E_period {N : ℕ} [NeZero N] (m m' : ℤ) (h : (N : ℤ) ∣ m - m') :
    E ((m : ℝ) / (N : ℝ)) = E ((m' : ℝ) / (N : ℝ)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsub : (m : ℝ) / (N : ℝ) = (m' : ℝ) / (N : ℝ) + ((m - m' : ℤ) : ℝ) / (N : ℝ) := by
    field_simp
    push_cast
    ring
  rw [hsub, E_add, E_intCast_div (N := N) (m - m') h, mul_one]

lemma E_nat_mod {N : ℕ} [NeZero N] (x : ℕ) :
    E ((x : ℝ) / (N : ℝ)) = E (((x % N : ℕ) : ℝ) / (N : ℝ)) := by
  refine E_period (N := N) (x : ℤ) ((x % N : ℕ) : ℤ) ⟨((x / N : ℕ) : ℤ), ?_⟩
  have hc : ((x % N : ℕ) : ℤ) + (N : ℤ) * ((x / N : ℕ) : ℤ) = (x : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  linarith [hc]

lemma Phi_add {N : ℕ} [NeZero N] (a b : ZMod N) :
    Phi N (a + b) = Phi N a * Phi N b := by
  have h1 : Phi N (a + b) = E (((a.val + b.val : ℕ) : ℝ) / (N : ℝ)) := by
    rw [Phi, ZMod.val_add, ← E_nat_mod]
  rw [h1, Phi, Phi,
    show (((a.val + b.val : ℕ) : ℝ) / (N : ℝ))
        = (a.val : ℝ) / (N : ℝ) + (b.val : ℝ) / (N : ℝ) by
      push_cast; ring,
    E_add]

lemma Phi_sub {N : ℕ} [NeZero N] (a b : ZMod N) :
    Phi N (a - b) = Phi N a * (Phi N b)⁻¹ := by
  have h : Phi N a = Phi N (a - b) * Phi N b := by
    rw [← Phi_add (a - b) b, sub_add_cancel]
  have hb : Phi N b ≠ 0 := by
    intro h0
    have := Phi_norm N b
    rw [h0, norm_zero] at this
    exact one_ne_zero this.symm
  rw [h, mul_assoc, mul_inv_cancel₀ hb, mul_one]

lemma Phi_intCast {N : ℕ} [NeZero N] (m : ℤ) :
    Phi N (m : ZMod N) = E ((m : ℝ) / (N : ℝ)) := by
  rw [Phi]
  refine E_period (N := N) (((m : ZMod N).val : ℕ) : ℤ) m ?_
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub m (((m : ZMod N).val : ℕ) : ℤ) N).mp (by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val])

lemma Phi_mul_intCast {N : ℕ} [NeZero N] (m : ℤ) (z : ZMod N) :
    Phi N (z * (m : ZMod N)) = E (((m * (z.val : ℤ) : ℤ) : ℝ) / (N : ℝ)) := by
  have hz : z * (m : ZMod N) = (((z.val : ℤ) * m : ℤ) : ZMod N) := by
    calc z * (m : ZMod N) = ((z.val : ℕ) : ZMod N) * (m : ZMod N) := by rw [ZMod.natCast_zmod_val]
      _ = ((z.val : ℤ) : ZMod N) * (m : ZMod N) := by rw [Int.cast_natCast]
      _ = (((z.val : ℤ) * m : ℤ) : ZMod N) := by rw [Int.cast_mul]
  have hE : Phi N (z * (m : ZMod N)) = E ((((z.val : ℤ) * m : ℤ) : ℝ) / (N : ℝ)) := by
    rw [Phi]
    refine E_period (N := N) (((z * (m : ZMod N)).val : ℕ) : ℤ) ((z.val : ℤ) * m) ?_
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub ((z.val : ℤ) * m)
      (((z * (m : ZMod N)).val : ℕ) : ℤ) N).mp (by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val, hz])
  rw [hE]
  congr 1
  push_cast
  ring

lemma Phi_eq_one_iff {N : ℕ} [NeZero N] (z : ZMod N) : Phi N z = 1 ↔ z = 0 := by
  rw [Phi, E_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hlt : (z.val : ℝ) < (N : ℝ) := by exact_mod_cast ZMod.val_lt z
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      have : (0 : ℝ) ≤ (z.val : ℝ) / (N : ℝ) := by positivity
      rwa [hn] at this
    have hn1 : (n : ℝ) < 1 := by
      have : (z.val : ℝ) / (N : ℝ) < 1 := by
        rw [div_lt_one hNpos]
        exact hlt
      rwa [hn] at this
    have hn' : n = 0 := by
      have h1 : (0 : ℤ) ≤ n := by exact_mod_cast hn0
      have h2 : n < (1 : ℤ) := by exact_mod_cast hn1
      omega
    have hz : (z.val : ℝ) = 0 := by
      have h2 : (z.val : ℝ) / (N : ℝ) = 0 := by rw [hn, hn']; simp
      rcases div_eq_zero_iff.mp h2 with h | h
      · exact h
      · exact absurd h (ne_of_gt hNpos)
    exact (ZMod.val_eq_zero z).mp (by exact_mod_cast hz)
  · intro hz
    rw [hz]
    refine ⟨0, by simp⟩

/-- **`Tsum` as a character sum over the solution set.**  The summand `E ((x.val h₁ + y.val h₂)/n)` of
`Tsum` is `Φ n (x h₁ + y h₂)`, since the two integer numerators agree modulo `n`. -/
theorem Tsum_eq_sum_Phi {n : ℕ} [NeZero n] (a h1 h2 : ℤ) :
    Tsum n a h1 h2
      = ∑ x : ZMod n, ∑ y : ZMod n,
          (if y ^ 2 = (a : ZMod n) * x ^ 2
            then Phi n (x * (h1 : ZMod n) + y * (h2 : ZMod n)) else 0) := by
  unfold Tsum
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases h : y ^ 2 = (a : ZMod n) * x ^ 2
  · rw [if_pos h, if_pos h, Phi]
    have hkey : (((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ZMod n)
        = (((x * (h1 : ZMod n) + y * (h2 : ZMod n)).val : ℕ) : ZMod n) := by
      rw [ZMod.natCast_zmod_val]
      push_cast
      rw [ZMod.natCast_zmod_val x, ZMod.natCast_zmod_val y]
    refine E_period (N := n) ((x.val : ℤ) * h1 + (y.val : ℤ) * h2)
      (((x * (h1 : ZMod n) + y * (h2 : ZMod n)).val : ℕ) : ℤ) ?_
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      (((x * (h1 : ZMod n) + y * (h2 : ZMod n)).val : ℕ) : ℤ)
      ((x.val : ℤ) * h1 + (y.val : ℤ) * h2) n).mp (by
        rw [Int.cast_natCast]
        exact hkey.symm)
  · rw [if_neg h, if_neg h]

/-! ### Sums of `Φ` over `ZMod N` -/

/-- The sum of `E (m j / N)` over `j < N` is the classical geometric sum `T N m`. -/
lemma sum_range_E_eq_T (N : ℕ) [NeZero N] (m : ℤ) :
    (∑ j ∈ Finset.range N, E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ))) = T N m := by
  set z : ℂ := E ((m : ℝ) / (N : ℝ)) with hz
  have hterm : ∀ j : ℕ, E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ)) = z ^ j := by
    intro j
    rw [hz, E_mul_div]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hzN : z ^ N = 1 := by
    rw [hz, E_pow, show (N : ℝ) * ((m : ℝ) / (N : ℝ)) = (m : ℝ) by
      have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp]
    exact E_int m
  have hdiv : (N : ℤ) ∣ m ↔ z = 1 := by
    rw [hz, E_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : (m : ℝ) = (k : ℝ) * (N : ℝ) := by
        have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
        rw [div_eq_iff hN] at hk
        exact hk
      have h3 : m = k * (N : ℤ) := by exact_mod_cast h2
      rw [h3]; ring
  by_cases h : (N : ℤ) ∣ m
  · rw [T_eq N (Nat.pos_of_ne_zero (NeZero.ne N)) m, if_pos h, hdiv.mp h]
    simp
  · rw [T_eq N (Nat.pos_of_ne_zero (NeZero.ne N)) m, if_neg h]
    have hz1 : z ≠ 1 := fun hh => h (hdiv.mpr hh)
    rw [geom_sum_eq hz1, hzN]
    simp

lemma sum_ZMod_E {N : ℕ} [NeZero N] (m : ℤ) :
    (∑ z : ZMod N, E (((m * (z.val : ℤ) : ℤ) : ℝ) / (N : ℝ))) = T N m := by
  rw [← sum_range_E_eq_T N m]
  refine Finset.sum_bij (fun (z : ZMod N) (_ : z ∈ Finset.univ) => z.val) ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_range.mpr (ZMod.val_lt z)
  · intro z1 _ z2 _ h; exact ZMod.val_injective N h
  · intro j hj
    exact ⟨(j : ZMod N), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)⟩
  · intro z _; rfl

lemma sum_ZMod_E_nat {N : ℕ} [NeZero N] (m : ℕ) :
    (∑ z : ZMod N, E (((m * z.val : ℕ) : ℝ) / (N : ℝ))) = T N (m : ℤ) := by
  rw [← sum_ZMod_E (N := N) (m := (m : ℤ))]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1

lemma sum_Phi_mul_intCast {N : ℕ} [NeZero N] (m : ℤ) :
    (∑ z : ZMod N, Phi N (z * (m : ZMod N))) = T N m := by
  rw [← sum_ZMod_E (N := N) m]
  exact Finset.sum_congr rfl (fun z _ => Phi_mul_intCast m z)

/-! ### The inclusion `iota` of `ZMod (p^(ν-i))` into `ZMod (p^ν)` -/

/-- `iota p ν i z = p^i * z` in `ZMod (p^ν)`; for `i ≤ ν` this is an injection onto the
multiples of `p^i`. -/
def iota (p ν i : ℕ) (z : ZMod (p ^ (ν - i))) : ZMod (p ^ ν) :=
  ((p ^ i * z.val : ℕ) : ZMod (p ^ ν))

lemma iota_eq_mul (p ν i : ℕ) (z : ZMod (p ^ (ν - i))) :
    iota p ν i z = (p : ZMod (p ^ ν)) ^ i * ((z.val : ℕ) : ZMod (p ^ ν)) := by
  rw [iota, Nat.cast_mul, Nat.cast_pow]

lemma iota_val {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) [NeZero (p ^ (ν - i))]
    (z : ZMod (p ^ (ν - i))) : (iota p ν i z).val = p ^ i * z.val := by
  rw [iota, ZMod.val_natCast, Nat.mod_eq_of_lt]
  calc p ^ i * z.val < p ^ i * p ^ (ν - i) :=
        Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) (pow_pos hp.pos i)
    _ = p ^ ν := by rw [← pow_add, Nat.add_sub_cancel' hi]

lemma iota_zero (p ν i : ℕ) : iota p ν i 0 = 0 := by
  rw [iota]
  simp

lemma iota_injective {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) [NeZero (p ^ (ν - i))] :
    Function.Injective (iota p ν i) := by
  intro z z' h
  have h2 := congrArg ZMod.val h
  rw [iota_val hp hi z, iota_val hp hi z'] at h2
  exact ZMod.val_injective _ (Nat.mul_left_cancel (pow_pos hp.pos i) h2)

lemma exists_iota_iff {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) (u : ZMod (p ^ ν)) :
    (∃ z : ZMod (p ^ (ν - i)), iota p ν i z = u) ↔ p ^ i ∣ u.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (ν - i)) := inferInstance
  constructor
  · rintro ⟨z, rfl⟩
    rw [iota_val hp hi]
    exact dvd_mul_right _ _
  · intro h
    haveI : NeZero (p ^ ν) := inferInstance
    have hlt : u.val / p ^ i < p ^ (ν - i) := by
      have h1 : u.val < p ^ ν := ZMod.val_lt u
      have h2 : u.val = p ^ i * (u.val / p ^ i) := (Nat.mul_div_cancel' h).symm
      rw [h2] at h1
      conv_rhs at h1 => rw [← Nat.add_sub_cancel' hi, pow_add]
      exact Nat.lt_of_mul_lt_mul_left h1
    refine ⟨((u.val / p ^ i : ℕ) : ZMod (p ^ (ν - i))), ?_⟩
    rw [iota, ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel' h, ZMod.natCast_zmod_val]

/-- The sum over the multiples of `p^i` in `ZMod (p^ν)`, reindexed by `iota`. -/
lemma sum_dvd_val {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) [NeZero (p ^ ν)]
    [NeZero (p ^ (ν - i))] (f : ZMod (p ^ ν) → ℂ) :
    (∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then f u else 0)
      = ∑ z : ZMod (p ^ (ν - i)), f (iota p ν i z) := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_bij (fun z (_ : z ∈ (Finset.univ : Finset (ZMod (p ^ (ν - i))))) =>
      iota p ν i z) (fun z _ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [iota_val hp hi]
        exact dvd_mul_right _ _)
      (fun z1 _ z2 _ h => iota_injective hp hi h)
      (fun u hu => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨z, hz⟩ := (exists_iota_iff hp hi u).mpr hu
        exact ⟨z, Finset.mem_univ _, hz⟩)
      (fun z _ => rfl)).symm

/-- The `i`-th layer sum of `Φ (u * c)`: dropping the level gives the full geometric sum. -/
lemma sum_A_Phi {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) [NeZero (p ^ ν)]
    [NeZero (p ^ (ν - i))] (c : ZMod (p ^ ν)) :
    (∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then Phi (p ^ ν) (u * c) else 0)
      = T (p ^ (ν - i)) (c.val : ℤ) := by
  rw [sum_dvd_val hp hi]
  rw [← sum_ZMod_E_nat (N := p ^ (ν - i)) (m := c.val)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Phi, ZMod.val_mul, iota_val hp hi, ← E_nat_mod]
  congr 1
  push_cast
  rw [div_eq_div_iff (by exact_mod_cast (pow_ne_zero ν hp.ne_zero))
        (by exact_mod_cast (pow_ne_zero (ν - i) hp.ne_zero)),
    ← show (p : ℝ) ^ i * (p : ℝ) ^ (ν - i) = (p : ℝ) ^ ν by
      rw [← pow_add, Nat.add_sub_cancel' hi]]
  ring

/-- The `i`-th layer sum of `Φ (u * m)` for an integer `m`. -/
lemma sum_A_Phi_intCast {p ν i : ℕ} (hp : p.Prime) (hi : i ≤ ν) [NeZero (p ^ ν)]
    [NeZero (p ^ (ν - i))] (m : ℤ) :
    (∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then Phi (p ^ ν) (u * (m : ZMod (p ^ ν))) else 0)
      = T (p ^ (ν - i)) m := by
  rw [sum_dvd_val hp hi]
  rw [← sum_ZMod_E (N := p ^ (ν - i)) (m := m)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Phi_mul_intCast, iota_val hp hi]
  congr 1
  push_cast
  rw [div_eq_div_iff (by exact_mod_cast (pow_ne_zero ν hp.ne_zero))
        (by exact_mod_cast (pow_ne_zero (ν - i) hp.ne_zero)),
    ← show (p : ℝ) ^ i * (p : ℝ) ^ (ν - i) = (p : ℝ) ^ ν by
      rw [← pow_add, Nat.add_sub_cancel' hi]]
  ring

/-! ### The `p`-adic order of an element of `ZMod (p^ν)` -/

/-- The `p`-adic order of a natural number capped at `ν` (`cval p ν 0 = ν`). -/
def cval (p ν : ℕ) (x : ℕ) : ℕ := if x = 0 then ν else min ν (padicValNat p x)

/-- The `p`-adic order of `z : ZMod (p^ν)`, capped at `ν`. -/
def ordv (p ν : ℕ) (z : ZMod (p ^ ν)) : ℕ := cval p ν z.val

lemma ordv_val (p ν : ℕ) (z : ZMod (p ^ ν)) : ordv p ν z = cval p ν z.val := rfl

lemma cval_le (p ν x : ℕ) : cval p ν x ≤ ν := by
  unfold cval
  split
  · exact le_rfl
  · exact min_le_left _ _

lemma ordv_le {p ν : ℕ} (z : ZMod (p ^ ν)) : ordv p ν z ≤ ν := cval_le p ν z.val

lemma dvd_iff_le_cval {p ν j : ℕ} (hp : p.Prime) (hj : j ≤ ν) (x : ℕ) :
    p ^ j ∣ x ↔ j ≤ cval p ν x := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h : x = 0
  · subst h
    rw [cval]
    simp [hj]
  · rw [cval, if_neg h, padicValNat_dvd_iff j x]
    constructor
    · rintro (h0 | hle)
      · exact absurd h0 h
      · exact le_min hj hle
    · intro hle
      exact Or.inr (le_trans hle (min_le_right _ _))

lemma pow_cval_dvd {p ν : ℕ} (hp : p.Prime) (x : ℕ) : p ^ cval p ν x ∣ x :=
  (dvd_iff_le_cval hp (cval_le p ν x) x).mpr le_rfl

lemma dvd_mod_of_dvd {p ν j x : ℕ} (hj : j ≤ ν) (h : p ^ j ∣ x) : p ^ j ∣ x % p ^ ν := by
  obtain ⟨k, rfl⟩ := h
  rw [show p ^ ν = p ^ j * p ^ (ν - j) by rw [← pow_add, Nat.add_sub_cancel' hj],
    Nat.mul_mod_mul_left]
  exact dvd_mul_right _ _

lemma dvd_of_dvd_mod {p ν j x : ℕ} (hj : j ≤ ν) (h : p ^ j ∣ x % p ^ ν) : p ^ j ∣ x := by
  rw [← Nat.div_add_mod x (p ^ ν)]
  exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow p hj) _) h

lemma cval_mod {p ν : ℕ} (hp : p.Prime) (x : ℕ) : cval p ν (x % p ^ ν) = cval p ν x := by
  refine le_antisymm ?_ ?_
  · have h := pow_cval_dvd (ν := ν) hp (x % p ^ ν)
    exact (dvd_iff_le_cval hp (cval_le p ν (x % p ^ ν)) x).mp
      (dvd_of_dvd_mod (j := cval p ν (x % p ^ ν)) (cval_le p ν (x % p ^ ν)) h)
  · have h := pow_cval_dvd (ν := ν) hp x
    exact (dvd_iff_le_cval hp (cval_le p ν x) (x % p ^ ν)).mp
      (dvd_mod_of_dvd (j := cval p ν x) (cval_le p ν x) h)

lemma min_add_min (a b ν : ℕ) : min ν (min ν a + min ν b) = min ν (a + b) := by
  omega

lemma cval_mul {p ν : ℕ} (hp : p.Prime) (x y : ℕ) :
    cval p ν (x * y) = min ν (cval p ν x + cval p ν y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [cval]
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [mul_zero, cval, if_pos rfl]
    exact (min_eq_left (Nat.le_add_left ν (cval p ν x))).symm
  rw [cval, if_neg (mul_ne_zero hx hy), cval, if_neg hx, cval, if_neg hy,
    padicValNat.mul hx hy, min_add_min]

lemma dvd_iff_le_cval_mul {p ν j : ℕ} (hp : p.Prime) (hj : j ≤ ν) (x y : ℕ) :
    p ^ j ∣ x * y ↔ j ≤ cval p ν x + cval p ν y := by
  rw [dvd_iff_le_cval hp hj (x * y), cval_mul hp x y]
  exact ⟨fun h => le_trans h (min_le_right _ _), fun h => le_min hj h⟩

lemma dvd_val_iff_le_ordv {p ν j : ℕ} (hp : p.Prime) (hj : j ≤ ν) (z : ZMod (p ^ ν)) :
    p ^ j ∣ z.val ↔ j ≤ ordv p ν z := dvd_iff_le_cval hp hj z.val

/-- `ordv` is additive, capped at `ν`. -/
lemma ordv_mul {p ν : ℕ} (hp : p.Prime) (z w : ZMod (p ^ ν)) :
    ordv p ν (z * w) = min ν (ordv p ν z + ordv p ν w) := by
  apply le_antisymm
  · have h1 : p ^ ordv p ν (z * w) ∣ z.val * w.val := by
      refine dvd_of_dvd_mod (j := ordv p ν (z * w)) (ordv_le _) ?_
      rw [← ZMod.val_mul]
      exact pow_cval_dvd (ν := ν) hp _
    have h2 := (dvd_iff_le_cval_mul hp (ordv_le (p := p) (ν := ν) (z * w)) z.val w.val).mp h1
    exact le_min (ordv_le _) (by simpa [ordv] using h2)
  · have hmin : min ν (ordv p ν z + ordv p ν w) ≤ ν := min_le_left _ _
    have h1 : p ^ min ν (ordv p ν z + ordv p ν w) ∣ z.val * w.val :=
      (dvd_iff_le_cval_mul hp hmin z.val w.val).mpr (by simpa [ordv] using le_rfl)
    have h2 : p ^ min ν (ordv p ν z + ordv p ν w) ∣ (z * w).val := by
      rw [ZMod.val_mul]
      exact dvd_mod_of_dvd hmin h1
    exact (dvd_iff_le_cval hp hmin ((z * w).val)).mp h2

/-- An element of `ZMod (p^ν)` is a unit iff its `p`-adic order is `0`. -/
lemma ordv_eq_zero_iff {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) (z : ZMod (p ^ ν)) :
    ordv p ν z = 0 ↔ IsUnit z := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ ν) := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  rw [ordv, cval, isUnit_iff_not_dvd_val hp (by omega : 0 < ν) z]
  by_cases h : z.val = 0
  · rw [if_pos h, h]
    simp only [dvd_zero, not_true, iff_false]
    omega
  · rw [if_neg h]
    have hiff : padicValNat p z.val = 0 ↔ ¬ p ∣ z.val := by
      constructor
      · intro hv hd
        have h1 : 1 ≤ padicValNat p z.val :=
          ((padicValNat_dvd_iff 1 z.val).mp (by simpa using hd)).resolve_left h
        omega
      · exact padicValNat.eq_zero_of_not_dvd
    rw [← hiff]
    constructor
    · intro hmin
      by_contra hv
      have h1 : 1 ≤ padicValNat p z.val := Nat.one_le_iff_ne_zero.mpr hv
      have h2 : 1 ≤ min ν (padicValNat p z.val) := le_min (by omega) h1
      omega
    · intro hv
      rw [hv]
      exact min_eq_right (Nat.zero_le ν)

lemma ordv_mul_unit {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) {u : ZMod (p ^ ν)} (hu : IsUnit u)
    (z : ZMod (p ^ ν)) : ordv p ν (u * z) = ordv p ν z := by
  rw [ordv_mul hp u z, (ordv_eq_zero_iff hp hν u).mpr hu, zero_add, min_eq_right (ordv_le z)]

lemma ordv_natCast {p ν : ℕ} (hp : p.Prime) (m : ℕ) :
    ordv p ν ((m : ℕ) : ZMod (p ^ ν)) = cval p ν m := by
  rw [ordv, ZMod.val_natCast, cval_mod hp]

/-- `Nat.gcd (p^ν) x = p ^ cval p ν x`. -/
lemma gcd_pow_cval {p ν : ℕ} (hp : p.Prime) (x : ℕ) :
    Nat.gcd (p ^ ν) x = p ^ cval p ν x := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [cval]
  have hdvd : Nat.gcd (p ^ ν) x ∣ p ^ ν := Nat.gcd_dvd_left _ _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hle : k ≤ cval p ν x := by
    have h1 : p ^ k ∣ x := hk' ▸ Nat.gcd_dvd_right _ _
    exact (dvd_iff_le_cval hp hk x).mp h1
  have hle2 : cval p ν x ≤ k := by
    have h2 : p ^ cval p ν x ∣ Nat.gcd (p ^ ν) x :=
      Nat.dvd_gcd (pow_dvd_pow p (cval_le p ν x)) (pow_cval_dvd hp x)
    rw [hk'] at h2
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
  rw [hk', le_antisymm hle hle2]

end

end Work.FIArea2
