import Mathlib
import Submission.Work.FIArea2.Tsum_odd_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Auxiliary lemmas for the non-square case of the local estimate

We collect here the arithmetic input of `Work.FIArea2.Tsum_nonsquare_bound`: for an odd prime `p`,
`ν ≥ 1`, `a` a unit modulo `p^ν` which is not a square modulo `p`, every solution `(x,y)` of
`y² = a x²` in `ZMod (p^ν)` has both coordinates divisible by `p^{⌈ν/2⌉}` — and conversely.

The engine is `Work.FIArea2.min_ordv_sq_eq` (`v(y²) = v(a x²)` gives
`min ν (2 v(y)) = min ν (2 v(x))` because `a` is a unit) and `Work.FIArea2.key_nonsquare`: if
`2 v(x) < ν` then `p^j ∣ x.val` and `p^j ∣ y.val` with `j = v(x)` (so `x.val = p^j X`, `y.val = p^j Y`
with `p ∤ X`), the congruence `p^ν ∣ a x.val² - y.val²` divided by `p^{2j}` gives
`p^{ν-2j} ∣ a X² - Y²`, hence `a ≡ (Y X⁻¹)² (mod p)` — contradicting the hypothesis that `a` is not
a square modulo `p`. -/

/-- **`v(y²) = v(a x²)` for a unit `a`.**  If `y² = a x²` in `ZMod (p^ν)` with `a` a unit and
`p` a prime, then `min ν (2 · ordv y) = min ν (2 · ordv x)`. -/
lemma min_ordv_sq_eq {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a : ℤ) (ha : IsUnit (a : ZMod (p ^ ν)))
    {x y : ZMod (p ^ ν)} (h : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2) :
    min ν (2 * ordv p ν y) = min ν (2 * ordv p ν x) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  haveI := hpf
  have h0 : ordv p ν (a : ZMod (p ^ ν)) = 0 := (ordv_eq_zero_iff hp hν _).mpr ha
  have hsq : ∀ u : ZMod (p ^ ν), ordv p ν (u ^ 2) = min ν (2 * ordv p ν u) := by
    intro u
    rw [pow_two, ordv_mul hp u u]
    congr 1
    ring
  rw [← hsq y, ← hsq x, h, ordv_mul hp (a : ZMod (p ^ ν)) (x ^ 2), h0, zero_add,
    min_eq_right (ordv_le (x ^ 2))]

/-- **The key non-square step.**  Let `p` be a prime, `ν ≥ 1`, `a` a unit modulo `p^ν` which is not
a square modulo `p`.  Then no solution `(x,y)` of `y² = a x²` in `ZMod (p^ν)` has
`2 · ordv x < ν`.

Writing `j = ordv x`, the equation gives `ordv y = j`, so `x.val = p^j X`, `y.val = p^j Y` with
`p ∤ X`; the congruence divides by `p^{2j}` to `p^{ν-2j} ∣ a X² - Y²` and hence, modulo `p`,
`a ≡ (Y X⁻¹)²`, i.e. `a` *is* a square modulo `p` — contradiction. -/
lemma key_nonsquare {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) (hnsq : ¬ IsSquare ((a : ZMod p)))
    {x y : ZMod (p ^ ν)} (h : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2)
    (hlt : 2 * ordv p ν x < ν) : False := by
  have hpf : Fact p.Prime := ⟨hp⟩
  haveI := hpf
  have hval := min_ordv_sq_eq hp hν a ha h
  have hy_lt : 2 * ordv p ν y < ν := by
    by_contra hc
    push Not at hc
    have hmy : min ν (2 * ordv p ν y) = ν := min_eq_left hc
    have hmx : min ν (2 * ordv p ν x) = 2 * ordv p ν x := min_eq_right (le_of_lt hlt)
    omega
  have hord : ordv p ν y = ordv p ν x := by
    have hmy : min ν (2 * ordv p ν y) = 2 * ordv p ν y := min_eq_right (le_of_lt hy_lt)
    have hmx : min ν (2 * ordv p ν x) = 2 * ordv p ν x := min_eq_right (le_of_lt hlt)
    have h2 : 2 * ordv p ν y = 2 * ordv p ν x := by rw [← hmy, ← hmx]; exact hval
    omega
  have hjle : ordv p ν x ≤ ν := ordv_le x
  have hxdvd : p ^ ordv p ν x ∣ x.val := (dvd_val_iff_le_ordv hp hjle x).mpr le_rfl
  have hydvd : p ^ ordv p ν x ∣ y.val := by
    refine (dvd_val_iff_le_ordv hp hjle y).mpr ?_
    rw [hord]
  obtain ⟨X, hX⟩ := hxdvd
  obtain ⟨Y, hY⟩ := hydvd
  have hXnot : ¬ p ∣ X := by
    intro hpX
    obtain ⟨X', hX'⟩ := hpX
    have h1 : ordv p ν x + 1 ≤ ν := by omega
    have h2 : p ^ (ordv p ν x + 1) ∣ x.val := by
      rw [hX, hX', pow_succ]
      exact ⟨X', by ring⟩
    have h3 : ordv p ν x + 1 ≤ ordv p ν x := (dvd_val_iff_le_ordv hp h1 x).mp h2
    omega
  have hcasty : (((y.val : ℤ)) : ZMod (p ^ ν)) = y := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcastx : (((x.val : ℤ)) : ZMod (p ^ ν)) = x := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have e1 : ((((y.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν)) = (((y.val : ℤ)) : ZMod (p ^ ν)) ^ 2 := by
    rw [Int.cast_pow]
  have e2 : ((a * ((x.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν))
      = (a : ZMod (p ^ ν)) * ((((x.val : ℤ)) : ZMod (p ^ ν))) ^ 2 := by
    rw [Int.cast_mul, Int.cast_pow]
  have hh : ((((y.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν))
      = ((a * ((x.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν)) := by
    rw [e1, e2, hcasty, hcastx]
    exact h
  have hdiv : ((p ^ ν : ℕ) : ℤ) ∣ a * ((x.val : ℤ)) ^ 2 - ((y.val : ℤ)) ^ 2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (((y.val : ℤ))^2) (a * ((x.val : ℤ))^2) (p^ν)).mp hh
  rw [Nat.cast_pow] at hdiv
  have hfac : (a * ((x.val : ℤ)) ^ 2 - ((y.val : ℤ)) ^ 2)
      = ((p:ℤ)^(ordv p ν x) * (p:ℤ)^(ordv p ν x)) * (a * (X:ℤ)^2 - (Y:ℤ)^2) := by
    rw [hX, hY]
    push_cast
    ring
  have hpow : ((p:ℤ)^ν) = ((p:ℤ)^(ordv p ν x) * (p:ℤ)^(ordv p ν x)) * (p:ℤ)^(ν - 2 * ordv p ν x) := by
    conv_lhs => rw [show ν = ordv p ν x + ordv p ν x + (ν - 2 * ordv p ν x) by omega]
    rw [pow_add, pow_add]
  have hcancel : (p:ℤ)^(ν - 2 * ordv p ν x) ∣ (a * (X:ℤ)^2 - (Y:ℤ)^2) := by
    rw [hfac, hpow] at hdiv
    have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_dvd_mul_iff_left (mul_ne_zero (pow_ne_zero _ hpz) (pow_ne_zero _ hpz))).mp hdiv
  have hpdvd : (p:ℤ) ∣ (a * (X:ℤ)^2 - (Y:ℤ)^2) := by
    have h1 : (p:ℤ) ∣ (p:ℤ)^(ν - 2 * ordv p ν x) := by
      obtain ⟨k, hk⟩ : ∃ k, ν - 2 * ordv p ν x = k + 1 := ⟨ν - 2 * ordv p ν x - 1, by omega⟩
      rw [hk, pow_succ]
      exact dvd_mul_left _ _
    exact dvd_trans h1 hcancel
  have hzero : (((a * (X:ℤ)^2 - (Y:ℤ)^2 : ℤ)) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpdvd
  have hmain : (a : ZMod p) * ((X : ZMod p))^2 = ((Y : ZMod p))^2 := by
    have hz := hzero
    rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_pow, Int.cast_natCast, Int.cast_natCast] at hz
    exact sub_eq_zero.mp hz
  have hXunit : IsUnit ((X : ZMod p)) := by
    have hne : ((X : ZMod p)) ≠ 0 := by
      intro h0'
      have h0'' : ((X : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using h0'
      have h : X % p = 0 := by
        have := (ZMod.natCast_eq_natCast_iff' X 0 p).mp h0''
        simpa using this
      exact hXnot (Nat.dvd_of_mod_eq_zero h)
    exact isUnit_iff_ne_zero.mpr hne
  have hsqu : IsSquare ((a : ZMod p)) := by
    rw [isSquare_iff_exists_sq]
    refine ⟨(Y : ZMod p) * (X : ZMod p)⁻¹, ?_⟩
    have hmult : ((X : ZMod p)) * ((X : ZMod p))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hXunit
    calc (a : ZMod p)
        = (a : ZMod p) * (((X : ZMod p)) * ((X : ZMod p))⁻¹)^2 := by
          rw [hmult, one_pow, mul_one]
      _ = (a : ZMod p) * ((X : ZMod p))^2 * (((X : ZMod p))⁻¹)^2 := by ring
      _ = ((Y : ZMod p))^2 * (((X : ZMod p))⁻¹)^2 := by rw [hmain]
      _ = ((Y : ZMod p) * ((X : ZMod p))⁻¹)^2 := by rw [mul_pow]
  exact hnsq hsqu

/-- **Both coordinates of a solution are divisible by `p^{⌈ν/2⌉}`.**  For an odd prime `p`, `ν ≥ 1`
and `a` a unit modulo `p^ν` which is not a square modulo `p`, every solution of `y² = a x²` in
`ZMod (p^ν)` has `ν ≤ 2 · ordv` in both coordinates, i.e. `p^{⌈ν/2⌉}` divides both `x.val` and
`y.val`. -/
lemma ordv_ge_of_sq_eq {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) (hnsq : ¬ IsSquare ((a : ZMod p)))
    {x y : ZMod (p ^ ν)} (h : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2) :
    ν ≤ 2 * ordv p ν x ∧ ν ≤ 2 * ordv p ν y := by
  have hval := min_ordv_sq_eq hp hν a ha h
  constructor
  · by_contra hc
    push Not at hc
    exact key_nonsquare hp hν a ha hnsq h hc
  · by_contra hc
    push Not at hc
    have hmy : min ν (2 * ordv p ν y) = 2 * ordv p ν y := min_eq_right (le_of_lt hc)
    have hlt : 2 * ordv p ν x < ν := by
      by_contra h2
      push Not at h2
      have hmx : min ν (2 * ordv p ν x) = ν := min_eq_left h2
      omega
    exact key_nonsquare hp hν a ha hnsq h hlt

/-- Divisibility form of `Work.FIArea2.ordv_ge_of_sq_eq`. -/
lemma p_pow_ceil_dvd_of_sq_eq {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) (hnsq : ¬ IsSquare ((a : ZMod p)))
    {x y : ZMod (p ^ ν)} (h : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2) :
    p ^ ((ν+1)/2) ∣ x.val ∧ p ^ ((ν+1)/2) ∣ y.val := by
  obtain ⟨hx, hy⟩ := ordv_ge_of_sq_eq hp hν a ha hnsq h
  have hcν : (ν+1)/2 ≤ ν := by omega
  exact ⟨(dvd_val_iff_le_ordv hp hcν x).mpr (by omega),
    (dvd_val_iff_le_ordv hp hcν y).mpr (by omega)⟩

/-- **Converse**: if `p^c` divides both coordinates and `ν ≤ 2c`, the congruence `y² = a x²`
holds in `ZMod (p^ν)`.  Indeed `p^{2c}` divides both squares (as integers) and `p^ν ∣ p^{2c}`. -/
lemma sq_eq_of_dvd_vals {p ν c : ℕ} (hc : ν ≤ 2 * c) [NeZero (p ^ ν)] (a : ℤ)
    {x y : ZMod (p ^ ν)} (hx : p ^ c ∣ x.val) (hy : p ^ c ∣ y.val) :
    y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 := by
  have hxc : ((p:ℤ)^c) ∣ (x.val : ℤ) := by exact_mod_cast hx
  have hyc : ((p:ℤ)^c) ∣ (y.val : ℤ) := by exact_mod_cast hy
  have hpx : ((p:ℤ)^c)^2 = (p:ℤ)^(2*c) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hxdvd : (p:ℤ)^(2*c) ∣ ((x.val : ℤ))^2 := by
    rw [← hpx]
    exact pow_dvd_pow_of_dvd hxc 2
  have hydvd : (p:ℤ)^(2*c) ∣ ((y.val : ℤ))^2 := by
    rw [← hpx]
    exact pow_dvd_pow_of_dvd hyc 2
  have hmul : (p:ℤ)^(2*c) ∣ a * ((x.val : ℤ))^2 := dvd_mul_of_dvd_right hxdvd a
  have hmain : (p:ℤ)^(2*c) ∣ a * ((x.val : ℤ))^2 - ((y.val : ℤ))^2 := dvd_sub hmul hydvd
  have hdiv : ((p ^ ν : ℕ) : ℤ) ∣ a * ((x.val : ℤ))^2 - ((y.val : ℤ))^2 := by
    rw [Nat.cast_pow]
    exact dvd_trans (pow_dvd_pow (p:ℤ) hc) hmain
  have hy2 : ((((y.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν))
      = ((a * ((x.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (((y.val : ℤ))^2) (a * ((x.val : ℤ))^2) (p^ν)).mpr hdiv
  have hcasty : (((y.val : ℤ)) : ZMod (p ^ ν)) = y := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcastx : (((x.val : ℤ)) : ZMod (p ^ ν)) = x := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have e1 : ((((y.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν)) = (((y.val : ℤ)) : ZMod (p ^ ν)) ^ 2 := by
    rw [Int.cast_pow]
  have e2 : ((a * ((x.val : ℤ)) ^ 2 : ℤ) : ZMod (p ^ ν))
      = (a : ZMod (p ^ ν)) * ((((x.val : ℤ)) : ZMod (p ^ ν))) ^ 2 := by
    rw [Int.cast_mul, Int.cast_pow]
  rw [e1, e2, hcasty, hcastx] at hy2
  exact hy2

/-- **The non-square case of the local estimate of *FI* Lemma 8.1.**  For an odd prime `p`, `ν ≥ 1`,
a unit `a` modulo `p^ν` which is **not** a square modulo `p`, and all `h₁, h₂ : ℤ`,

  `‖Tsum (p^ν) a h₁ h₂‖ ≤ (ν+1)³ · (p^ν, h₁² - a h₂²)`.

Route.  Every solution of `y² = a x²` in `ZMod (p^ν)` has `p^{⌈ν/2⌉} ∣ x.val` and
`p^{⌈ν/2⌉} ∣ y.val`: if `j := ordv p ν x` satisfies `2j < ν`, then `x = ι_j z`, `y = ι_j z'` with
`z, z'` units and dividing the congruence by `p^{2j}` gives `z'² = a z²` in `ZMod (p^{ν-2j})`, so
`z' z⁻¹` is a square root of `a` modulo `p` — contradiction; applying the same to `y` (using
`v(a x²) = min(ν, 2 v(x))`) covers `y`.  Conversely `p^{⌈ν/2⌉} ∣ x.val` and `p^{⌈ν/2⌉} ∣ y.val`
certainly give the congruence.  So `Work.FIArea2.Tsum_eq_sum_Phi` is the product
`(∑_{x : p^c ∣ x.val} Φ (x h₁))·(∑_{y : p^c ∣ y.val} Φ (y h₂))` with `c = ⌈ν/2⌉`, and
`Work.FIArea2.sum_A_Phi_intCast` evaluates both factors as
`T (p^{ν-c}) hᵢ = p^{⌊ν/2⌋} [p^{⌊ν/2⌋} ∣ hᵢ]`; hence
`‖Tsum‖ = p^{2⌊ν/2⌋} [p^{⌊ν/2⌋} ∣ h₁] [p^{⌊ν/2⌋} ∣ h₂]`, which is `0` when a bracket fails and
otherwise is `p^{2⌊ν/2⌋} = p^{min (ν, 2⌊ν/2⌋)} ≤ Nat.gcd (p^ν) (h₁² - a h₂²)` because
`p^{2⌊ν/2⌋} ∣ h₁² - a h₂²`. -/
theorem Tsum_nonsquare_bound {p ν : ℕ} (hp : p.Prime) (hodd : Odd p) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a h1 h2 : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) (hnsq : ¬ IsSquare ((a : ZMod p))) :
    ‖Tsum (p ^ ν) a h1 h2‖
      ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set c := (ν + 1) / 2 with hcdef
  have hcν : c ≤ ν := by omega
  have h2c : ν ≤ 2 * c := by omega
  have hsol : ∀ x y : ZMod (p ^ ν), y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 →
      p ^ c ∣ x.val ∧ p ^ c ∣ y.val :=
    fun x y h => p_pow_ceil_dvd_of_sq_eq hp hν a ha hnsq h
  have hconv : ∀ x y : ZMod (p ^ ν), p ^ c ∣ x.val → p ^ c ∣ y.val →
      y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2 :=
    fun x y hx hy => sq_eq_of_dvd_vals h2c a hx hy
  have hfac : Tsum (p ^ ν) a h1 h2
      = (∑ x : ZMod (p ^ ν), if p ^ c ∣ x.val then Phi (p ^ ν) (x * (h1 : ZMod (p ^ ν))) else 0)
        * (∑ y : ZMod (p ^ ν), if p ^ c ∣ y.val then Phi (p ^ ν) (y * (h2 : ZMod (p ^ ν))) else 0) := by
    rw [Tsum_eq_sum_Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : p ^ c ∣ x.val
    · rw [if_pos hx, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hy : y ^ 2 = (a : ZMod (p ^ ν)) * x ^ 2
      · rw [if_pos hy, if_pos (hsol x y hy).2, Phi_add]
      · rw [if_neg hy, if_neg (fun hc' => hy (hconv x y hx hc')), mul_zero]
    · rw [if_neg hx, zero_mul]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [if_neg]
      intro hy
      exact hx (hsol x y hy).1
  rw [hfac, norm_mul, sum_A_Phi_intCast hp hcν h1, sum_A_Phi_intCast hp hcν h2]
  set N := p ^ (ν - c) with hN
  have hNpos : 1 ≤ N := by
    rw [hN]
    exact Nat.one_le_pow _ _ hp.pos
  have hTN : ∀ m : ℤ, ‖T N m‖ = if (N : ℤ) ∣ m then (N : ℝ) else 0 := by
    intro m
    rw [T_eq N hNpos m]
    by_cases hm : (N : ℤ) ∣ m
    · simp only [if_pos hm, Complex.norm_natCast]
    · simp only [if_neg hm, norm_zero]
  rw [hTN h1, hTN h2]
  by_cases hA : (N : ℤ) ∣ h1
  · by_cases hB : (N : ℤ) ∣ h2
    · rw [if_pos hA, if_pos hB]
      have hNsq : N * N = p ^ (2 * (ν - c)) := by
        rw [hN, ← pow_two, ← pow_mul]
        congr 1
        omega
      have hdivg : p ^ (2 * (ν - c)) ∣ Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) := by
        refine Nat.dvd_gcd (pow_dvd_pow p (by omega)) ?_
        have hNq : ((N : ℤ)) = (p : ℤ) ^ (ν - c) := by
          rw [hN]
          exact Nat.cast_pow p (ν - c)
        have hA' : (p : ℤ) ^ (ν - c) ∣ h1 := by rw [← hNq]; exact hA
        have hB' : (p : ℤ) ^ (ν - c) ∣ h2 := by rw [← hNq]; exact hB
        have h1sq : ((p : ℤ) ^ (ν - c)) ^ 2 ∣ h1 ^ 2 := pow_dvd_pow_of_dvd hA' 2
        have h2sq : ((p : ℤ) ^ (ν - c)) ^ 2 ∣ h2 ^ 2 := pow_dvd_pow_of_dvd hB' 2
        have h2m : ((p : ℤ) ^ (ν - c)) ^ 2 ∣ a * h2 ^ 2 := dvd_mul_of_dvd_right h2sq a
        have hsub : ((p : ℤ) ^ (ν - c)) ^ 2 ∣ h1 ^ 2 - a * h2 ^ 2 := dvd_sub h1sq h2m
        have hpow : ((p : ℤ) ^ (ν - c)) ^ 2 = (p : ℤ) ^ (2 * (ν - c)) := by
          rw [pow_two, ← pow_add]
          congr 1
          omega
        rw [hpow] at hsub
        have := (Int.natAbs_dvd_natAbs).mpr hsub
        simpa [Int.natAbs_pow] using this
      have hle : p ^ (2 * (ν - c)) ≤ Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) :=
        Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos ν)) hdivg
      have hgoal : (N : ℝ) * (N : ℝ)
          ≤ (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
        rw [← Nat.cast_mul, hNsq]
        exact_mod_cast hle
      calc (N : ℝ) * (N : ℝ) ≤ (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := hgoal
        _ ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
            have h1le : (1 : ℝ) ≤ ((ν : ℝ) + 1) ^ 3 := by
              have h : (1 : ℝ) ≤ (ν : ℝ) + 1 := by exact_mod_cast (show 1 ≤ ν + 1 by omega)
              calc (1 : ℝ) = 1 ^ 3 := by norm_num
                _ ≤ ((ν : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
            calc (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ)
                = 1 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by ring
              _ ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) :=
                  mul_le_mul_of_nonneg_right h1le (Nat.cast_nonneg _)
    · rw [if_neg hB, mul_zero]
      exact mul_nonneg (pow_nonneg (by positivity) 3) (Nat.cast_nonneg _)
  · rw [if_neg hA, zero_mul]
    exact mul_nonneg (pow_nonneg (by positivity) 3) (Nat.cast_nonneg _)

end

end Work.FIArea2
