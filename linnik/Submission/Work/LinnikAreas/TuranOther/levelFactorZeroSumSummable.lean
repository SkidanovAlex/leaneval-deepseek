import Mathlib
import Submission.Work.LinnikAreas.TuranOther.levelFactorDefs

open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-!
# Summability of the multiplicity-weighted zero sum of one level factor

For a prime `p` and `‖c‖ = 1`, the level factor `f(s) = 1 - c·p^{-s}` has exactly the lattice
`lvlZero p c n = lvlRoot p c + n·lvlPeriod p` (`n : ℤ`) as its zero set, and every one of its
zeros is simple.  Consequently the zero sum `Σ_u ord_u(f)·(t-u)^{-(k+1)}` against the inverse
power weight is a transfer, along the injection `n ↦ lvlZero p c n`, of the explicit `ℤ`-series
`Σ_n (t - lvlZero p c n)^{-(k+1)}`, which converges for `k ≥ 1`.

The pieces of the argument, in order:
* `summable_nat_shift_zpow` — comparison of `Σ_n (A + φ n)^{-(k+1)}` (`n : ℕ`, `‖φ n‖ = n`) with
  the convergent `p`-series `Σ_n n^{-(k+1)}`, `k + 1 ≥ 2`;
* `summable_int_add_zpow` — the two-sided version, splitting `ℤ` into `ℕ` and `-n - 1`;
* `lvlE_eq_zero_iff`, `analyticOrderNatAt_lvlE_lvlZero` — the zero set and its simplicity;
* `levelFactorZeroSumSummable` — the transfer to the `ℂ`-indexed sum.
-/

/-- Every `n : ℕ` with `‖A + φ n‖ ≥ n/2` contributes to a sum bounded by the `p`-series
`Σ 2^{m} / n^{m}`, which converges for `m ≥ 2`. -/
private lemma summable_nat_shift_zpow (A : ℂ) {m : ℕ} (hm : 2 ≤ m) (φ : ℕ → ℂ)
    (hφ : ∀ n, ‖φ n‖ = (n : ℝ)) :
    Summable (fun n : ℕ => (A + φ n) ^ (-(m : ℤ))) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hmaj : Summable (fun n : ℕ => (2 : ℝ) ^ m * (1 / (n : ℝ) ^ m)) := by
    have h := (Real.summable_one_div_nat_add_rpow 0 ((m : ℕ) : ℝ)).mpr hm1
    have h2 := h.mul_left ((2 : ℝ) ^ m)
    simpa [Real.rpow_natCast] using h2
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨Nat.ceil (2 * ‖A‖) + 1, fun n hn => ?_⟩
  have hpos : 0 < (n : ℝ) := by
    have h1 : 1 ≤ n := by omega
    exact_mod_cast h1
  have h2A : 2 * ‖A‖ ≤ (n : ℝ) := by
    have h1 : 2 * ‖A‖ ≤ (⌈2 * ‖A‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * ‖A‖⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hle : (n : ℝ) / 2 ≤ ‖A + φ n‖ := by
    have h1 : ‖φ n‖ ≤ ‖A + φ n‖ + ‖A‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (A + φ n) A
    rw [hφ n] at h1
    linarith
  rw [norm_zpow, zpow_neg, zpow_natCast, inv_eq_one_div]
  have hpow : ((n : ℝ) / 2) ^ m ≤ ‖A + φ n‖ ^ m := pow_le_pow_left₀ (by linarith) hle m
  have hpp : 0 < ((n : ℝ) / 2) ^ m := pow_pos (by linarith) m
  calc 1 / ‖A + φ n‖ ^ m ≤ 1 / ((n : ℝ) / 2) ^ m := one_div_le_one_div_of_le hpp hpow
    _ = (2 : ℝ) ^ m * (1 / (n : ℝ) ^ m) := by rw [div_pow, one_div_div, div_eq_mul_one_div]

/-- For any `A : ℂ` and `k ≥ 1`, the two-sided series `∑_{n : ℤ} (A + n)^{-(k+1)}` converges
(the exponent `-(k+1) ≤ -2` is strictly less than `-1`). -/
private theorem summable_int_add_zpow (A : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n : ℤ => (A + (n : ℂ)) ^ (-(k + 1) : ℤ)) := by
  have hk2 : 2 ≤ k + 1 := by omega
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_nat_shift_zpow A hk2 (fun n : ℕ => (n : ℂ))
      (fun n => Complex.norm_natCast n)
  · have h := summable_nat_shift_zpow (A - 1) hk2 (fun n : ℕ => -(n : ℂ))
      (by intro n; rw [norm_neg, Complex.norm_natCast])
    refine h.congr (fun n => ?_)
    push_cast
    ring_nf

/-- `(a⁻¹)^{-(k+1)} = a^{k+1}` for a natural `k`. -/
private lemma inv_zpow_neg_add_one (a : ℂ) (k : ℕ) :
    (a⁻¹) ^ (-((k : ℤ) + 1)) = a ^ (k + 1 : ℕ) := by
  have h : (-((k : ℤ) + 1)) = -(↑(k + 1) : ℤ) := by push_cast; ring
  rw [h, inv_zpow', neg_neg, zpow_natCast]

/-- For a prime `p` and `‖c‖ = 1`, the zeros of the level factor `lvlE p c s = 1 - c·p^{-s}`
are exactly the lattice points `lvlZero p c n = lvlRoot p c + n·lvlPeriod p`, `n : ℤ`. -/
theorem lvlE_eq_zero_iff {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1) (s : ℂ) :
    lvlE p c s = 0 ↔ ∃ n : ℤ, s = lvlZero p c n := by
  have hL := lvlL_ne_zero hp
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; norm_num at hc
  constructor
  · intro h
    rw [lvlE_apply] at h
    have h1 : c * Complex.exp (-((lvlL p : ℂ) * s)) = 1 := (sub_eq_zero.mp h).symm
    have h2 : Complex.exp ((lvlL p : ℂ) * s) = c := by
      have h3 : (Complex.exp ((lvlL p : ℂ) * s))⁻¹ = c⁻¹ := by
        rw [← Complex.exp_neg]
        exact eq_inv_of_mul_eq_one_right h1
      exact inv_inj.mp h3
    rw [← exp_lvlL_mul_lvlRoot hL hc0] at h2
    rw [Complex.exp_eq_exp_iff_exists_int] at h2
    obtain ⟨m, hm⟩ := h2
    refine ⟨m, ?_⟩
    have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hL
    refine mul_left_cancel₀ hLc ?_
    rw [hm, lvlZero, mul_add]
    have hP := lvlL_mul_lvlPeriod (p := p) hL
    rw [show (lvlL p : ℂ) * ((m : ℂ) * lvlPeriod p)
        = (m : ℂ) * ((lvlL p : ℂ) * lvlPeriod p) by ring]
    rw [hP]
  · rintro ⟨n, rfl⟩
    exact lvlE_lvlZero hL hc0 n

/-- Every lattice zero of the level factor `lvlE p c s = 1 - c·p^{-s}` (with `p` prime and
`‖c‖ = 1`) is a simple zero. -/
theorem analyticOrderNatAt_lvlE_lvlZero {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1)
    (n : ℤ) : analyticOrderNatAt (lvlE p c) (lvlZero p c n) = 1 := by
  have hL := lvlL_ne_zero hp
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; norm_num at hc
  have hzu : lvlE p c (lvlZero p c n) = 0 := lvlE_lvlZero hL hc0 n
  have hce : c * Complex.exp (-((lvlL p : ℂ) * lvlZero p c n)) = 1 :=
    (sub_eq_zero.mp hzu).symm
  have hderiv : deriv (lvlE p c) (lvlZero p c n) ≠ 0 := by
    have hd : HasDerivAt (lvlE p c)
        ((lvlL p : ℂ) * c * Complex.exp (-((lvlL p : ℂ) * lvlZero p c n)))
        (lvlZero p c n) := by
      have h1 : HasDerivAt (fun s : ℂ => -((lvlL p : ℂ) * s)) (-(lvlL p : ℂ))
          (lvlZero p c n) := by
        simpa [neg_mul] using (hasDerivAt_id (lvlZero p c n)).const_mul (-(lvlL p : ℂ))
      have h2 : HasDerivAt (fun s : ℂ => Complex.exp (-((lvlL p : ℂ) * s)))
          (Complex.exp (-((lvlL p : ℂ) * lvlZero p c n)) * (-(lvlL p : ℂ)))
          (lvlZero p c n) :=
        (Complex.hasDerivAt_exp _).comp (lvlZero p c n) h1
      have h3 : HasDerivAt (fun s : ℂ => c * Complex.exp (-((lvlL p : ℂ) * s)))
          (c * (Complex.exp (-((lvlL p : ℂ) * lvlZero p c n)) * (-(lvlL p : ℂ))))
          (lvlZero p c n) :=
        h2.const_mul c
      have h4 : HasDerivAt (fun s : ℂ => 1 - c * Complex.exp (-((lvlL p : ℂ) * s)))
          (0 - c * (Complex.exp (-((lvlL p : ℂ) * lvlZero p c n)) * (-(lvlL p : ℂ))))
          (lvlZero p c n) :=
        (hasDerivAt_const _ (1 : ℂ)).sub h3
      exact h4.congr_deriv (by ring)
    rw [hd.deriv]
    rw [mul_assoc, hce, mul_one]
    exact_mod_cast hL
  have h1 : analyticOrderAt (lvlE p c) (lvlZero p c n) = 1 :=
    (analyticAt_lvlE p c _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzu hderiv
  simp [analyticOrderNatAt, h1]

/-- Summability of the multiplicity-weighted zero sum of one Euler/level factor
`s ↦ 1 - c·p^{-s}` (`p` prime, `‖c‖ = 1`) against the inverse power weight `(t-u)^{-(k+1)}`
(`k ≥ 1`, `Re t > 1`).

Routing note: the zeros of `f s = 1 - c·p^{-s}` are exactly the lattice points
`lvlZero p c n = lvlRoot p c + n·lvlPeriod p` (`n : ℤ`) of the module
`Submission.Work.LinnikAreas.TuranOther.levelFactorDefs` (rewrite to `lvlE p c` via `lvlE_eq` and
use `Complex.exp_eq_exp_iff_exists_int`; `lvlE_lvlZero` gives the converse inclusion and
`lvlZero_injective` injectivity), and each is a simple zero since the derivative there is
`lvlL p = log p ≠ 0`.  Summability is then the transfer, along the injection
`n ↦ lvlZero p c n`, of the explicit ℤ-series `∑_n ‖t - lvlZero p c n‖^{-(k+1)}`, which is bounded
by a multiple of `∑_n (1 + |n|)^{-(k+1)}` for large `|n|` using `sub_lvlZero_eq`
(`t - lvlZero p c n = (lvlC p)⁻¹·(lvlC p·(t - lvlRoot p c) + n)`), and the latter converges since
`k + 1 ≥ 2`. -/
theorem levelFactorZeroSumSummable {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) := by
  rw [← lvlE_eq hp c]
  have hL : lvlL p ≠ 0 := lvlL_ne_zero hp
  have hinj : Function.Injective (lvlZero p c) := lvlZero_injective hL c
  have hsupp : ∀ u : ℂ, u ∉ Set.range (lvlZero p c) →
      ((analyticOrderNatAt (lvlE p c) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) = 0 := by
    intro u hu
    have hne : lvlE p c u ≠ 0 := by
      intro hz
      obtain ⟨n, hn⟩ := (lvlE_eq_zero_iff hp hc u).mp hz
      exact hu ⟨n, hn.symm⟩
    have hord : analyticOrderNatAt (lvlE p c) u = 0 := by
      have h0 := (analyticOrderAt_eq_zero (f := lvlE p c) (z₀ := u)).mpr (Or.inr hne)
      simp [analyticOrderNatAt, h0]
    rw [hord]
    simp
  have hSval : ∀ n : ℤ, ((analyticOrderNatAt (lvlE p c) (lvlZero p c n) : ℕ) : ℂ)
      * (t - lvlZero p c n) ^ (-(k + 1) : ℤ) = (t - lvlZero p c n) ^ (-(k + 1) : ℤ) := by
    intro n
    rw [analyticOrderNatAt_lvlE_lvlZero hp hc n]
    norm_num
  have hZ : Summable (fun n : ℤ => (t - lvlZero p c n) ^ (-(k + 1) : ℤ)) := by
    have hC := summable_int_add_zpow (lvlC p * (t - lvlRoot p c)) hk
    have hmul := hC.mul_left ((lvlC p) ^ (k + 1))
    refine hmul.congr (fun n => ?_)
    rw [sub_lvlZero_eq hL c n t, mul_zpow, inv_zpow_neg_add_one]
  have hS : Summable (fun u : Set.range (lvlZero p c) =>
      ((analyticOrderNatAt (lvlE p c) (u : ℂ) : ℕ) : ℂ) * (t - (u : ℂ)) ^ (-(k + 1) : ℤ)) := by
    have h1 : Summable ((fun n : ℤ => (t - lvlZero p c n) ^ (-(k + 1) : ℤ)) ∘
        (Equiv.ofInjective (lvlZero p c) hinj).symm) :=
      (Equiv.summable_iff (e := (Equiv.ofInjective (lvlZero p c) hinj).symm)
        (f := fun n : ℤ => (t - lvlZero p c n) ^ (-(k + 1) : ℤ))).mpr hZ
    refine h1.congr (fun u => ?_)
    have hsv := hSval ((Equiv.ofInjective (lvlZero p c) hinj).symm u)
    rw [Equiv.apply_ofInjective_symm hinj u] at hsv
    rw [Function.comp_apply, Equiv.apply_ofInjective_symm hinj u]
    exact hsv.symm
  have hSc : Summable (fun u : {v : ℂ // v ∉ Set.range (lvlZero p c)} =>
      ((analyticOrderNatAt (lvlE p c) (u : ℂ) : ℕ) : ℂ) * (t - (u : ℂ)) ^ (-(k + 1) : ℤ)) := by
    have h0 : (fun u : {v : ℂ // v ∉ Set.range (lvlZero p c)} =>
        ((analyticOrderNatAt (lvlE p c) (u : ℂ) : ℕ) : ℂ) * (t - (u : ℂ)) ^ (-(k + 1) : ℤ))
        = fun _ => 0 := by
      funext u
      exact hsupp u (by simpa using u.2)
    rw [h0]
    exact summable_zero
  exact (summable_subtype_and_compl).mp ⟨hS, hSc⟩

end Work.LinnikAreas.TuranOther
