
/-
# `Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq`

The classical factorisation of the Hecke `L`-function of the principal strict character modulo `4d`:

  `L(s, principalStrict d) = ζ(s)·L(s,χ₄)·G_d(s)`,   `G_d(s) = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})`,

valid for `re s > 1`, where `χ₄` is the quadratic character modulo `4` (`axisChi4`) and
`ζ·L(·,χ₄) = ζ_{ℚ(i)}` is the Dedekind zeta function of `ℚ(i)`.

The proof compares the Euler products.  The Hecke `L`-series is the product over the rational
primes of its local factors `heckeFp`, and the local factor at a prime `p` is

* at a *good* prime `p ∤ 4d`: `(1-p^{-s})⁻¹(1-χ₄(p)p^{-s})⁻¹`.  Here the primary elements of norm
  `p^ν` are the `ν+1` divisors of `p^ν` (at a split prime) resp. the single `(-p)^{ν/2}` (at an
  inert prime, only for even `ν`); since their norms are coprime to `4d` the principal character
  takes the value `1` on all of them.  Via the local recursion
  (`heckeLam_splitSum`/`heckeLam_inertSumEven`) this gives `λ(p) = 1+χ₄(p)`, `λ(p²) = 1+χ₄(p)+χ₄(p)²`,
  and `heckeLam_localInverse` converts these two values into the closed form
  `Σ_ν λ(p^ν)X^ν = (1-X)⁻¹(1-χ₄(p)X)⁻¹`;
* at a *bad* prime `p ∣ 4d`: `1`
  (`heckeLam_chiTriv_localFactor_dvd`): every primary element of norm `p^ν`, `ν ≥ 1`, has norm
  sharing the factor `p` with `4d`, so it is not a unit modulo `4d` and the character vanishes.

The correction `G_d` contributes at a bad prime exactly the reciprocal
`(1-p^{-s})(1-χ₄(p)p^{-s})` of the bad Euler factor of `ζ·L(·,χ₄)`, so that the two `HasProd`s over
the rational primes coincide.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea6Hecke.R.heckeLam_chiTriv_localFactor_dvd
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## 1. Elementary auxiliaries -/

/-- `(a * b)⁻¹ = a⁻¹ * b⁻¹` in `ℂ` (unconditional). -/
lemma mul_inv_eq_inv_mul (a b : ℂ) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have h : (a * b) * (a⁻¹ * b⁻¹) = 1 := by
    calc (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, one_mul]
  calc (a * b)⁻¹ = (a * b)⁻¹ * 1 := (mul_one _).symm
    _ = (a * b)⁻¹ * ((a * b) * (a⁻¹ * b⁻¹)) := by rw [h]
    _ = ((a * b)⁻¹ * (a * b)) * (a⁻¹ * b⁻¹) := by ring
    _ = 1 * (a⁻¹ * b⁻¹) := by rw [inv_mul_cancel₀ (mul_ne_zero ha hb)]
    _ = a⁻¹ * b⁻¹ := one_mul _

/-- `chiTriv d` and `principalStrict d` are the very same function (the indicator of the units
modulo `4d`); they were introduced in different files. -/
lemma chiTriv_eq_principalStrict (d : ℕ) :
    Work.FIArea6Hecke.R.chiTriv d = Work.FIArea6Hecke.principalStrict d := by
  funext z
  by_cases h : Work.FIArea5.S16Hecke.IsUnitMod4d d z <;>
    simp [Work.FIArea6Hecke.R.chiTriv, Work.FIArea6Hecke.principalStrict, h]

/-- `psi (principalStrict d) 0` is just `principalStrict d`. -/
lemma psi_principalStrict_zero (d : ℕ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0 z
      = Work.FIArea6Hecke.principalStrict d z := by
  rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]

/-- The value of `χ₄` at an integer congruent to `3` modulo `4`. -/
lemma axisChi4_eq_neg_one_of_mod_four {n : ℕ} (h : n % 4 = 3) :
    Work.FIArea6Hecke.R.axisChi4 n = -1 := by
  rw [Work.FIArea6Hecke.R.axisChi4_eq_if, if_neg (by omega : ¬ n % 2 = 0),
    if_neg (by omega : ¬ n % 4 = 1)]

/-- A Gaussian integer whose norm is coprime to `4d` is a unit modulo `4d`. -/
lemma principalStrict_of_gnorm_coprime (d : ℕ) (hd : 1 ≤ d) {z : GaussianInt}
    (h : Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)) :
    Work.FIArea6Hecke.principalStrict d z = 1 := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  exact Work.FIArea6Hecke.principalStrict_of_unit
    ((Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime z).mpr h)

/-- `psi (principalStrict d) 0 z = 1` when `|z|²` is coprime to `4d`. -/
lemma psi_principalStrict_of_coprime (d : ℕ) (hd : 1 ≤ d) {z : GaussianInt}
    (h : Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)) :
    Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0 z = 1 := by
  rw [psi_principalStrict_zero, principalStrict_of_gnorm_coprime d hd h]

/-- The local Euler factor of the Hecke `L`-series, rewritten as a power series in `p^{-s}`:
`∑_e λ(p^e)p^{-es} = ∑_e λ(p^e)(p^{-s})^e`. -/
lemma heckeFp_eq_tsum_mul (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ) :
    Work.FIArea5.S16Hecke.heckeFp chi k p s =
      ∑' e : ℕ,
        Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e) * (((p : ℕ) : ℂ) ^ (-s)) ^ e := by
  rw [Work.FIArea5.S16Hecke.heckeFp]
  refine tsum_congr fun e => ?_
  rw [div_eq_mul_inv, ← Complex.cpow_neg,
    show -((e : ℂ) * s) = (-s) * (e : ℂ) by ring, Complex.cpow_mul_nat]

/-- `1 - (p:ℂ)^{-s} ≠ 0` for `p > 1` and `re s > 1`. -/
lemma one_sub_natCast_cpow_neg_ne_zero {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    1 - ((p : ℂ) ^ (-s)) ≠ 0 :=
  sub_ne_zero.mpr (Work.FIArea6Hecke.R.natCast_cpow_neg_ne_one hp hs).symm

/-- `1 - χ₄(p)·p^{-s} ≠ 0` for `p > 1` and `re s > 1`. -/
lemma one_sub_axisChi4_mul_ne_zero {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    1 - Work.FIArea6Hecke.R.axisChi4 p * ((p : ℂ) ^ (-s)) ≠ 0 := by
  refine sub_ne_zero.mpr fun h => ?_
  have hnorm : ‖Work.FIArea6Hecke.R.axisChi4 p * ((p : ℂ) ^ (-s))‖ = 1 := by rw [← h]; simp
  have hle : ‖Work.FIArea6Hecke.R.axisChi4 p * ((p : ℂ) ^ (-s))‖ ≤ (p : ℝ) ^ (-s.re) := by
    rw [norm_mul]
    calc ‖Work.FIArea6Hecke.R.axisChi4 p‖ * ‖((p : ℂ) ^ (-s))‖
        ≤ 1 * ‖((p : ℂ) ^ (-s))‖ :=
          mul_le_mul_of_nonneg_right (Work.FIArea6Hecke.R.axisChi4_norm_le_one p) (norm_nonneg _)
      _ = (p : ℝ) ^ (-s.re) := by
          rw [one_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)
  linarith

/-- The correction factor is `1` outside the finite set of primes dividing `4d`, so its product
converges to the finite product `axisBadPoly`. -/
lemma hasProd_axisBadCorr (d : ℕ) (s : ℂ) :
    HasProd (fun p : Nat.Primes => Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s)
      (Work.FIArea6Hecke.R.axisBadPoly d s) := by
  classical
  let e : {q // q ∈ (4 * d).primeFactors} ↪ Nat.Primes :=
    ⟨fun q => ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩,
     fun a b h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
  let t : Finset Nat.Primes := ((4 * d).primeFactors.attach).map e
  have hf : ∀ p : Nat.Primes, p ∉ t →
      Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s = 1 := by
    intro p hp
    by_contra hne
    have hmem : (p : ℕ) ∈ (4 * d).primeFactors := by
      by_contra hcon
      exact hne (Work.FIArea6Hecke.R.axisBadCorr_eq_one hcon)
    exact hp (Finset.mem_map.mpr
      ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
  have hM : Multipliable (fun p : Nat.Primes => Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s) :=
    multipliable_of_ne_finset_one (s := t) hf
  have h := hM.hasProd
  rwa [Work.FIArea6Hecke.R.tprod_axisBadCorr d s] at h

/-! ## 2. The local Euler factor at every prime -/

/-- At a prime `p ∣ 4d` the local Euler factor is `1`. -/
lemma heckeFp_eq_one_of_dvd (d : ℕ) (hd : 1 ≤ d) (p : Nat.Primes) (hpd : (p : ℕ) ∣ 4 * d)
    {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s = 1 := by
  rw [heckeFp_eq_tsum_mul, ← chiTriv_eq_principalStrict d]
  exact Work.FIArea6Hecke.R.heckeLam_chiTriv_localFactor_dvd hd p.prop hpd s hs

/-- The local eigenvalue at a good prime: `λ(p) = 1 + χ₄(p)`. -/
lemma heckeLam_prime_good (d : ℕ) (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ 4 * d) :
    Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 p
      = 1 + Work.FIArea6Hecke.R.axisChi4 p := by
  have hcop : Nat.Coprime p (4 * d) := hp.coprime_iff_not_dvd.mpr hpd
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    exact hpd (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact Nat.odd_iff.mp h
  rcases em (p % 4 = 1) with h41 | h41
  · -- split prime
    obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ :=
      Work.FIArea5.S16Hecke.splitPrimaryClass p hp h41
    have key := Work.FIArea5.S16Hecke.heckeLam_splitSum (Work.FIArea6Hecke.principalStrict d) 0 p
      hp.pos (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
      π π' hπ hπ' hgπ hgπ' hclass 1
    rw [pow_one] at key
    rw [key, psi_principalStrict_of_coprime d hd (by rw [hgπ]; exact hcop),
      psi_principalStrict_of_coprime d hd (by rw [hgπ']; exact hcop),
      Work.FIArea5.S16Hecke.geo_one, Work.FIArea6Hecke.R.axisChi4_eq_one_of_mod_four h41]
  · -- inert prime
    have h43 : p % 4 = 3 := by omega
    rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h41,
      axisChi4_eq_neg_one_of_mod_four h43]
    norm_num

/-- The local eigenvalue at the square of a good prime: `λ(p²) = 1 + χ₄(p) + χ₄(p)²`. -/
lemma heckeLam_prime_sq_good (d : ℕ) (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ 4 * d) :
    Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 (p ^ 2)
      = 1 + Work.FIArea6Hecke.R.axisChi4 p + (Work.FIArea6Hecke.R.axisChi4 p) ^ 2 := by
  have hcop : Nat.Coprime p (4 * d) := hp.coprime_iff_not_dvd.mpr hpd
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    exact hpd (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact Nat.odd_iff.mp h
  rcases em (p % 4 = 1) with h41 | h41
  · obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ :=
      Work.FIArea5.S16Hecke.splitPrimaryClass p hp h41
    rw [Work.FIArea5.S16Hecke.heckeLam_splitSum (Work.FIArea6Hecke.principalStrict d) 0 p hp.pos
        (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
        π π' hπ hπ' hgπ hgπ' hclass 2]
    rw [psi_principalStrict_of_coprime d hd (by rw [hgπ]; exact hcop),
      psi_principalStrict_of_coprime d hd (by rw [hgπ']; exact hcop),
      Work.FIArea5.S16Hecke.geo_two, Work.FIArea6Hecke.R.axisChi4_eq_one_of_mod_four h41]
    norm_num
  · have h43 : p % 4 = 3 := by omega
    obtain ⟨hq, -, hgq, hclass⟩ := Work.FIArea5.S16Hecke.inertPrimaryClass p hp h43
    rw [show p ^ 2 = p ^ (2 * 1) by norm_num,
      Work.FIArea5.S16Hecke.heckeLam_inertSumEven (Work.FIArea6Hecke.principalStrict d) 0 p hp.pos
        (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
        (-(p : GaussianInt)) hq hgq hclass 1]
    rw [pow_one,
      psi_principalStrict_of_coprime d hd (by rw [hgq]; exact hcop.pow_left 2),
      axisChi4_eq_neg_one_of_mod_four h43]
    norm_num

/-- At a prime `p ∤ 4d` the local Euler factor is `(1-p^{-s})⁻¹(1-χ₄(p)p^{-s})⁻¹`. -/
lemma heckeFp_eq_good (d : ℕ) (hd : 1 ≤ d) (p : Nat.Primes) (hpd : ¬ (p : ℕ) ∣ 4 * d) {s : ℂ}
    (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s =
      (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
        (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  have hX : ‖(((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  rw [heckeFp_eq_tsum_mul]
  have hInv := Work.FIArea5.S16Hecke.heckeLam_localInverse
    (chi := Work.FIArea6Hecke.principalStrict d) (k := 0) (z := (((p : ℕ) : ℂ) ^ (-s)))
    p.prop (Work.FIArea6Hecke.principalStrict_mul d) (Work.FIArea6Hecke.principalStrict_one d)
    (Work.FIArea6Hecke.norm_principalStrict_le_one d) hX
  rw [heckeLam_prime_good d hd p.prop hpd, heckeLam_prime_sq_good d hd p.prop hpd] at hInv
  have hpoly : 1 - (1 + Work.FIArea6Hecke.R.axisChi4 (p : ℕ)) * (((p : ℕ) : ℂ) ^ (-s))
        + ((1 + Work.FIArea6Hecke.R.axisChi4 (p : ℕ)) ^ 2
            - (1 + Work.FIArea6Hecke.R.axisChi4 (p : ℕ)
                + (Work.FIArea6Hecke.R.axisChi4 (p : ℕ)) ^ 2))
          * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2)
      = (1 - (((p : ℕ) : ℂ) ^ (-s)))
        * (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))) := by
    ring
  rw [hpoly] at hInv
  exact (inv_eq_of_mul_eq_one_left hInv).symm.trans (mul_inv_eq_inv_mul _ _)

/-- **The pointwise local factor identity**: the local Euler factor of `L(·,principalStrict d)` at
`p` equals the product of the local factors of `ζ` and `L(·,χ₄)` times the correction at `p`. -/
lemma heckeFp_pointwise (d : ℕ) (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    ∀ p : Nat.Primes,
      Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s =
        (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
          (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
            Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s := by
  intro p
  by_cases hp : (p : ℕ) ∈ (4 * d).primeFactors
  · have hpd : (p : ℕ) ∣ 4 * d := (Nat.mem_primeFactors.mp hp).2.1
    have h1 : 1 - (((p : ℕ) : ℂ) ^ (-s)) ≠ 0 :=
      one_sub_natCast_cpow_neg_ne_zero p.prop.one_lt hs
    have h2 : 1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)) ≠ 0 :=
      one_sub_axisChi4_mul_ne_zero p.prop.one_lt hs
    rw [heckeFp_eq_one_of_dvd d hd p hpd hs, Work.FIArea6Hecke.R.axisBadCorr, if_pos hp]
    have h3 : (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
          (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
            ((1 - (((p : ℕ) : ℂ) ^ (-s))) *
              (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))) = 1 := by
      calc (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
            (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
              ((1 - (((p : ℕ) : ℂ) ^ (-s))) *
                (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))))
          = (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ * (1 - (((p : ℕ) : ℂ) ^ (-s))) *
              ((1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
                (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))) := by
            ring
        _ = 1 := by rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, one_mul]
    exact h3.symm
  · have hpd : ¬ (p : ℕ) ∣ 4 * d := by
      intro h
      exact hp (Nat.mem_primeFactors.mpr ⟨p.prop, h, by omega⟩)
    rw [heckeFp_eq_good d hd p hpd hs, Work.FIArea6Hecke.R.axisBadCorr, if_neg hp, mul_one]

/-! ## 3. The Euler product of `L(·,χ₄)` -/

/-- The completely multiplicative function `n ↦ χ₄(n)·n^{-s}`, whose Euler product is that of
`L(s,χ₄)`. -/
def axisChi4Summand (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := Work.FIArea6Hecke.R.axisChi4 n * ((n : ℂ) ^ s)⁻¹
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    simp only [Work.FIArea6Hecke.R.axisChi4_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_inv_eq_inv_mul]
    ring

/-- The Euler product of `L(·,χ₄)` on `re s > 1`. -/
theorem axisChi4_LSeries_eulerProduct_aux {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹)
      (LSeries Work.FIArea6Hecke.R.axisChi4 s) := by
  have hsum : Summable (fun n : ℕ => ‖axisChi4Summand s n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (Real.summable_nat_rpow_inv.mpr hs)
    rcases eq_or_ne n 0 with h | h
    · subst h
      simp [show axisChi4Summand s 0 = 0 by simp [axisChi4Summand],
        Real.zero_rpow (show s.re ≠ 0 by linarith)]
    · have hn : 0 < n := Nat.pos_of_ne_zero h
      rw [show axisChi4Summand s n
          = Work.FIArea6Hecke.R.axisChi4 n * ((n : ℂ) ^ s)⁻¹ from rfl]
      rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos hn]
      calc ‖Work.FIArea6Hecke.R.axisChi4 n‖ * ((n : ℝ) ^ s.re)⁻¹
          ≤ 1 * ((n : ℝ) ^ s.re)⁻¹ :=
            mul_le_mul_of_nonneg_right (Work.FIArea6Hecke.R.axisChi4_norm_le_one n) (by positivity)
        _ = ((n : ℝ) ^ s.re)⁻¹ := one_mul _
  have key := EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := axisChi4Summand s)
    hsum
  have h1 : (∑' n : ℕ, axisChi4Summand s n) = LSeries Work.FIArea6Hecke.R.axisChi4 s := by
    rw [LSeries_def₀ Work.FIArea6Hecke.R.axisChi4_zero s]
    refine tsum_congr fun n => ?_
    simp only [axisChi4Summand, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, div_eq_mul_inv]
  have h2 : ∀ p : Nat.Primes,
      (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹
        = (1 - axisChi4Summand s p)⁻¹ := by
    intro p
    simp only [axisChi4Summand, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ← Complex.cpow_neg]
  rw [h1] at key
  exact key.congr_fun fun p => h2 p

/-! ## 4. The assembly of the Euler products -/

/-- **The assembly.**  Given the pointwise local-factor identity and the Euler product of
`L(·,χ₄)`, the four `HasProd` statements for `L(·,principalStrict d)`, `ζ`, `L(·,χ₄)` and `G_d`
multiply to the factorisation. -/
theorem heckeLSeries_principalStrict_eq_of_pointwise
    (hpt : ∀ (d : ℕ), 1 ≤ d → ∀ {s : ℂ}, 1 < s.re → ∀ p : Nat.Primes,
      Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s =
        (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
          (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
            Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s)
    (hχ : ∀ {s : ℂ}, 1 < s.re →
      HasProd (fun p : Nat.Primes =>
        (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹)
        (LSeries Work.FIArea6Hecke.R.axisChi4 s))
    (d : ℕ) (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s =
      riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s *
        Work.FIArea6Hecke.R.axisBadPoly d s := by
  have hL : HasProd
      (fun p : Nat.Primes =>
        Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s)
      (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s) :=
    Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd (Work.FIArea6Hecke.principalStrict d) 0
      (Work.FIArea6Hecke.principalStrict_one d) (Work.FIArea6Hecke.principalStrict_mul d)
      (Work.FIArea6Hecke.norm_principalStrict_le_one d) hs
  have hz : HasProd (fun p : Nat.Primes => (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd hs
  have hχ4 : HasProd
      (fun p : Nat.Primes =>
        (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹)
      (LSeries Work.FIArea6Hecke.R.axisChi4 s) := hχ hs
  have hG : HasProd (fun p : Nat.Primes => Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s)
      (Work.FIArea6Hecke.R.axisBadPoly d s) := hasProd_axisBadCorr d s
  have hcomb : HasProd
      (fun p : Nat.Primes =>
        (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
          (1 - Work.FIArea6Hecke.R.axisChi4 (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
            Work.FIArea6Hecke.R.axisBadCorr d (p : ℕ) s)
      (riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s *
        Work.FIArea6Hecke.R.axisBadPoly d s) :=
    (hz.mul hχ4).mul hG
  have hcomb2 : HasProd
      (fun p : Nat.Primes =>
        Work.FIArea5.S16Hecke.heckeFp (Work.FIArea6Hecke.principalStrict d) 0 p s)
      (riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s *
        Work.FIArea6Hecke.R.axisBadPoly d s) :=
    hcomb.congr_fun fun p => hpt d hd hs p
  exact (hcomb2.unique hL).symm

theorem heckeLSeries_principalStrict_eq (d : ℕ) (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s =
      riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s *
        Work.FIArea6Hecke.R.axisBadPoly d s :=
  heckeLSeries_principalStrict_eq_of_pointwise
    (fun d hd _s hs => heckeFp_pointwise d hd hs)
    (fun hs => axisChi4_LSeries_eulerProduct_aux hs) d hd hs

end

end Work.FIArea6Hecke.R
