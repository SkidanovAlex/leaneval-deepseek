import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Commons.NumberTheory.Sieve.Esum_rec_sieve

/-!
# The Rosser–Iwaniec `λ⁻` (lower bound) sieve inequality for `BoundingSieve`

This file proves `Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower`:

`Σ_{d ∣ P(z)} λ⁻(d) · (weight of the multiples of d) - remSum ≤ S(A,z)`,

i.e. the standard **minorant property** of the Rosser–Iwaniec lower weights `λ⁻`
(`lamMinus`): the weight sum `Σ_{d ∣ n} λ⁻(d)` is a minorant of the indicator of coprimality
with `P(z)`.

## The mathematics

For a squarefree modulus `n` and a level `D`, the lower Rosser–Iwaniec weight
`λ⁻(d) = μ(d)` if `d` is *lower admissible* (`rdMinus D d`: every even-`ω` divisor `e ≠ 1` of `d`
satisfies `e·(minFac e)² ≤ D`), and `0` otherwise.  The key facts are the following two
*recursions*, for `q` a prime larger than every prime factor of `d`:

* `rdMinus D (q * d) ↔ rdPlus (D / q) d`
* `rdPlus D (q * d) ↔ q³ ≤ D ∧ rdMinus (D / q) d`

(the odd Rosser–Iwaniec weights `rdPlus` being defined by the same condition on the *odd*-`ω`
divisors).  Writing `Wm n D = Σ_{d ∣ n, rdMinus D d} μ(d)` and `Wp n D` for the same sum with
`rdPlus`, they give the recursions

* `Wm (q*d) D = Wm d D - Wp d (D/q)`
* `Wp (q*d) D = Wp d D - (if q³ ≤ D then Wm d (D/q) else 0)`,

from which the pair of bounds `Wm n D ≤ [n = 1]`, `[n = 1] ≤ Wp n D` follows by strong induction
on `n`, using

`Wm (q*d) D = Wm d D - Wp d (D/q) ≤ [d = 1] - [d = 1] = 0`  and
`Wp (q*d) D ≥ [d = 1] - (if q³ ≤ D then [d = 1] else 0) ≥ 0`.

-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## The support weight `e·(minFac e)²` and elementary arithmetic of `σ`-divisors -/

/-- The weight `e · (minFac e)²` appearing in the Rosser–Iwaniec support conditions. -/
noncomputable def cval (e : ℕ) : ℝ := (e : ℝ) * (e.minFac : ℝ) ^ 2

lemma rdMinus_iff_cval (D : ℝ) (d : ℕ) :
    rdMinus D d ↔ ∀ e ∈ d.divisors, Even e.primeFactors.card → e ≠ 1 → cval e ≤ D := Iff.rfl

lemma rdPlus_iff_cval (D : ℝ) (d : ℕ) :
    rdPlus D d ↔ ∀ e ∈ d.divisors, Odd e.primeFactors.card → cval e ≤ D := Iff.rfl

lemma even_of_odd_succ {m : ℕ} (h : Odd (m + 1)) : Even m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

lemma odd_of_even_succ {m : ℕ} (h : Even (m + 1)) : Odd m :=
  Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h)

lemma even_succ_of_odd {m : ℕ} (h : Odd m) : Even (m + 1) :=
  Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h)

/-- For `q` prime and `q ∤ f`, the number of prime factors of `q*f` is one more than that of
`f`. -/
lemma card_aux (q f : ℕ) (hq : q.Prime) (hf : f ≠ 0) (h : ¬ q ∣ f) :
    (q * f).primeFactors.card = f.primeFactors.card + 1 := by
  have hnotmem : q ∉ f.primeFactors := fun hmem => h (Nat.mem_primeFactors.mp hmem).2.1
  rw [Nat.primeFactors_mul hq.ne_zero hf, hq.primeFactors]
  rw [Finset.singleton_union, Finset.card_insert_of_notMem hnotmem]

/-- Removing the smallest prime factor lowers the number of prime factors by one. -/
lemma card_mul_div_minFac (e : ℕ) (hsq : Squarefree e) (he1 : e ≠ 1) :
    e.primeFactors.card = (e / e.minFac).primeFactors.card + 1 := by
  have hp : (e.minFac).Prime := Nat.minFac_prime he1
  have he0 : e ≠ 0 := hsq.ne_zero
  have hf0 : e / e.minFac ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) (Nat.minFac_dvd e))
      (Nat.minFac_pos e)
    omega
  have hnd : ¬ e.minFac ∣ (e / e.minFac) := by
    intro hd
    have h1 : e.minFac * e.minFac ∣ e.minFac * (e / e.minFac) := Nat.mul_dvd_mul_left _ hd
    rw [Nat.mul_div_cancel' (Nat.minFac_dvd e)] at h1
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) _ hp h1
  have h2 := card_aux e.minFac (e / e.minFac) hp hf0 hnd
  rw [Nat.mul_div_cancel' (Nat.minFac_dvd e)] at h2
  omega

/-- `minFac` of `q * f` for a prime `q` larger than `minFac f`. -/
lemma minFac_mul_prime {q f : ℕ} (hq : q.Prime) (hf1 : f ≠ 1) (h : f.minFac < q) :
    (q * f).minFac = f.minFac := by
  have hqf1 : q * f ≠ 1 := by
    rcases eq_or_ne f 0 with hf | hf
    · simp [hf]
    · have : 2 ≤ q * f := Nat.mul_le_mul hq.two_le (Nat.one_le_iff_ne_zero.mpr hf)
      omega
  have hr : (f.minFac).Prime := Nat.minFac_prime hf1
  have h4 : ((q * f).minFac).Prime := Nat.minFac_prime hqf1
  have hle1 : (q * f).minFac ≤ f.minFac :=
    Nat.minFac_le_of_dvd hr.two_le (dvd_mul_of_dvd_right (Nat.minFac_dvd f) q)
  have hle2 : f.minFac ≤ (q * f).minFac := by
    rcases h4.dvd_mul.mp (Nat.minFac_dvd (q * f)) with h6 | h6
    · exfalso
      have h7 : q = (q * f).minFac := (hq.dvd_iff_eq h4.ne_one).mp h6
      omega
    · exact Nat.minFac_le_of_dvd h4.two_le h6
  exact le_antisymm hle1 hle2

/-- The key inequality: for a squarefree `e` with at least two prime factors, removing the
smallest prime factor `p` multiplies the weight `cval` by at least `1/p`:
`cval e ≤ q · cval (e / minFac e)` for any `q ≥ minFac e`. -/
lemma cval_le_minFac_mul_cval_div (e q : ℕ) (hsq : Squarefree e) (h2 : 2 ≤ e.primeFactors.card)
    (hle : e.minFac ≤ q) : cval e ≤ (q : ℝ) * cval (e / e.minFac) := by
  have he1 : e ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hcard := card_mul_div_minFac e hsq he1
  have hf1 : e / e.minFac ≠ 1 := by
    intro h; rw [h] at hcard; simp at hcard; omega
  have hrf : 2 ≤ ((e / e.minFac).minFac) := (Nat.minFac_prime hf1).two_le
  have hdiv : (e / e.minFac).minFac ∣ e :=
    dvd_trans (Nat.minFac_dvd _) (Nat.div_dvd_of_dvd (Nat.minFac_dvd e))
  have hle' : e.minFac ≤ (e / e.minFac).minFac := Nat.minFac_le_of_dvd hrf hdiv
  have hmul : (e.minFac : ℝ) * ((e / e.minFac : ℕ) : ℝ) = (e : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd e)]
  have hp0 : (0:ℝ) ≤ (e.minFac : ℝ) := by positivity
  have hf0' : (0:ℝ) ≤ ((e / e.minFac : ℕ) : ℝ) := by positivity
  have hpr : (e.minFac : ℝ) ≤ (((e / e.minFac).minFac : ℕ) : ℝ) := by exact_mod_cast hle'
  have hpq : (e.minFac : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  have h1 : (e.minFac : ℝ)^2 ≤ (((e / e.minFac).minFac : ℕ) : ℝ)^2 := pow_le_pow_left₀ hp0 hpr 2
  have hA : (e.minFac : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ)
      ≤ (((e / e.minFac).minFac : ℕ) : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right h1 hf0'
  have hB : (e.minFac : ℝ) * ((e.minFac : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ))
      ≤ (q : ℝ) * ((e.minFac : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hpq (by positivity)
  have hC : (q : ℝ) * ((e.minFac : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ))
      ≤ (q : ℝ) * ((((e / e.minFac).minFac : ℕ) : ℝ)^2 * ((e / e.minFac : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hA]) (by positivity)
  unfold cval
  calc (e : ℝ) * (e.minFac : ℝ) ^ 2
      = (e.minFac : ℝ) * ((e / e.minFac : ℕ) : ℝ) * (e.minFac : ℝ) ^ 2 := by rw [hmul]
    _ ≤ (q : ℝ) * ((e / e.minFac : ℕ) : ℝ) * (((e / e.minFac).minFac : ℕ) : ℝ) ^ 2 := by
        linarith [hB, hC]
    _ = (q : ℝ) * (((e / e.minFac : ℕ) : ℝ) * (((e / e.minFac).minFac : ℕ) : ℝ) ^ 2) := by ring

lemma div_ne_zero_of_dvd {f d : ℕ} (hfd : f ∣ d) (hd0 : d ≠ 0) : f ≠ 0 :=
  fun h => hd0 (Nat.eq_zero_of_zero_dvd (h ▸ hfd))

lemma primeFactors_subset_of_dvd {f d : ℕ} (hfd : f ∣ d) (hd0 : d ≠ 0) :
    f.primeFactors ⊆ d.primeFactors := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp1, dvd_trans hp2 hfd, hd0⟩

/-- `q * d` is squarefree when `q` is a prime not dividing the squarefree `d`. -/
lemma squarefree_mul_prime {q d : ℕ} (hq : q.Prime) (hd : Squarefree d) (hcop : ¬ q ∣ d) :
    Squarefree (q * d) := by
  rw [Nat.squarefree_iff_prime_squarefree] at hd ⊢
  intro p hp hpd
  have hpq : p ∣ q ∨ p ∣ d := hp.dvd_mul.mp (dvd_trans (dvd_mul_right p p) hpd)
  rcases hpq with h1 | h1
  · have hpq' : q = p := (hq.dvd_iff_eq hp.ne_one).mp h1
    exact hcop ((Nat.mul_dvd_mul_iff_left hq.pos).mp (hpq'.symm ▸ hpd))
  · have hpc : p.Coprime q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      intro hqp
      have hqp' : p = q := (hp.dvd_iff_eq hq.ne_one).mp hqp
      exact hcop (hqp' ▸ h1)
    exact hd p hp ((hpc.mul_left hpc).dvd_of_dvd_mul_left hpd)

lemma prime_not_dvd_prod_of_notMem {a : ℕ} (ha : a.Prime) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (h : a ∉ s) : ¬ a ∣ ∏ p ∈ s, p := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty]; exact fun hh => ha.ne_one (Nat.dvd_one.mp hh)
  | insert b t hb ih =>
      rw [Finset.prod_insert hb]
      intro hdvd
      rcases ha.dvd_mul.mp hdvd with h1 | h1
      · have h2 : b = a := ((hs b (Finset.mem_insert_self b t)).dvd_iff_eq ha.ne_one).mp h1
        exact h (h2 ▸ Finset.mem_insert_self b t)
      · exact ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
          (fun hmem => h (Finset.mem_insert_of_mem hmem)) h1

lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      exact squarefree_mul_prime (hs a (Finset.mem_insert_self a t))
        (ih fun p hp => hs p (Finset.mem_insert_of_mem hp))
        (prime_not_dvd_prod_of_notMem (hs a (Finset.mem_insert_self a t))
          (fun p hp => hs p (Finset.mem_insert_of_mem hp)) ha)

/-- A squarefree number with exactly one prime factor is prime. -/
lemma prime_of_card_primeFactors_eq_one {e : ℕ} (hsq : Squarefree e)
    (hc : e.primeFactors.card = 1) : e.Prime := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have he : e = p := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hp, Finset.prod_singleton]
  rw [he]
  exact (Nat.mem_primeFactors.mp (hp ▸ Finset.mem_singleton_self p)).1

/-- Möbius function at `q * f`, `q` prime not dividing `f`. -/
lemma moebius_mul_prime {q f : ℕ} (hq : q.Prime) (h : ¬ q ∣ f) :
    ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) = -((ArithmeticFunction.moebius f : ℤ) : ℝ) := by
  have hcop : q.Coprime f := hq.coprime_iff_not_dvd.mpr h
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  ring

/-! ## The two recursions for the Rosser–Iwaniec support conditions -/

/-- **First recursion.**  Multiplying the modulus by a prime `q` larger than all its prime
factors exchanges the lower support condition at level `D` with the upper one at level `D/q`. -/
lemma rdMinus_mul_prime {q d : ℕ} (hq : q.Prime) (hd : Squarefree d) (hcop : ¬ q ∣ d)
    (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    rdMinus D (q * d) ↔ rdPlus (D / q) d := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hqd0 : q * d ≠ 0 := Nat.mul_ne_zero hq.ne_zero hd0
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq.pos
  have hmin_lt : ∀ {f : ℕ}, f ∣ d → f ≠ 1 → f.minFac < q := by
    intro f hfd hf1
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    exact hbig _ (primeFactors_subset_of_dvd hfd hd0
      (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hf1, Nat.minFac_dvd f, hf0⟩))
  rw [rdMinus_iff_cval, rdPlus_iff_cval]
  constructor
  · intro h f hf hodd
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    have hf1 : f ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
    have hfqd : q * f ∈ (q * d).divisors :=
      Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hfd, hqd0⟩
    have hnot : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have h2 := card_aux q f hq hf0 hnot
    have heven : Even (q * f).primeFactors.card := by
      rw [h2]; exact even_succ_of_odd hodd
    have hne1 : q * f ≠ 1 := by
      have : 2 ≤ q * f := Nat.mul_le_mul hq.two_le (Nat.one_le_iff_ne_zero.mpr hf0)
      omega
    have hle := h (q * f) hfqd heven hne1
    have hcq : cval (q * f) = (q:ℝ) * cval f := by
      unfold cval
      rw [minFac_mul_prime hq hf1 (hmin_lt hfd hf1), Nat.cast_mul]
      ring
    rw [hcq] at hle
    rw [le_div_iff₀ hqpos]
    linarith
  · intro h e he heven he1
    obtain ⟨hedvd, -⟩ := Nat.mem_divisors.mp he
    by_cases hqe : q ∣ e
    · obtain ⟨f, rfl⟩ := hqe
      have hfd : f ∣ d := (Nat.mul_dvd_mul_iff_left hq.pos).mp hedvd
      have hfmem : f ∈ d.divisors := Nat.mem_divisors.mpr ⟨hfd, hd0⟩
      have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
      have h3 := card_aux q f hq hf0 (fun hqf => hcop (dvd_trans hqf hfd))
      have hodd : Odd f.primeFactors.card := by
        rw [h3] at heven
        exact odd_of_even_succ heven
      have hf1 : f ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
      have hle := h f hfmem hodd
      have hcq : cval (q * f) = (q:ℝ) * cval f := by
        unfold cval
        rw [minFac_mul_prime hq hf1 (hmin_lt hfd hf1), Nat.cast_mul]
        ring
      rw [hcq]
      rw [le_div_iff₀ hqpos] at hle
      linarith
    · have hed : e ∣ d := ((hq.coprime_iff_not_dvd.mpr hqe).symm).dvd_of_dvd_mul_left hedvd
      have hsqe : Squarefree e := Squarefree.squarefree_of_dvd hed hd
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have he2 : 2 ≤ e.primeFactors.card := by
        have h1 : 1 ≤ e.primeFactors.card := by
          have hne : e.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
          exact Finset.card_pos.mpr hne
        obtain ⟨k, hk⟩ := heven
        omega
      have hcf := card_mul_div_minFac e hsqe he1
      have hodd : Odd (e / e.minFac).primeFactors.card := by
        rw [hcf] at heven
        exact odd_of_even_succ heven
      have hfmem : e / e.minFac ∈ d.divisors :=
        Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd e)) hed, hd0⟩
      have hle := h _ hfmem hodd
      have hleminfac : e.minFac ≤ q := by
        have hp : (e.minFac).Prime := Nat.minFac_prime he1
        have hdvd : e.minFac ∣ q * d := dvd_trans (Nat.minFac_dvd e) hedvd
        rcases hp.dvd_mul.mp hdvd with h1 | h1
        · have : q = e.minFac := (hq.dvd_iff_eq hp.ne_one).mp h1
          omega
        · exact le_of_lt (hbig _ (Nat.mem_primeFactors.mpr ⟨hp, h1, hd0⟩))
      have hkey := cval_le_minFac_mul_cval_div e q hsqe he2 hleminfac
      rw [le_div_iff₀ hqpos] at hle
      linarith

/-- **Second recursion.**  Multiplying the modulus by a prime `q` larger than all its prime
factors turns the upper support condition at level `D` into `q³ ≤ D` together with the lower
condition at level `D/q`. -/
lemma rdPlus_mul_prime {q d : ℕ} (hq : q.Prime) (hd : Squarefree d) (hcop : ¬ q ∣ d)
    (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    rdPlus D (q * d) ↔ (q:ℝ)^3 ≤ D ∧ rdMinus (D / q) d := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hqd0 : q * d ≠ 0 := Nat.mul_ne_zero hq.ne_zero hd0
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq.pos
  have hmin_lt : ∀ {f : ℕ}, f ∣ d → f ≠ 1 → f.minFac < q := by
    intro f hfd hf1
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    exact hbig _ (primeFactors_subset_of_dvd hfd hd0
      (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hf1, Nat.minFac_dvd f, hf0⟩))
  rw [rdPlus_iff_cval, rdMinus_iff_cval]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hmem : q ∈ (q * d).divisors := Nat.mem_divisors.mpr ⟨dvd_mul_right q d, hqd0⟩
      have hodd : Odd q.primeFactors.card := by rw [hq.primeFactors]; simp
      have hle := h q hmem hodd
      have hcq : cval q = (q:ℝ)^3 := by
        unfold cval
        rw [hq.minFac_eq]
        ring
      rwa [hcq] at hle
    · intro e he heven he1
      obtain ⟨hed, -⟩ := Nat.mem_divisors.mp he
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have hmeme : q * e ∈ (q * d).divisors :=
        Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hed, hqd0⟩
      have h2 := card_aux q e hq he0 (fun hqe => hcop (dvd_trans hqe hed))
      have hodd : Odd (q * e).primeFactors.card := by
        rw [h2]; exact Even.add_one heven
      have hle := h (q * e) hmeme hodd
      have hcq : cval (q * e) = (q:ℝ) * cval e := by
        unfold cval
        rw [minFac_mul_prime hq he1 (hmin_lt hed he1), Nat.cast_mul]
        ring
      rw [hcq] at hle
      rw [le_div_iff₀ hqpos]
      linarith
  · rintro ⟨h3, h⟩ e he hodd
    obtain ⟨hedvd, -⟩ := Nat.mem_divisors.mp he
    by_cases hqe : q ∣ e
    · obtain ⟨f, rfl⟩ := hqe
      have hfd : f ∣ d := (Nat.mul_dvd_mul_iff_left hq.pos).mp hedvd
      have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
      rcases eq_or_ne f 1 with hf | hf
      · have hcq : cval (q * f) = (q:ℝ)^3 := by
          rw [hf, mul_one]
          unfold cval
          rw [hq.minFac_eq]
          ring
        rw [hcq]
        exact h3
      · have h2 := card_aux q f hq hf0 (fun hqf => hcop (dvd_trans hqf hfd))
        have heven' : Even f.primeFactors.card := by
          rw [h2] at hodd
          exact even_of_odd_succ hodd
        have hle := h f (Nat.mem_divisors.mpr ⟨hfd, hd0⟩) heven' hf
        have hcq : cval (q * f) = (q:ℝ) * cval f := by
          unfold cval
          rw [minFac_mul_prime hq hf (hmin_lt hfd hf), Nat.cast_mul]
          ring
        rw [hcq]
        rw [le_div_iff₀ hqpos] at hle
        linarith
    · have hed : e ∣ d := ((hq.coprime_iff_not_dvd.mpr hqe).symm).dvd_of_dvd_mul_left hedvd
      have hsqe : Squarefree e := Squarefree.squarefree_of_dvd hed hd
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have he1 : e ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
      have hcard : e.primeFactors.card = 1 ∨ 3 ≤ e.primeFactors.card := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hcard with hc1 | hc3
      · have hep : e.Prime := prime_of_card_primeFactors_eq_one hsqe hc1
        have helt : e < q := hbig e (Nat.mem_primeFactors.mpr ⟨hep, hed, hd0⟩)
        have hcq : cval e = (e:ℝ)^3 := by
          unfold cval
          rw [hep.minFac_eq]
          ring
        rw [hcq]
        have hle : (e:ℝ) ≤ (q:ℝ) := by exact_mod_cast (le_of_lt helt)
        have h3' : ((e:ℝ)^3 : ℝ) ≤ (q:ℝ)^3 := pow_le_pow_left₀ (by positivity) hle 3
        linarith
      · have hcf := card_mul_div_minFac e hsqe he1
        have heven : Even (e / e.minFac).primeFactors.card := by
          rw [hcf] at hodd
          exact even_of_odd_succ hodd
        have hf1 : e / e.minFac ≠ 1 := by
          intro h1
          rw [h1] at hcf
          simp at hcf
          omega
        have hfmem : e / e.minFac ∈ d.divisors :=
          Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd e)) hed, hd0⟩
        have hle := h _ hfmem heven hf1
        have hleminfac : e.minFac ≤ q := le_of_lt (hbig _
          (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime he1, dvd_trans (Nat.minFac_dvd e) hed, hd0⟩))
        have hkey := cval_le_minFac_mul_cval_div e q hsqe (by omega) hleminfac
        rw [le_div_iff₀ hqpos] at hle
        linarith

/-! ## The Möbius sums `Wm`, `Wp` and their recursions -/

/-- The lower Rosser–Iwaniec Möbius sum `Σ_{d ∣ n, rdMinus D d} μ(d)`. -/
noncomputable def Wm (n : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

/-- The upper Rosser–Iwaniec Möbius sum `Σ_{d ∣ n, rdPlus D d} μ(d)`. -/
noncomputable def Wp (n : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

lemma Wm_mul_prime {q d : ℕ} (hq : q.Prime) (hd : Squarefree d) (hcop : ¬ q ∣ d)
    (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    Wm (q * d) D = Wm d D - Wp d (D / q) := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hterm : ∀ f ∈ d.divisors,
      (if rdMinus D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)
        = - (if rdPlus (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) := by
    intro f hf
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hsqf : Squarefree f := Squarefree.squarefree_of_dvd hfd hd
    have hqnf : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have hbig' : ∀ p ∈ f.primeFactors, p < q :=
      fun p hp => hbig p (primeFactors_subset_of_dvd hfd hd0 hp)
    have hiff := rdMinus_mul_prime (d := f) hq hsqf hqnf hbig' D
    have hmu := moebius_mul_prime hq hqnf
    by_cases h1 : rdPlus (D / q) f
    · rw [if_pos (hiff.mpr h1), if_pos h1, hmu] <;> ring
    · rw [if_neg (fun hc => h1 (hiff.mp hc)), if_neg h1] <;> ring
  calc Wm (q * d) D
      = (∑ f ∈ d.divisors, (if rdMinus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        + (∑ f ∈ d.divisors,
            (if rdMinus D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)) := by
          rw [Wm, Commons.NumberTheory.Sieve.sum_divisors_mul_prime
              (fun f => if rdMinus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) q d hq hcop]
    _ = (∑ f ∈ d.divisors, (if rdMinus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        - (∑ f ∈ d.divisors,
            (if rdPlus (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)) := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]; ring
    _ = Wm d D - Wp d (D / q) := by rw [Wm, Wp]

lemma Wp_mul_prime {q d : ℕ} (hq : q.Prime) (hd : Squarefree d) (hcop : ¬ q ∣ d)
    (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    Wp (q * d) D = Wp d D - (if (q:ℝ)^3 ≤ D then Wm d (D / q) else 0) := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hterm : ∀ f ∈ d.divisors,
      (if rdPlus D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)
        = - (if (q:ℝ)^3 ≤ D then
              (if rdMinus (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)
              else 0) := by
    intro f hf
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hsqf : Squarefree f := Squarefree.squarefree_of_dvd hfd hd
    have hqnf : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have hbig' : ∀ p ∈ f.primeFactors, p < q :=
      fun p hp => hbig p (primeFactors_subset_of_dvd hfd hd0 hp)
    have hiff := rdPlus_mul_prime (d := f) hq hsqf hqnf hbig' D
    have hmu := moebius_mul_prime hq hqnf
    by_cases h2 : (q:ℝ)^3 ≤ D
    · rw [if_pos h2]
      by_cases h1 : rdMinus (D / q) f
      · rw [if_pos (hiff.mpr ⟨h2, h1⟩), if_pos h1, hmu] <;> ring
      · rw [if_neg (fun hc => h1 (hiff.mp hc).2), if_neg h1] <;> ring
    · rw [if_neg (fun hc => h2 (hiff.mp hc).1), if_neg h2] <;> ring
  calc Wp (q * d) D
      = (∑ f ∈ d.divisors, (if rdPlus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        + (∑ f ∈ d.divisors,
            (if rdPlus D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)) := by
          rw [Wp, Commons.NumberTheory.Sieve.sum_divisors_mul_prime
              (fun f => if rdPlus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) q d hq hcop]
    _ = (∑ f ∈ d.divisors, (if rdPlus D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        - (∑ f ∈ d.divisors, (if (q:ℝ)^3 ≤ D then
            (if rdMinus (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) else 0)) := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]; ring
    _ = Wp d D - (if (q:ℝ)^3 ≤ D then Wm d (D / q) else 0) := by
          rw [Wp]
          by_cases hc : (q:ℝ)^3 ≤ D
          · simp only [if_pos hc, Wm]
          · simp only [if_neg hc]
            simp

/-! ## The minorant/majorant property of `λ⁻` / `λ⁺` -/

theorem Wm_Wp_bounds : ∀ n : ℕ, Squarefree n →
    (∀ D : ℝ, 0 ≤ D → Wm n D ≤ (if n = 1 then 1 else 0)) ∧
    (∀ D : ℝ, 0 ≤ D → (if n = 1 then 1 else 0) ≤ Wp n D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_ne n 0 with h0 | h0
    · exact absurd (h0 ▸ hn) not_squarefree_zero
    rcases eq_or_ne n 1 with h1 | h1
    · subst h1
      constructor
      · intro D _
        rw [Wm, Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdMinus D 1 := by
          rw [rdMinus]
          intro e he _ he1
          exact absurd (Nat.dvd_one.mp (Nat.mem_divisors.mp he).1) he1
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, if_pos rfl]
        norm_num
      · intro D _
        rw [Wp, Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdPlus D 1 := by
          rw [rdPlus]
          intro e he hodd
          exact absurd hodd (by rw [Nat.dvd_one.mp (Nat.mem_divisors.mp he).1]; simp)
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, if_pos rfl]
        norm_num
    · have hn2 : 1 < n := by omega
      set q := n.primeFactors.max' (Nat.nonempty_primeFactors.mpr hn2) with hqdef
      have hqmem : q ∈ n.primeFactors := Finset.max'_mem _ _
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
      have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hqmem).2.1
      have hqmax : ∀ p ∈ n.primeFactors, p ≤ q := fun p hp => Finset.le_max' _ p hp
      set m := n / q with hmdef
      have hmul : q * m = n := Nat.mul_div_cancel' hqdvd
      have hmsq : Squarefree m := by
        have hh := hn; rw [← hmul] at hh; exact hh.of_mul_right
      have hmlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) hqprime.one_lt
      have hcop : ¬ q ∣ m := by
        intro hdiv
        have hqq : q * q ∣ q * m := Nat.mul_dvd_mul_left q hdiv
        rw [hmul] at hqq
        exact (Nat.squarefree_iff_prime_squarefree.mp hn) q hqprime hqq
      have hbig : ∀ p ∈ m.primeFactors, p < q := by
        intro p hp
        have hp_n : p ∈ n.primeFactors := by
          obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
          exact Nat.mem_primeFactors.mpr
            ⟨hp1, dvd_trans hp2 (by rw [← hmul]; exact dvd_mul_left m q), h0⟩
        have hle : p ≤ q := hqmax p hp_n
        have hne : p ≠ q := by
          intro hpq
          exact hcop (hpq ▸ (Nat.mem_primeFactors.mp hp).2.1)
        omega
      have ih' := ih m hmlt hmsq
      constructor
      · intro D hD
        have hDq : 0 ≤ D / q := div_nonneg hD (by positivity)
        have hWm : Wm n D = Wm m D - Wp m (D / q) := by
          rw [← hmul]; exact Wm_mul_prime hqprime hmsq hcop hbig D
        rw [hWm, if_neg h1]
        have h1' := ih'.1 D hD
        have h2' := ih'.2 (D / q) hDq
        linarith
      · intro D hD
        have hDq : 0 ≤ D / q := div_nonneg hD (by positivity)
        have hWp : Wp n D = Wp m D - (if (q:ℝ)^3 ≤ D then Wm m (D / q) else 0) := by
          rw [← hmul]; exact Wp_mul_prime hqprime hmsq hcop hbig D
        rw [hWp, if_neg h1]
        have h1' := ih'.2 D hD
        have h2' := ih'.1 (D / q) hDq
        have hnn : (0:ℝ) ≤ (if m = 1 then 1 else 0) := by split <;> norm_num
        by_cases hc : (q:ℝ)^3 ≤ D
        · rw [if_pos hc]; linarith
        · rw [if_neg hc]; linarith

/-- **The Rosser–Iwaniec minorant property** of `λ⁻`: for every squarefree `n` and level `D`,
the Möbius sum over the lower-admissible divisors is at most the indicator of `n = 1`. -/
theorem lamMinus_moebius_sum_le (n : ℕ) (hn : Squarefree n) (D : ℝ) (hD : 0 ≤ D) :
    (∑ d ∈ n.divisors, (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
      ≤ (if n = 1 then 1 else 0) :=
  (Wm_Wp_bounds n hn).1 D hD

/-! ## The product `P(z)` and the coprimality condition -/

lemma Pz_ne_zero (A : BoundingSieve) (z : ℝ) : Pz A z ≠ 0 := by
  rw [Pz]
  exact Finset.prod_ne_zero_iff.mpr
    (fun p hp => ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1).ne_zero)

lemma Pz_primeFactors (A : BoundingSieve) (z : ℝ) :
    (Pz A z).primeFactors = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < z) := by
  rw [Pz]
  exact Nat.primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)

lemma Pz_squarefree (A : BoundingSieve) (z : ℝ) : Squarefree (Pz A z) := by
  rw [Pz]
  exact squarefree_prod_primes (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)

/-- Coprimality with `P(z)` is the sifting condition of the sieve. -/
lemma coprime_Pz_iff (A : BoundingSieve) (n : ℕ) (z : ℝ) :
    Nat.gcd n (Pz A z) = 1 ↔ ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < z → ¬ p ∣ n := by
  rw [← Nat.coprime_iff_gcd_eq_one, Pz, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp hpz hp_dvd
    have hmem : p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < z) :=
      Finset.mem_filter.mpr ⟨hp, hpz⟩
    have hpc : p.Prime := (Nat.mem_primeFactors.mp hp).1
    exact (hpc.coprime_iff_not_dvd.mp (Nat.coprime_comm.mp (h p hmem))) hp_dvd
  · intro h p hp
    obtain ⟨hp1, hpz⟩ := Finset.mem_filter.mp hp
    have hpc : p.Prime := (Nat.mem_primeFactors.mp hp1).1
    exact Nat.coprime_comm.mp (hpc.coprime_iff_not_dvd.mpr (h p hp1 hpz))

/-! ## The target: the `λ⁻` lower bound for `siftedSumR` -/

/-- **The Rosser–Iwaniec `λ⁻` lower-bound sieve inequality.**  For every `BoundingSieve` `A`,
real sift limit `z ≥ 2` and level `D ≥ 0`,
`Σ_{d ∣ P(z)} λ⁻(d) · multSum(d) - remSum(A,D) ≤ S(A,z)`. -/
theorem lamMinus_sieve_lower (A : BoundingSieve) (z D : ℝ) (hD : 0 ≤ D) (hz : 2 ≤ z) :
    (∑ d ∈ (Work.ChenPlan.LinearSieve.Pz A z).divisors,
        Work.ChenPlan.LinearSieve.lamMinus (Work.ChenPlan.LinearSieve.Pz A z) D d * A.multSum d)
        - Submission.ChenPlan.remSum A D
      ≤ Work.ChenPlan.LinearSieve.siftedSumR A z := by
  have hPz0 : Pz A z ≠ 0 := Pz_ne_zero A z
  have hlam : ∀ d ∈ (Pz A z).divisors,
      lamMinus (Pz A z) D d = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    intro d hd
    obtain ⟨hdd, -⟩ := Nat.mem_divisors.mp hd
    rw [lamMinus]
    by_cases h : rdMinus D d
    · rw [if_pos ⟨hdd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  rw [Finset.sum_congr rfl (fun d hd => by rw [hlam d hd])]
  have hbound : (∑ d ∈ (Pz A z).divisors,
        (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.multSum d)
      ≤ siftedSumR A z := by
    calc (∑ d ∈ (Pz A z).divisors,
            (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.multSum d)
        = ∑ d ∈ (Pz A z).divisors, ∑ n ∈ A.support,
            (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              * (if d ∣ n then A.weights n else 0) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [BoundingSieve.multSum, Finset.mul_sum]
      _ = ∑ n ∈ A.support, ∑ d ∈ (Pz A z).divisors,
            (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              * (if d ∣ n then A.weights n else 0) :=
          Finset.sum_comm
      _ ≤ ∑ n ∈ A.support, (if Nat.gcd n (Pz A z) = 1 then 1 else 0) * A.weights n := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have h1 : (∑ d ∈ (Pz A z).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                  * (if d ∣ n then A.weights n else 0))
              = A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)) := by
            have hset : (Pz A z).divisors.filter (fun d => d ∣ n) = (Nat.gcd n (Pz A z)).divisors := by
              ext d
              rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
              constructor
              · rintro ⟨⟨h1, -⟩, h2⟩
                exact ⟨Nat.dvd_gcd h2 h1, fun hh => hPz0 (Nat.gcd_eq_zero_iff.mp hh).2⟩
              · rintro ⟨h1, -⟩
                exact ⟨⟨dvd_trans h1 (Nat.gcd_dvd_right n (Pz A z)), hPz0⟩,
                  dvd_trans h1 (Nat.gcd_dvd_left n (Pz A z))⟩
            calc (∑ d ∈ (Pz A z).divisors,
                  (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                    * (if d ∣ n then A.weights n else 0))
                = ∑ d ∈ (Pz A z).divisors,
                    (if d ∣ n then (if rdMinus D d then
                      ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.weights n else 0) := by
                  refine Finset.sum_congr rfl (fun d _ => ?_)
                  by_cases h : d ∣ n <;> simp [h]
              _ = (∑ d ∈ (Pz A z).divisors.filter (fun d => d ∣ n),
                    (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                      * A.weights n) := by
                  rw [Finset.sum_filter]
              _ = (∑ d ∈ (Pz A z).divisors.filter (fun d => d ∣ n),
                    (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
                    * A.weights n :=
                  (Finset.sum_mul _ _ _).symm
              _ = (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                    (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
                    * A.weights n := by
                  rw [hset]
              _ = A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                    (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)) := by ring
          rw [h1]
          have h2 : (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
              ≤ (if Nat.gcd n (Pz A z) = 1 then 1 else 0) :=
            lamMinus_moebius_sum_le _
              (Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n (Pz A z)) (Pz_squarefree A z)) D hD
          calc A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
              ≤ A.weights n * (if Nat.gcd n (Pz A z) = 1 then 1 else 0) :=
                mul_le_mul_of_nonneg_left h2 (A.weights_nonneg n)
            _ = (if Nat.gcd n (Pz A z) = 1 then 1 else 0) * A.weights n := by ring
      _ = ∑ n ∈ A.support,
            (if ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < z → ¬ p ∣ n then A.weights n else 0) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h : Nat.gcd n (Pz A z) = 1
          · rw [if_pos h, if_pos ((coprime_Pz_iff A n z).mp h)]; ring
          · rw [if_neg h, if_neg (fun hh => h ((coprime_Pz_iff A n z).mpr hh))]; ring
      _ = siftedSumR A z := by rw [siftedSumR]
  have hrem := remSum_nonneg A D
  linarith

end

end Work.ChenPlan.LinearSieve.RI
