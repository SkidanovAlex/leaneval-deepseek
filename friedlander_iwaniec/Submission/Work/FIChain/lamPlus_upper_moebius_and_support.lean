/-
# `Work.FIChain.lamPlus_upper_moebius_and_support`

The two facts the FI endgame needs about the Rosser–Iwaniec upper weight `lamPlus P D`:
`BoundingSieve.IsUpperMoebius (lamPlus P D)` and the support bound `(d : ℝ) < D` for squarefree
`rdPlus D`-admissible `d` (with `1 < D`).

The mathematics is ported from the Chen workspace's Rosser–Iwaniec files
(`Submission/Work/ChenPlan/LinearSieve/RI/{basic,upper_moebius,support_lt,lamMinus_sieve_lower}.lean`),
which this workspace cannot import (its `Submission.Chen.Interface` imports the absent
`ChallengeDeps`).  The definitions are already in `Submission/Work/FIChain/Rossers.lean`; the
helper material (`cval` and the Möbius sums `Wm`, `Wp` with their recursions and the bound
`Wm_Wp_bounds`) is inlined below with the `Work.ChenPlan.LinearSieve.RI` names renamed to this
file's.

The two facts about `Wm`, `Wp` (for squarefree `n`, `D ≥ 0`):
`Wm n D ≤ [n = 1] ≤ Wp n D`, proved by strong induction on `n` from the recursions
`Wm (q*d) D = Wm d D - Wp d (D/q)`,
`Wp (q*d) D = Wp d D - [q³ ≤ D] · Wm d (D/q)` (`q` the largest prime factor of `n`),
which in turn come from `rdMinus D (q*d) ↔ rdPlus (D/q) d` and
`rdPlus D (q*d) ↔ q³ ≤ D ∧ rdMinus (D/q) d`.
-/
import Mathlib
import Submission.Work.FIChain.Rossers

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Work.FIChain

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## Splitting a divisor sum at a prime (ported from `Commons.NumberTheory.Sieve.Esum_rec_sieve`) -/

lemma divisors_mul_prime_eq_ri (q N : ℕ) (hq : q.Prime) (hqd : ¬ q ∣ N) :
    (q * N).divisors = N.divisors ∪ N.divisors.image (fun d => q * d) := by
  have hN0 : N ≠ 0 := fun h => hqd (h ▸ dvd_zero q)
  have hqN0 : q * N ≠ 0 := Nat.mul_ne_zero hq.ne_zero hN0
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hdvd, _⟩
    by_cases h : q ∣ d
    · obtain ⟨e, rfl⟩ := h
      right
      exact ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd, hN0⟩, rfl⟩
    · left
      exact ⟨Nat.Coprime.dvd_of_dvd_mul_left ((hq.coprime_iff_not_dvd.mpr h).symm) hdvd, hN0⟩
  · rintro (⟨hdvd, _⟩ | ⟨e, ⟨hed, _⟩, rfl⟩)
    · exact ⟨dvd_mul_of_dvd_right hdvd q, hqN0⟩
    · exact ⟨Nat.mul_dvd_mul_left q hed, hqN0⟩

lemma disjoint_divisors_image_mul_prime (q N : ℕ) (hqd : ¬ q ∣ N) :
    Disjoint N.divisors (N.divisors.image (fun d => q * d)) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  rw [Finset.mem_image] at hd2
  obtain ⟨e, he, rfl⟩ := hd2
  exact hqd (dvd_trans (dvd_mul_right q e) (Nat.mem_divisors.mp hd1).1)

lemma sum_divisors_mul_prime_ri (F : ℕ → ℝ) (q N : ℕ) (hq : q.Prime) (hqd : ¬ q ∣ N) :
    ∑ d ∈ (q * N).divisors, F d
      = ∑ d ∈ N.divisors, F d + ∑ d ∈ N.divisors, F (q * d) := by
  rw [divisors_mul_prime_eq_ri q N hq hqd,
      Finset.sum_union (disjoint_divisors_image_mul_prime q N hqd)]
  congr 1
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hq.pos hab

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
          rw [Wm, sum_divisors_mul_prime_ri
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
          rw [Wp, sum_divisors_mul_prime_ri
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

/-- **Removing the smallest prime factor increases `cval`.**  If `d` is squarefree, `d ≠ 1`, and
`e · minFac d = d` with `e ≠ 1`, then `d < cval e`.  Indeed `minFac e > minFac d` because
`d` is squarefree, so `d = e · minFac d < e · minFac e ≤ e · (minFac e)² = cval e`. -/
lemma lt_cval_of_mul {d e : ℕ} (hsq : Squarefree d) (hd1 : d ≠ 1)
    (he : e * d.minFac = d) (he1 : e ≠ 1) : (d : ℝ) < cval e := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hmprime : (d.minFac).Prime := Nat.minFac_prime hd1
  have hemfprime : (e.minFac).Prime := Nat.minFac_prime he1
  have hemfdvd : e.minFac ∣ d := by
    rw [← he]; exact dvd_mul_of_dvd_left (Nat.minFac_dvd e) _
  have hle : d.minFac ≤ e.minFac := Nat.minFac_le_of_dvd hemfprime.two_le hemfdvd
  have hne : d.minFac ≠ e.minFac := by
    intro h
    have hmvdve : d.minFac ∣ e := h ▸ Nat.minFac_dvd e
    have hmm : d.minFac * d.minFac ∣ d := by
      obtain ⟨k, hk⟩ := hmvdve
      refine ⟨k, ?_⟩
      calc d = e * d.minFac := he.symm
        _ = d.minFac * k * d.minFac := by rw [hk]
        _ = d.minFac * d.minFac * k := by ring
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq d.minFac hmprime) hmm
  have hltm : d.minFac < e.minFac := lt_of_le_of_ne hle hne
  have he0 : e ≠ 0 := by
    intro h; rw [h, zero_mul] at he; exact hd0 he.symm
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr he0
  have hmcast : (d.minFac : ℝ) < (e.minFac : ℝ) := by exact_mod_cast hltm
  have hdeq : (d : ℝ) = (e : ℝ) * (d.minFac : ℝ) := by
    have h1 : (d : ℝ) = ((e * d.minFac : ℕ) : ℝ) := by rw [he]
    rw [h1]; push_cast; ring
  have h1 : (e : ℝ) * (d.minFac : ℝ) < (e : ℝ) * (e.minFac : ℝ) :=
    mul_lt_mul_of_pos_left hmcast hepos
  have he1le : (1 : ℝ) ≤ (e.minFac : ℝ) := by
    have : (1 : ℕ) ≤ e.minFac := le_of_lt hemfprime.one_lt
    exact_mod_cast this
  have h2 : (e : ℝ) * (e.minFac : ℝ) ≤ (e : ℝ) * (e.minFac : ℝ) ^ 2 := by
    have hsq' : (e.minFac : ℝ) ≤ (e.minFac : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq' hepos.le
  unfold cval
  linarith

/-- An upper-admissible squarefree `d` satisfies `d < D` (for `D > 1`). -/
lemma rdPlus_lt {D : ℝ} (hD : 1 < D) {d : ℕ} (hsq : Squarefree d) (hd : rdPlus D d) :
    (d : ℝ) < D := by
  rcases eq_or_ne d 1 with h1 | hd1
  · subst h1; simp only [Nat.cast_one]; exact hD
  · have hd0 : d ≠ 0 := hsq.ne_zero
    by_cases hev : Even d.primeFactors.card
    · have hcard := card_mul_div_minFac d hsq hd1
      have hoddE : Odd (d / d.minFac).primeFactors.card := by
        apply odd_of_even_succ
        rw [← hcard]; exact hev
      have hemem : d / d.minFac ∈ d.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd d), hd0⟩
      have hc : cval (d / d.minFac) ≤ D := hd _ hemem hoddE
      have hnp : ¬ d.Prime := by
        intro hp
        have hev' := hev
        rw [hp.primeFactors] at hev'
        obtain ⟨k, hk⟩ := hev'
        simp only [Finset.card_singleton] at hk
        omega
      have he1 : d / d.minFac ≠ 1 := by
        intro h
        have hdm : d = d.minFac := by
          calc d = d / d.minFac * d.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd d)).symm
            _ = 1 * d.minFac := by rw [h]
            _ = d.minFac := one_mul _
        exact hnp (hdm.symm ▸ Nat.minFac_prime hd1)
      have hlt := lt_cval_of_mul hsq hd1 (Nat.div_mul_cancel (Nat.minFac_dvd d)) he1
      linarith
    · have hodd : Odd d.primeFactors.card := Nat.not_even_iff_odd.mp hev
      have hmem : d ∈ d.divisors := Nat.mem_divisors_self d hd0
      have hc : cval d ≤ D := hd d hmem hodd
      have hmf2 : (2 : ℝ) ≤ (d.minFac : ℝ) := by
        exact_mod_cast (Nat.minFac_prime hd1).two_le
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hd0
      have hbig : (d : ℝ) * 4 ≤ cval d := by
        unfold cval
        have h4 : (4 : ℝ) ≤ (d.minFac : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left h4 hdpos.le
      linarith

/-! ## The squarefree kernel -/

/-- The **squarefree kernel** `∏_{p ∣ n} p` of `n`: the largest squarefree divisor of `n`. -/
def sqKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma sqKernel_ne_zero {n : ℕ} (hn : n ≠ 0) : sqKernel n ≠ 0 := by
  rw [sqKernel, Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.mem_primeFactors.mp hp).1.ne_zero

lemma squarefree_sqKernel (n : ℕ) : Squarefree (sqKernel n) :=
  squarefree_prod_primes (fun p hp => (Nat.mem_primeFactors.mp hp).1)

lemma sqKernel_dvd (n : ℕ) : sqKernel n ∣ n := Nat.prod_primeFactors_dvd n

lemma sqKernel_one : sqKernel 1 = 1 := by simp [sqKernel]

/-- A squarefree divisor of `n` divides the squarefree kernel of `n`. -/
lemma dvd_sqKernel_of_squarefree_dvd {d n : ℕ} (hn : n ≠ 0) (hsq : Squarefree d) (h : d ∣ n) :
    d ∣ sqKernel n := by
  rw [sqKernel, ← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_dvd_prod_of_subset d.primeFactors n.primeFactors (fun p => p)
    (Nat.primeFactors_mono h hn)

/-! ## The main theorem -/

theorem upper_moebius (P : ℕ) (D : ℝ) :
    BoundingSieve.IsUpperMoebius (lamPlus P D) := by
  intro n
  rcases eq_or_ne n 0 with h0 | hn0
  · subst h0
    rw [Nat.divisors_zero, Finset.sum_empty]
    norm_num
  rcases lt_or_ge D 0 with hDneg | hD
  · -- `D < 0`: only `d = 1` is admissible
    have h1mem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
    have hrd1 : rdPlus D 1 := by
      rw [rdPlus]
      intro e he hodd
      exact absurd hodd (by rw [Nat.dvd_one.mp (Nat.mem_divisors.mp he).1]; simp)
    have hterm : ∀ d ∈ n.divisors, lamPlus P D d = if d = 1 then (1 : ℝ) else 0 := by
      intro d hd
      rcases eq_or_ne d 1 with hd1 | hd1
      · subst hd1
        rw [lamPlus, if_pos ⟨one_dvd P, hrd1⟩, ArithmeticFunction.moebius_apply_one]
        norm_num
      · rw [if_neg hd1, lamPlus, if_neg]
        rintro ⟨-, hr⟩
        have hd0 : d ≠ 0 := div_ne_zero_of_dvd (Nat.mem_divisors.mp hd).1 hn0
        have hp : (d.minFac).Prime := Nat.minFac_prime hd1
        have hmem : d.minFac ∈ d.divisors := Nat.mem_divisors.mpr ⟨Nat.minFac_dvd d, hd0⟩
        have hodd : Odd (d.minFac).primeFactors.card := by
          rw [hp.primeFactors, Finset.card_singleton]; exact odd_one
        have hle := hr d.minFac hmem hodd
        rw [hp.minFac_eq] at hle
        have h2 : (2 : ℝ) ≤ (d.minFac : ℝ) := by exact_mod_cast hp.two_le
        have hcube : (d.minFac : ℝ) ^ 3 ≤ D := by
          calc (d.minFac : ℝ) ^ 3 = (d.minFac : ℝ) * (d.minFac : ℝ) ^ 2 := by ring
            _ ≤ D := hle
        have h8 : (2 : ℝ) ^ 3 ≤ (d.minFac : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
        linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' n.divisors 1 (fun _ => (1 : ℝ)),
      if_pos h1mem]
    split <;> norm_num
  · -- `D ≥ 0`: reduce to the squarefree kernel of `gcd n P`
    have hg0 : Nat.gcd n P ≠ 0 := fun h => hn0 (Nat.gcd_eq_zero_iff.mp h).1
    have hfilt : n.divisors.filter (fun d => d ∣ P) = (Nat.gcd n P).divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdn, -⟩, hdP⟩
        exact ⟨Nat.dvd_gcd hdn hdP, hg0⟩
      · rintro ⟨hd, -⟩
        exact ⟨⟨dvd_trans hd (Nat.gcd_dvd_left n P), hn0⟩,
          dvd_trans hd (Nat.gcd_dvd_right n P)⟩
    have hstep1 : ∑ d ∈ n.divisors, lamPlus P D d
        = ∑ d ∈ (Nat.gcd n P).divisors,
            (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
      have h1 : ∑ d ∈ n.divisors, lamPlus P D d
          = ∑ d ∈ n.divisors, (if d ∣ P then
              (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) else 0) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [lamPlus]
        by_cases hP : d ∣ P <;> by_cases hr : rdPlus D d <;> simp [hP, hr]
      rw [h1, ← Finset.sum_filter, hfilt]
    have hk0 : sqKernel (Nat.gcd n P) ≠ 0 := sqKernel_ne_zero hg0
    have hsub : (sqKernel (Nat.gcd n P)).divisors ⊆ (Nat.gcd n P).divisors := by
      intro d hd
      exact Nat.mem_divisors.mpr
        ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (sqKernel_dvd _), hg0⟩
    have hzero : ∀ d ∈ (Nat.gcd n P).divisors, d ∉ (sqKernel (Nat.gcd n P)).divisors →
        (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 0 := by
      intro d hd hnot
      have hnsq : ¬ Squarefree d := fun hsq =>
        hnot (Nat.mem_divisors.mpr
          ⟨dvd_sqKernel_of_squarefree_dvd hg0 hsq (Nat.mem_divisors.mp hd).1, hk0⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      split <;> norm_num
    have hbound := (Wm_Wp_bounds (sqKernel (Nat.gcd n P)) (squarefree_sqKernel _)).2 D hD
    have hkn : (if n = 1 then (1 : ℝ) else 0)
        ≤ (if sqKernel (Nat.gcd n P) = 1 then (1 : ℝ) else 0) := by
      by_cases hn1 : n = 1
      · subst hn1
        rw [if_pos rfl, if_pos (by rw [Nat.gcd_one_left, sqKernel_one])]
      · rw [if_neg hn1]
        split <;> norm_num
    calc (if n = 1 then (1 : ℝ) else 0)
        ≤ (if sqKernel (Nat.gcd n P) = 1 then (1 : ℝ) else 0) := hkn
      _ ≤ Wp (sqKernel (Nat.gcd n P)) D := hbound
      _ = ∑ d ∈ (Nat.gcd n P).divisors,
            (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) :=
          Finset.sum_subset hsub hzero
      _ = ∑ d ∈ n.divisors, lamPlus P D d := hstep1.symm

/-! ## The target -/

/-- The two facts the FI endgame needs about the Rosser–Iwaniec upper weight
`λ⁺ = Work.FIChain.lamPlus P D` (defined in `Submission/Work/FIChain/Rossers.lean`):

* `BoundingSieve.IsUpperMoebius (lamPlus P D)` — equivalently `ρ n = Σ_{d ∣ n} λ⁺(d) ≥ 0`, the
  `SieveInput` conjunct that neither the Selberg `Λ²` weight (`|σ| ≤ 1`, good quality, but
  `ρ` negative) nor its `lcm`-square (`ρ ≥ 0` but `|λ| ≤ 3^{ω}`) supplies;
* the support bound `Squarefree d → rdPlus D d → (d : ℝ) < D`.

**Port these from the Chen workspace's files, which are in this repository and can be READ but not
IMPORTED** (`Submission/Work/ChenPlan/LinearSieve/RI/basic.lean` has the definitions — identical to
`Rossers.lean`'s — and `RI/upper_moebius.lean`, `RI/support_lt.lean`,
`RI/lamMinus_sieve_lower.lean` have the proofs; importing them fails only because
`Submission.Chen.Interface` imports `ChallengeDeps`, absent here).  The statements there are
`Work.ChenPlan.LinearSieve.upper_moebius (P) (D) : BoundingSieve.IsUpperMoebius (lamPlus P D)` and
`Work.ChenPlan.LinearSieve.RI.support_lt`, so the proofs port with a rename of the
`Work.ChenPlan.LinearSieve.*` definitions to this file's.  Do not import the Chen closure; the
helper `cval`/`Wm_Wp_bounds` of `RI/lamMinus_sieve_lower.lean` have to be inlined. -/
theorem lamPlus_upper_moebius_and_support (P : ℕ) (D : ℝ) (hD : 1 < D) :
    BoundingSieve.IsUpperMoebius (Work.FIChain.lamPlus P D) ∧
      (∀ d : ℕ, Squarefree d → Work.FIChain.rdPlus D d → (d : ℝ) < D) :=
  ⟨upper_moebius P D, fun d hsq hd => rdPlus_lt hD hsq hd⟩

end

end Work.FIChain
