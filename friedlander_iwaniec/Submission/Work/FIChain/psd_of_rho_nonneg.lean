import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.prod_primeFactors_dvd_quot
import Submission.Commons.Data.Nat.squarefree_prod_primes

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The multilinear sieve sum

For a squarefree-supported weight `lam` supported in `[1,Δ]`, a multiplicative `g` with
`0 ≤ g p ≤ 1` at the primes and a modulus `d`, the quantity of interest is

    ∑_{ν ≤ Δ} lam ν · g (ν / gcd ν d) .

On the squarefree support of `lam` this equals the *multilinear* sum

    psfSum Δ lam d g = ∑_{ν ≤ Δ} lam ν · ∏_{p ∣ ν, p ∤ d} g p ,

and the point of the present file is that the latter is a nonnegative combination of its values at
the vertices `g p ∈ {0,1}` (induction on the primes where `g p ∉ {0,1}`), while at a vertex it is
`rhoOf lam M ≥ 0` for the squarefree `M = ∏_{p ≤ Δ, p ∣ d or g p = 1} p`. -/

/-- `psfDens g d n = ∏_{p ∣ n} (if p ∣ d then 1 else g p)`: the density `g` with the local factor
at each prime dividing `d` replaced by `1`. -/
def psfDens (g : ℕ → ℝ) (d n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, if p ∣ d then 1 else g p

/-- The vertex divisor `M = ∏_{p ≤ Δ, p ∣ d or x p = 1} p` of the vertex case. -/
def psfM (Δ d : ℕ) (x : ℕ → ℝ) : ℕ :=
  ∏ p ∈ (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1), p

/-- The multilinear sieve sum `∑_{ν ≤ Δ} lam ν · ∏_{p ∣ ν, p ∤ d} x p`. -/
def psfSum (Δ : ℕ) (lam : ℕ → ℝ) (d : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 Δ, lam ν * psfDens x d ν

/-- The primes `p ≤ Δ` at which `x p` is not (yet) a vertex, i.e. `x p ∉ {0,1}`. -/
def psfBad (Δ : ℕ) (x : ℕ → ℝ) : Finset ℕ :=
  (Nat.primesBelow (Δ + 1)).filter (fun p => ¬ (x p = 0 ∨ x p = 1))

/-! ## Elementary structure of `psfDens` and bipartite linearity of `psfSum` -/

lemma psfDens_mono (x : ℕ → ℝ) (d n : ℕ) :
    psfDens x d n = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ d), x p := by
  rw [psfDens, Finset.prod_filter]
  exact Finset.prod_congr rfl fun p _ => by by_cases h : p ∣ d <;> simp [h]

/-- The product `∏_{p ∈ A} x p` is affine in each single value `x q`. -/
lemma prod_update_affine (x : ℕ → ℝ) (A : Finset ℕ) (q : ℕ) :
    ∏ p ∈ A, x p
      = (1 - x q) * (∏ p ∈ A, Function.update x q 0 p)
        + x q * (∏ p ∈ A, Function.update x q 1 p) := by
  rcases em (q ∈ A) with hq | hq
  · rw [← Finset.insert_erase hq, Finset.prod_insert (Finset.notMem_erase q _),
        Finset.prod_insert (Finset.notMem_erase q _),
        Finset.prod_insert (Finset.notMem_erase q _)]
    rw [Function.update_self, Function.update_self]
    have h1 : ∏ p ∈ A.erase q, Function.update x q 0 p = ∏ p ∈ A.erase q, x p :=
      Finset.prod_congr rfl fun p hp => Function.update_of_ne (Finset.mem_erase.mp hp).1 0 x
    have h2 : ∏ p ∈ A.erase q, Function.update x q 1 p = ∏ p ∈ A.erase q, x p :=
      Finset.prod_congr rfl fun p hp => Function.update_of_ne (Finset.mem_erase.mp hp).1 1 x
    rw [h1, h2]; ring
  · have h1 : ∏ p ∈ A, Function.update x q 0 p = ∏ p ∈ A, x p :=
      Finset.prod_congr rfl fun p hp => Function.update_of_ne (fun hpq => hq (by cases hpq; exact hp)) 0 x
    have h2 : ∏ p ∈ A, Function.update x q 1 p = ∏ p ∈ A, x p :=
      Finset.prod_congr rfl fun p hp => Function.update_of_ne (fun hpq => hq (by cases hpq; exact hp)) 1 x
    rw [h1, h2]; ring

lemma psfDens_update (x : ℕ → ℝ) (d q ν : ℕ) :
    psfDens x d ν
      = (1 - x q) * psfDens (Function.update x q 0) d ν
        + x q * psfDens (Function.update x q 1) d ν := by
  rw [psfDens_mono, psfDens_mono, psfDens_mono, prod_update_affine]

/-- `psfSum` is affine in each single value of `x`. -/
lemma psfSum_update (Δ : ℕ) (lam : ℕ → ℝ) (d q : ℕ) (x : ℕ → ℝ) :
    psfSum Δ lam d x
      = (1 - x q) * psfSum Δ lam d (Function.update x q 0)
        + x q * psfSum Δ lam d (Function.update x q 1) := by
  simp only [psfSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [psfDens_update]
  ring

/-! ## The vertex case

At a vertex `x p ∈ {0,1}` for every prime `p ≤ Δ`, the density `psfDens x d ν` is the indicator of
the divisor-closed condition "every prime `p ∣ ν` satisfies `p ∣ d` or `x p = 1`", so the sum is
`∑_{ν ∣ M} lam ν = rhoOf lam M ≥ 0`. -/

lemma psfM_prime {Δ d : ℕ} {x : ℕ → ℝ} {p : ℕ} (hp : p ∈ (Nat.primesBelow (Δ + 1)).filter
    (fun p => p ∣ d ∨ x p = 1)) : p.Prime :=
  (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2

lemma psfM_ne_zero (Δ d : ℕ) (x : ℕ → ℝ) : psfM Δ d x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => (psfM_prime hp).ne_zero

lemma psfM_squarefree (Δ d : ℕ) (x : ℕ → ℝ) : Squarefree (psfM Δ d x) :=
  Commons.Data.Nat.squarefree_prod_primes fun _ hp => psfM_prime hp

lemma prime_dvd_psfM_iff {Δ d : ℕ} {x : ℕ → ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ psfM Δ d x ↔ p ∈ (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1) := by
  have hpf : (psfM Δ d x).primeFactors
      = (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1) :=
    Nat.primeFactors_prod fun _ hq => psfM_prime hq
  rw [← hpf, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨hp, h, psfM_ne_zero Δ d x⟩, fun h => h.2.1⟩

/-- A prime `p ≤ Δ` with `p ∣ d` or `x p = 1` lies in the vertex set. -/
lemma mem_psfM_set_of_prime_le {Δ d : ℕ} {x : ℕ → ℝ} {p : ℕ} (hp : p.Prime) (hpΔ : p ≤ Δ)
    (h : p ∣ d ∨ x p = 1) :
    p ∈ (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1) :=
  Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hpΔ, hp⟩, h⟩

/-- For squarefree `ν ≤ Δ`, the "divisor-closed" condition at `ν` is `ν ∣ M`. -/
lemma psfM_dvd_iff {Δ d : ℕ} {x : ℕ → ℝ} {ν : ℕ} (hν : ν ∈ Finset.Icc 1 Δ)
    (hsqν : Squarefree ν) :
    (∀ p ∈ ν.primeFactors, p ∣ d ∨ x p = 1) ↔ ν ∣ psfM Δ d x := by
  obtain ⟨h1ν, hνΔ⟩ := Finset.mem_Icc.mp hν
  constructor
  · intro h
    have hsub : ν.primeFactors ⊆ (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpν : p ∣ ν := (Nat.mem_primeFactors.mp hp).2.1
      have hpνle : p ≤ ν := Nat.le_of_dvd (by omega) hpν
      exact mem_psfM_set_of_prime_le hpp (le_trans hpνle hνΔ) (h p hp)
    calc ν = ∏ p ∈ ν.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsqν).symm
      _ ∣ ∏ p ∈ (Nat.primesBelow (Δ + 1)).filter (fun p => p ∣ d ∨ x p = 1), p :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = psfM Δ d x := rfl
  · intro h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpν : p ∣ ν := (Nat.mem_primeFactors.mp hp).2.1
    have hpd : p ∣ psfM Δ d x := dvd_trans hpν h
    exact (Finset.mem_filter.mp ((prime_dvd_psfM_iff hpp).mp hpd)).2

/-- At a vertex, `psfDens x d ν` is the indicator of the divisor-closed condition. -/
lemma psfDens_vertex {Δ d : ℕ} {x : ℕ → ℝ}
    (hx : ∀ p : ℕ, p.Prime → p ≤ Δ → (x p = 0 ∨ x p = 1))
    {ν : ℕ} (hν : ν ∈ Finset.Icc 1 Δ) :
    psfDens x d ν
      = if (∀ p ∈ ν.primeFactors, p ∣ d ∨ x p = 1) then 1 else 0 := by
  obtain ⟨h1ν, hνΔ⟩ := Finset.mem_Icc.mp hν
  rw [psfDens]
  trans ∏ p ∈ ν.primeFactors, (if (p ∣ d ∨ x p = 1) then (1:ℝ) else 0)
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpν : p ∣ ν := (Nat.mem_primeFactors.mp hp).2.1
    have hpνle : p ≤ ν := Nat.le_of_dvd (by omega) hpν
    have hpΔ : p ≤ Δ := le_trans hpνle hνΔ
    rcases hx p hpp hpΔ with h0 | h1
    · by_cases hpd : p ∣ d <;> simp [hpd, h0]
    · by_cases hpd : p ∣ d <;> simp [hpd, h1]
  · exact Finset.prod_boole

/-- **The vertex case**: `psfSum` is nonnegative whenever `x` is `{0,1}`-valued at the primes
`p ≤ Δ`. -/
lemma psfSum_vertex {Δ : ℕ} {lam : ℕ → ℝ} {d : ℕ} {x : ℕ → ℝ}
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hsq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n)
    (hx : ∀ p : ℕ, p.Prime → p ≤ Δ → (x p = 0 ∨ x p = 1)) :
    0 ≤ psfSum Δ lam d x := by
  have hstep1 : psfSum Δ lam d x
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * psfDens x d ν := by
    rw [psfSum]
    exact (Finset.sum_subset (Finset.filter_subset _ _) fun ν hν hνnot => by
      rw [hsq ν (fun hs => hνnot (Finset.mem_filter.mpr ⟨hν, hs⟩)), zero_mul]).symm
  have hstep2 : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * psfDens x d ν
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (if ν ∣ psfM Δ d x then lam ν else 0) := by
    refine Finset.sum_congr rfl fun ν hν => ?_
    obtain ⟨hνIcc, hνsq⟩ := Finset.mem_filter.mp hν
    have hiff : (∀ p ∈ ν.primeFactors, p ∣ d ∨ x p = 1) ↔ ν ∣ psfM Δ d x :=
      psfM_dvd_iff hνIcc hνsq
    rw [psfDens_vertex hx hνIcc]
    by_cases h : ν ∣ psfM Δ d x
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h, mul_zero]
  have hstep3 : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        (if ν ∣ psfM Δ d x then lam ν else 0)
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => Squarefree ν ∧ ν ∣ psfM Δ d x), lam ν := by
    rw [← Finset.sum_filter, Finset.filter_filter]
  have hstep4 : ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => Squarefree ν ∧ ν ∣ psfM Δ d x), lam ν
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => ν ∣ psfM Δ d x), lam ν := by
    rw [Finset.filter_congr (fun ν _ => ⟨fun h => h.2,
      fun h => ⟨Squarefree.squarefree_of_dvd h (psfM_squarefree Δ d x), h⟩⟩)]
  have hstep5 : ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => ν ∣ psfM Δ d x), lam ν
      = ∑ ν ∈ (psfM Δ d x).divisors.filter (fun ν => ν ≤ Δ), lam ν := by
    congr 1
    ext ν
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h3, psfM_ne_zero Δ d x⟩, h2⟩
    · rintro ⟨⟨h3, _⟩, h2⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h0 => psfM_ne_zero Δ d x (Nat.zero_dvd.mp (h0 ▸ h3))
  have hstep6 : ∑ ν ∈ (psfM Δ d x).divisors.filter (fun ν => ν ≤ Δ), lam ν
      = Submission.ASP.rhoOf lam (psfM Δ d x) := by
    rw [Submission.ASP.rhoOf]
    exact Finset.sum_subset (Finset.filter_subset _ _) fun ν hν hνnot =>
      hsupp ν (by
        have : ¬ ν ≤ Δ := fun h => hνnot (Finset.mem_filter.mpr ⟨hν, h⟩)
        omega)
  calc (0:ℝ) ≤ Submission.ASP.rhoOf lam (psfM Δ d x) := hρ _
    _ = ∑ ν ∈ (psfM Δ d x).divisors.filter (fun ν => ν ≤ Δ), lam ν := hstep6.symm
    _ = ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => ν ∣ psfM Δ d x), lam ν := hstep5.symm
    _ = ∑ ν ∈ (Finset.Icc 1 Δ).filter (fun ν => Squarefree ν ∧ ν ∣ psfM Δ d x), lam ν :=
          hstep4.symm
    _ = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (if ν ∣ psfM Δ d x then lam ν else 0) := hstep3.symm
    _ = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * psfDens x d ν := hstep2.symm
    _ = psfSum Δ lam d x := hstep1.symm

/-! ## From the vertices to the whole box -/

/-- **`psfSum` is nonnegative for `0 ≤ x p ≤ 1`.**  Induction on the number of primes `p ≤ Δ` at
which `x p ∉ {0,1}`: `psfSum` is affine in each such value, so it is a convex combination of its
values at the two vertices obtained by setting `x p := 0` or `x p := 1`, and the vertex case is
`psfSum_vertex`. -/
lemma psfSum_nonneg {Δ : ℕ} {lam : ℕ → ℝ} {d : ℕ}
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hsq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n)
    (x : ℕ → ℝ) (hx : ∀ p : ℕ, p.Prime → 0 ≤ x p ∧ x p ≤ 1) :
    0 ≤ psfSum Δ lam d x := by
  suffices H : ∀ k : ℕ, ∀ x : ℕ → ℝ, (∀ p : ℕ, p.Prime → 0 ≤ x p ∧ x p ≤ 1) →
      (psfBad Δ x).card = k → 0 ≤ psfSum Δ lam d x by
    exact H (psfBad Δ x).card x hx rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hk
    rcases Finset.eq_empty_or_nonempty (psfBad Δ x) with hemp | ⟨q, hq⟩
    · refine psfSum_vertex hsupp hsq hρ ?_
      intro p hp hpΔ
      by_contra hcon
      have hmem : p ∈ psfBad Δ x :=
        Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hpΔ, hp⟩, hcon⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty p hmem
    · obtain ⟨hqpB, _hqbad⟩ := Finset.mem_filter.mp hq
      obtain ⟨_hqlt, hqprime⟩ := Nat.mem_primesBelow.mp hqpB
      have hxq := hx q hqprime
      have hx0 : ∀ p : ℕ, p.Prime →
          0 ≤ (Function.update x q 0) p ∧ (Function.update x q 0) p ≤ 1 := by
        intro p hp
        rw [Function.update_apply]
        by_cases h : p = q
        · subst h; simp
        · rw [if_neg h]; exact hx p hp
      have hx1 : ∀ p : ℕ, p.Prime →
          0 ≤ (Function.update x q 1) p ∧ (Function.update x q 1) p ≤ 1 := by
        intro p hp
        rw [Function.update_apply]
        by_cases h : p = q
        · subst h; simp
        · rw [if_neg h]; exact hx p hp
      have hsub0 : psfBad Δ (Function.update x q 0) ⊆ (psfBad Δ x).erase q := by
        intro p hp
        obtain ⟨hpB, hpbad⟩ := Finset.mem_filter.mp hp
        have hpq : p ≠ q := by
          rintro rfl
          rw [Function.update_self] at hpbad
          exact hpbad (Or.inl rfl)
        rw [Finset.mem_erase]
        refine ⟨hpq, Finset.mem_filter.mpr ⟨hpB, ?_⟩⟩
        intro hcon
        apply hpbad
        rcases hcon with h0 | h1
        · left; rwa [Function.update_of_ne hpq]
        · right; rwa [Function.update_of_ne hpq]
      have hsub1 : psfBad Δ (Function.update x q 1) ⊆ (psfBad Δ x).erase q := by
        intro p hp
        obtain ⟨hpB, hpbad⟩ := Finset.mem_filter.mp hp
        have hpq : p ≠ q := by
          rintro rfl
          rw [Function.update_self] at hpbad
          exact hpbad (Or.inr rfl)
        rw [Finset.mem_erase]
        refine ⟨hpq, Finset.mem_filter.mpr ⟨hpB, ?_⟩⟩
        intro hcon
        apply hpbad
        rcases hcon with h0 | h1
        · left; rwa [Function.update_of_ne hpq]
        · right; rwa [Function.update_of_ne hpq]
      have hcard0 : (psfBad Δ (Function.update x q 0)).card < k := by
        have h1 : (psfBad Δ (Function.update x q 0)).card ≤ ((psfBad Δ x).erase q).card :=
          Finset.card_le_card hsub0
        have h2 : ((psfBad Δ x).erase q).card = (psfBad Δ x).card - 1 :=
          Finset.card_erase_of_mem hq
        have h3 : 0 < (psfBad Δ x).card := Finset.card_pos.mpr ⟨q, hq⟩
        omega
      have hcard1 : (psfBad Δ (Function.update x q 1)).card < k := by
        have h1 : (psfBad Δ (Function.update x q 1)).card ≤ ((psfBad Δ x).erase q).card :=
          Finset.card_le_card hsub1
        have h2 : ((psfBad Δ x).erase q).card = (psfBad Δ x).card - 1 :=
          Finset.card_erase_of_mem hq
        have h3 : 0 < (psfBad Δ x).card := Finset.card_pos.mpr ⟨q, hq⟩
        omega
      have h0 := ih (psfBad Δ (Function.update x q 0)).card hcard0
        (Function.update x q 0) hx0 rfl
      have h1 := ih (psfBad Δ (Function.update x q 1)).card hcard1
        (Function.update x q 1) hx1 rfl
      rw [psfSum_update Δ lam d q x]
      exact add_nonneg (mul_nonneg (by linarith [hxq.2]) h0) (mul_nonneg hxq.1 h1)

/-! ## The bridge to `g (ν / gcd ν d)` -/

/-- On squarefree `n`, the local density of `psfDens` reproduces `g (n / gcd n d)`. -/
lemma psfDens_eq_div_gcd (g : ℕ → ℝ) (d n : ℕ) (hg1 : g 1 = 1)
    (hgmul : ∀ m k : ℕ, Nat.Coprime m k → g (m * k) = g m * g k) (hn : Squarefree n) :
    psfDens g d n = g (n / Nat.gcd n d) :=
  prod_primeFactors_dvd_quot g d n hg1 hgmul hn

/-- **The PSD axioms of `SieveInput` are a consequence of `ρ ≥ 0`.**  If `lam` is squarefree-supported
and supported in `[1,Δ]`, and `rhoOf lam n = ∑_{ν|n} lam ν ≥ 0` for every `n`, then for every
*multiplicative* `g` with `0 ≤ g p ≤ 1` at the primes, and every `d`,
`∑_{ν ≤ Δ} lam ν * g (ν / gcd ν d) ≥ 0`.

Proof idea (do not skip the squarefree hypothesis: it makes `ν / gcd ν d` squarefree, so the sum
is multilinear in the values `g p`).  Fix `d` and write the sum as `Φ(g)`.  For a prime `p ≤ Δ`
the function `g p ↦ Φ` is affine, so `Φ` is a convex combination of its values with `g p := 0` and
`g p := 1`; inducting on the number of primes `p ≤ Δ` with `g p ∉ {0,1}` reduces to the vertex case
`g = 1_S` (`S` a set of primes), where the sum equals `rhoOf lam (m · ∏_{p∈S} p)` for
`m = ∏_{p ∣ d, p ≤ Δ} p` (a squarefree number), hence is `≥ 0` by `hρ`. -/
theorem psd_of_rho_nonneg {Δ : ℕ} {lam : ℕ → ℝ}
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hsq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n) :
    ∀ (g : ℕ → ℝ), (∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p ≤ 1) →
      (∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) →
      ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d) := by
  intro g hg hgmul d
  by_cases h1 : g 1 = 1
  · have hbridge : ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)
        = psfSum Δ lam d g := by
      refine Finset.sum_congr rfl fun ν _ => ?_
      by_cases hs : Squarefree ν
      · rw [← psfDens_eq_div_gcd g d ν h1 hgmul hs]
      · rw [hsq ν hs, zero_mul, zero_mul]
    rw [hbridge]
    exact psfSum_nonneg hsupp hsq hρ g hg
  · have hg1 : g 1 = 0 := by
      have hmul := hgmul 1 1 (Nat.coprime_one_left 1)
      simp only [mul_one] at hmul
      have hz : g 1 * (1 - g 1) = 0 := by linarith
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd (by linarith : g 1 = 1) h1
    have hzero : ∀ n : ℕ, 1 ≤ n → g n = 0 := by
      intro n _hn
      have h := hgmul n 1 (Nat.coprime_one_right n)
      rw [mul_one] at h
      rw [hg1, mul_zero] at h
      exact h
    rw [Finset.sum_eq_zero (fun ν hν => by
      rw [hzero (ν / Nat.gcd ν d) (by
        rw [Nat.one_le_div_iff (Nat.gcd_pos_of_pos_left d (by
          exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hν).1))]
        exact Nat.gcd_le_left d (by
          exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hν).1)), mul_zero])]

end

end Work.FIChain
