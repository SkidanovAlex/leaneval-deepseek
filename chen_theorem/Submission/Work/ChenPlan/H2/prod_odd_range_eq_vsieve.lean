import Mathlib
import Submission.Work.ChenPlan.H2.SieveDeps

namespace Work.ChenPlan.H2

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-- `oddPrimesLt Y` is `oddLt Y`: the set of odd primes below `Y`. -/
lemma oddPrimesLt_eq_oddLt (Y : ℕ) :
    Commons.NumberTheory.Chen.oddPrimesLt Y = oddLt Y := by
  ext p
  simp only [Commons.NumberTheory.Chen.oddPrimesLt, oddLt, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨h1, hp, hp2⟩
    refine ⟨h1, hp, ?_⟩
    have := hp.two_le
    omega
  · rintro ⟨h1, hp, hp3⟩
    refine ⟨h1, hp, ?_⟩
    omega

/-- The prime factors of the odd primorial `oddPrimLt M` are the odd primes below `M`. -/
lemma oddPrimLt_primeFactors (M : ℕ) : (oddPrimLt M).primeFactors = oddLt M := by
  rw [oddPrimLt_eq_prod_oddLt]
  exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)

/-- `Vsieve Y` as a product over `oddLt Y`. -/
lemma Vsieve_eq_prod (Y : ℕ) :
    Commons.NumberTheory.Chen.Vsieve Y = ∏ p ∈ oddLt Y, (1 - 1/((p:ℝ)-1)) := by
  rw [Commons.NumberTheory.Chen.Vsieve, oddPrimesLt_eq_oddLt]

/-- The odd primes in the window `[max w 3, z')` are exactly the set difference
`oddLt ⌈z'⌉₊ \ oddLt (max ⌈w⌉₊ 3)`. -/
lemma filter_oddLt_eq_sdiff {M : ℕ} {w z' : ℝ} (hw : 2 ≤ w) (hwz : w < z')
    (hz'M : z' ≤ M) :
    (oddLt M).filter (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z')
      = oddLt ⌈z'⌉₊ \ oddLt (max ⌈w⌉₊ 3) := by
  have hzM : ⌈z'⌉₊ ≤ M := Nat.ceil_le.mpr hz'M
  ext p
  rw [Finset.mem_filter, Finset.mem_sdiff, Submission.mem_oddLt, Submission.mem_oddLt,
    Submission.mem_oddLt]
  constructor
  · rintro ⟨⟨hpp, hp3, hpM⟩, hwp, hpz⟩
    refine ⟨⟨hpp, hp3, ?_⟩, ?_⟩
    · rwa [Nat.lt_ceil]
    · rintro ⟨-, -, hplt⟩
      have h1 : ⌈w⌉₊ ≤ p := Nat.ceil_le.mpr hwp
      omega
  · rintro ⟨⟨hpp, hp3, hpz⟩, hnot⟩
    have hmax : max ⌈w⌉₊ 3 ≤ p := by
      by_contra hc
      exact hnot ⟨hpp, hp3, by omega⟩
    refine ⟨⟨hpp, hp3, lt_of_lt_of_le (Nat.lt_ceil.mp hpz) hzM⟩, ?_, Nat.lt_ceil.mp hpz⟩
    exact le_trans (Nat.le_ceil w) (by exact_mod_cast le_trans (le_max_left _ _) hmax)

/-- The main product identity: for `s ≤ t`, the product of `(1 - 1/φ(p))⁻¹` over the odd
primes in `[s, t)` equals `Vsieve s / Vsieve t`. -/
lemma prod_odd_range (s t : ℕ) (hst : s ≤ t) :
    (∏ p ∈ oddLt t \ oddLt s, (1 - Work.ChenPlan.H1.invTotient p)⁻¹)
      = Commons.NumberTheory.Chen.Vsieve s / Commons.NumberTheory.Chen.Vsieve t := by
  have hsub : oddLt s ⊆ oddLt t := by
    intro p hp
    rw [Submission.mem_oddLt] at hp ⊢
    exact ⟨hp.1, hp.2.1, by omega⟩
  rw [Finset.prod_inv_distrib]
  have hgsub : (∏ p ∈ oddLt t \ oddLt s, (1 - Work.ChenPlan.H1.invTotient p))
      = ∏ p ∈ oddLt t \ oddLt s, (1 - 1/((p:ℝ)-1)) := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpp : p.Prime := (Submission.mem_oddLt.mp (Finset.mem_sdiff.mp hp).1).1
    rw [Work.ChenPlan.H1.invTotient_apply, Nat.totient_prime hpp,
      Nat.cast_sub (by have := hpp.two_le; omega : 1 ≤ p), Nat.cast_one, inv_eq_one_div]
  rw [hgsub]
  have hprod := Finset.prod_sdiff (s₁ := oddLt s) (s₂ := oddLt t)
    (f := fun p : ℕ => (1 - 1/((p:ℝ)-1))) hsub
  rw [← Vsieve_eq_prod t, ← Vsieve_eq_prod s] at hprod
  have hP : (∏ p ∈ oddLt t \ oddLt s, (1 - 1/((p:ℝ)-1)))
      = Commons.NumberTheory.Chen.Vsieve t / Commons.NumberTheory.Chen.Vsieve s := by
    rw [eq_div_iff (ne_of_gt (Commons.NumberTheory.Chen.Vsieve_pos s))]
    exact hprod
  rw [hP, inv_div]

theorem prod_odd_range_eq_vsieve (M : ℕ) {w z' : ℝ} (hw : 2 ≤ w) (hwz : w < z') (hz'M : z' ≤ M) :
    (∏ p ∈ (Commons.NumberTheory.Chen.ChenEight.oddPrimLt M).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - Work.ChenPlan.H1.invTotient p)⁻¹)
      = Commons.NumberTheory.Chen.Vsieve (max ⌈w⌉₊ 3) / Commons.NumberTheory.Chen.Vsieve ⌈z'⌉₊ := by
  have hz3 : 3 ≤ ⌈z'⌉₊ := by
    have h2 : (2:ℝ) < z' := by linarith
    have h3 : (2:ℝ) < ((⌈z'⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le h2 (Nat.le_ceil z')
    have : 2 < ⌈z'⌉₊ := by exact_mod_cast h3
    omega
  have hst : max ⌈w⌉₊ 3 ≤ ⌈z'⌉₊ :=
    max_le (Nat.ceil_le.mpr (le_of_lt (lt_of_lt_of_le hwz (Nat.le_ceil z')))) hz3
  rw [oddPrimLt_primeFactors, filter_oddLt_eq_sdiff hw hwz hz'M]
  exact prod_odd_range (max ⌈w⌉₊ 3) ⌈z'⌉₊ hst

end

end Work.ChenPlan.H2
