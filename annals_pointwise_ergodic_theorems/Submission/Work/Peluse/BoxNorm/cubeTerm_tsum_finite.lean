import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The cube term of the box norm has finite support

Peluse's box-norm power `boxSumPow` is defined through the `tsum` over all of `ℤ` of the cube term
`∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')` (see `Work.Peluse.cubeTerm`).

When `f` is supported in `[-N,N]` (in the sense of `Work.Peluse.SupportIn`) and the steps
`h i`, `h' i` lie in the finite sets `Q i`, every corner of the cube satisfies

`|ω·h + (1-ω)·h'| ≤ ∑ i, ∑_{z ∈ Q i} |z|`,

so the cube term vanishes at all but finitely many `x`.  This file identifies the `tsum` with the
finite sum over the interval `[-M, M]` with `M = N + ∑ i, ∑_{z ∈ Q i} |z|`.

## Main results

* `Work.Peluse.BoxNorm.natAbs_sum_le`: the triangle inequality for a finite sum of integers;
* `Work.Peluse.BoxNorm.star_iterate_zero_eq_zero`: iterated conjugation kills `0`;
* `Work.Peluse.BoxNorm.cornerShift_natAbs_le`: the corner bound;
* `Work.Peluse.BoxNorm.cubeTerm_tsum_finite`: the `tsum` is the finite sum over `[-M, M]`.
-/

namespace Work.Peluse.BoxNorm

open scoped BigOperators

/-- The triangle inequality for a finite sum of integers:
`|∑_{i ∈ s} g i| ≤ ∑_{i ∈ s} |g i|`, written with `Int.natAbs`. -/
lemma natAbs_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℤ) :
    (∑ i ∈ s, g i).natAbs ≤ ∑ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc (g a + ∑ i ∈ s, g i).natAbs
          ≤ (g a).natAbs + (∑ i ∈ s, g i).natAbs := Int.natAbs_add_le _ _
        _ ≤ (g a).natAbs + ∑ i ∈ s, (g i).natAbs := Nat.add_le_add_left ih _

/-- Iterated conjugation kills `0`. -/
lemma star_iterate_zero_eq_zero (k : ℕ) : (star^[k]) (0 : ℂ) = 0 := by
  induction k with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; simp

/-- Every corner `ω·h + (1-ω)·h'` of the cube lies within distance
`∑ i, ∑_{z ∈ Q i} |z|` of the origin, whenever the steps `h i`, `h' i` lie in `Q i`. -/
lemma cornerShift_natAbs_le {t : ℕ} (Q : Fin t → Finset ℤ)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) (ω : Fin t → Bool) :
    (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω).natAbs
      ≤ ∑ i, (Q i).sum (fun z => z.natAbs) := by
  rw [Work.Peluse.cornerShift]
  calc (∑ i : Fin t, (if ω i then (h i).1 else (h' i).1)).natAbs
      ≤ ∑ i : Fin t, (if ω i then (h i).1 else (h' i).1).natAbs :=
        natAbs_sum_le _ _
    _ ≤ ∑ i : Fin t, (Q i).sum (fun z => z.natAbs) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : ω i
        · simp only [hi, if_true]
          exact Finset.single_le_sum (fun z _ => Nat.zero_le _) (h i).2
        · simp only [hi]
          exact Finset.single_le_sum (fun z _ => Nat.zero_le _) (h' i).2

theorem cubeTerm_tsum_finite {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) {N : ℕ}
    (hN : Work.Peluse.SupportIn f N)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = ∑ x ∈ Finset.Icc (-(((N + ∑ i, (Q i).sum (fun z => z.natAbs)) : ℕ) : ℤ))
            (((N + ∑ i, (Q i).sum (fun z => z.natAbs)) : ℕ) : ℤ),
          ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) := by
  classical
  set S : ℕ := ∑ i, (Q i).sum (fun z => z.natAbs) with hS
  set M : ℕ := N + S with hM
  have hvan : ∀ x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ),
      (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) ?_
    have hcs : (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
        (fun _ : Fin t => false)).natAbs ≤ S := by
      rw [hS]
      exact cornerShift_natAbs_le Q h h' _
    have hxM : M < x.natAbs := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hx
      omega
    have htri : x.natAbs ≤ (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
        (fun _ : Fin t => false)).natAbs
          + (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
              (fun _ : Fin t => false)).natAbs := by
      have h := Int.natAbs_add_le
        (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) (fun _ : Fin t => false))
        (-(Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) (fun _ : Fin t => false)))
      simpa using h
    have hlt : N < (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
        (fun _ : Fin t => false)).natAbs := by
      omega
    rw [hN _ hlt, star_iterate_zero_eq_zero]
  rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) hvan]

end Work.Peluse.BoxNorm
