import Mathlib

namespace Work.DSM5b

theorem pow_mem_span_of_monic {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {h : A} {s : ℕ} (hs : 0 < s) (c : Fin s → R)
    (hmon : h ^ s = ∑ i : Fin s, algebraMap R A (c i) * h ^ (i : ℕ)) (m : ℕ) :
    ∃ d : Fin s → R, h ^ m = ∑ i : Fin s, algebraMap R A (d i) * h ^ (i : ℕ) := by
  -- Express every power of `h` in the span of `1, h, …, h^{s-1}` using the monic relation
  -- `h^s = ∑ c_i h^i`, by strong induction on the exponent.
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < s
    · -- Base case `m < s`: the expansion is the single term `1 · h^m`.
      refine ⟨fun i => if (i : ℕ) = m then (1 : R) else 0, ?_⟩
      have hsum :
          (∑ i : Fin s, algebraMap R A (if (i : ℕ) = m then (1 : R) else 0) * h ^ (i : ℕ))
            = h ^ m := by
        rw [Finset.sum_eq_single_of_mem (⟨m, hm⟩ : Fin s) (Finset.mem_univ _)
              (fun b _ hb => by
                have hbm : (b : ℕ) ≠ m := fun hval => hb (Fin.ext hval)
                simp [hbm])]
        simp
      exact hsum.symm
    · -- Inductive step `s ≤ m`: reduce `h^m = h^{m-s} · h^s` and use the relation.
      push Not at hm
      have hms : m - s + s = m := Nat.sub_add_cancel hm
      have hki : ∀ i : Fin s, m - s + (i : ℕ) < m := by
        intro i; have hi := i.isLt; omega
      choose e he using fun i : Fin s => ih (m - s + (i : ℕ)) (hki i)
      refine ⟨fun j => ∑ i : Fin s, c i * e i j, ?_⟩
      have h1 : h ^ (m - s) * h ^ s = h ^ m := by rw [← pow_add, hms]
      have hstep : h ^ m = ∑ i : Fin s, algebraMap R A (c i) * h ^ (m - s + (i : ℕ)) := by
        rw [← h1, hmon]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_assoc, mul_comm (h ^ (m - s)) (algebraMap R A (c i)), mul_assoc, ← pow_add]
      rw [hstep]
      have hmid : ∑ i : Fin s, algebraMap R A (c i) * h ^ (m - s + (i : ℕ))
          = ∑ i : Fin s, algebraMap R A (c i)
              * (∑ j : Fin s, algebraMap R A (e i j) * h ^ (j : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he i]
      rw [hmid]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, mul_assoc]

end Work.DSM5b
