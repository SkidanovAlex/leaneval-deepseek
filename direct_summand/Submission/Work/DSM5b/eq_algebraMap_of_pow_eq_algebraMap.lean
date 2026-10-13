import Mathlib

namespace Work.DSM5b

/-- If `R` is a perfect ring of prime characteristic `p` and `A` is a reduced `R`-algebra,
then any `x : A` whose `p ^ n`-th power lies in the image of `R` already lies in the image
of `R`. -/
theorem eq_algebraMap_of_pow_eq_algebraMap (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R]
    [CharP R p] [PerfectRing R p] {A : Type*} [CommRing A] [Algebra R A] [IsReduced A]
    (x : A) (n : ℕ) (r : R) (h : x ^ (p ^ n) = algebraMap R A r) :
    ∃ r' : R, x = algebraMap R A r' := by
  by_cases hA : Subsingleton A
  · exact ⟨0, Subsingleton.elim x _⟩
  · have hNontrivial : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    -- `A` inherits characteristic `p` from `R`, hence satisfies `CharP A p`.
    have hCharA : CharP A p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime p)).mpr (by
        rw [← map_natCast (algebraMap R A), CharP.cast_eq_zero R p, map_zero])
    -- Perfection of `R` provides a `p ^ n`-th root of `r` inside `R`.
    obtain ⟨s, hs⟩ : ∃ s : R, s ^ p ^ n = r :=
      ⟨(iterateFrobeniusEquiv R p n).symm r, by
        rw [← iterateFrobeniusEquiv_def]
        exact (iterateFrobeniusEquiv R p n).apply_symm_apply r⟩
    refine ⟨s, ?_⟩
    -- Freshman's dream in characteristic `p`: `(x - s) ^ (p ^ n) = x ^ (p ^ n) - s ^ (p ^ n) = 0`.
    have hzero : (x - algebraMap R A s) ^ p ^ n = 0 := by
      rw [sub_pow_char_pow, h, ← map_pow, hs, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)

end Work.DSM5b
