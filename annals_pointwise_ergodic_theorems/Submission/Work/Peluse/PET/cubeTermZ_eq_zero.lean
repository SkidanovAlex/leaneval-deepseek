import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

namespace Work.Peluse.PET

open scoped BigOperators

/-- The cube term of Peluse's box norm vanishes at every `x` outside the ball
`[-rad, rad]`, `rad = N + ∑ i, ∑_{z ∈ Q i} |z|`: every corner `x + ω·h + (1-ω)·h'` then lies
outside the support `[-N,N]` of `f`, so each of the `2^t` factors of the product is zero. -/
theorem cubeTermZ_eq_zero {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) {N : ℕ}
    (hN : Work.Peluse.SupportIn f N) (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) {x : ℤ}
    (hx : x ∉ Work.Peluse.BoxNorm.ball t Q N) :
    Work.Peluse.BoxNorm.cubeTermZ Q f h h' x = 0 := by
  classical
  have hxrad : Work.Peluse.BoxNorm.rad t Q N < x.natAbs := by
    have h := hx
    simp only [Work.Peluse.BoxNorm.ball, Finset.mem_Icc, not_and_or, not_le] at h
    omega
  have hzero : ∀ ω : Fin t → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) = 0 := by
    intro ω
    have hcs : (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω).natAbs + N
        ≤ Work.Peluse.BoxNorm.rad t Q N := by
      have h1 := Work.Peluse.BoxNorm.cornerShift_natAbs_le Q h h' ω
      rw [Work.Peluse.BoxNorm.rad]
      omega
    have htri : x.natAbs
        ≤ (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω).natAbs
          + (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω).natAbs := by
      have h := Int.natAbs_add_le
        (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)
        (-(Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))
      simpa using h
    have hlt : N
        < (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω).natAbs := by
      omega
    rw [hN _ hlt, Work.Peluse.BoxNorm.star_iterate_zero_eq_zero]
  rw [Work.Peluse.BoxNorm.cubeTermZ]
  exact Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) (hzero _)

end Work.Peluse.PET
