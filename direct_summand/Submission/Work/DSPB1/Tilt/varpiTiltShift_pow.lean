import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSPB1.Basic

namespace Work.DSPB1.Tilt

/-- In a perfect ring of characteristic `p`, iterated `p`-th roots undo `p`-powering:
the `p ^ k`-th power of the `k`-fold Frobenius root of `x` is `x`.

This is the ring-theoretic core of `Work.DSPB1.Tilt.varpiTiltShift_pow`: `varpiTiltShift P k`
is the `k`-fold Frobenius root of `varpiTilt P` (`Work.DSPB1.varpiTiltShift_eq_symm`). -/
theorem pow_frobeniusEquiv_symm_iterate {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]
    [PerfectRing R p] (k : ℕ) (x : R) :
    ((frobeniusEquiv R p).symm^[k] x) ^ p ^ k = x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem varpiTiltShift_pow {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    [Fact ¬IsUnit (p : C)] (P : DSMap.PerfectoidData p C) (k : ℕ) :
    (Work.DSPB1.varpiTiltShift P k) ^ p ^ k = Work.DSPB1.varpiTilt P := by
  rw [Work.DSPB1.varpiTiltShift_eq_symm]
  exact pow_frobeniusEquiv_symm_iterate k (Work.DSPB1.varpiTilt P)

end Work.DSPB1.Tilt
