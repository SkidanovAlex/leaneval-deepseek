import Mathlib
import Submission.Work.DSEQP.PerfRing

universe u

namespace Work.DSEQP

theorem perf_frobEquiv_symm_of (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) [CharP R p] [CharP (Work.DSEQP.Perf R p hp) p]
    [PerfectRing (Work.DSEQP.Perf R p hp) p] (i : ℕ) (x : R) :
    (frobeniusEquiv (Work.DSEQP.Perf R p hp) p).symm ((Work.DSEQP.Perf.of R p hp) i x)
      = (Work.DSEQP.Perf.of R p hp) (i + 1) x := by
  refine ((frobeniusEquiv (Work.DSEQP.Perf R p hp) p).symm_apply_eq).mpr ?_
  rw [frobeniusEquiv_def]
  exact ((Perf.of_succ_pow (R := R) (p := p) (hp := hp) i x)).symm

end Work.DSEQP
