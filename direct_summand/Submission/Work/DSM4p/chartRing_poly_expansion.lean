import Mathlib
import Submission.Work.DSM4p.Chart

namespace Work.DSM4p

theorem chartRing_poly_expansion {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {G T : ℕ → R}
    (hG : Work.DSM4p.IsRootSystem p G) (hT : Work.DSM4p.IsRootSystem p T) (N : ℕ)
    (r : Work.DSM4p.chartRing hG T N) :
    ∃ P : MvPolynomial ℕ R,
      r = ∑ μ ∈ P.support, algebraMap R (Work.DSM4p.chartRing hG T N) (P.coeff μ) *
        ∏ j ∈ μ.support,
          (⟨Work.DSM4p.chartGen hG T N j, Work.DSM4p.chartGen_mem hG T N j⟩ :
            Work.DSM4p.chartRing hG T N) ^ (μ j) := by
  obtain ⟨P, hP⟩ := Work.DSM4p.chartLevel_mem_aeval_range hG T N r
  refine ⟨P, ?_⟩
  apply Subtype.ext
  rw [← hP, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  push_cast
  rfl

end Work.DSM4p
