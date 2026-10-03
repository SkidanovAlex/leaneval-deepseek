import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea7.P231.quadEigen_triple

namespace Work.FIArea7.P231

/-- If `m` and `n` are not coprime, the double sum of the `ε`-summand over `primarySet m ×
primarySet n` vanishes: every term is either killed by the Gauss-coprimality guard in
`epsSummand`, or has `w, z` Gauss-coprime with `gnorm w = m`, `gnorm z = n` and hence
`[wz] = 0` by `JKSym_mul_eq_zero_of_not_coprime_gnorm`. -/
lemma epsSummand_sum_eq_zero_of_not_coprime {m n : ℕ} (hmn : ¬ Nat.Coprime m n)
    (e : GaussianInt) (A B : GaussianInt → ℂ) :
    ∑ w ∈ Work.FIArea7.primarySet m, ∑ z ∈ Work.FIArea7.primarySet n,
      Work.FIArea7.epsSummand e A B w z = 0 := by
  refine Finset.sum_eq_zero (fun w hw => ?_)
  refine Finset.sum_eq_zero (fun z hz => ?_)
  rw [Work.FIArea7.epsSummand]
  split_ifs with hcop
  · have hwP : Work.FIPlan.IsPrimary w := Work.FIArea7.isPrimary_of_mem_primarySet hw
    have hzP : Work.FIPlan.IsPrimary z := Work.FIArea7.isPrimary_of_mem_primarySet hz
    have hnc : ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) := by
      rw [Work.FIArea7.gnorm_of_mem_primarySet hw,
        Work.FIArea7.gnorm_of_mem_primarySet hz]
      exact hmn
    rw [Work.FIArea7.JKSym_mul_eq_zero_of_not_coprime_gnorm hwP hzP hcop hnc, mul_zero,
      mul_zero]
  · rfl

end Work.FIArea7.P231
