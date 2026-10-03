/-
# `Submission.Work.FIArea7CF.nzTup_filter_prod_subset_piFinset` — clash-free copy of `Submission.Work.FIArea7.Pub213.nzTup_filter_prod_subset_piFinset`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.Conv6Defs
import Submission.Work.FIArea7CF.R2countDefs

namespace Work.FIArea7.Pub213

theorem nzTup_filter_prod_subset_piFinset (R : ℤ) (N : ℝ) (u : GaussianInt) (hu : u ≠ 0) :
    (Work.FIArea7.Pub213.nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u)
      ⊆ Fintype.piFinset (fun _ : Fin 6 =>
          (Work.FIPlan.gnorm u).divisors.biUnion (fun m => Work.FIArea7.Sz m)) := by
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, htu⟩ := ht
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_biUnion]
  refine ⟨Work.FIPlan.gnorm (t i), ?_, Work.FIArea7.mem_Sz_of_gnorm_eq rfl⟩
  rw [Nat.mem_divisors]
  refine ⟨?_, ?_⟩
  · have hgn : Work.FIPlan.gnorm u = ∏ j : Fin 6, Work.FIPlan.gnorm (t j) := by
      rw [← htu, Work.FIArea7.tupProd, Work.FIArea7.gnorm_prod_univ]
    rw [hgn]
    exact Finset.dvd_prod_of_mem (fun j => Work.FIPlan.gnorm (t j)) (Finset.mem_univ i)
  · intro h0
    exact hu (Work.FIArea7.gnorm_eq_zero_iff.mp h0)

end Work.FIArea7.Pub213
