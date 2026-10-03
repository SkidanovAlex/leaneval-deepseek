/-
# `Submission.Work.FIArea7CF.sum_gnorm_fiber_le` — clash-free copy of `Submission.Work.FIArea7.Pub213.sum_gnorm_fiber_le`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.Conv6Defs
import Submission.Work.FIArea7CF.R2countDefs
import Submission.Work.FIArea7CF.r2count_upper

set_option autoImplicit false

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "gnorm" => Work.FIPlan.gnorm

/-- Bundling the sum `∑_{u ∈ s} f(|u|²)` by the fibre of the norm map does not increase the
sum, because the fibre of `M` injects into the finset of all Gaussian integers of norm `M`,
which has `r2count M` elements. -/
lemma sum_gnorm_fiber_le {s : Finset GaussianInt} {f : ℕ → ℝ} (hf : ∀ M, 0 ≤ f M)
    (Y : ℕ) (hY : ∀ u ∈ s, (Work.FIPlan.gnorm u : ℝ) ≤ (Y : ℝ))
    (hne : ∀ u ∈ s, u ≠ 0) :
    ∑ u ∈ s, f (Work.FIPlan.gnorm u)
      ≤ ∑ M ∈ Finset.Icc 1 Y, (Work.FIArea7.r2count M : ℝ) * f M := by
  -- every norm of an element of `s` lies in `Icc 1 Y`
  have hmem : ∀ u ∈ s, gnorm u ∈ Finset.Icc 1 Y := by
    intro u hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hne u hu (gnorm_eq_zero_iff.mp h)),
      by exact_mod_cast hY u hu⟩
  -- on each fibre the summand is constant
  have hfiber : ∀ M ∈ Finset.Icc 1 Y,
      (∑ u ∈ s.filter (fun u => gnorm u = M), f (gnorm u))
        = ((s.filter (fun u => gnorm u = M)).card : ℝ) * f M := by
    intro M hM
    have hconst : ∀ u ∈ s.filter (fun u => gnorm u = M), f (gnorm u) = f M :=
      fun u hu => by rw [(Finset.mem_filter.mp hu).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  calc ∑ u ∈ s, f (gnorm u)
      = ∑ M ∈ Finset.Icc 1 Y, ∑ u ∈ s.filter (fun u => gnorm u = M), f (gnorm u) :=
        (Finset.sum_fiberwise_of_maps_to hmem (fun u => f (gnorm u))).symm
    _ = ∑ M ∈ Finset.Icc 1 Y, ((s.filter (fun u => gnorm u = M)).card : ℝ) * f M :=
        Finset.sum_congr rfl hfiber
    _ ≤ ∑ M ∈ Finset.Icc 1 Y, (Work.FIArea7.r2count M : ℝ) * f M := by
        refine Finset.sum_le_sum (fun M hM => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (hf M)
        have hsub : s.filter (fun u => gnorm u = M) ⊆ Work.FIArea7.Sz M := by
          intro u hu
          rw [Finset.mem_filter] at hu
          rw [Work.FIArea7.mem_Sz_iff]
          exact ⟨hu.2, Work.FIArea7.mem_gBox_of_gnorm_eq hu.2⟩
        have h1 : (s.filter (fun u => gnorm u = M)).card ≤ Work.FIArea7.r2count M := by
          have := Finset.card_le_card hsub
          rwa [← Work.FIArea7.r2count_eq_Sz_card M] at this
        exact_mod_cast h1

end

end Work.FIArea7.Pub213
