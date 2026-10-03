/-
# `Submission.Work.FIArea7CF.Conv6Defs` — clash-free copy of `Submission.Work.FIArea7.Pub213.Conv6Defs`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→qb_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7CF.qBilinDefs

set_option autoImplicit false

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The elements of the box `Work.FIPlan.gBox R` of *nonzero* norm at most `N`. -/
def nzBox (R : ℤ) (N : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter (fun z => 0 < Work.FIPlan.gnorm z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)

lemma mem_nzBox {R : ℤ} {N : ℝ} {z : GaussianInt} :
    z ∈ nzBox R N ↔ z ∈ Work.FIPlan.gBox R ∧ 0 < Work.FIPlan.gnorm z ∧
      (Work.FIPlan.gnorm z : ℝ) ≤ N := by
  simp only [nzBox, Finset.mem_filter]

/-- The six-tuples drawn from `nzBox R N`: every tuple that can contribute to `conv6 R β` when
`β` vanishes off `{0 < |z|² ≤ N}`. -/
def nzTup (R : ℤ) (N : ℝ) : Finset (Fin 6 → GaussianInt) :=
  Fintype.piFinset (fun _ : Fin 6 => nzBox R N)

lemma mem_nzTup {R : ℤ} {N : ℝ} {t : Fin 6 → GaussianInt} :
    t ∈ nzTup R N ↔ ∀ i : Fin 6, t i ∈ nzBox R N := by
  rw [nzTup, Fintype.mem_piFinset]

/-- The number of tuples of `nzTup R N` whose product is `u`. -/
def tupCount (R : ℤ) (N : ℝ) (u : GaussianInt) : ℕ :=
  ((nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u)).card

/-- The ordered sixfold factorisations of `M`. -/
def sixFac (M : ℕ) : Finset (Fin 6 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 6 => Finset.Icc 1 M)).filter (fun m => ∏ i, m i = M)

lemma mem_sixFac {M : ℕ} {m : Fin 6 → ℕ} :
    m ∈ sixFac M ↔ (∀ i : Fin 6, m i ∈ Finset.Icc 1 M) ∧ ∏ i, m i = M := by
  simp only [sixFac, Finset.mem_filter, Fintype.mem_piFinset]

end

end Work.FIArea7.Pub213
