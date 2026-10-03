import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.prop232Defs

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

/-- For `m ≤ M` the `gnorm`-fibre of `primaryDisc M` is exactly the set `primarySet m` of
primary elements of norm `m`. -/
lemma primaryDisc_filter_gnorm_eq (M m : ℕ) (hm : m ≤ M) :
    (Work.FIArea7.primaryDisc M).filter (fun z => Work.FIPlan.gnorm z = m)
      = Work.FIArea7.primarySet m := by
  ext z
  simp only [Finset.mem_filter, Work.FIArea7.mem_primaryDisc, Work.FIArea7.mem_primarySet]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hm⟩, h3⟩

/-- The disc `primaryDisc M` is the disjoint union of the norm fibres `primarySet m` for
`1 ≤ m ≤ M`; consequently any sum over it decomposes fibre by fibre. -/
lemma sum_primaryDisc_eq (M : ℕ) (f : GaussianInt → ℂ) :
    ∑ w ∈ Work.FIArea7.primaryDisc M, f w
      = ∑ m ∈ Finset.Icc 1 M, ∑ w ∈ Work.FIArea7.primarySet m, f w := by
  have h : ∀ i ∈ Work.FIArea7.primaryDisc M, Work.FIPlan.gnorm i ∈ Finset.Icc 1 M := by
    intro i hi
    rw [Finset.mem_Icc]
    have hprim : Work.FIPlan.IsPrimary i := (Work.FIArea7.mem_primaryDisc.mp hi).1
    have hle : Work.FIPlan.gnorm i ≤ M := (Work.FIArea7.mem_primaryDisc.mp hi).2
    obtain ⟨k, hk⟩ := Work.FIArea7.odd_gnorm_of_isPrimary hprim
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (s := Work.FIArea7.primaryDisc M)
        (t := Finset.Icc 1 M) (g := Work.FIPlan.gnorm) h f]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [primaryDisc_filter_gnorm_eq M m (Finset.mem_Icc.mp hm).2]

lemma sum_primaryDisc_two (M N : ℕ) (F : GaussianInt → GaussianInt → ℂ) :
    ∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N, F w z
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∑ w ∈ Work.FIArea7.primarySet m, ∑ z ∈ Work.FIArea7.primarySet n, F w z := by
  rw [sum_primaryDisc_eq M (fun w => ∑ z ∈ Work.FIArea7.primaryDisc N, F w z)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show (∑ w ∈ Work.FIArea7.primarySet m, ∑ z ∈ Work.FIArea7.primaryDisc N, F w z)
        = ∑ w ∈ Work.FIArea7.primarySet m, ∑ n ∈ Finset.Icc 1 N,
            ∑ z ∈ Work.FIArea7.primarySet n, F w z from
      Finset.sum_congr rfl (fun w _ => sum_primaryDisc_eq N (F w))]
  exact Finset.sum_comm

end Work.FIArea7.P231
