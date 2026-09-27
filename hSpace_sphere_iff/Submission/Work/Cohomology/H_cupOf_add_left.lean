import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_cupOf_mk
import Submission.Work.Cohomology.H_cupOf_add_right

namespace Work.Cohomology

section Helpers

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- `· ⌣ v` is additive on cochains, in subtraction form. -/
lemma cupOf_sub_left {n p q : ℕ} (h : p + q = n)
    (u₁ u₂ : Submission.Cohomology.Cochain S R p) (v : Submission.Cohomology.Cochain S R q) :
    Submission.Cohomology.cupOf S R h (u₁ - u₂) v
      = Submission.Cohomology.cupOf S R h u₁ v - Submission.Cohomology.cupOf S R h u₂ v := by
  ext σ; simp [sub_mul]

/-- The cup product of classes is well defined in its first argument. -/
lemma H_mk_cupOf_congr_left {n p q : ℕ} (h : p + q = n)
    (u : Submission.Cohomology.Cochain S R p) (hu : u ∈ Submission.Cohomology.cycles S R p)
    (v : Submission.Cohomology.Cochain S R q) (hv : v ∈ Submission.Cohomology.cycles S R q)
    (u' : Submission.Cohomology.Cochain S R p) (hu' : u' ∈ Submission.Cohomology.cycles S R p)
    (hd : u - u' ∈ Submission.Cohomology.boundaries S R p) :
    Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u v)
        (Submission.Cohomology.cupOf_mem_cycles h hu hv)
      = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u' v)
        (Submission.Cohomology.cupOf_mem_cycles h hu' hv) := by
  have hsub : Submission.Cohomology.cupOf S R h u v - Submission.Cohomology.cupOf S R h u' v
      = Submission.Cohomology.cupOf S R h (u - u') v := by
    ext σ; simp [sub_mul]
  rw [Submission.Cohomology.H.mk_eq_mk_iff, hsub]
  exact cupOf_mem_boundaries_left h hd hv

/-- The computation rule for `H.cupOf` on an explicit representative of its first argument. -/
lemma H_cupOf_mk_left {n p q : ℕ} (h : p + q = n)
    (u : Submission.Cohomology.Cochain S R p) (hu : u ∈ Submission.Cohomology.cycles S R p)
    (y : Submission.Cohomology.H S R q) :
    Submission.Cohomology.H.cupOf h (Submission.Cohomology.H.mk u hu) y
      = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h hu (Quotient.out y).2) := by
  have hd : (Quotient.out (Submission.Cohomology.H.mk u hu)).1 - u
      ∈ Submission.Cohomology.boundaries S R p := by
    rw [← Submission.Cohomology.H.mk_eq_mk_iff]
    exact Submodule.Quotient.mk_out (Submission.Cohomology.H.mk u hu)
  unfold Submission.Cohomology.H.cupOf
  exact H_mk_cupOf_congr_left h (Quotient.out (Submission.Cohomology.H.mk u hu)).1
    (Quotient.out (Submission.Cohomology.H.mk u hu)).2 (Quotient.out y).1 (Quotient.out y).2
    u hu hd

end Helpers

theorem H_cupOf_add_left {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ} (h : p + q = n)
    (x₁ x₂ : Submission.Cohomology.H S R p) (y : Submission.Cohomology.H S R q) :
    Submission.Cohomology.H.cupOf h (x₁ + x₂) y
      = Submission.Cohomology.H.cupOf h x₁ y + Submission.Cohomology.H.cupOf h x₂ y := by
  have hsum : Submission.Cohomology.H.mk ((Quotient.out x₁).1 + (Quotient.out x₂).1)
      (add_mem (Quotient.out x₁).2 (Quotient.out x₂).2) = x₁ + x₂ := by
    rw [← H_mk_add (Quotient.out x₁).1 (Quotient.out x₂).1 (Quotient.out x₁).2
        (Quotient.out x₂).2, H_mk_out x₁, H_mk_out x₂]
  have hd : (Quotient.out (x₁ + x₂)).1 - ((Quotient.out x₁).1 + (Quotient.out x₂).1)
      ∈ Submission.Cohomology.boundaries S R p :=
    (Submission.Cohomology.H.mk_eq_mk_iff (Quotient.out (x₁ + x₂)).1
        ((Quotient.out x₁).1 + (Quotient.out x₂).1) (Quotient.out (x₁ + x₂)).2
        (add_mem (Quotient.out x₁).2 (Quotient.out x₂).2)).mp
      (by rw [H_mk_out (x₁ + x₂), hsum])
  calc Submission.Cohomology.H.cupOf h (x₁ + x₂) y
      = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out (x₁ + x₂)).1 (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out (x₁ + x₂)).2 (Quotient.out y).2) :=
        rfl
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h
            ((Quotient.out x₁).1 + (Quotient.out x₂).1) (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h
            (add_mem (Quotient.out x₁).2 (Quotient.out x₂).2) (Quotient.out y).2) :=
        H_mk_cupOf_congr_left h (Quotient.out (x₁ + x₂)).1 (Quotient.out (x₁ + x₂)).2
          (Quotient.out y).1 (Quotient.out y).2
          ((Quotient.out x₁).1 + (Quotient.out x₂).1)
          (add_mem (Quotient.out x₁).2 (Quotient.out x₂).2) hd
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x₁).1 (Quotient.out y).1
            + Submission.Cohomology.cupOf S R h (Quotient.out x₂).1 (Quotient.out y).1)
          (add_mem
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x₁).2 (Quotient.out y).2)
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x₂).2 (Quotient.out y).2)) := by
        rw [Submission.Cohomology.H.mk_eq_mk_iff, Submission.Cohomology.cupOf_add_left, sub_self]
        exact Submodule.zero_mem _
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x₁).1 (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x₁).2 (Quotient.out y).2)
        + Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x₂).1 (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x₂).2 (Quotient.out y).2) := by
        rw [H_mk_add]
    _ = Submission.Cohomology.H.cupOf h x₁ y + Submission.Cohomology.H.cupOf h x₂ y := by
        rw [← H_cupOf_mk_left h (Quotient.out x₁).1 (Quotient.out x₁).2 y, H_mk_out x₁,
          ← H_cupOf_mk_left h (Quotient.out x₂).1 (Quotient.out x₂).2 y, H_mk_out x₂]

end Work.Cohomology
