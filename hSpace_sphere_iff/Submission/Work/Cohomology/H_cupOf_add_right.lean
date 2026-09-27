import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology

namespace Work.Cohomology

section Helpers

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- If `b` is a coboundary in degree `q` and `u` is a `p`-cocycle, then `u ⌣ b` is a coboundary. -/
lemma cupOf_mem_boundaries_right {n p q : ℕ} (h : p + q = n)
    (u : Submission.Cohomology.Cochain S R p) (hu : u ∈ Submission.Cohomology.cycles S R p)
    (b : Submission.Cohomology.Cochain S R q) (hb : b ∈ Submission.Cohomology.boundaries S R q) :
    Submission.Cohomology.cupOf S R h u b ∈ Submission.Cohomology.boundaries S R n := by
  rcases q with _ | q
  · simp only [Submission.Cohomology.boundaries, Submodule.mem_bot] at hb
    rw [hb, Submission.Cohomology.cupOf_zero_right]
    exact Submodule.zero_mem _
  · rw [Submission.Cohomology.mem_boundaries_succ] at hb
    obtain ⟨c, hc⟩ := hb
    rw [← hc]
    exact Submission.Cohomology.cupOf_coboundary_right_mem_boundaries h hu c

/-- `u ⌣ ·` is additive on cochains, in subtraction form. -/
lemma cupOf_sub_right {n p q : ℕ} (h : p + q = n) (u : Submission.Cohomology.Cochain S R p)
    (v₁ v₂ : Submission.Cohomology.Cochain S R q) :
    Submission.Cohomology.cupOf S R h u (v₁ - v₂)
      = Submission.Cohomology.cupOf S R h u v₁ - Submission.Cohomology.cupOf S R h u v₂ := by
  ext σ; simp [mul_sub]

/-- `H.mk` of the `Quotient.out` representative of a class is that class. -/
lemma H_mk_out {n : ℕ} (x : Submission.Cohomology.H S R n) :
    Submission.Cohomology.H.mk (Quotient.out x).1 (Quotient.out x).2 = x :=
  Submodule.Quotient.mk_out x

/-- `H.mk` is additive. -/
lemma H_mk_add {n : ℕ} (u v : Submission.Cohomology.Cochain S R n)
    (hu : u ∈ Submission.Cohomology.cycles S R n) (hv : v ∈ Submission.Cohomology.cycles S R n) :
    Submission.Cohomology.H.mk u hu + Submission.Cohomology.H.mk v hv
      = Submission.Cohomology.H.mk (u + v) (add_mem hu hv) := by
  unfold Submission.Cohomology.H.mk
  rw [← Submodule.Quotient.mk_add]
  rfl

/-- The cup product of classes is well defined in its second argument. -/
lemma H_mk_cupOf_congr_right {n p q : ℕ} (h : p + q = n)
    (u : Submission.Cohomology.Cochain S R p) (hu : u ∈ Submission.Cohomology.cycles S R p)
    (v : Submission.Cohomology.Cochain S R q) (hv : v ∈ Submission.Cohomology.cycles S R q)
    (v' : Submission.Cohomology.Cochain S R q) (hv' : v' ∈ Submission.Cohomology.cycles S R q)
    (hd : v - v' ∈ Submission.Cohomology.boundaries S R q) :
    Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u v)
        (Submission.Cohomology.cupOf_mem_cycles h hu hv)
      = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u v')
        (Submission.Cohomology.cupOf_mem_cycles h hu hv') := by
  have hsub : Submission.Cohomology.cupOf S R h u v - Submission.Cohomology.cupOf S R h u v'
      = Submission.Cohomology.cupOf S R h u (v - v') := by
    ext σ; simp [mul_sub]
  rw [Submission.Cohomology.H.mk_eq_mk_iff, hsub]
  exact cupOf_mem_boundaries_right h u hu (v - v') hd

/-- The computation rule for `H.cupOf` on an explicit representative of its second argument. -/
lemma H_cupOf_mk_right {n p q : ℕ} (h : p + q = n)
    (x : Submission.Cohomology.H S R p)
    (v : Submission.Cohomology.Cochain S R q) (hv : v ∈ Submission.Cohomology.cycles S R q) :
    Submission.Cohomology.H.cupOf h x (Submission.Cohomology.H.mk v hv)
      = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h (Quotient.out x).1 v)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 hv) := by
  have hd : (Quotient.out (Submission.Cohomology.H.mk v hv)).1 - v
      ∈ Submission.Cohomology.boundaries S R q := by
    rw [← Submission.Cohomology.H.mk_eq_mk_iff]
    exact Submodule.Quotient.mk_out (Submission.Cohomology.H.mk v hv)
  unfold Submission.Cohomology.H.cupOf
  exact H_mk_cupOf_congr_right h (Quotient.out x).1 (Quotient.out x).2
    (Quotient.out (Submission.Cohomology.H.mk v hv)).1
    (Quotient.out (Submission.Cohomology.H.mk v hv)).2 v hv hd

end Helpers

theorem H_cupOf_add_right {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ} (h : p + q = n)
    (x : Submission.Cohomology.H S R p) (y₁ y₂ : Submission.Cohomology.H S R q) :
    Submission.Cohomology.H.cupOf h x (y₁ + y₂)
      = Submission.Cohomology.H.cupOf h x y₁ + Submission.Cohomology.H.cupOf h x y₂ := by
  have hsum : Submission.Cohomology.H.mk ((Quotient.out y₁).1 + (Quotient.out y₂).1)
      (add_mem (Quotient.out y₁).2 (Quotient.out y₂).2) = y₁ + y₂ := by
    rw [← H_mk_add (Quotient.out y₁).1 (Quotient.out y₂).1 (Quotient.out y₁).2
        (Quotient.out y₂).2,
      H_mk_out y₁, H_mk_out y₂]
  have hd : (Quotient.out (y₁ + y₂)).1 - ((Quotient.out y₁).1 + (Quotient.out y₂).1)
      ∈ Submission.Cohomology.boundaries S R q :=
    (Submission.Cohomology.H.mk_eq_mk_iff (Quotient.out (y₁ + y₂)).1
        ((Quotient.out y₁).1 + (Quotient.out y₂).1) (Quotient.out (y₁ + y₂)).2
        (add_mem (Quotient.out y₁).2 (Quotient.out y₂).2)).mp
      (by rw [H_mk_out (y₁ + y₂), hsum])
  calc Submission.Cohomology.H.cupOf h x (y₁ + y₂)
      = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out (y₁ + y₂)).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out (y₁ + y₂)).2) :=
        rfl
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x).1
            ((Quotient.out y₁).1 + (Quotient.out y₂).1))
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2
            (add_mem (Quotient.out y₁).2 (Quotient.out y₂).2)) :=
        H_mk_cupOf_congr_right h (Quotient.out x).1 (Quotient.out x).2
          (Quotient.out (y₁ + y₂)).1 (Quotient.out (y₁ + y₂)).2
          ((Quotient.out y₁).1 + (Quotient.out y₂).1)
          (add_mem (Quotient.out y₁).2 (Quotient.out y₂).2) hd
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y₁).1
            + Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y₂).1)
          (add_mem
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y₁).2)
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y₂).2)) := by
        rw [Submission.Cohomology.H.mk_eq_mk_iff, Submission.Cohomology.cupOf_add_right, sub_self]
        exact Submodule.zero_mem _
    _ = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y₁).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y₁).2)
        + Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y₂).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y₂).2) := by
        rw [H_mk_add]
    _ = Submission.Cohomology.H.cupOf h x y₁ + Submission.Cohomology.H.cupOf h x y₂ := by
        rw [← H_cupOf_mk_right h x (Quotient.out y₁).1 (Quotient.out y₁).2, H_mk_out y₁,
          ← H_cupOf_mk_right h x (Quotient.out y₂).1 (Quotient.out y₂).2, H_mk_out y₂]

end Work.Cohomology
