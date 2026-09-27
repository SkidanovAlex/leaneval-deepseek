import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_cupOf_mk

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-!
# Left scalar compatibility of the cup product on cohomology

The cohomology `H S R n` is the quotient of the `n`-cocycles by the `n`-coboundaries, and the cup
product `H.cupOf` is defined on classes by choosing representatives with `Quot.out`.  This file
proves that `H.cupOf h · y` is `R`-linear in its first argument:

`(r • x) ⌣ y = r • (x ⌣ y)`.

The proof has two ingredients:

* `HCupOfSmulLeft_H_mk_smul`, the compatibility of `H.mk` with scalar multiplication (a direct
  consequence of `Submodule.Quotient.mk_smul` for the quotient of the cocycles);
* the well-definedness of `· ⌣ y` up to coboundaries, which reduces to the chain–level fact that
  the cup product of a coboundary with a cocycle is a coboundary
  (`Submission.Work.Cohomology.cupOf_mem_boundaries_left`).
-/

section Helpers

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- `H.mk` is compatible with scalar multiplication: the class of `r • u` is `r` times the class
of `u`. -/
lemma HCupOfSmulLeft_H_mk_smul {n : ℕ} (r : R) (u : Submission.Cohomology.Cochain S R n)
    (hu : u ∈ Submission.Cohomology.cycles S R n) :
    r • Submission.Cohomology.H.mk u hu
      = Submission.Cohomology.H.mk (r • u) (Submodule.smul_mem _ r hu) := by
  rw [Submission.Cohomology.H.mk, ← Submodule.Quotient.mk_smul]
  rfl

/-- `H.mk` of the `Quotient.out` representative of a class is that class. -/
lemma HCupOfSmulLeft_H_mk_out {n : ℕ} (x : Submission.Cohomology.H S R n) :
    Submission.Cohomology.H.mk (Quotient.out x).1 (Quotient.out x).2 = x :=
  Submodule.Quotient.mk_out x

/-- The cup product at cochain level is additive in its first argument, in subtraction form. -/
lemma HCupOfSmulLeft_cupOf_sub_left {n p q : ℕ} (h : p + q = n)
    (u₁ u₂ : Submission.Cohomology.Cochain S R p)
    (v : Submission.Cohomology.Cochain S R q) :
    Submission.Cohomology.cupOf S R h (u₁ - u₂) v
      = Submission.Cohomology.cupOf S R h u₁ v - Submission.Cohomology.cupOf S R h u₂ v := by
  ext σ; simp [sub_mul]

end Helpers

theorem H_cupOf_smul_left {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ} (h : p + q = n)
    (r : R) (x : Submission.Cohomology.H S R p) (y : Submission.Cohomology.H S R q) :
    Submission.Cohomology.H.cupOf h (r • x) y = r • Submission.Cohomology.H.cupOf h x y := by
  -- The representative chosen for `r • x` differs from `r • (Quotient.out x).1` by a coboundary.
  have hzr : (Quotient.out (r • x)).1 - r • (Quotient.out x).1
      ∈ Submission.Cohomology.boundaries S R p := by
    rw [← Submission.Cohomology.H.mk_eq_mk_iff (Quotient.out (r • x)).1 (r • (Quotient.out x).1)
        (Quotient.out (r • x)).2 (Submodule.smul_mem _ r (Quotient.out x).2)]
    rw [HCupOfSmulLeft_H_mk_out (r • x),
      ← HCupOfSmulLeft_H_mk_smul r (Quotient.out x).1 (Quotient.out x).2,
      HCupOfSmulLeft_H_mk_out x]
  -- Rewrite the right hand side to an explicit representative.
  have hR : r • Submission.Cohomology.H.cupOf h x y
      = Submission.Cohomology.H.mk
          (r • Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y).1)
          (Submodule.smul_mem _ r
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y).2)) := by
    rw [show Submission.Cohomology.H.cupOf h x y
        = Submission.Cohomology.H.mk
            (Submission.Cohomology.cupOf S R h (Quotient.out x).1 (Quotient.out y).1)
            (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out x).2 (Quotient.out y).2) from rfl]
    rw [HCupOfSmulLeft_H_mk_smul]
  rw [hR]
  rw [show Submission.Cohomology.H.cupOf h (r • x) y
      = Submission.Cohomology.H.mk
          (Submission.Cohomology.cupOf S R h (Quotient.out (r • x)).1 (Quotient.out y).1)
          (Submission.Cohomology.cupOf_mem_cycles h (Quotient.out (r • x)).2 (Quotient.out y).2)
      from rfl]
  -- It now suffices to compare the two cochains modulo coboundaries.
  rw [Submission.Cohomology.H.mk_eq_mk_iff]
  rw [← Submission.Cohomology.cupOf_smul_left]
  rw [← HCupOfSmulLeft_cupOf_sub_left]
  exact cupOf_mem_boundaries_left h hzr (Quotient.out y).2

end Work.Cohomology
