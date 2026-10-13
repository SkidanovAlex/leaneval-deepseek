import Mathlib
import Submission.Work.WilG4a.lip_loci_defs
import Submission.Work.WilG4a.Sset_explicit

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-- Reading `derSet` at a point of the form `Fin.snoc x s`: `s` is the slice derivative
of `f` at `x` iff `HasDerivAt (sliceFun f x) s (x (last))`. -/
theorem mem_derSet_snoc (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (x : Fin (p + 1) → ℝ) (s : ℝ) :
    Fin.snoc x s ∈ derSet f ↔ HasDerivAt (sliceFun f x) s (x (Fin.last p)) := by
  rw [mem_derSet]
  simp only [IsSliceDeriv]
  simp

/-- The projection of `derSet f` onto the parameter-and-variable coordinates is exactly the
differentiability locus `sliceDiff f` of the slice. -/
theorem projLast_derSet_eq (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) :
    projLast (derSet f) = sliceDiff f := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs⟩
    exact (mem_derSet_snoc p f x s).mp hs |>.differentiableAt
  · intro hd
    exact ⟨deriv (sliceFun f x) (x (Fin.last p)), (mem_derSet_snoc p f x _).mpr hd.hasDerivAt⟩

theorem sliceDiff_mem (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        Work.WilG4a.sliceDiff f ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨Work.WilG1.Plumb.AFR (p + 1) F0 + 1 + 1,
    Polynomial.C 2 * Polynomial.X +
      Polynomial.C (2 * Work.WilG1.Plumb.KK (p + 1) + (p + 1) * 4 + 80), ?_⟩
  intro D f hf
  -- The derivative set `derSet f = Sset (p+1) (last p) (famFun f)` is an `Ω`-set with the
  -- explicit format and degree of `Sset_explicit`.
  have hS : derSet f ∈ S.Ω (Work.WilG1.Plumb.AFR (p + 1) F0 + 1)
      ((Polynomial.C 2 * Polynomial.X +
        Polynomial.C (2 * Work.WilG1.Plumb.KK (p + 1) + (p + 1) * 4 + 80)).eval D)
      (p + 2) := by
    have h := Sset_explicit (S := S) (N := p + 1) (F := F0) (D := D) (f := famFun f)
      (Fin.last p) hf
    simpa [derSet] using h
  -- Project the derivative coordinate away: `projLast (derSet f) = sliceDiff f`.
  rw [← projLast_derSet_eq p f]
  exact S.proj hS

end Work.WilG4a
