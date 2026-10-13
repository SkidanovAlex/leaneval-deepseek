import Mathlib
import Submission.Work.DSEQP.AcDefs

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

theorem AcShift {A : Type} [CommRing A] {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsIntegral X] {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {ι : Type} [Finite ι] (S : Work.DSEQP.PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    {e j : ℕ} (h : e ≤ j) (x : (DSMap.cech A X f U).X n) :
    S.ofLvl U n j ((Work.DSEQP.PerfSetup.frobC p U n)^[j - e] x) = S.ofLvl U n e x := by
  rw [PerfSetup.ofLvl, PerfSetup.ofLvl]
  congr 1
  funext a
  rw [PerfSetup.cunpack_frobC_iter]
  exact Perf.of_f (R := Γ(X, PerfSetup.CechOp U n a)) (p := p) (hp := S.hpU _) h
    (PerfSetup.cunpack U n x a)

end Work.DSEQP
