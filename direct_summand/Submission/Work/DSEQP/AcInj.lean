import Mathlib
import Submission.Work.DSEQP.AcDefs

namespace Work.DSEQP

universe u

open scoped AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace Perf

/-- For a reduced ring `R` of characteristic `p`, the level-`i` map `R → R^{1/p^i} → R^{1/p^∞}`
is injective: the `p^i`-th root of an element is unique (in a reduced ring a `p`-th power that
vanishes forces the element to vanish). -/
theorem of_injective_of_isReduced {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp : (p : R) = 0) [IsReduced R] (i : ℕ) : Function.Injective (of R p hp i) := by
  intro x y h
  have hz : of R p hp i (x - y) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (of_eq_zero R p hp hz)

end Perf

open PerfSetup

/-- The level-`e` map `ofLvl` from the ordinary Čech complex to the perfected one is injective
in every degree: both `kpack` (the component decomposition) and the perfection map `Perf.of`
are injective, the latter because the sections of an integral scheme over an open are reduced. -/
theorem AcInj {A : Type} [CommRing A] {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsIntegral X] {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {ι : Type} [Finite ι] (S : Work.DSEQP.PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) (h : S.ofLvl U n e x = 0) : x = 0 := by
  have hstep : ∀ a, Perf.of (Γ(X, CechOp U n a)) p (S.hpU _) e
      (PerfSetup.cunpack U n x a) = 0 := by
    intro a
    have hk := congrFun (congrArg (S.kunpack U n) h) a
    rw [PerfSetup.kunpack_ofLvl] at hk
    rw [PerfSetup.kunpack_apply] at hk
    exact hk.trans (map_zero _)
  have hcu : ∀ a, PerfSetup.cunpack U n x a = 0 := fun a =>
    Perf.of_injective_of_isReduced (S.hpU _) e (by rw [hstep a, map_zero])
  have hy : PerfSetup.cunpack U n x = 0 := funext hcu
  have hzero : PerfSetup.cunpack U n (0 : (DSMap.cech A X f U).X n) = 0 := by
    funext a
    rw [PerfSetup.cunpack_apply]
    exact map_zero _
  calc x = PerfSetup.cpack U n (PerfSetup.cunpack U n x) := (PerfSetup.cpack_cunpack U n x).symm
    _ = PerfSetup.cpack U n 0 := by rw [hy]
    _ = PerfSetup.cpack U n (PerfSetup.cunpack U n (0 : (DSMap.cech A X f U).X n)) := by
        rw [hzero]
    _ = 0 := PerfSetup.cpack_cunpack U n 0

end Work.DSEQP
