import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.CapThetaLift
import Submission.Work.Pi6.MSSK.mono_fibreInc
import Submission.Work.Pi6.MSSK.fibreIncCapThetaLift
import Submission.Work.Pi6.MSSK.capThetaLift_isCycle
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

/-!
# `capThetaLiftZeroCyc`

A cycle `x` of the pull-back `T_σ = Δ[s] ×_{Sing B} Sing E` has the property that the chain-level
lift `capThetaLift' R p σ K x` of the cap product with `thetaTop` is again a cycle.  This does not
depend on the extra hypothesis `hcap` of `capThetaLiftZeroCyc` (which records that the cap product
of `c` with `thetaTop` is `c` itself): the lift of *any* cycle is a cycle, because `fibreInc` is a
monomorphism of simplicial sets and carries the lift to the cap product `thetaTop ⌢ x`, which is a
cycle by the boundary formula for the cap product (`cap_d`) and `thetaTop_cocycle`.

For `K ≥ 1` this is exactly `capThetaLift_isCycle` with `y = 0`; for `K = 0` the differential
`d 0 (next 0)` of a chain complex indexed by `ℕ` is zero by the shape of `ComplexShape.down ℕ`.
-/

/-- **A cycle lifts to a cycle**: if `x` is a cycle of the chains of `T_σ` in degree `s + K`, then
`capThetaLift' R p σ K x` is a cycle of the chains of `T_{σ(s)}`. -/
lemma capThetaLift_zero_of_cycle {R : Type} [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + K))
    (hx : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s+K) ((ComplexShape.down ℕ).next (s+K)))) x = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).d K ((ComplexShape.down ℕ).next K)))
      (Work.Pi6.MSSK.capThetaLift' R p σ K x) = 0 := by
  cases K with
  | zero =>
    -- In degree `0` the differential `d 0 (next 0) = d 0 0` is zero by the shape.
    rw [ChainComplex.next_nat_zero]
    rw [HomologicalComplex.shape
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (Work.Pi6.MSSK.lastV s ≫ σ)))
      0 0 ?_]
    · simp
    · intro h
      exact Nat.noConfusion h
  | succ j =>
    -- In positive degrees apply `capThetaLift_isCycle` with the zero chain of the boundary
    -- subcomplex, using that `x` is a cycle.
    have hnext : (ComplexShape.down ℕ).next (s + (j+1)) = s + j := by
      rw [← Nat.add_assoc s j 1]
      exact ChainComplex.next_nat_succ (s + j)
    have hnext' : (ComplexShape.down ℕ).next (j+1) = j := ChainComplex.next_nat_succ j
    have h := Work.Pi6.MSSK.capThetaLift_isCycle R p σ x
        (0 : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X (s + j)) ?_
    · rw [hnext']
      exact h
    · rw [hnext] at hx
      simp only [map_zero]
      exact hx.symm

theorem capThetaLiftZeroCyc {R : Type} [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k))
    (hc : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0+k) ((ComplexShape.down ℕ).next (0+k)))) c = 0)
    (hcap : Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) (Work.Pi6.MSSK.thetaTop R p σ) k c
        = Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) (Nat.zero_add k) c) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).d k ((ComplexShape.down ℕ).next k)))
      (Work.Pi6.MSSK.capThetaLift' R p σ k c) = 0 := by
  exact capThetaLift_zero_of_cycle p σ k c hc

end Work.Pi6.MSSK
