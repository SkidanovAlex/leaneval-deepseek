import Mathlib
import Submission.Work.GroupChunk.AbelJacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics

universe u

/-- **Surjectivity of the Abel–Jacobi map `picAJ` on field points.**

Every degree-zero divisor class `c` over `F` is of the form `|divOf p - g·P0|` for some
effective divisor `p` of degree `g` on `C_F`.  Indeed, a representative `A` of `c` has degree
`0`, so `A + g·P0` has degree `g ≥ g`; by Riemann–Roch (`Input.rr7`) it is linearly equivalent
to an effective divisor `E` of degree `g`, and `E = divOf p` for a point `p` of `Sym^g C`
(`SymGeom.divOf_complete`).  Then `picAJ p = |E - g·P0| = |A| = c`. -/
theorem exists_picAJ_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] {F : Type u} [Field F] [Algebra K F]
    (c : Work.GCBasics.Pic0 C F) :
    ∃ p : Work.GCBasics.FPt (D.Sym D.g) F, D.picAJ p = c := by
  induction c using QuotientAddGroup.induction_on with
  | _ A =>
    obtain ⟨A0, hA0mem⟩ := A
    have hA0 : Work.GCBasics.Ddeg C F A0 = 0 := hA0mem
    set c0 : Work.GCBasics.Dv C F := Work.GroupChunk.bcKF F D.P0g with hc0
    have hdegc0 : Work.GCBasics.Ddeg C F c0 = (D.g : ℤ) := by
      rw [hc0, Work.GroupChunk.deg_bcKF, Work.GroupChunk.Input.P0g_deg]
    set B : Work.GCBasics.Dv C F := A0 + c0 with hB
    have hdegB : Work.GCBasics.Ddeg C F B = (D.g : ℤ) := by
      rw [hB, map_add, hA0, hdegc0, zero_add]
    obtain ⟨E, hEff, hdegE, hlin⟩ := D.rr7 B (le_of_eq hdegB.symm)
    have hdegE' : (C.baseChange F).deg E = D.g := hdegE.trans hdegB
    obtain ⟨p, hp⟩ := (D.symGeom D.g).divOf_complete E hEff hdegE'
    refine ⟨p, ?_⟩
    change Work.GCBasics.Pic0.mk (D.divOf D.g p - c0) _ = Work.GCBasics.Pic0.mk A0 hA0
    rw [Work.GCBasics.Pic0.mk_eq_iff]
    have hBsub : B - c0 = A0 := by rw [hB]; abel
    have hkey : Work.GCBasics.LinEquiv C (E - c0) (B - c0) :=
      (Work.GCBasics.LinEquiv.sub_iff E B c0).mpr hlin.symm
    rw [hBsub, ← hp] at hkey
    exact hkey

end Work.GroupChunk
