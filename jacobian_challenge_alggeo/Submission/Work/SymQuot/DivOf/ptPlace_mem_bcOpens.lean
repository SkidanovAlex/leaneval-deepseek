import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- **The `m`-th lifted point lies in the base-changed chart.**

If a lift `x : Fin n → C(F'')` of the point `p` of `Symⁿ C` lands in the chart open
`d.openOf = Vⁿ ⊆ Cⁿ` of a chart `d` of `p`, then its `m`-th coordinate `x m`, regarded as the
closed point `ptToPoint (x m)` of `C_{F''}`, lies in the base-changed affine chart
`bcOpens F'' d.V ⊆ C_{F''}`.

This is purely formal: `Π_m x_m` lands in `d.openOf = ⋂_m pr_m ⁻¹ᵁ V` by hypothesis, the `m`-th
coordinate of `Π_m x_m` is `x m` (`Limits.Pi.lift_comp_π`), and the projection `C_{F''} ⟶ C`
sends `ptToPoint (x m)` to `(x m).left` applied to the closed point of `Spec F''`
(because `ptLeft (x m)` is a section of that projection, `Work.SpecLin.ptLeft_fst`). -/
theorem ptPlace_mem_bcOpens {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'') (m : Fin n)
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
      ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
        Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf) :
    (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' d.V := by
  -- the lift `Π_m x_m`, as a morphism of `K`-schemes
  let L : Work.SpecLin.specOf (K := K) F'' ⟶ Work.SymQuot.prod C.toOver n := Limits.Pi.lift x
  -- its value at the closed point of `Spec F''` lies in `Vⁿ`
  have hmem : L.left (IsLocalRing.closedPoint F'') ∈ d.openOf := by
    have h1 : (IsLocalRing.closedPoint F'') ∈ L.left ⁻¹ᵁ d.openOf := h (Set.mem_univ _)
    exact (Scheme.Hom.mem_preimage _).mp h1
  -- hence the `m`-th coordinate lies in `V`
  have h2 : (Work.SymQuot.proj C.toOver n m).left (L.left (IsLocalRing.closedPoint F'')) ∈ d.V :=
    Work.SymQuot.mem_piOpen.mp hmem m
  -- the `m`-th coordinate of the lift is `x m`
  have hcomp : (Work.SymQuot.proj C.toOver n m).left (L.left (IsLocalRing.closedPoint F''))
      = (x m).left (IsLocalRing.closedPoint F'') := by
    have hlift : (L ≫ Work.SymQuot.proj C.toOver n m) = x m := Limits.Pi.lift_comp_π x m
    have hb := congrArg (fun (f : Work.SpecLin.specOf (K := K) F'' ⟶ C.toOver) =>
      f.left (IsLocalRing.closedPoint F'')) hlift
    rw [Over.comp_left] at hb
    exact hb
  rw [hcomp] at h2
  -- the projection `C_{F''} ⟶ C` sends `ptToPoint (x m)` to `(x m)` at the closed point
  have hproj : (C.baseChangeFst F'') (Work.SpecLin.ptToPoint (x m))
      = (x m).left (IsLocalRing.closedPoint F'') :=
    congrArg (fun (f : Spec (CommRingCat.of F'') ⟶ C.left) =>
      f (IsLocalRing.closedPoint F'')) (Work.SpecLin.ptLeft_fst (x m))
  change (C.baseChangeFst F'') (Work.SpecLin.ptToPoint (x m)) ∈ d.V
  rw [hproj]
  exact h2

end Work.SymQuot.DivOf
