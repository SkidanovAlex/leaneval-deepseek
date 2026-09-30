import Mathlib
import Submission.Work.KeyLemma.SymPow
import Submission.Work.KeyLemma.Sum.exists_enum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators Classical MonObj MonoidalCategory CartesianMonoidalCategory

namespace Work.KeyLemma.Curve

universe u

/-- **The sum map on a divisor which is presented by a multiset of `k`-points agrees with the
multiset sum.**  If `s` is a multiset of `k`-points of `C` whose attached divisor `toDiv C s` is
the effective divisor `E` of degree `n` on the nose, then the value of the sum morphism
`Φ : Sym^n C ⟶ A` at the point of `Sym^n C` classified by `E` is the sum `Σ f(s)` of the images
of the points of `s`.

The proof enumerates the multiset `s` (of total mass `n`) as a family
`x : Fin n → Point C` (`Work.KeyLemma.Sum.exists_enum`), so that `s = ∑ m, single (x m) 1`.  Then
the sum of the images is computed by `IsSumMorphism` at the point `powMap x` of `Sym^n C`, whose
classified divisor is `toDiv C s = E`. -/
theorem sumMapPow_eq_sumOfPoints {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (G : Work.KeyLemma.Curve.SymPow C n)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] {Φ : G.S ⟶ A}
    {f : C.toOver ⟶ A} (hΦ : Work.KeyLemma.Curve.IsSumMorphism G Φ f)
    {D : C.Div} (hD : D.IsEffective) (hn : C.deg D = (n : ℤ))
    (s : Work.KeyLemma.Curve.SumDiv C)
    (hs : Work.KeyLemma.Curve.SumDiv.toDiv C s = D) :
    Work.KeyLemma.Curve.sumMapPow G Φ D hD hn =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s := by
  -- the multiset `s` has total mass `n`
  have hdeg : Work.KeyLemma.Curve.SumDiv.deg s = n := by
    have h1 : C.deg (Work.KeyLemma.Curve.SumDiv.toDiv C s) =
        (Work.KeyLemma.Curve.SumDiv.deg s : ℤ) :=
      Work.KeyLemma.Sum.deg_toDiv C s
    rw [hs, hn] at h1
    exact_mod_cast h1.symm
  -- enumerate `s` as `Fin n → Point C`
  obtain ⟨x, hx⟩ := Work.KeyLemma.Sum.exists_enum s hdeg
  -- the point `powMap x` of `Sym^n C` classifies `D`
  have hp : G.divOf (G.powMap x) = D := by rw [G.divOf_powMap, hx, hs]
  rw [Work.KeyLemma.Curve.sumMapPow_spec G Φ hD hn hp, hΦ x, ← hx]
  -- `sumOfPoints` is a monoid homomorphism in the multiset, so it turns the sum into a product
  have hprod : (∏ m : Fin n, (x m ≫ f)) =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints C f
        (∑ m : Fin n, Finsupp.single (x m) 1) := by
    rw [show Work.KeyLemma.Curve.SumDiv.sumOfPoints C f
          (∑ m : Fin n, Finsupp.single (x m) 1) =
        ∏ m : Fin n,
          Work.KeyLemma.Curve.SumDiv.sumOfPoints C f (Finsupp.single (x m) 1) from
      (Finsupp.prod_finsetSum_index
        (fun p : Work.KeyLemma.Curve.Point C => pow_zero (p ≫ f))
        (fun p a b => pow_add (p ≫ f) a b)).symm]
    simp
  exact hprod

theorem sumMapPow_toDiv {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (G : Work.KeyLemma.Curve.SymPow C n)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] {Φ : G.S ⟶ A}
    {f : C.toOver ⟶ A} (hΦ : Work.KeyLemma.Curve.IsSumMorphism G Φ f)
    (s : Work.KeyLemma.Curve.SumDiv C) (E : Work.KeyLemma.Curve.EffDiv C n)
    (hE : Work.KeyLemma.Curve.SumDiv.toDiv C s = E.1) :
    Work.KeyLemma.Curve.sumMap G Φ E = Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s := by
  rw [Work.KeyLemma.Curve.sumMap_apply]
  exact sumMapPow_eq_sumOfPoints G hΦ E.isEffective E.deg_eq s hE

end Work.KeyLemma.Curve
