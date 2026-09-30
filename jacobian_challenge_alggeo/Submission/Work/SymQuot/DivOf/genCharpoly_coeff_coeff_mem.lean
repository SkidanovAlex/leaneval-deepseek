import Mathlib
import Submission.Work.SymQuot.DivOf.CharIdealGen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

variable {K : Type u} [Field K]

/-- **The generic characteristic polynomial is `S_n`-invariant.**  The action of `S_n` on the
sections over the invariant open `Vⁿ ⊆ Cⁿ` permutes the coordinate pullbacks
(`SectionHom_coordPullbackAt`), hence merely permutes the factors `T - ∑_i X_i·b_i^(m)` of
`genCharpoly`, and therefore fixes it. -/
theorem genCharpoly_map_sectionHom (C : Work.CurveBasics.Curve K) (n : ℕ) (V : C.left.Opens)
    {r : ℕ} (b : Fin r → Γ(C.left, V)) (τ : ULift.{u} (Equiv.Perm (Fin n))) :
    Polynomial.map
        (MvPolynomial.map ((Work.SymQuot.symAction C n).sectionHom
          (Work.SymQuot.piOpen C.toOver V n)
          (Work.SymQuot.DivOf.symPiOpen_invariant C n V) τ))
        (genCharpoly C n V b) = genCharpoly C n V b := by
  let g : Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n) →+*
      Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n) :=
    (Work.SymQuot.symAction C n).sectionHom (Work.SymQuot.piOpen C.toOver V n)
      (Work.SymQuot.DivOf.symPiOpen_invariant C n V) τ
  change Polynomial.map (MvPolynomial.map g) (genCharpoly C n V b) = genCharpoly C n V b
  have hfac : ∀ m : Fin n,
      Polynomial.map (MvPolynomial.map g)
        (Polynomial.X - Polynomial.C (∑ i : Fin r,
          MvPolynomial.C (coordPullbackAt C n V m (b i)) * MvPolynomial.X i))
      = Polynomial.X - Polynomial.C (∑ i : Fin r,
          MvPolynomial.C (coordPullbackAt C n V (τ.down.symm m) (b i)) * MvPolynomial.X i) := by
    intro m
    have hcoord : ∀ i : Fin r, g (coordPullbackAt C n V m (b i))
        = coordPullbackAt C n V (τ.down.symm m) (b i) := fun i =>
      RingHom.congr_fun (sectionHom_coordPullbackAt C n V
        (Work.SymQuot.DivOf.symPiOpen_invariant C n V) τ m) (b i)
    have hsum : MvPolynomial.map g (∑ i : Fin r,
          MvPolynomial.C (coordPullbackAt C n V m (b i)) * MvPolynomial.X i)
        = ∑ i : Fin r,
            MvPolynomial.C (coordPullbackAt C n V (τ.down.symm m) (b i)) * MvPolynomial.X i := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, hcoord i]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hsum]
  have h1 : Polynomial.map (MvPolynomial.map g) (genCharpoly C n V b) =
      ∏ m : Fin n, Polynomial.map (MvPolynomial.map g)
        (Polynomial.X - Polynomial.C (∑ i : Fin r,
          MvPolynomial.C (coordPullbackAt C n V m (b i)) * MvPolynomial.X i)) := by
    rw [genCharpoly, Polynomial.map_prod]
  rw [h1, Finset.prod_congr rfl (fun m _ => hfac m),
    Equiv.prod_comp τ.down.symm (fun m => Polynomial.X - Polynomial.C (∑ i : Fin r,
      MvPolynomial.C (coordPullbackAt C n V m (b i)) * MvPolynomial.X i)),
    ← genCharpoly]

theorem genCharpoly_coeff_coeff_mem {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] (V : C.left.Opens) {r : ℕ}
    (b : Fin r → C.left.presheaf.obj (Opposite.op V)) (k : ℕ) (α : Fin r →₀ ℕ) :
    ((Work.SymQuot.DivOf.genCharpoly C n V b).coeff k).coeff α ∈
      Work.SymQuot.chartInvariants (C := C) (n := n)
        (Work.SymQuot.piOpen C.toOver V n)
        (Work.SymQuot.DivOf.symPiOpen_invariant C n V) := by
  rw [Work.SymQuot.GAction.mem_invariants_iff]
  intro σ
  have h := genCharpoly_map_sectionHom C n V b σ⁻¹
  have h1 := congrArg (fun p => p.coeff k) h
  rw [Polynomial.coeff_map] at h1
  have h2 := congrArg (fun q => q.coeff α) h1
  rw [MvPolynomial.coeff_map] at h2
  exact h2

end Work.SymQuot.DivOf
