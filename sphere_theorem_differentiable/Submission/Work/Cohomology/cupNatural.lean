import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Naturality of the Alexander–Whitney cup product

The cup product on singular cochains is natural with respect to maps of simplicial sets: for
`f : X ⟶ Y` and cochains `α` in degree `n`, `β` in degree `m` on `Y`, pulling back along `f` and
then taking the cup product agrees with taking the cup product on `Y` and pulling back:

`f*(α) ⌣ f*(β) = f*(α ⌣ β)`,

where `f*` denotes the transpose (`LinearMap.dualMap`) of the `(chainComplexMap f).f` component.

The proof is by the usual computation on generators: `genEval` is natural
(`genEval_dualMap`), the front/back faces commute with `f` (`app_frontFace`, `app_backFace`),
and `cup_apply` expresses both sides on a singular simplex.  The auxiliary `cup_ext` records
that a linear functional on `n`-chains is determined by its values on the generators
`ιChainComplex σ` (which jointly present `(X.chainComplex R).X n` as a coproduct).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- `genEval` is natural in the simplicial set: evaluating the pullback along `f` of a cochain `α`
on a simplex `σ` is evaluating `α` on the image `f σ`. -/
theorem genEval_dualMap (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (α : (Y.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (σ : X _⦋n⦌) :
    genEval R X (((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap α) σ
      = genEval R Y α (f.app _ σ) := by
  simp only [genEval, LinearMap.dualMap_apply]
  congr 1
  have h := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n) =>
      g.hom 1) (SSet.ι_chainComplexMap_f (X := X) (Y := Y) f (ModuleCat.of R R) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The front face commutes with a map of simplicial sets. -/
theorem app_frontFace {X Y : SSet} (f : X ⟶ Y) (N n : ℕ) (h : n ≤ N)
    (σ : X _⦋N⦌) :
    f.app _ (frontFace X n N h σ) = frontFace Y n N h (f.app _ σ) := by
  simp [frontFace]

/-- The back face commutes with a map of simplicial sets. -/
theorem app_backFace {X Y : SSet} (f : X ⟶ Y) (n m : ℕ) (σ : X _⦋n + m⦌) :
    f.app _ (backFace X n m σ) = backFace Y n m (f.app _ σ) := by
  simp [backFace]

/-- A linear functional on the `n`-chains of a simplicial set is determined by its values on the
generators `ιChainComplex σ`, i.e. by `genEval` on all `n`-simplices. -/
theorem cup_ext (R : Type) [CommRing R] (X : SSet) {n : ℕ}
    {a b : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R}
    (h : ∀ σ : X _⦋n⦌, genEval R X a σ = genEval R X b σ) : a = b := by
  have hmor : ModuleCat.ofHom a = ModuleCat.ofHom b := by
    apply SSet.chainComplex_hom_ext (C := ModuleCat R)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact h σ
  simpa using congrArg ModuleCat.Hom.hom hmor

/-- **Naturality of the Alexander–Whitney cup product.** Pulling back cochains along a map of
simplicial sets commutes with the cup product. -/
theorem cupNatural (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n m : ℕ}
    (α : (Y.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (Y.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    Work.Cohomology.cup R X
        (((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap α)
        (((SSet.chainComplexMap f (ModuleCat.of R R)).f m).hom.dualMap β) =
      (((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom.dualMap
        (Work.Cohomology.cup R Y α β)) := by
  apply cup_ext R X
  intro σ
  rw [cup_apply R X]
  rw [genEval_dualMap, genEval_dualMap, genEval_dualMap]
  rw [app_frontFace, app_backFace, cup_apply R Y]

end

end Work.Cohomology
