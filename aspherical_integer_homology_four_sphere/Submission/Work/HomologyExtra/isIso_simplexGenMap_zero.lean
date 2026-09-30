import Mathlib
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.RelProjIso
import Submission.Work.HomologyExtra.SimplexPairHomology
import Submission.Work.HomologyExtra.cycleClass_naturality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-! ## Auxiliary computations for `Δ⁰ = point`

The pair `(Δ⁰, ∂Δ⁰)` is the pair `(point, ∅)`: the boundary of the one-point simplex is empty.
Consequently the inclusion of the singular chains of `∂Δ⁰` into those of `Δ⁰` is the zero map,
so the projection onto the relative chains — and hence the induced map in homology — is an
isomorphism.  -/

/-- **The boundary of `Δ⁰` is empty.** `Δ⁰ = StdSimplex ℝ (Fin 1)` is a single point, whose only
barycentric coordinate is `1 ≠ 0`. -/
theorem simplexBoundary_zero_eq_empty : simplexBoundary 0 = ∅ := by
  ext w
  simp only [simplexBoundary, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, hi⟩
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rw [Convexity.StdSimplex.weights_apply_eq_one w i] at hi
  norm_num at hi

/-- There is no singular `k`-simplex of the empty space (in the singular simplicial set of
`TopCat.of ∅`). -/
theorem isEmpty_toSSet_empty (k : ℕ) : IsEmpty ((TopCat.toSSet.obj
    (TopCat.of (∅ : Set (simplex 0)))).obj (Opposite.op (SimplexCategory.mk k))) := by
  refine ⟨fun x => ?_⟩
  exact isEmptyElim ((TopCat.toSSetObjEquiv (TopCat.of (∅ : Set (simplex 0)))
    (Opposite.op (SimplexCategory.mk k))) x
      (Convexity.StdSimplex.single ⟨0, Nat.succ_pos k⟩))

/-- **The inclusion of the empty subspace induces the zero map of chain complexes.**  In each
degree the source is a coproduct indexed by the (empty) set of `k`-simplices of `∅`. -/
theorem inclChain_simplexBoundary_zero :
    Work.Homology.inclChain Work.Homology.ZMod (simplex 0) (simplexBoundary 0) = 0 := by
  rw [simplexBoundary_zero_eq_empty]
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.zero_f]
  have h : (SSet.chainComplexMap (TopCat.toSSet.map (Work.Homology.incl (∅ : Set (simplex 0))))
      Work.Homology.ZMod).f k = 0 := by
    have := isEmpty_toSSet_empty k
    apply SSet.chainComplex_hom_ext
    intro x
    exact isEmptyElim x
  exact h

/-- **The class of the identity `0`-simplex augments to `1`**: the cycle class of `ι₀` in the
singular chains of `Δ⁰`, composed with the augmentation `ε : H₀(Δ⁰; ℤ) → ℤ`, is the identity
of `ℤ`. -/
theorem cycleClass_simplexIdChain_zero_comp_ε :
    cycleClass (simplexIdChain 0) (by simp) ≫
      (simplex 0).singularHomology₀ε Work.Homology.ZMod = 𝟙 Work.Homology.ZMod := by
  rw [cycleClass_def]
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε (C := ModuleCat ℤ)
    (TopCat.toSSet.obj (simplex 0)) Work.Homology.ZMod (simplexId 0)

/-- **The identity simplex generates `H₀(Δ⁰, ∂Δ⁰)`**: `simplexGenMap 0`, the class of the identity
`0`-simplex `ι₀ : Δ⁰ → Δ⁰` in `H₀(Δ⁰, ∂Δ⁰; ℤ)`, is an isomorphism.

`Δ⁰ = Convexity.StdSimplex ℝ (Fin 1)` is a single point (its only barycentric coordinate is `1`),
so `simplexBoundary 0 = {w | ∃ i, w.weights i = 0}` is **empty**: the pair `(Δ⁰, ∂Δ⁰)` is the pair
`(point, ∅)`.

Route.
1. `simplexGenMap 0 = cycleClass (simplexIdChain 0) _ ≫ relProjHom ℤ 0 (simplex 0) (simplexBoundary 0)`
   by `Work.HomologyExtra.cycleClass_naturality` applied to `relProj ℤ (simplex 0) (simplexBoundary 0)`
   and the definition `simplexRelChain 0 = simplexIdChain 0 ≫ (relProj …).f 0`.
2. `p := relProjHom ℤ 0 (simplex 0) (simplexBoundary 0)` is an isomorphism, because
   `inclChain ℤ (simplex 0) (simplexBoundary 0) = 0` (the boundary is empty), so that `relProj` is
   the cokernel projection out of a zero map.
3. `cycleClass (simplexIdChain 0) _ ≫ ε = 𝟙 ℤ` with `ε` the augmentation of `H₀(Δ⁰)`, which is an
   isomorphism since `Δ⁰` is contractible, hence path-connected; so `cycleClass (simplexIdChain 0) _`
   is an isomorphism as well.
4. Compose 3 with 2. -/
theorem isIso_simplexGenMap_zero :
    CategoryTheory.IsIso (Work.HomologyExtra.simplexGenMap 0) := by
  have hrel : IsIso (Work.Homology.relProj Work.Homology.ZMod (simplex 0) (simplexBoundary 0)) :=
    CategoryTheory.Limits.cokernel.π_of_zero inclChain_simplexBoundary_zero
  have hp : IsIso (Work.Homology.relProjHom Work.Homology.ZMod 0 (simplex 0)
      (simplexBoundary 0)) := inferInstance
  have hcyc : IsIso (cycleClass (simplexIdChain 0) (by simp)) :=
    isIso_of_comp_hom_eq_id ((simplex 0).singularHomology₀ε Work.Homology.ZMod)
      cycleClass_simplexIdChain_zero_comp_ε
  have hgen : simplexGenMap 0 = cycleClass (simplexIdChain 0) (by simp) ≫
      Work.Homology.relProjHom Work.Homology.ZMod 0 (simplex 0) (simplexBoundary 0) := by
    show cycleClass (simplexRelChain 0) (simplexRelChain_d 0) = _
    show cycleClass (simplexIdChain 0 ≫ (Work.Homology.relProj Work.Homology.ZMod (simplex 0)
      (simplexBoundary 0)).f 0) (simplexRelChain_d 0) = _
    exact (cycleClass_naturality (Work.Homology.relProj Work.Homology.ZMod (simplex 0)
      (simplexBoundary 0)) (simplexIdChain 0) (by simp)).symm
  rw [hgen]
  infer_instance

end

end Work.HomologyExtra
