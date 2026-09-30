import Mathlib
import Submission.Work.HomologyExtra.SimplexClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The connecting homomorphism of the pair `(Δⁿ⁺¹, ∂Δⁿ⁺¹)` on the fundamental class

The snake lemma description of the connecting homomorphism of the pair sequence: if `x₃` is a
cycle of the relative chains `C(X,A)`, `x₂` a lift of it in `C(X)` and `x₁` the boundary of `x₂`
viewed in `C(A)`, then `δ([x₃]) = [x₁]`.  Applied to the identity simplex of `Δⁿ⁺¹` (whose
boundary is the fundamental cycle of `∂Δⁿ⁺¹`) this gives
`simplexGenMap (n+1) ≫ pairδ = simplexBoundaryClass n`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- `liftCycles` does not depend on the presentation of the next degree: the morphism is
characterised by the fact that it lifts the cycle `k` along the monomorphism
`K.iCycles i : K.cycles i ⟶ K.X i`. -/
theorem liftCycles_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {A : ModuleCat ℤ}
    (k : A ⟶ K.X i) {j j' : ℕ} (hj : (ComplexShape.down ℕ).next i = j)
    (hj' : (ComplexShape.down ℕ).next i = j')
    (hk : k ≫ K.d i j = 0) (hk' : k ≫ K.d i j' = 0) :
    K.liftCycles k j hj hk = K.liftCycles k j' hj' hk' := by
  rw [← cancel_mono (K.iCycles i), HomologicalComplex.liftCycles_i,
    HomologicalComplex.liftCycles_i]

/-- **The connecting homomorphism on the class of a cycle.**  Let `S` be a short exact sequence of
chain complexes of `ℤ`-modules and `c.Rel i j` a consecutive pair of degrees.  If `x₃` is a cycle
of `S.X₃` in degree `i`, `x₂` a lift of it in `S.X₂` and `x₁` the boundary of `x₂`, viewed as a
cycle of `S.X₁` in degree `j`, then the connecting homomorphism sends the class of `x₃` to the
class of `x₁`. -/
theorem cycleClass_comp_δ_eq {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (hS : S.ShortExact) {i j : ℕ} (hij : (ComplexShape.down ℕ).Rel i j) {A : ModuleCat ℤ}
    (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i ((ComplexShape.down ℕ).next i) = 0)
    (x₂ : A ⟶ S.X₂.X i) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.X₁.d j ((ComplexShape.down ℕ).next j) = 0)
    (hfac : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j) :
    cycleClass x₃ hx₃ ≫ hS.δ i j hij = cycleClass x₁ hx₁ := by
  have hx₃j : x₃ ≫ S.X₃.d i j = 0 := by
    rw [(ComplexShape.down ℕ).next_eq' hij] at hx₃
    exact hx₃
  rw [cycleClass_def, cycleClass_def]
  have h1 : S.X₃.liftCycles x₃ ((ComplexShape.down ℕ).next i) rfl hx₃ =
      S.X₃.liftCycles x₃ j ((ComplexShape.down ℕ).next_eq' hij) hx₃j :=
    liftCycles_congr x₃ rfl ((ComplexShape.down ℕ).next_eq' hij) hx₃ hx₃j
  rw [h1, Category.assoc]
  have key := hS.δ_eq (i := i) (j := j) (hij := hij) x₃ hx₃j x₂ hx₂ x₁ hfac
    ((ComplexShape.down ℕ).next j) rfl
  rw [key]


/-- **The connecting homomorphism of `(Δⁿ⁺¹, ∂Δⁿ⁺¹)` on the fundamental class**: the class of
the identity simplex in the top relative homology of the simplex pair is sent to the
fundamental class of the boundary sphere. -/
theorem simplexGenMap_pairdelta (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.HomologyExtra.simplexGenMap (n + 1))
      (Work.Homology.pairδ Work.Homology.ZMod (Work.HomologyExtra.simplex (n + 1))
        (Work.HomologyExtra.simplexBoundary (n + 1)) n) =
      Work.HomologyExtra.simplexBoundaryClass n := by
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by simp [ComplexShape.down]
  have hx₂ : simplexIdChain (n + 1) ≫
      (Work.Homology.pairSeq Work.Homology.ZMod (simplex (n + 1))
        (simplexBoundary (n + 1))).g.f (n + 1) = simplexRelChain (n + 1) := rfl
  have key := cycleClass_comp_δ_eq
    (Work.Homology.pairSeq_shortExact Work.Homology.ZMod (simplex (n + 1))
      (simplexBoundary (n + 1))) hij
    (simplexRelChain (n + 1)) (simplexRelChain_d (n + 1))
    (simplexIdChain (n + 1)) hx₂
    (simplexBoundaryChain n) (simplexBoundaryChain_d n)
    (simplexBoundaryChain_incl n)
  unfold Work.HomologyExtra.simplexGenMap Work.HomologyExtra.simplexBoundaryClass
  unfold Work.Homology.pairδ
  exact key

end

end Work.HomologyExtra
