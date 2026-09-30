import Mathlib
import Submission.Work.Stems.HurewiczMap
import Submission.Work.Stems.Pi
import Submission.Work.Cohomology.homologyContractible

/-!
# The Hurewicz map: unit, naturality, and the homomorphism packaging

`Submission/Work/Stems/HurewiczMap.lean` defines the Hurewicz map
`hurewiczMap n : πₙ(X,x₀) → Hₙ(X;ℤ)` and proves that it is additive in degrees `≥ 2`
(`hurewiczMap_mul`).  This file completes the elementary theory:

* `Work.Stems.hurewiczMap_one` — the Hurewicz map kills the unit (the constant map induces `0` on
  positive-degree homology, because it factors through the one-point space);
* `Work.Stems.hurewiczChain_natural`, `Work.Stems.hurewiczMap_natural` — naturality in the space:
  postcomposition of a cube commutes with the cube–sphere descent, so the Hurewicz map is natural;
* `Work.Stems.hurewiczHom` — the additive packaging `Additive (πₙ X) →+ Hₙ(X)` of these two facts
  (together with `hurewiczMap_mul`).

The construction of `πₙ` in Mathlib uses the cube `Iⁿ`, and the passage to the sphere is the
quotient map `collapseMap : Iⁿ → Sⁿ` of `Work.Stems.exists_collapsingMap`; everything here is a
consequence of that quotient-universal property (`cubeLift_comp`) and of the explicit four-term
form of `HomotopyGroup.map_mk`.
-/

open CategoryTheory AlgebraicTopology
open CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-! ## The cube of a postcomposed loop -/

/-- The cube obtained from a cube `p : Ω^ N X x` by postcomposing with a continuous map
`f : C(X,Y)`: the representative used by `HomotopyGroup.map`. -/
def genLoopMap {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (p : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩

@[simp] theorem genLoopMap_apply {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Ω^ N X x) (t : I^N) : genLoopMap f p t = f (p t) := rfl

@[simp] theorem HomotopyGroup.map_mk' {N X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x : X} (p : Ω^ N X x) :
    HomotopyGroup.map f ⟦p⟧ = ⟦genLoopMap f p⟧ := rfl

/-! ## The cube lift of a constant cube -/

/-- The cube lift of a constant cube is the constant map. -/
theorem cubeLift_const (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X} :
    cubeLift n hn (GenLoop.const : Ω^ (Fin n) X x₀) = ContinuousMap.const (sphere n) x₀ := by
  ext y
  obtain ⟨q, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
  have h := congrFun (congrArg DFunLike.coe
    (cubeLift_comp n hn (GenLoop.const : Ω^ (Fin n) X x₀))) q
  simpa using h

/-! ## The Hurewicz class of a constant map -/

/-- The constant map `Sⁿ → X` induces `0` on `Hₙ` for `n ≥ 1`, since it factors through the
one-point space, whose positive-degree homology vanishes. -/
theorem hurewiczClass_const (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    hurewiczClass n hn (ContinuousMap.const (sphere n) x₀) = 0 := by
  have hcomp : (ContinuousMap.const (PUnit : Type) x₀).comp
      (ContinuousMap.const (sphere n) PUnit.unit) = ContinuousMap.const (sphere n) x₀ := by
    ext y; rfl
  rw [← hcomp, hurewiczClass_natural]
  have hz : hurewiczClass n hn (ContinuousMap.const (sphere n) PUnit.unit) = 0 := by
    haveI : Subsingleton ((chains (TopCat.of PUnit)).homology n) :=
      ModuleCat.isZero_iff_subsingleton.mp (Work.Cohomology.homologyPUnit ℤ n (by omega))
    exact Subsingleton.elim _ _
  rw [hz]
  exact map_zero _

/-! ## The unit of the Hurewicz map -/

/-- **The Hurewicz map sends `1` to `0`** in every degree `n + 1 ≥ 1`. -/
theorem hurewiczMap_one (n : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X} :
    hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀
        (1 : HomotopyGroup (Fin (n + 1)) X x₀) = 0 := by
  rw [HomotopyGroup.one_def, hurewiczMap_mk]
  simp only [hurewiczChain, cubeLift_const]
  exact hurewiczClass_const (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀

/-! ## Naturality in the space -/

/-- The cube lift of a postcomposed cube: postcomposition commutes with the descent along the
collapse `Iⁿ → Sⁿ`. -/
theorem cubeLift_genLoopMap (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x₀ : X} (p : Ω^ (Fin n) X x₀) :
    cubeLift n hn (genLoopMap f p) = f.comp (cubeLift n hn p) := by
  ext y
  obtain ⟨q, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
  have h₁ := congrFun (congrArg DFunLike.coe (cubeLift_comp n hn (genLoopMap f p))) q
  have h₂ := congrFun (congrArg DFunLike.coe (cubeLift_comp n hn p)) q
  simp only [ContinuousMap.comp_apply] at h₁ h₂ ⊢
  rw [h₁, h₂]
  rfl

/-- Naturality of the Hurewicz *chain* in the space. -/
theorem hurewiczChain_natural (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x₀ : X} (p : Ω^ (Fin n) X x₀) :
    hurewiczChain n hn (f x₀) (genLoopMap f p) =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n
        (hurewiczChain n hn x₀ p) := by
  simp only [hurewiczChain, cubeLift_genLoopMap, hurewiczClass_natural]

/-- **Naturality of the Hurewicz map** in the space: the Hurewicz map commutes with the maps
induced by a continuous map. -/
theorem hurewiczMap_natural (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x₀ : X} (a : HomotopyGroup (Fin n) X x₀) :
    hurewiczMap n hn (f x₀) (HomotopyGroup.map f a) =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n
        (hurewiczMap n hn x₀ a) := by
  induction a using Quotient.inductionOn with
  | h p => exact hurewiczChain_natural n hn f p

/-! ## The Hurewicz map as an additive homomorphism -/

/-- **The Hurewicz map as an additive homomorphism** `Additive (πₙ₊₁(X,x₀)) →+ Hₙ₊₁(X;ℤ)`,
for `n : ℕ`.  (`hurewiczMap_one` and `hurewiczMap_mul` in additive form.) -/
def hurewiczHom (n : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X) :
    Additive (HomotopyGroup (Fin (n + 1)) X x₀) →+
      (chains (TopCat.of X)).homology (n + 1) where
  toFun a := hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ (Additive.toMul a)
  map_zero' := hurewiczMap_one n
  map_add' a b := hurewiczMap_mul n (Additive.toMul a) (Additive.toMul b)

@[simp] theorem hurewiczHom_apply (n : ℕ) {X : Type} [TopologicalSpace X]
    (x₀ : X) (a : Additive (HomotopyGroup (Fin (n + 1)) X x₀)) :
    hurewiczHom n x₀ a = hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀
      (Additive.toMul a) := rfl

end

end Work.Stems
