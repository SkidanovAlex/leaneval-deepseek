import Mathlib
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Gen.LineTensor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Twisting a complex bundle by a complex line bundle

`Work.LerayHirsch.twistCore L E` is the tensor product `L ⊗ E` of a complex **line** bundle `L` with
an arbitrary complex gluing-data bundle `E`, in the standard fibre `EuclideanSpace ℂ (Fin n)`: over
the product cover the transition function is the product of the scalar transition of `L`
(`Work.Gen.scl`) with the transition of `E`.  This is the construction the splitting of the
tautological sequence `0 → ℓ → π^*E → Q → 0` needs (`ℓ^* ⊗ π^*E`, and the un-twisting by `ℓ`
afterwards); it complements `Work.Gen.tensorLine` (line ⊗ line).

Basic API: `twistCore_baseSet`, `twistCore_indexAt`, `twistCore_coordChange` (all `rfl`),
`twistCore_coordChange_eq` (the unfolding used by callers), and
`twistCore_bundleComap` (functoriality: `f^*(L ⊗ E) = f^*L ⊗ f^*E`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ιL ιE : Type} {n : ℕ}

/-- **Tensor product of a complex line bundle with a complex bundle**: `L ⊗ E`, with the same
model fibre as `E` and the product cover. -/
def twistCore (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) (ιL × ιE) where
  baseSet p := L.baseSet p.1 ∩ E.baseSet p.2
  isOpen_baseSet p := (L.isOpen_baseSet p.1).inter (E.isOpen_baseSet p.2)
  indexAt x := (L.indexAt x, E.indexAt x)
  mem_baseSet_at x := ⟨L.mem_baseSet_at x, E.mem_baseSet_at x⟩
  coordChange p q x := Work.Gen.scl (L.coordChange p.1 q.1 x) • E.coordChange p.2 q.2 x
  coordChange_self p x hx v := by
    have hs : Work.Gen.scl (L.coordChange p.1 p.1 x) = 1 := by
      have hfun : L.coordChange p.1 p.1 x = ContinuousLinearMap.id ℂ _ := by
        apply ContinuousLinearMap.ext
        intro w
        exact L.coordChange_self p.1 x hx.1 w
      rw [hfun, Work.Gen.scl_id]
    rw [hs, one_smul, E.coordChange_self p.2 x hx.2 v]
  continuousOn_coordChange p q := by
    have h1 : ContinuousOn (fun x => Work.Gen.scl (L.coordChange p.1 q.1 x))
        (L.baseSet p.1 ∩ L.baseSet q.1) :=
      Work.Gen.continuous_scl.comp_continuousOn (L.continuousOn_coordChange p.1 q.1)
    have h1' : ContinuousOn (fun x => Work.Gen.scl (L.coordChange p.1 q.1 x))
        ((L.baseSet p.1 ∩ E.baseSet p.2) ∩ (L.baseSet q.1 ∩ E.baseSet q.2)) :=
      h1.mono (fun x hx => ⟨hx.1.1, hx.2.1⟩)
    have h2' : ContinuousOn (fun x => E.coordChange p.2 q.2 x)
        ((L.baseSet p.1 ∩ E.baseSet p.2) ∩ (L.baseSet q.1 ∩ E.baseSet q.2)) :=
      (E.continuousOn_coordChange p.2 q.2).mono (fun x hx => ⟨hx.1.2, hx.2.2⟩)
    exact h1'.smul h2' 
  coordChange_comp p q r x hx v := by
    have hxL1 : x ∈ L.baseSet p.1 ∩ L.baseSet q.1 := ⟨hx.1.1.1, hx.1.2.1⟩
    have hxL2 : x ∈ L.baseSet q.1 ∩ L.baseSet r.1 := ⟨hx.1.2.1, hx.2.1⟩
    have hE1 : x ∈ E.baseSet p.2 ∩ E.baseSet q.2 := ⟨hx.1.1.2, hx.1.2.2⟩
    have hE2 : x ∈ E.baseSet q.2 ∩ E.baseSet r.2 := ⟨hx.1.2.2, hx.2.2⟩
    have hL : Work.Gen.scl (L.coordChange p.1 r.1 x)
        = Work.Gen.scl (L.coordChange q.1 r.1 x) * Work.Gen.scl (L.coordChange p.1 q.1 x) := by
      rw [← Work.Gen.scl_comp]
      congr 1
      apply ContinuousLinearMap.ext
      intro w
      exact (L.coordChange_comp p.1 q.1 r.1 x ⟨hxL1, hx.2.1⟩ w).symm
    have hEc : E.coordChange q.2 r.2 x (E.coordChange p.2 q.2 x v)
        = E.coordChange p.2 r.2 x v :=
      E.coordChange_comp p.2 q.2 r.2 x ⟨hE1, hx.2.2⟩ v
    rw [smul_apply, smul_apply, map_smul, smul_smul, hEc, ← hL, smul_apply]

@[simp] theorem twistCore_baseSet (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) (p : ιL × ιE) :
    (twistCore L E).baseSet p = L.baseSet p.1 ∩ E.baseSet p.2 := rfl

@[simp] theorem twistCore_indexAt (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) (x : B) :
    (twistCore L E).indexAt x = (L.indexAt x, E.indexAt x) := rfl

@[simp] theorem twistCore_coordChange (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) (p q : ιL × ιE) (x : B) :
    (twistCore L E).coordChange p q x
      = Work.Gen.scl (L.coordChange p.1 q.1 x) • E.coordChange p.2 q.2 x := rfl

/-- The unfolding of the transition functions of a twist, in the form callers use. -/
theorem twistCore_coordChange_eq (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) (p q : ιL × ιE) (x : B)
    (v : EuclideanSpace ℂ (Fin n)) :
    (twistCore L E).coordChange p q x v
      = Work.Gen.scl (L.coordChange p.1 q.1 x) • (E.coordChange p.2 q.2 x v) := by
  rw [twistCore_coordChange, smul_apply]

/-- The twist is functorial under pullback: `f^*(L ⊗ E) = f^*L ⊗ f^*E`. -/
theorem twistCore_bundleComap {B' : Type} [TopologicalSpace B']
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) (f : C(B', B)) :
    twistCore (bundleComap L f) (bundleComap E f) = bundleComap (twistCore L E) f := by
  refine bundleCore_ext rfl rfl (fun p q x => rfl)

end

end Work.LerayHirsch
