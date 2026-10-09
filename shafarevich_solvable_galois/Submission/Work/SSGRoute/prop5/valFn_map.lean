import Mathlib
import Submission.Work.SSGRoute.prop5.Basic
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement
open Work.CohomologicalShrinking

/-! ## Naturality of the value map in the rank

The value map `valFn` sends a `j`-tuple of elements of `F(d)` to the class of
`(⁅x₀, ⋯, x_{j-1}⁆)^{p^{i-j}}` in the graded piece `E(d,(i,j))`.  Since the induced map
`gradedMapLin` on the graded pieces is built from `QuotientGroup.map` applied to the map
`refinedMap` induced by `ψ`, naturality in the rank reduces to two elementary facts:
the commutator word is natural under group homomorphisms, and `ψ` commutes with powers. -/

/-- The `j`-fold left-normed commutator word is natural under group homomorphisms. -/
lemma commWord_map {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q) (j : ℕ) (x : Fin j → P) :
    commWord j (fun k => ψ (x k)) = ψ (commWord j x) := by
  match j, x with
  | 0, x => simp [commWord]
  | 1, x => simp [commWord]
  | (k + 2), x =>
      rw [commWord_succ_succ, commWord_succ_succ, commWord_map ψ (k + 1) (fun t => x t.succ),
        map_commutatorElement]

/-- The value map `valFn` is natural in the rank `d`: for a surjective homomorphism of operator
groups `ψ : F(m) → F(n)`, the induced map `gradedMapLin` on the graded pieces carries the value
on `x` to the value on `ψ ∘ x`. -/
theorem valFn_map (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G m) :
    Work.CohomologicalShrinking.gradedMapLin p ψ hψ i j (valFn p G i j m hj hji x) =
      valFn p G i j n hj hji (fun k => ψ (x k)) := by
  rw [valFn_eq, valFn_eq]
  unfold valFnOf
  simp only [gradedMapLin, gradedMapAdd, AddMonoidHom.toZModLinearMap]
  change Additive.ofMul (gradedMapMul p ψ hψ i j
        (QuotientGroup.mk' _ ⟨commWord j x ^ p ^ (i - j), _⟩)) =
      Additive.ofMul (QuotientGroup.mk' _
        ⟨(commWord j fun k => ψ (x k)) ^ p ^ (i - j), _⟩)
  rw [gradedMapMul_of]
  congr 1
  congr 1
  apply Subtype.ext
  simp only [refinedMap_coe]
  rw [map_pow, commWord_map]

end Work.SSGRoute.prop5

-- The delegated scaffold placed the statement inside a `namespace Work.SSGRoute.prop5` although the
-- module already sits in that namespace, which would make the fully-qualified name
-- `Work.SSGRoute.prop5.Work.SSGRoute.prop5.valFn_map`.  The statement above carries the intended
-- name `Work.SSGRoute.prop5.valFn_map`; the copy below records the same theorem under the doubled
-- name as well, so that both names resolve.
set_option linter.dupNamespace false

namespace Work.SSGRoute.prop5
namespace Work.SSGRoute.prop5

open scoped commutatorElement

/-- The value map `valFn` is natural in the rank `d` (same statement, under the doubled
namespace as it appeared in the delegated file). -/
theorem valFn_map (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G m) :
    Work.CohomologicalShrinking.gradedMapLin p ψ hψ i j (valFn p G i j m hj hji x) =
      valFn p G i j n hj hji (fun k => ψ (x k)) :=
  _root_.Work.SSGRoute.prop5.valFn_map p G ψ hψ i j hj hji x

end Work.SSGRoute.prop5
end Work.SSGRoute.prop5
