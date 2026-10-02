import Mathlib
import Submission.Work.ThomBordism.subtypeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Dropping the empty pieces of a null-bordism family

A `Work.ThomBordism.NullBordismFamily ι F` is an oriented bordism whose boundary is identified with
the disjoint union `Σ i, (F i).pt` of the pieces of the family `F : ι → Man8`.  The `Σ`-type does
not see the pieces whose underlying space is *empty*: if `(F i).pt = ∅` then the `i`-th summand
contributes nothing to the disjoint union, so the families with index type `Fin N × ι` and with index
type `Fin N × {i : ι // Nonempty (F i).pt}` describe essentially the same bordisms.

This file makes that precise (`nullBordismFamily_subtype`): a null-bordism family with the
*nonempty* indices only (`Fin N × {i // Nonempty (F i).pt}`) yields one with all indices
(`Fin N × ι`).  The bounding manifold `W`, its relative fundamental class `w` and the
local-generator condition `w_fund` are untouched; only the identification `∂W ≃ₜ Σ (F i).pt` of the
boundary changes, through the homeomorphism `subHomeo` of `Work.ThomBordism.subtypeDefs` (the
identity on the fibres, with the index transported along `Subtype.val`), and with it the boundary
equation `w ↦ ∑ i, [F i]`:

* the summand attached to an *empty* index `i` vanishes, because the fundamental class of an empty
  `Man8` is `0` (`Work.ThomBordism.Man8.c_eq_zero_of_isEmpty`);
* for the surviving indices the two summands are *equal as cycles*: the two parametrisations of the
  boundary differ only in the proof component of the index, where the two witnesses of
  `Nonempty (F i).pt` are identified by proof irrelevance.

Both facts are fed into the `Finset` bookkeeping
`Work.ThomBordism.Finset.sum_prod_subtype_eq_sum_of_eq_zero`, packaged here as the generic
`Work.ThomBordism.sum_eq_sum_of_pointwise`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

attribute [local instance] Classical.propDecidable

namespace Work.ThomBordism

noncomputable section

open Work.Cohomology

/-- **Bookkeeping for dropping the empty pieces of a family.**  A sum over the indices satisfying `P`
equals the sum over all indices, provided the summands agree on the `P`-part and the summands outside
it vanish.  (`Work.ThomBordism.Finset.sum_prod_subtype_eq_sum_of_eq_zero` is the case `f = g`.) -/
theorem sum_eq_sum_of_pointwise {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (N : ℕ)
    {M : Type*} [AddCommMonoid M] (f : Fin N × {i : ι // P i} → M) (g : Fin N × ι → M)
    (hp : ∀ x : Fin N × {i : ι // P i}, g ⟨x.1, x.2.1⟩ = f x)
    (hz : ∀ x : Fin N × ι, ¬ P x.2 → g x = 0) :
    (∑ x, f x) = ∑ x : Fin N × ι, g x := by
  rw [← Finset.sum_prod_subtype_eq_sum_of_eq_zero P N (f := g) hz]
  exact Finset.sum_congr rfl fun x _ => (hp x).symm

/-- **Dropping the empty pieces of a null-bordism family.**  A null-bordism of the family with the
nonempty indices only is a null-bordism of the whole family: the empty pieces contribute nothing to
the boundary (`Man8.c_eq_zero_of_isEmpty`) and the two boundaries are homeomorphic
(`subHomeo`). -/
theorem nullBordismFamily_subtype {ι : Type} [Fintype ι] (F : ι → Man8) (N : ℕ)
    (W : NullBordismFamily (Fin N × {i : ι // Nonempty (F i).pt}) (fun x => F x.2.1)) :
    Nonempty (NullBordismFamily (Fin N × ι) (fun x => F x.2)) := by
  let b : Set W.W := (modelWithCornersEuclideanHalfSpace 9).boundary W.W
  let bdry' : b ≃ₜ (Σ x : Fin N × ι, (F x.2).pt) := subBdry F N W
  refine ⟨{ W := W.W, bdry := bdry', w := W.w, hw := ?_, w_fund := W.w_fund }⟩
  rw [W.hw]
  refine sum_eq_sum_of_pointwise
    (M := (chainC ℤ (TopCat.toSSet.obj (TopCat.of b))).homology 8)
    (fun i => Nonempty (F i).pt) N ?_ ?_ ?_ ?_
  · -- the two summands agree on the nonempty indices: the two parametrisations coincide
    intro x
    have hbd : (TopCat.ofHom ⟨fun y : (F x.2.1).pt => bdry'.symm ⟨⟨x.1, x.2.1⟩, y⟩,
          bdry'.continuous_invFun.comp continuous_sigmaMk⟩ : (F x.2.1).X ⟶ TopCat.of b)
        = (TopCat.ofHom ⟨fun y : (F x.2.1).pt => W.bdry.symm ⟨x, y⟩,
          W.bdry.continuous_invFun.comp continuous_sigmaMk⟩ : (F x.2.1).X ⟶ TopCat.of b) := by
      apply TopCat.ext
      intro y
      show bdry'.symm ⟨⟨x.1, x.2.1⟩, y⟩ = W.bdry.symm ⟨x, y⟩
      rw [subBdry_symm_apply, subHomeo_symm_apply]
    rw [hbd]
  · -- the summands at the empty indices vanish
    intro x hx
    haveI : IsEmpty (F x.2).pt := not_nonempty_iff.mp hx
    rw [show ((fun x => F x.2) x).c = 0 from Man8.c_eq_zero_of_isEmpty (F x.2)]
    exact map_zero _

end

end Work.ThomBordism
