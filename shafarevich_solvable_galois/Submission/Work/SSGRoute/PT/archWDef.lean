import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The linked place `archW` of a seam embedding (leaf-free module)

`Work.SSGRoute.PT.archW` was moved here, verbatim, out of `PT/archSwapHalf.lean`.  The reason is a
*cycle* on the critical path of the leaf `E1aClean.localDictionary_natural_family_arch`
(H161's `SSGRoute/ACTION_leaf_endgame_cycles_and_cut_list.md`, cut 3):

* `E1aClean/LeadNatWit.lean` — which the leaf's one-line closure must import — reaches
  `ArchNat/archUniformNatural.lean`, the only consumer of `archW` outside `PT/archSwapHalf`;
* `archUniformNatural.lean` currently imports `PT/archSwapHalf.lean`, and that module *needs the
  leaf* (its `archβl`/`archβc` are the leaf's `∃`-witnesses), so the leaf cannot be closed in place;
* with `archW` in *this* module — whose import cone is `Mathlib` + `NK.GlobalCFT.Place`, hence
  leaf-free — the `archUniformNatural → archSwapHalf` import edge can be cut, and
  `archUniformNatural` can import this module instead.

`PT/archSwapHalf.lean` imports this module, so the name `Work.SSGRoute.PT.archW` and its type are
unchanged and no consumer of `archSwapHalf` is affected.
-/

namespace Work.SSGRoute.PT

section Seam

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The linked place of a seam embedding**: for `φ : Ω →+* ℂ` the place `w = mk (φ|_K)` of `K`
at which the archimedean clauses of the local dictionary are stated.  A seam for the
involution `c` is `φ ∘ c = conj ∘ φ`, so that `φ|_K` is the infinite place "fixed by `c`" (the
real place of `K` cut out by `c`); `K_w = ℂ` at level `L` as soon as `res_L c ≠ 1`. -/
noncomputable def archW (φ : Ω →+* ℂ) : NK.GlobalCFT.Place ↥K :=
  NK.GlobalCFT.Place.ofInfinite
    (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))

end Seam

end Work.SSGRoute.PT
