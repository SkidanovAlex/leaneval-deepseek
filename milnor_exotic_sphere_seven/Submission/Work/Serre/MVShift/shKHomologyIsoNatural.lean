/-
# Naturality of the degree-shift comparison `shK_homologyIso`

`Work.Serre.MVShift.shK_homologyIso K n k hk` identifies the `k`-th homology of the degree-`n`
shift `shK K n` of a cochain complex of `ℚ`-modules with `K.homology (k+n)`, in the interior
`k ≥ 1`.  The present file records that this comparison is **natural** in the complex: a morphism
`φ : K ⟶ L` intertwines the comparison for `K` and for `L` through `homologyMap φ (k+n)` on the
one side and `homologyMap (shMap φ n) k` on the other.

The mathematical content is the naturality of Mathlib's `restrictionHomologyIso` under the
restriction `restrictionMap φ e`; the degree bookkeeping for the shape embedding `shEmb n` is done
in `Submission/Work/Serre/MVShift/shS_delta_comm.lean` (namespace `ShSdeltaAux`), where the same
square is proved with the two sides interchanged, so the statement here follows by symmetry.
-/
import Mathlib
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Serre.MVShift.shS_delta_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.MVShift

theorem shKHomologyIsoNatural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n k : ℕ)
    (hk : 1 ≤ k) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.MVShift.shMap φ n) k)
        (Work.Serre.MVShift.shK_homologyIso L n k hk).hom
      = CategoryTheory.CategoryStruct.comp (Work.Serre.MVShift.shK_homologyIso K n k hk).hom
          (HomologicalComplex.homologyMap φ (k + n)) := by
  exact (ShSdeltaAux.shK_homologyIso_natural φ n k hk).symm

end Work.Serre.MVShift
