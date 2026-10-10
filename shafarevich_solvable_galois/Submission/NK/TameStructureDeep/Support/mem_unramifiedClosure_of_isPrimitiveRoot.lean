import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Submission.NK.LocalAnabelian.ResidueField.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep

universe u

/-- **Every prime-to-`p` root of unity lies in `κ(μ_{p'})`.** -/
theorem mem_unramifiedClosure_of_isPrimitiveRoot {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] {p n : ℕ} (hn : ¬ p ∣ n) {ζ : K'} (hζ : IsPrimitiveRoot ζ n) :
    ζ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
  rw [NK.LocalAnabelian.unramifiedClosure]
  refine SetLike.le_def.mp (le_iSup_of_le (⟨n, hn⟩ : {n : ℕ // ¬ p ∣ n})
    (le_iSup_of_le ζ (le_iSup_of_le hζ le_rfl))) ?_
  exact IntermediateField.mem_adjoin_simple_self κ ζ

end NK.TameStructureDeep
