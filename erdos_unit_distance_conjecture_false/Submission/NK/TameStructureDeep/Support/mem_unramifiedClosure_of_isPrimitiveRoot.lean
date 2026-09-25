/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Membership in `κ(μ_{p'})` for prime-to-`p` roots of unity

`NK.LocalAnabelian.unramifiedClosure p = ⨆ κ⟮ζ⟯` over all primitive `n`-th roots of unity with
`¬ p ∣ n`.  This file records the immediate membership criterion: every root of unity of order
prime to `p` lies in the closure.  It is the basic API lemma for the unramified closure.
-/
import Submission.NK.LocalAnabelian.ResidueField.Defs

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
