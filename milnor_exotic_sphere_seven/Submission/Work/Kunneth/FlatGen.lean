import Mathlib
import Submission.Work.Kunneth.FlatDefs
import Submission.Work.Kunneth.hIn_tpLof_cycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The summand generator of `homTens C M` as a cycle

The element `flatElem C M n p q hpq u m` of `tpX C (sumShift M) n` is a cycle of the homological
Künneth complex (`Work.Kunneth.hIn_tpLof_cycle`); this file names the resulting element of the
cycle module `Zₙ`.  It is the cycle whose homology class is the image of the summand generator
`[u] ⊗ m` under the flat Künneth isomorphism (`Work.Kunneth.flatKunneth_exists`, §8.2 of the
README).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The summand generator `iCycles u ⊗ m` of `homTens C M`, as a cycle. -/
noncomputable def flatGen (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) : ↥(cycKer (homTens C M) n) :=
  ⟨flatElem C M n p q hpq u m, by
    show ((homTens C M).d n (n - 1)).hom (flatElem C M n p q hpq u m) = 0
    rw [show (homTens C M).d n (n - 1) = ModuleCat.ofHom (hIn C M n) from
      homTens_d_in C M n]
    exact hIn_tpLof_cycle C M n p q hpq u m⟩

/-- The underlying element of `flatGen`. -/
theorem flatGen_val (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) :
    ((flatGen C M n p q hpq u m : ↥(cycKer (homTens C M) n)) : ↥((homTens C M).X n))
      = flatElem C M n p q hpq u m := rfl

end

end Work.Kunneth
