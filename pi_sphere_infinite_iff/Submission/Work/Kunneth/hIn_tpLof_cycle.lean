import Mathlib
import Submission.Work.Kunneth.FlatDefs
import Submission.Work.Kunneth.HomAux

/-!
# The generators of the flat Künneth complex are cycles

`Work.Kunneth.hIn` is the differential of the homological Künneth complex
`homTens C M = tpC C (sumShift M)` (`Work.Kunneth.HomDefs`).  This file proves that the summand
generator `iCycles u ⊗ m` (`u` a cycle of `C`, `m ∈ M q`) is a cycle: since the differential of
`sumShift M` vanishes, the Koszul differential on the `(p,q)`-summand is `∂ ⊗ 1`, and `∂ u = 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The summand generator `iCycles u ⊗ m` of the homological Künneth complex is a cycle. -/
theorem hIn_tpLof_cycle (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) :
    hIn C M n (tpLof C (sumShift M) n ⟨(p, q), hpq⟩
      ((C.iCycles p).hom u ⊗ₜ[ℤ] m)) = 0 := by
  rcases n with _ | k
  · rw [hIn_zero]
    rfl
  · erw [hIn_succ, tpD_sumShift_lof C M k ⟨(p, q), hpq⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] m)]
    by_cases hp : 1 ≤ (⟨(p, q), hpq⟩ : tpIdx (k + 1)).1.1
    · rw [dif_pos hp]
      erw [hDIn_tmul_cycle, map_zero]
    · rw [dif_neg hp]

end

end Work.Kunneth
