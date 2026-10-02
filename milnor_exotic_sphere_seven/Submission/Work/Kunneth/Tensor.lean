import Mathlib
import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.tpD_comp_tpD

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tensor product of two chain complexes of `ℤ`-modules

`Work.Kunneth.tpC C D` is the chain complex `⨁_{p+q=n} C_p ⊗_ℤ D_q` with the Koszul
differential `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y` (the differential itself,
`Work.Kunneth.tpD`, and the summand inclusions `Work.Kunneth.tpι` are in
`Submission/Work/Kunneth/TensorDefs.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The tensor product of two chain complexes of `ℤ`-modules**: the complex with
`(C ⊗ D)_n = ⨁_{p+q=n} C_p ⊗_ℤ D_q` and the Koszul differential. -/
def tpC (C D : ChainComplex (ModuleCat ℤ) ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (tpX C D n)) (fun n => ModuleCat.ofHom (tpD C D n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, tpD_comp_tpD, ModuleCat.ofHom_zero])

@[simp]
theorem tpC_X (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (tpC C D).X n = ModuleCat.of ℤ (tpX C D n) := rfl

@[simp]
theorem tpC_d (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (tpC C D).d (n + 1) n = ModuleCat.ofHom (tpD C D n) := by
  simp only [tpC, ChainComplex.of_d]

end

end Work.Kunneth
