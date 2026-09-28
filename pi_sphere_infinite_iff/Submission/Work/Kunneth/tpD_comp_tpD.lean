import Mathlib
import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.tpDpq_comp

/-!
# The Koszul differential of the tensor product squares to zero

`Work.Kunneth.tpD C D n` is the Koszul differential `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y` of the
tensor product of two chain complexes of `ℤ`-modules
(`Submission/Work/Kunneth/TensorDefs.lean`).  This file contains the statement that it squares to
zero, which is what makes the tensor product `Work.Kunneth.tpC`
(`Submission/Work/Kunneth/Tensor.lean`) a chain complex.

The vanishing on a single summand is the companion lemma `Work.Kunneth.tpDpq_comp`; here it is
assembled into the statement for the whole direct sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The sign identity `(-1)^(p-1) + (-1)^p = 0` for `p ≥ 1`. -/
theorem neg_one_pow_sub_add (p : ℕ) (hp : 1 ≤ p) :
    (-1 : ℤ) ^ (p - 1) + (-1 : ℤ) ^ p = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, pow_succ]
  ring

/-- The summand of the differential of the tensor product, composed with the whole differential,
vanishes: this assembles `Work.Kunneth.tpDpq_comp`. -/
theorem tpD_lof_comp (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx (n + 2)) :
    (tpD C D n).comp (tpDpq C D (n + 1) pq) = 0 :=
  tpDpq_comp C D n pq

/-- **The Koszul differential of the tensor product squares to zero.** -/
theorem tpD_comp_tpD (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    LinearMap.comp (tpD C D n) (tpD C D (n + 1)) = 0 := by
  apply DirectSum.linearMap_ext
  intro pq
  rw [LinearMap.comp_assoc, LinearMap.zero_comp]
  have h : (tpD C D (n + 1)).comp (DirectSum.lof ℤ (tpIdx (n + 2))
      (fun rs => tpSummand C D rs.1.1 rs.1.2) pq) = tpDpq C D (n + 1) pq := by
    rw [tpD]
    apply LinearMap.ext
    intro a
    rw [LinearMap.comp_apply, DirectSum.toModule_lof]
  rw [h, tpDpq_comp]

end

end Work.Kunneth
