import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.SL2ModelClass
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.Models.PSL2.D_facts
import Submission.Work.Models.PSL2.w_facts
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.singer_cycle_model
import Submission.Work.ZassenhausSuzuki.Odd.sl2_conj_involution

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `PSL(2,2ⁿ)` is strongly real

The model `PSL2Model n` is `PSL(2, GF(2ⁿ)) = SL(2, GF(2ⁿ))`: the centre of `SL(2,F)` is
trivial in characteristic two, so `Work.Models.PSL2.pslEquiv` is an isomorphism.

We prove that `SL(2,F)`, `F` a finite field of characteristic two, is **strongly real**: every
element is a product of two involutions.  Indeed `Work.ZassenhausSuzuki.Odd.sl2_conj_involution`
provides, for every `A`, an involution `b` with `b * A * b = A⁻¹`; then
`A = (A * b) * b` and `(A * b)² = A * (b * A * b) = A * A⁻¹ = 1`.  Transporting along
`pslEquiv` gives the same statement in `PSL2Model n`.

The inverting involution comes from the companion-matrix normal form
`Work.ZassenhausSuzuki.sl2_conj_companion` (every element of non-zero trace is conjugate to
`!![0,1;1,t]`, which the Weyl element `w = !![0,1;1,0]` inverts) while elements of trace zero
are their own inverse.
-/

namespace Work.ZassenhausSuzuki.Odd

set_option linter.unusedVariables false

open Matrix

/-- **`SL(2,F)` is strongly real**, `F` a finite field of characteristic two: every element is
a product of two involutions. -/
theorem sl2_stronglyReal {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * a = 1 ∧ b * b = 1 ∧ a * b = A := by
  obtain ⟨b, hb, hbc⟩ := sl2_conj_involution A
  refine ⟨A * b, b, ?_, hb, ?_⟩
  · -- `(A * b)² = A * (b * A * b) = A * A⁻¹ = 1`
    calc (A * b) * (A * b) = A * (b * A * b) := by group
      _ = A * A⁻¹ := by rw [hbc]
      _ = 1 := mul_inv_cancel A
  · rw [mul_assoc, hb, mul_one]

/-- In `PSL(2, 2ⁿ)` every element of odd order other than the identity is a product of two
involutions (`a * a = 1`, `b * b = 1`, `a * b = x`). -/
theorem psl2Model_odd_isStronglyReal (n : ℕ) (hn : 2 ≤ n) (x : LeanEval.GroupTheory.Defs.PSL2Model n)
    (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) :
    ∃ a b : LeanEval.GroupTheory.Defs.PSL2Model n, a * a = 1 ∧ b * b = 1 ∧ a * b = x := by
  obtain ⟨e⟩ := Work.Models.PSL2.pslEquiv n
  obtain ⟨a, b, ha, hb, hab⟩ := sl2_stronglyReal (e.symm x)
  refine ⟨e a, e b, ?_, ?_, ?_⟩
  · rw [← map_mul, ha, map_one]
  · rw [← map_mul, hb, map_one]
  · rw [← map_mul, hab, MulEquiv.apply_symm_apply]

end Work.ZassenhausSuzuki.Odd
