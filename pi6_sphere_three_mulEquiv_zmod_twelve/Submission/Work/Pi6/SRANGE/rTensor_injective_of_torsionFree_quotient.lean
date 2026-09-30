import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Pi6.SRANGE

/--
If `f : A →ₗ[ℤ] B` is injective and the quotient `B ⧸ range f` is torsion-free, then tensoring `f`
with any commutative ring `S` stays injective.

Over `ℤ` (a Dedekind domain / PID) a module is flat exactly when it is torsion-free, so
`B ⧸ range f` is flat.  The short exact sequence `0 → A → B → B ⧸ range f → 0` then has flat
cokernel, and `LinearMap.lTensor_injective_of_exact_of_flat` shows that `- ⊗ S` is left-exact on
it; equivalently (via `TensorProduct.comm`) so is `S ⊗ -`, which is `f.rTensor S`.
-/
theorem rTensor_injective_of_torsionFree_quotient (S : Type) [CommRing S]
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (hf : Function.Injective f) (hB : Module.IsTorsionFree ℤ B)
    (h : Module.IsTorsionFree ℤ (B ⧸ LinearMap.range f)) :
    Function.Injective (f.rTensor S) := by
  -- Fix the canonical module structure on the quotient (the one `Submodule.mkQ` uses).
  letI : Module ℤ (B ⧸ LinearMap.range f) := Submodule.Quotient.module _
  -- All `ℤ`-module structures on an additive commutative monoid are equal, so torsion-freeness
  -- transports from the instance appearing in the statement.
  have h' : Module.IsTorsionFree ℤ (B ⧸ LinearMap.range f) := by
    convert h using 1
    exact Subsingleton.elim _ _
  haveI : Module.IsTorsionFree ℤ (B ⧸ LinearMap.range f) := h'
  -- Over the integers, torsion-free means flat.
  haveI : Module.Flat ℤ (B ⧸ LinearMap.range f) := inferInstance
  -- `0 → A → B → B ⧸ range f → 0` is exact with flat cokernel, hence `f ⊗ S` is injective.
  have hl : Function.Injective (f.lTensor S) :=
    LinearMap.lTensor_injective_of_exact_of_flat (f := Submodule.mkQ (LinearMap.range f))
      (Submodule.mkQ_surjective _) f hf (by rw [LinearMap.exact_iff]; simp) S
  -- `S ⊗ f` injective iff `f ⊗ S` injective.
  exact (f.lTensor_inj_iff_rTensor_inj S).mp hl

end Work.Pi6.SRANGE
