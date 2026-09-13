import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.LinearMap

open Module

noncomputable section

/-- Linear maps `g : A →ₗ[K] B` whose kernel contains `ker f` are in bijection with
linear maps out of the quotient `A ⧸ ker f`, via `Submodule.liftQ`. -/
def kerLeEquiv {K : Type*} [Field K] {A B C : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C] (f : A →ₗ[K] C) :
    {g : A →ₗ[K] B // LinearMap.ker f ≤ LinearMap.ker g} ≃ (A ⧸ LinearMap.ker f →ₗ[K] B) where
  toFun g := Submodule.liftQ (LinearMap.ker f) g.1 g.2
  invFun h := ⟨h.comp (LinearMap.ker f).mkQ,
    (le_of_eq (Submodule.ker_mkQ (LinearMap.ker f)).symm).trans
      (LinearMap.ker_le_ker_comp (LinearMap.ker f).mkQ h)⟩
  left_inv g := by
    apply Subtype.ext
    exact Submodule.liftQ_mkQ (LinearMap.ker f) g.1 g.2
  right_inv h := by
    apply Submodule.linearMap_qext (LinearMap.ker f)
    simp [Submodule.liftQ_mkQ]

theorem card_hom_ker_le_pow {K : Type*} [Field K] [Fintype K] {A B C : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] [AddCommGroup B] [Module K B] [FiniteDimensional K B] [AddCommGroup C] [Module K C] (f : A →ₗ[K] C) : Nat.card {g : A →ₗ[K] B // LinearMap.ker f ≤ LinearMap.ker g} = Nat.card K ^ (Module.finrank K (LinearMap.range f) * Module.finrank K B) := by
  classical
  rw [Nat.card_congr (kerLeEquiv f)]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := A ⧸ LinearMap.ker f →ₗ[K] B)]
  rw [Module.finrank_linearMap]
  rw [(LinearMap.quotKerEquivRange f).finrank_eq]

end

end Commons.LinearAlgebra.LinearMap