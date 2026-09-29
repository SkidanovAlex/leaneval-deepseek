import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Derivation.DifferentialRing

namespace Commons.FieldTheory.Differential

open IntermediateField

theorem deriv_mem_adjoin_range {F L : Type*} [Field F] [Differential F] [Field L] [Algebra F L]
    [Differential L] [DifferentialAlgebra F L] {ι : Type*} (u : ι → L)
    (hu : ∀ i, ∃ b : F, Differential.deriv (u i) = algebraMap F L b) :
    ∀ x ∈ IntermediateField.adjoin F (Set.range u),
      Differential.deriv x ∈ IntermediateField.adjoin F (Set.range u) := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hu i
    rw [hb]
    exact IntermediateField.algebraMap_mem _ b
  | algebraMap a =>
    rw [DifferentialAlgebra.deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ (Differential.deriv a)
  | add y z hy hz ihy ihz =>
    rw [Derivation.map_add]
    exact add_mem ihy ihz
  | inv y hy ihy =>
    rw [Derivation.leibniz_inv, smul_eq_mul, neg_mul]
    exact neg_mem (mul_mem (pow_mem (inv_mem hy) 2) ihy)
  | mul y z hy hz ihy ihz =>
    rw [Derivation.leibniz]
    exact add_mem (mul_mem hy ihz) (mul_mem hz ihy)

end Commons.FieldTheory.Differential