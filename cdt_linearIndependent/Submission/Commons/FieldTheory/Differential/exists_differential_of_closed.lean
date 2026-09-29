import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing

namespace Commons.FieldTheory.Differential

theorem exists_differential_of_closed {F L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    (E : IntermediateField F L) (hE : ∀ x ∈ E, Differential.deriv x ∈ E) :
    ∃ d : Differential E, ∀ x : E, d.deriv x = ⟨Differential.deriv (x : L), hE (x : L) x.2⟩ := by
  let g : E →+ E :=
    { toFun := fun x => ⟨Differential.deriv (x : L), hE (x : L) x.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Subtype.ext
        simp [map_add] }
  have hg : ∀ x : E, (g x : L) = Differential.deriv (x : L) := fun x => rfl
  refine ⟨⟨Derivation.mk' g.toIntLinearMap ?_⟩, ?_⟩
  · intro a b
    apply Subtype.ext
    simp only [AddMonoidHom.coe_toIntLinearMap, E.coe_add, smul_eq_mul, E.coe_mul, hg,
      Derivation.leibniz, smul_eq_mul]
  · intro x
    rfl

end Commons.FieldTheory.Differential