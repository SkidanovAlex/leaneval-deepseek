import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.S3

open MonoidAlgebra

/-- Conjugation by `g` restricted to a normal subgroup `K`, as a monoid homomorphism. -/
private def conjHom {L : Type*} [Group L] {K : Subgroup L} (hKn : K.Normal) (g : L) :
    ↥K →* ↥K where
  toFun a := ⟨g * (a : L) * g⁻¹, hKn.conj_mem (a : L) a.2 g⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group

theorem conj_range_le_range {F : Type*} [Field F] {L : Type*} [Group L] {K : Subgroup L}
    (hKn : K.Normal) {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F L V) (g : L) (r : MonoidAlgebra F ↥K) :
    (ρ g) * (Representation.asAlgebraHom (ρ.comp K.subtype)) r * (ρ g⁻¹)
      ∈ (Representation.asAlgebraHom (ρ.comp K.subtype)).range := by
  refine ⟨MonoidAlgebra.mapDomain (conjHom hKn g) r, ?_⟩
  -- Show: `Φ (mapDomain (conjHom hKn g) r) = ρ g * Φ r * ρ g⁻¹`
  have key : ∀ r : MonoidAlgebra F ↥K,
      Representation.asAlgebraHom (ρ.comp K.subtype) (MonoidAlgebra.mapDomain (conjHom hKn g) r)
        = (ρ g) * (Representation.asAlgebraHom (ρ.comp K.subtype)) r * (ρ g⁻¹) := by
    intro r
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp [MonoidAlgebra.mapDomain_zero]
    | add x y hx hy =>
        simp only [MonoidAlgebra.mapDomain_add, map_add, hx, hy, mul_add, add_mul]
    | single a c =>
        rw [MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single,
            Representation.asAlgebraHom_single]
        show c • ρ (((conjHom hKn g a : ↥K) : L))
            = ρ g * (c • ρ ((a : ↥K) : L)) * ρ g⁻¹
        rw [show (((conjHom hKn g a : ↥K) : L)) = g * ((a : ↥K) : L) * g⁻¹ from rfl,
            map_mul, map_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  exact key r

end Work.ThmF.Prove.S3
