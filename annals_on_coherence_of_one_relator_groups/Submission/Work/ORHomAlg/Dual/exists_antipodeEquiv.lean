import Mathlib

namespace Work.ORHomAlg.Dual

universe u v

/-- For a group `G` and a commutative semiring `K`, the antipode of the group algebra
`K[G]` (sending `g` to `g⁻¹`) is a ring anti-automorphism, hence a ring equivalence with the
opposite ring: `K[G] ≃+* (K[G])ᵐᵒᵖ`, mapping `single g c` to `op (single g⁻¹ c)`. -/
theorem exists_antipodeEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G] :
    ∃ e : MonoidAlgebra K G ≃+* (MonoidAlgebra K G)ᵐᵒᵖ,
      ∀ (g : G) (c : K), e (MonoidAlgebra.single g c) =
        MulOpposite.op (MonoidAlgebra.single g⁻¹ c) := by
  classical
  -- The antipode of a Hopf algebra, packaged as a ring homomorphism into the opposite ring.
  let φ : MonoidAlgebra K G →+* (MonoidAlgebra K G)ᵐᵒᵖ :=
    (HopfAlgebra.antipodeAlgHomOp K (MonoidAlgebra K G)).toRingHom
  -- Its value on the generators `single g c`.
  have hφ : ∀ (g : G) (c : K), φ (MonoidAlgebra.single g c) =
      MulOpposite.op (MonoidAlgebra.single g⁻¹ c) := by
    intro g c
    simp only [φ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    simp [MonoidAlgebra.antipode_single, CommSemiring.antipode_eq_id]
  -- The antipode on a group algebra is an involution.
  have hS2 : ∀ x : MonoidAlgebra K G,
      HopfAlgebra.antipode K (HopfAlgebra.antipode K x) = x := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | single g c => simp [MonoidAlgebra.antipode_single, CommSemiring.antipode_eq_id]
  -- The two-sided inverse of `φ`, given by the antipode on the opposite ring.
  have hleft : Function.LeftInverse
      (fun y : (MonoidAlgebra K G)ᵐᵒᵖ => HopfAlgebra.antipode K y.unop) φ := by
    intro x
    show HopfAlgebra.antipode K (MulOpposite.unop (φ x)) = x
    have : MulOpposite.unop (φ x) = HopfAlgebra.antipode K x := rfl
    rw [this, hS2]
  have hright : Function.RightInverse
      (fun y : (MonoidAlgebra K G)ᵐᵒᵖ => HopfAlgebra.antipode K y.unop) φ := by
    intro y
    show φ (HopfAlgebra.antipode K (MulOpposite.unop y)) = y
    have : φ (HopfAlgebra.antipode K (MulOpposite.unop y)) =
        MulOpposite.op
          (HopfAlgebra.antipode K (HopfAlgebra.antipode K (MulOpposite.unop y))) := rfl
    rw [this, hS2]
    exact MulOpposite.op_unop y
  exact ⟨{ toFun := ⇑φ
           invFun := fun y : (MonoidAlgebra K G)ᵐᵒᵖ => HopfAlgebra.antipode K y.unop
           left_inv := hleft
           right_inv := hright
           map_mul' := φ.map_mul
           map_add' := φ.map_add },
         fun g c => hφ g c⟩

end Work.ORHomAlg.Dual
