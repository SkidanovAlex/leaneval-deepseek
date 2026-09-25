import Mathlib

namespace NK.NUV2

open Submodule

universe u

noncomputable section

/-- Additive homomorphisms between `ℤ`-modules are the same thing as `ℤ`-linear maps; this is
the `ℤ_p`-linear equivalence between the two descriptions (`ℤ_p = PadicInt p` acting pointwise). -/
def linEquivAddHomPadicInt (p : ℕ) [Fact p.Prime] (Q : Type*) [AddCommGroup Q] :
    (Q →ₗ[ℤ] PadicInt p) ≃ₗ[PadicInt p] (Q →+ PadicInt p) where
  toFun f := f.toAddMonoidHom
  invFun f := f.toIntLinearMap
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

theorem rank_addMonoidHom_padicInt {p : ℕ} [Fact p.Prime] (U : Type*) [AddCommGroup U]
    [Module.Finite ℤ U] :
    Module.rank (PadicInt p) (U →+ PadicInt p) = (Module.finrank ℤ U : Cardinal) := by
  -- Replace additive homomorphisms by `ℤ`-linear maps.
  rw [← (linEquivAddHomPadicInt p U).rank_eq]
  -- Factor out the torsion subgroup of `U`.
  let T : Submodule ℤ U := Submodule.torsion ℤ U
  let Q := U ⧸ T
  haveI : Module.Finite ℤ Q := inferInstance
  haveI : Module.IsTorsionFree ℤ Q := inferInstance
  haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  have hq : Function.Surjective (T.mkQ : U →ₗ[ℤ] Q) := T.mkQ_surjective
  -- A homomorphism out of `U` vanishes on the torsion subgroup, because `ℤ_p` is torsion free.
  have hcompl : ∀ f : U →ₗ[ℤ] PadicInt p, T ≤ f.ker := by
    intro f x hx
    rw [LinearMap.mem_ker]
    have hx' : x ∈ AddCommGroup.torsion U := by
      rw [← Submodule.torsion_int]
      exact hx
    obtain ⟨n, hn, hnx⟩ :=
      isOfFinAddOrder_iff_zsmul_eq_zero.mp ((AddCommGroup.mem_torsion x).mp hx')
    have hzero : n • f x = 0 := by
      rw [← f.map_smul n x, hnx, map_zero]
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd h hn
    · exact h
  -- Precomposition with the quotient map identifies the duals of `U` and of `U ⧸ torsion U`.
  let Ψ : (Q →ₗ[ℤ] PadicInt p) →ₗ[PadicInt p] (U →ₗ[ℤ] PadicInt p) :=
    { toFun := fun g => g.comp T.mkQ
      map_add' := by intro g h; ext x; rfl
      map_smul' := by intro c g; ext x; rfl }
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := hq x
      exact congrArg (fun f : U →ₗ[ℤ] PadicInt p => f y) h
    · intro f
      exact ⟨T.liftQ f (hcompl f), Submodule.liftQ_mkQ T f (hcompl f)⟩
  have hrank : Module.rank (PadicInt p) (U →ₗ[ℤ] PadicInt p)
      = Module.rank (PadicInt p) (Q →ₗ[ℤ] PadicInt p) :=
    ((LinearEquiv.ofBijective Ψ hbij).rank_eq).symm
  rw [hrank]
  -- `Q` is finite free, and a basis of `Q` displays `Hom(Q, ℤ_p)` as free of the same rank.
  have hb := Module.finBasis ℤ Q
  have hrank2 : Module.rank (PadicInt p) (Q →ₗ[ℤ] PadicInt p)
      = (Module.finrank ℤ Q : Cardinal) := by
    rw [rank_eq_card_basis ((Pi.basisFun (PadicInt p) (Fin (Module.finrank ℤ Q))).map
      (hb.constr (PadicInt p)))]
    simp
  rw [hrank2]
  -- Finally `finrank ℤ (U ⧸ torsion U) = finrank ℤ U`.
  rw [Module.finrank_eq_rank ℤ Q, Module.finrank_eq_rank ℤ U]
  exact rank_quotient_eq_of_le_torsion le_rfl

end

end NK.NUV2
