import Submission.Work.SSGRoute.E1aClean.BaseChangeInstances
import Submission.Work.SSGRoute.E1cGeneric.ext_res_mulEquiv_n_rules
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The `Ext`-side transport of the level-change square

`res_res_eq` is the module identification the transport needs: restricting a `G`-representation
along `galKIncl L` and then along `(galKMulEquiv L).symm` is restricting along the subgroup
inclusion `L.fixingSubgroup.subtype`.  It is `rfl`-level: `Rep.res f M` unfolds to
`Rep.of (X := M.V) (M.ρ.comp f)`, so the two sides differ only by `MonoidHom.comp_assoc` and the
coherence `galKIncl_galKMulEquiv_symm`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **The module identification of the `Ext`-side transport.** -/
theorem res_res_eq (L : IntermediateField k K)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Rep.res (galKMulEquiv L).symm.toMonoidHom (Rep.res (galKIncl L) M)
      = Rep.res (L.fixingSubgroup).subtype M := by
  have h : (galKIncl L).comp (galKMulEquiv L).symm.toMonoidHom
      = (L.fixingSubgroup).subtype :=
    MonoidHom.ext fun τ => galKIncl_galKMulEquiv_symm L τ
  letI : Module SSGRoute.PTExt.Coeff M.V := M.hV2
  show Rep.of (X := M.V) ((M.ρ.comp (galKIncl L)).comp
      (galKMulEquiv L).symm.toMonoidHom)
    = Rep.of (X := M.V) (M.ρ.comp (L.fixingSubgroup).subtype)
  rw [MonoidHom.comp_assoc, h]

end

end Work.SSGRoute.E1aClean
