import Mathlib
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `ZMod p ⊗[ℤ] A ≃+ A ⧸ p·A`

Tensoring an abelian group `A` with `ZMod p = ℤ ⧸ (p)` is the same as quotienting `A` by the
subgroup `p·A` of `p`-multiples.  This is the `A = R ⧸ I` case of the general base-change
isomorphism `M ⧸ I·M ≃ (R ⧸ I) ⊗[R] M` (`TensorProduct.quotTensorEquivQuotSMul`), together with
`ℤ ⧸ Ideal.span {p} ≃+* ZMod p` (`Int.quotientSpanNatEquivZMod`).
-/

open scoped TensorProduct

namespace Work.Pi6.K2Z

/-- **`ZMod p ⊗[ℤ] A` is `A ⧸ p·A`.**  The base-change isomorphism for the ring quotient
`ℤ ⧸ (p) ≅ ZMod p`, transported along the identification of the corresponding submodule of `A`
with the subgroup `Work.Pi6.EMZ.pH p A` of `p`-multiples. -/
theorem tensorZModQuot (A : Type) [AddCommGroup A] (p : ℕ) :
    Nonempty (TensorProduct ℤ (ZMod p) A ≃+ (A ⧸ Work.Pi6.EMZ.pH p A)) := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  -- `(p) • ⊤` is the range of multiplication by `p`, i.e. the `p`-multiples `p·A`.
  have hsmul : I • (⊤ : Submodule ℤ A) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : A →ₗ[ℤ] A)) := by
    apply le_antisymm
    · refine (Submodule.smul_le).mpr ?_
      intro r hr n _
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
      rw [← hc]
      refine LinearMap.mem_range.mpr ⟨c • n, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [smul_smul, mul_comm]
    · intro x hx
      obtain ⟨n, rfl⟩ := LinearMap.mem_range.mp hx
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton (p : ℤ)))
        Submodule.mem_top
  have hsub : (I • (⊤ : Submodule ℤ A)).toAddSubgroup = Work.Pi6.EMZ.pH p A := by
    rw [hsmul]; rfl
  refine ⟨?_⟩
  -- The base-change isomorphism `(ℤ ⧸ I) ⊗ A ≃ A ⧸ I • ⊤`, precomposed with
  -- `ZMod p ≃ ℤ ⧸ I`.
  have e : TensorProduct ℤ (ZMod p) A ≃ₗ[ℤ] A ⧸ (I • (⊤ : Submodule ℤ A)) :=
    ((TensorProduct.congr (Int.quotientSpanNatEquivZMod p).toAddEquiv.toIntLinearEquiv
        (LinearEquiv.refl ℤ A)).symm).trans
      (TensorProduct.quotTensorEquivQuotSMul A I)
  exact e.toAddEquiv.trans (QuotientAddGroup.quotientAddEquivOfEq hsub)

end Work.Pi6.K2Z
