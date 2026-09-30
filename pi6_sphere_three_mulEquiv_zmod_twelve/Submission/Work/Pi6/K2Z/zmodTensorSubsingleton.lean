import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.K2Z

open scoped TensorProduct

/-- If the base change `ZMod p ⊗[ℤ] A` of an abelian group `A` along `ℤ → ZMod p` is trivial,
then every element of `A` is divisible by `p`.

The hypothesis is phrased as the triviality of `ModuleCat.extendScalars (Int.castRingHom (ZMod p))`
applied to `A`; that object is `ZMod p ⊗[ℤ] A` with the `ℤ`-module structure on `ZMod p` induced by
the ring homomorphism.  The proof identifies `ZMod p ⊗[ℤ] A` with `A ⧸ (p ℤ) • ⊤` (tensoring with a
quotient of the ring is quotienting by the corresponding submodule), whence `(p ℤ) • ⊤ = ⊤`, and
then every `a : A` lies in the range of multiplication by `p`. -/
theorem zmodTensorSubsingleton (A : Type) [AddCommGroup A] (p : ℕ)
    (h : Subsingleton ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))) :
    ∀ a : A, ∃ b : A, (p : ℤ) • b = a := by
  -- The `ℤ`-module structure on `ZMod p` used inside `extendScalars` agrees with the canonical one.
  have hinst : (Module.compHom (ZMod p) (Int.castRingHom (ZMod p))) =
      (AddCommGroup.toIntModule (ZMod p)) := by
    apply Module.ext
    funext n x
    show (Int.castRingHom (ZMod p)) n • x = n • x
    exact Int.cast_smul_eq_zsmul (ZMod p) n x
  have hT : Subsingleton (ZMod p ⊗[ℤ] A) := hinst ▸ h
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  -- `ZMod p ⊗ A` is `A ⧸ (I • ⊤)`: tensoring with the quotient `ℤ ⧸ I` of the base ring.
  have e : ZMod p ⊗[ℤ] A ≃ₗ[ℤ] A ⧸ (I • (⊤ : Submodule ℤ A)) :=
    ((TensorProduct.congr (Int.quotientSpanNatEquivZMod p).toAddEquiv.toIntLinearEquiv
        (LinearEquiv.refl ℤ A)).symm).trans
      (TensorProduct.quotTensorEquivQuotSMul A I)
  have hQ : Subsingleton (A ⧸ (I • (⊤ : Submodule ℤ A))) := e.surjective.subsingleton
  have htop : I • (⊤ : Submodule ℤ A) = ⊤ := Submodule.Quotient.subsingleton_iff.mp hQ
  intro a
  have ha : a ∈ I • (⊤ : Submodule ℤ A) := by rw [htop]; exact Submodule.mem_top
  -- `I • ⊤` is contained in the range of multiplication by `p`.
  have hle : I • (⊤ : Submodule ℤ A) ≤ LinearMap.range ((p : ℤ) • (1 : A →ₗ[ℤ] A)) := by
    refine (Submodule.smul_le).mpr ?_
    intro r hr n _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
    rw [← hc]
    refine LinearMap.mem_range.mpr ⟨c • n, ?_⟩
    exact (smul_comm c (p : ℤ) n).symm.trans (smul_smul c (p : ℤ) n)
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp (hle ha)
  exact ⟨b, by simpa [LinearMap.smul_apply] using hb⟩

end Work.Pi6.K2Z
