import Mathlib
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.ExtChain

/-- **The canonical `E1a` coefficient is `p`-torsion.**  The underlying abelian group of
`N = e1aN0 p k Ω K T E = DualMod p (E ⊗_{𝔽_p} T)` is an `𝔽_p`-module, so the `ℤ`-scalar action of
`Coeff = ULift ℤ` annihilates it at `p`: `p • x = 0` for every `x`.

(This is the hypothesis `hN` that the first-variable module-structure lemmas
`Work.ExtChain.ext2_fn_p_odd` and `Work.ExtChain.ext2_fn_two_of_trivial` require, for the module
`Rep.res H.subtype (e1aN0 p k Ω K T E)` of a subgroup `H`; note `(Rep.res H.subtype N).V = N.V` is
`rfl`, so the statement below is the one that applies.) -/
theorem ptorsion_e1aN0 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] :
    ∀ x : (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V, (p : SSGRoute.PTExt.Coeff) • x = 0 := by
  -- The coefficient ring is `Coeff = ULift ℤ`; its scalar action on the underlying abelian group
  -- is the generic `ULift.module`-structure over `Module ℤ`, i.e. `(p : Coeff) • x = p • x`
  -- (`nsmul`).  The underlying type is `DualMod p (E ⊗_{𝔽_p} T)`, an `𝔽_p`-module, hence of
  -- exponent `p`, which is `ZModModule.char_nsmul_eq_zero`.
  intro x
  rw [ULift.smul_def]
  simp only [ULift.down_natCast]
  rw [Nat.cast_smul_eq_nsmul]
  haveI : Module (ZMod p) (↑(Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) :=
    inferInstanceAs (Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
  exact ZModModule.char_nsmul_eq_zero p x

end Work.ExtChain
