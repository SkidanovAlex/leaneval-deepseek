import Submission.NK.Reconstruct.GammaDual
import Submission.NK.GlobalCFT.IdeleClassGroupExact

/-!
# The continuous dual of a topological commutative group as a `ℤ_ℓ`-module

`NK.Reconstruct.Dual G ℓ = {f : Additive G →+ ℤ_ℓ // Continuous f}` is defined
(`Submission/Work/Reconstruct/GammaDual.lean`) for an arbitrary topological commutative group, but
the workspace equips it with a `ℤ_ℓ`-module structure only for `G = Γ_K`
(`Submission/Work/Reconstruct/gammaSmul.lean`).  The idèle-class-group computation of CoNF (10.3.20)
needs it for `G` a local unit group, for `G = ∏_v 𝒪_vˣ` and for `G = C_K` — the rank of the dual is
the invariant `r_ℓ(K)` — so this file supplies the general pointwise structure

  `(a • χ)(x) = a * χ(x)`      (`NK.RankTheoryDeep.smul_dual_apply`)

at a *lower instance priority* than the one in `gammaSmul.lean`, so that no existing proof changes
the instance it uses.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.RankTheoryDeep

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] {ℓ : ℕ} [Fact ℓ.Prime]

/-- The pointwise `ℤ_ℓ`-action on the continuous dual: `(a • χ)(x) = a * χ(x)`. -/
noncomputable instance instSmulDualChar : SMul (PadicInt ℓ) (NK.Reconstruct.Dual G ℓ) where
  smul a χ := ⟨a • (χ : Additive G →+ PadicInt ℓ), χ.2.const_mul a⟩

@[simp] theorem smul_dual_apply (a : PadicInt ℓ) (χ : NK.Reconstruct.Dual G ℓ)
    (x : Additive G) :
    ((a • χ : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ) x
      = a * (χ : Additive G →+ PadicInt ℓ) x := rfl

/-- **The continuous dual is a `ℤ_ℓ`-module** for the pointwise action (at a lower instance priority
than the `Γ_K`-specific instance of `Submission/Work/Reconstruct/gammaSmul.lean`). -/
noncomputable instance (priority := 100) instModuleDualChar :
    Module (PadicInt ℓ) (NK.Reconstruct.Dual G ℓ) :=
  Function.Injective.module (PadicInt ℓ)
    ((AddSubgroup.subtype (NK.Reconstruct.dualCarrier G ℓ)).comp
      (AddMonoidHom.id _ ) ) (by
    intro a b h
    exact Subtype.ext h) (fun _ _ => rfl)

end NK.RankTheoryDeep
