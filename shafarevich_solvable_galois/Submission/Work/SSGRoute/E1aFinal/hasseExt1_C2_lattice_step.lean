import Mathlib
import Submission.Work.SSGRoute.E1aFinal.HasseDefs
import Submission.Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aFinal

open CategoryTheory

/-- **(S2) The index-two step of the `C₂`-lattice Hasse principle.**  Let `M₀ ⊆ M` be
`H`-representations whose underlying `ℤ`-modules are finite free, such that `M/M₀ ≅ ℤ/2` (generated
by `m`, with `2m ∈ M₀`) and the generator `σ̄` of `H` acts trivially on `M/M₀` (this is
`StepData M₀ M`).  If the coefficient change `Kˣ → 𝕀_K` is injective on `Ext¹_H(M₀, ·)`, then it is
injective on `Ext¹_H(M, ·)`.

Route: the long exact sequence of `0 → M₀ → M → ℤ/2 → 0` in the first variable (Mathlib's
`Abelian.Ext.covariant_sequence_exact₁/₂/₃`, as used in `ExtChain/hasseExt1_syzygy_lattice.lean`),
together with the arithmetic of the `ℤ/2` column.  With `Q = ℤ/2` (trivial action) the presentation
`0 → ℤ →² ℤ → ℤ/2 → 0` gives `Ext¹_H(ℤ/2, X) ≅ X^H/2X^H` and `Hom_H(ℤ/2, X) = X^H[2]`, so the
column reads `Fˣ/(Fˣ)² → (𝕀_K)^H/2(𝕀_K)^H` (injective ⟺ the square Hasse principle
`Fˣ ∩ 2(𝕀_K)^H = (Fˣ)²`, `F = K^{σ̄}`: an element of `F` that is a local square everywhere is a
square), while the `Hom`-level input is Hasse's norm theorem `Kˣ ∩ Nm(𝕀_K) = Nm(Kˣ)` together with
Hilbert 90 for `H`.  All of these are in the workspace
(`NK.GlobalCFTdeep.cyclicHasseInput.hasse_norm`, `Submission/NK/HassePrinciple/*`,
`Submission/Work/QuadraticLocalGlobal/`, `Submission/Work/HasseMinkowski/`).

Proof: `HasseStat M` is *by definition* the statement of the general `C₂`-lattice Hasse principle
`Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general`, which is proved unconditionally in the
workspace (`ExtChain/C2Lift.lean` and its bricks `c2_adapted_basis`, `c2_hasse_brick`,
`c2_h90_brick`), so the index-two step — and indeed every lattice-theoretic step of the
chain — is immediate.  (The alternative route through the index-two long exact sequence is
`StepData`-specific: from the exactness of `Ext¹_H(M/M₀,Kˣ) → Ext¹_H(M,Kˣ) → Ext¹_H(M₀,Kˣ)` and
`HasseStat M₀`, a class killed by the coefficient change is in the kernel of the restriction, and
the remaining `ℤ/2`-column statement that such a class is killed only if it vanishes is weaker
still.) -/
theorem hasseExt1_C2_lattice_step (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (M₀ M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
    [Module.Finite ℤ M₀.V] [Module.Free ℤ M₀.V]
    [Module.Finite ℤ M.V] [Module.Free ℤ M.V]
    (h : StepData M₀ M) (hM₀ : HasseStat M₀) :
    HasseStat M :=
  fun z hz =>
    Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general p k Ω K σ hσ hnt M z hz

end Work.SSGRoute.E1aFinal
