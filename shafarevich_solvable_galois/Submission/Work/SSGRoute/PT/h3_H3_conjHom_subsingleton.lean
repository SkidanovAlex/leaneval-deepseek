import Mathlib
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.h3_H3_subsingleton_of_image
import Submission.Work.SSGRoute.PTembedding.homRep_dualMod_units_of_isCyclotomicDual
import Submission.Work.SSGRoute.EulerSymm.h3Functoriality
import Submission.Work.SSGRoute.EulerSymm.h3Congr
import Submission.Work.SSGRoute.PTfin.subsingleton_H3_conjHom_of_units
import Submission.Work.SSGRoute.PT.finite_dualMod_tensor
import Submission.Work.SSGRoute.PT.conjHomUnits_dualMod_tensor_addEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# `H³(D_A, Hom_ℤ(N₁,Ωˣ)) = 0` from `cd_p(D_A) ≤ 2`

The target `Work.SSGRoute.PT.h3_H3_conjHom_subsingleton` is the vanishing of the third cohomology
of the decomposition group `D_A = SSGRoute.decomp k A` with coefficients in the *conjugation
module* `Hom_ℤ(N₁, Ωˣ)` (`Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))`), for `N₁` a finite
`𝔽_p[Gal(K/k)]`-module; it is the input `Ext³_{D_A}(N₁, Ωˣ) = 0` of the `α²`-dévissage of the
local Euler characteristic (`PT/mkb_ld02_core.lean`).

The proof is a *coefficient change*: since `N₁` is `p`-torsion, every `f : N₁ → Ωˣ` takes values
in `μ_p`; hence `Hom_ℤ(N₁,Ωˣ) ≅ Hom(N₁, μ_p) ≅ N₁^∨(1) = DualMod p (N₁ ⊗ T)` as `D_A`-modules
(the Tate twist cancels `T = μ_p^∨` against `μ_p`, see
`Work.SSGRoute.PT.conjHomUnits_addEquiv_dualMod_tensor`).  The module `N₁^∨(1)` is *finite*, so
the arithmetic input `h3` (`cd_p(D_A) ≤ 2`) applies to it — directly through the model bridge
`PTCore.subsingleton_h3loc_iff_subsingleton_H3` — and the vanishing transports back along the
`H³`-functoriality of an equivariant additive isomorphism
(`Work.SSGRoute.EulerSymm.h3AddEquivCongr`).

This file isolates the (twist-free) formal part of that argument: the assembly
`h3_H3_conjHom_subsingleton_of_addEquiv`, which takes the equivariant coefficient isomorphism as
a hypothesis; the coefficient isomorphism itself is
`Work.SSGRoute.PT.conjHomUnits_addEquiv_dualMod_tensor`.
-/

namespace Work.SSGRoute.PT

/-- The finite `𝔽_p[Gal(K/k)]`-module `N₁^∨(1) = DualMod p (N₁ ⊗_{𝔽_p} T)`
(`T = μ_p^∨` the cyclotomic dual), the coefficient module isomorphic to `Hom_ℤ(N₁,Ωˣ)`. -/
abbrev conjDualCoeff (p : ℕ) (T N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
    [AddCommGroup T] [Module (ZMod p) T] : Type :=
  Work.SSGRoute.DualMod p (TensorProduct (ZMod p) N₁ T)

/-- **The formal assembly.**  If the conjugation module `Hom_ℤ(N₁,Ωˣ)` is `D_A`-equivariantly
isomorphic to the *finite* module `N₁^∨(1) = DualMod p (N₁ ⊗ T)`, then the vanishing of `H³`
for finite coefficients (`h3`) gives `H³(D_A, Hom_ℤ(N₁,Ωˣ)) = 0`: `h3` gives
`Subsingleton (H3loc … (N₁^∨(1)) …)`, the model bridge transports it to
`Subsingleton (H³(D_A, N₁^∨(1)))`, and `H³` is invariant under an equivariant additive
isomorphism of coefficient modules. -/
theorem h3_H3_conjHom_subsingleton_of_addEquiv
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h3 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)))
    (N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
      [DistribMulAction (K ≃ₐ[k] K) N₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N₁] [Finite N₁]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A) N₁]
    (hpinN : ∀ (σ : ↥(SSGRoute.decomp k A)) (n : N₁),
      σ • n = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • n)
    (e : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)) ≃+ conjDualCoeff p T N₁)
    (he : (letI : DistribMulAction ↥(SSGRoute.decomp k A) (conjDualCoeff p T N₁) :=
        Work.SSGRoute.decompDistribMulAction K (conjDualCoeff p T N₁) A
       ∀ (σ : ↥(SSGRoute.decomp k A)) (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
        e (σ • f) = σ • e f)) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)))
      ↥(SSGRoute.decomp k A)) := by
  classical
  haveI : Finite (conjDualCoeff p T N₁) := Work.SSGRoute.PT.finite_dualMod_tensor p N₁ T
  letI : DistribMulAction ↥(SSGRoute.decomp k A) (conjDualCoeff p T N₁) :=
    Work.SSGRoute.decompDistribMulAction K (conjDualCoeff p T N₁) A
  -- the arithmetic input, for the finite module `N₁^∨(1)`
  have hXloc : Subsingleton
      (Work.SSGRoute.H3loc p k Ω K (conjDualCoeff p T N₁) (SSGRoute.decomp k A)) :=
    h3 (conjDualCoeff p T N₁)
  -- the model bridge to the standard model `H³(↥D_A, ·)`
  have hX : Subsingleton
      (Work.SSGRoute.H3 (M := conjDualCoeff p T N₁) ↥(SSGRoute.decomp k A)) :=
    (Work.SSGRoute.PTCore.subsingleton_h3loc_iff_subsingleton_H3 p k Ω K (conjDualCoeff p T N₁)
      (SSGRoute.decomp k A)
      (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A)
      (fun σ m => rfl)).mp hXloc
  -- transport along the equivariant coefficient isomorphism
  obtain ⟨f⟩ := Work.SSGRoute.EulerSymm.h3AddEquivCongr e he
  haveI := hX
  exact ⟨fun a b => f.injective (Subsingleton.elim (f a) (f b))⟩

theorem h3_H3_conjHom_subsingleton
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h3 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)))
    (N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
      [DistribMulAction (K ≃ₐ[k] K) N₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N₁] [Finite N₁]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A) N₁]
    (hpinN : ∀ (σ : ↥(SSGRoute.decomp k A)) (n : N₁),
      σ • n = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • n) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)))
      ↥(SSGRoute.decomp k A)) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  haveI : Finite T := Finite.of_injective u u.injective
  obtain ⟨e, he⟩ :=
    conjHomUnits_dualMod_tensor_addEquiv p k Ω K ζ hζ hζK T hT A N₁ hpinN
  exact h3_H3_conjHom_subsingleton_of_addEquiv p k Ω K T A hA h3 N₁ hpinN e he

end Work.SSGRoute.PT
