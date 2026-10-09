import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Euler-symmetry node `Work.SSGRoute.euler_symm_input`: shared vocabulary

The target `Work.SSGRoute.euler_symm_input` (node `EulerSymm` of the Poitou–Tate counting
identity) is the **symmetry of the local Euler characteristic** at a finite place `A` of `Ω`
over `k`:

  `χ(D_A, M) = χ(D_A, M^∨(1))`,  `M^∨(1) = DualMod p (M ⊗ T)` (Tate dual, `T ≅ μ_p^{-1}`),

where `χ(D_A, X) = h⁰ − h¹ + h² = dim H⁰(D_A,X) − dim H¹(D_A,X) + dim H²(D_A,X)` in the locally
constant cochain model `LTDDefs/Basic.lean`, `D_A = decomp k A`.

This file only fixes the vocabulary (`chiD`, `ffun`, `tateDual`) so that the pieces of the proof
can be stated and delegated separately.  Nothing here is `sorry`.
-/

namespace Work.SSGRoute.EulerSymm

open scoped TensorProduct

/-- The **Tate dual** of a finite `𝔽_p[Gal(K/k)]`-module: `M^∨(1) = Hom(M ⊗ T, 𝔽_p)`, where `T` is
the cyclotomic dual (`IsCyclotomicDual`). -/
abbrev tateDual (p : ℕ) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] : Type :=
  DualMod p (M ⊗[ZMod p] T)

/-- The **local Euler characteristic at an arbitrary closed subgroup** `H ≤ G_k = Ω ≃ₐ[k] Ω` of
the absolute Galois group,

  `chiH H X = dim H⁰(H, X) − dim H¹(H, X) + dim H²(H, X) ∈ ℤ`,

in the locally constant cochain model of `LTDDefs/Basic.lean`.  (`H1loc`/`H2loc` accept an
arbitrary subgroup `H` of `Ω ≃ₐ[k] Ω`.) -/
noncomputable def chiH (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (H : Subgroup (Ω ≃ₐ[k] Ω)) (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] : ℤ :=
  (Module.finrank (ZMod p) (H0loc p k Ω K X H) : ℤ)
    - (Module.finrank (ZMod p) (H1loc p k Ω K X H) : ℤ)
    + (Module.finrank (ZMod p) (H2loc p k Ω K X H) : ℤ)

/-- The **local Euler characteristic** at the finite place `A`,

  `chiD X = dim H⁰(D_A, X) − dim H¹(D_A, X) + dim H²(D_A, X) ∈ ℤ`,

`D_A = decomp k A`, in the locally constant cochain model of `LTDDefs/Basic.lean`. -/
noncomputable def chiD (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] : ℤ :=
  chiH p k Ω K (SSGRoute.decomp k A) X

/-- The additive invariant of the Artin induction argument for the symmetry of the Euler
characteristic: `ffun X = χ(D_A, X) − χ(D_A, X^∨(1))`, as a function on finite
`𝔽_p[Gal(K/k)]`-modules with the exact binder structure of `Work.SSGRoute.milne210`. -/
noncomputable def ffun (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (A : ValuationSubring Ω) :
    (M : Type) → [AddCommGroup M] → [Module (ZMod p) M] → [DistribMulAction (K ≃ₐ[k] K) M] →
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] → [Finite M] → ℚ :=
  fun M _ _ _ _ _ => ((chiD p k Ω K A M : ℤ) : ℚ)
    - ((chiD p k Ω K A (DualMod p (M ⊗[ZMod p] T)) : ℤ) : ℚ)

@[simp] theorem ffun_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (A : ValuationSubring Ω) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ffun p k Ω K T A M = ((chiD p k Ω K A M : ℤ) : ℚ)
      - ((chiD p k Ω K A (DualMod p (M ⊗[ZMod p] T)) : ℤ) : ℚ) := rfl

end Work.SSGRoute.EulerSymm
