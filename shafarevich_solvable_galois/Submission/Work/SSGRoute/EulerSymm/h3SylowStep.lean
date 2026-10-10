import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.EulerSymm.h3CoprimeIndex
import Submission.Work.SSGRoute.EulerSymm.shapiroH3Coind
import Submission.Work.SSGRoute.HS.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A6, step 1: reduction of the vanishing of `H³(D_A, ·)` to an open subgroup of prime-to-`p` index

Packages `EulerSymm/h3CoprimeIndex` (the transfer step, A6(a)) for the decomposition group
`D := decomp k A` of a finite place `A` of `Ω` over `k`: if `U ≤ D` is open of index prime to `p`,
`M` is a finite `𝔽_p[Gal(K/k)]`-module, and `H³(U,M) = 0`, then `H³(D,M) = 0`.

The Shapiro isomorphism at `U` is supplied by the (now `sorry`-free and axiom-clean)
`EulerSymm/shapiroH3Coind`, so nothing in this file imports a tainted node.  The three
group-theoretic facts that turn this into the *Sylow* step — that for
`U₀ = (D ⊓ P.comap (res k K)).subgroupOf D` (`P` a `p`-Sylow of the finite group `Gal(K/k)`) the
index `[D : U₀]` is prime to `p` and `U₀` is open in `D` — are recorded as the explicit hypotheses
`hcop` and `hUopen` here; see `NOTE_additive_state.md` §8 for their proofs to be formalised.
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

open Classical

theorem subsingleton_H3_decomp_of_subsingleton_H3_subgroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUopen : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] (hcop : Nat.Coprime U.index p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hMUd : letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
      Work.AbsoluteKummer.IsDiscreteModule ↥U M)
    (h : letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
      Subsingleton (Work.SSGRoute.H3 (M := M) ↥U)) :
    letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
    Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A)) := by
  letI hDsmul : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
  haveI hSM : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) M :=
    ⟨fun a b m => by
      show SSGRoute.res k K (a : Ω ≃ₐ[k] Ω) • (b • m)
        = b • (SSGRoute.res k K (a : Ω ≃ₐ[k] Ω) • m)
      exact smul_comm _ b m⟩
  exact h3CoprimeIndex p U hcop
    (shapiroH3Coind (G := ↥(SSGRoute.decomp k A)) U hUopen hMUd) h

end Work.SSGRoute.EulerSymm
