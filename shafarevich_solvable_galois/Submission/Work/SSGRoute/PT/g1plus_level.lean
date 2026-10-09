import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.exists_level_factors_locConstOnTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G1⁺` (`canonical_localPairing_reciprocity_converse`): the assembly, step 1

Taking the assembly of

  **`Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`** (`G1⁺`, the lead design
  `_lead_design/ssg_pt_design_1002/DESIGN.md` §4, branch B),

clause by clause.  Its conclusion is `∃ pair, (clauses (1)–(7) verbatim from
`Work.SSGRoute.canonical_localPairing_with_reciprocity`) ∧ (clause (8))`, where `pair` is the
canonical pairing built from the *global class formation*:

> `pair M H a b` at a finite place `H = decomp k A` is defined by choosing a finite Galois level
> `L ≤ Ω` through which `a|_H` and `b|_H` factor, and setting
> `pair = χ_L (ι_{w'} (levelPair (βl a) [b]))`,

with `χ_L` the coherent `p`-torsion invariant (`PT.pt_coherent_pTorsion_invariant`, S1),
`βl` the local dictionary (`ext_h1_localGlobal_dictionary`, S6), `[b] ∈ H¹(D_{w'}, M')`,
`ι_{w'}` the orbit-placement map into `H²(Gal(L/k), 𝕀_L) → H²(Gal(L/k), C_L)`, and `levelPair`
from `SSGRoute.PTDefs`.  At an involution the same recipe is used at the real place.

## The ingredient map (all names measured on disk, 10-03)

| role | on-disk object | state |
|---|---|---|
| finite level from an open subgroup (Krull) | `Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le` | **proved** |
| finite quotient a locally constant cocycle factors through | `Work.SSGRoute.Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles` | **proved** |
| coherent `χ` on `p`-torsion of `H²(·,C_·)` | `PT.pt_coherent_pTorsion_invariant` (S1) | dispatched, statement on disk |
| orbit-supported `z` dying in `C_L` is `0` | `PT.pt_orbitIdele_H2_eq_zero` (S2) | **proved** |
| global + local dictionaries and the square | `ext_h1_localGlobal_dictionary` (S6) | statement on disk (in flight) |
| involution square, `p = 2` | S6r — *to be stated by this assembly* | not on disk |
| level pairing | `SSGRoute.PTDefs.levelPair`, `PTDefsOmega.inflCIn`, `inflHIn` | **proved** |
| local duality (perfectness of clause (4)) | `Work.SSGRoute.local_duality_ext_in` | **proved** |
| clause (8)'s chain | `ext_idele_shapiro`, `phi1_mono_sylow_in`, `PT.pt_extSegment_exact`, `e9_glue_phiAt` | **proved** |
| the orbit-placement map `ι_w` | *not yet on disk* (the `E7cOmega` lane has the orbit-supported subclass `exists_orbitSupported_extLoc`, `eq_of_extLoc_eq_of_orbitSupported`) | — |

## This file

Step 1 of the `pair` definition: **the level choice**.  `pair` is defined by choosing `L` through
which the two cochains factor; this file provides the existence of such an `L` in the form the
definition consumes, for an arbitrary locally constant cochain `a` on an arbitrary subgroup `H`
(the two applications are `H = decomp k A` at a finite place and `H = Subgroup.zpowers c` at an
involution).  It is independent of S1/S6/`ι_w`, hence a legitimate separate obligation.
-/

open scoped Topology

namespace Work.SSGRoute.PT

/-- **The level choice for `G1⁺`'s `pair`.**  A cochain `a` which is locally constant on a subgroup
`H ≤ Gal(Ω/k)` factors, on `H`, through the restriction map `Gal(Ω/k) →* Gal(L/k)` of a *finite
normal* intermediate field `L ≥ K`:

  `∃ L ≥ K, FiniteDimensional k L ∧ Normal k L ∧ ∃ a₀, ∀ σ ∈ H, a σ = a₀ (σ|_L)`.

This is the first step of the construction of `pair M H a b` in the lead design: "choosing a finite
Galois level `L ≤ Ω` where `a|_H`, `b|_H` factor".  Proof route: `IsLocConstOn H a` gives an open
`U` on which `a` is right-`(U ∩ H)`-invariant; intersect with `K.fixingSubgroup` and apply the Krull
fact `exists_finiteDimensional_normal_fixingSubgroup_le` to get a finite normal `L ≥ K` with
`L.fixingSubgroup ≤ U`; then `σ|_L = τ|_L ⟹ σ⁻¹τ ∈ L.fixingSubgroup ≤ U`, and
`σ⁻¹τ ∈ H`, so `a σ = a τ`-invariance gives the factorisation. -/
theorem exists_level_factors_locConstOn
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (hH : SSGRoute.IsLocConstOn H a) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧ ∃ a₀ : (L ≃ₐ[k] L) → M,
        ∀ σ ∈ H, a σ = a₀ (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨L, hfin, hnorm, hKL, a₀, _, ha₀, _⟩ :=
    exists_level_factors_locConstOnTwo k Ω K H a a hH hH
  exact ⟨L, hfin, hnorm, hKL, a₀, ha₀⟩

end Work.SSGRoute.PT
