import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.EulerSymm.h3SylowStep
import Submission.Work.SSGRoute.EulerSymm.sylow_datum
import Submission.Work.SSGRoute.PTCore.h3loc_decomp_subsingleton
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_pgroup_action
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# `H³` of the decomposition group at a finite place vanishes

The requested statement

  `∀ M [finite 𝔽_p[Gal(K/k)]-module], Subsingleton (H3loc p k Ω K M (decomp k A))`

is `cd_p(D_A) ≤ 2` (`D_A = decomp k A = SSGRoute.decomp k A`; Serre, *Cohomologie galoisienne*,
II §5; Neukirch–Schmidt–Wingberg (7.1.8)).

## The route formalised here

No case split on the residue characteristic is needed: the `p`-Sylow route works uniformly, and
the arithmetic input `H³(D, 𝔽_p) = 0` is available at *every* finite place (see below).

1. **The model bridge** (`LTDDefs.H3locEquivH3`, via
   `PTCore.subsingleton_h3loc_iff_subsingleton_H3`): `H3loc p k Ω K M (decomp k A)` is the same as
   the standard continuous-cohomology model `H³(↥(decomp k A), M)` for the canonical action
   `decompDistribMulAction K M A`.

2. **The `p`-Sylow datum** (`EulerSymm.exists_sylowDatum`): for the finite Galois level `K/k`
   there is an open subgroup `U ≤ ↥(decomp k A)` of index prime to `p` and a homomorphism
   `act : ↥U →* ↥P` into a *finite `p`-group* `P ≤ Gal(K/k)` such that `act` is the restriction
   `res k K` and `H³(U, 𝔽_p) = 0`.  The vanishing of `H³(U, 𝔽_p)` is the arithmetic input: with
   `ζ` a primitive `p`-th root of unity in `Ω`, `k(ζ)/k` is finite Galois of degree dividing
   `p - 1` (`adjoin_primitiveRoot_isGalois_coprime`) and `U` is the decomposition group of `A`
   intersected with `Gal(Ω/L)` for the finite field `L = Ω^{res k K⁻¹(P)}·k(ζ) ∋ ζ`; there
   `H³(decomp(L,A), 𝔽_p) = 0` by `EulerSymm.h3triv_subsingleton_fixingSubgroup`
   (`cd_p(G_{L_𝔭}) ≤ 2` at the completion, via the Kummer sequence and the `p`-divisibility of
   the local Brauer group).

3. **Dévissage** (`PTembedding.h3_subsingleton_of_pgroup_action`): since `U` acts on the finite
   `𝔽_p[Gal(K/k)]`-module `M` through the finite `p`-group `P`, the vanishing of `H³(U, 𝔽_p)`
   implies `H³(U, M) = 0` (filtration of `M` with trivial quotients).

4. **Transfer** (`EulerSymm.h3CoprimeIndex`, via
   `EulerSymm.subsingleton_H3_decomp_of_subsingleton_H3_subgroup`): for the open subgroup
   `U ≤ ↥(decomp k A)` of index prime to `p`, `H³(U,M) = 0` implies `H³(D_A,M) = 0`
   (Shapiro in degree `3` plus an averaging over the cosets).

Combining 1–4 gives the statement.

## Relation to earlier work in the tree

The `p`-a-unit case was previously isolated in `h3loc_decomp_subsingleton_of_unit` (Hochschild–Serre
for `I_A ◁ D_A`, using `H²(I_A,·) = 0` and `H³(I_A,·) = 0`); that argument is *not* needed here and
is filed in `Work.SSGRoute.PTCore.h3loc_decomp_subsingleton_of_unit`.  The residue-characteristic
case is the one that the two-step reduction cannot reach (`H²(I_A, 𝔽_p) ≠ 0` there), but the
`p`-Sylow route above handles all places at once.
-/

namespace Work.SSGRoute.PT

/-- **`H³` of the decomposition group at a finite place vanishes on finite coefficient modules**:
`cd_p(G_{k_v}) ≤ 2` at every finite place `A` of `Ω` over the number field `k`, with no hypothesis
on the residue characteristic.  See the module docstring for the route. -/
theorem h3loc_decomp_subsingleton_of_finPlace
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  -- ## the `p`-Sylow datum of the decomposition group
  obtain ⟨U, P, act, hP, hUopen, hUfidx, hcop, hactres, _hdisc, hbaseU⟩ :=
    Work.SSGRoute.EulerSymm.exists_sylowDatum p k Ω K A hA
  -- ## the canonical action of `D_A` on `M` (through `res k K`)
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := Work.SSGRoute.decompDistribMulAction K M A
  haveI hUfi : U.FiniteIndex := hUfidx
  -- ## the compactness needed for the dévissage
  haveI hCompD : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp
      (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A).isCompact
  haveI hCompU : CompactSpace ↥U :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen U hUopen).isCompact
  -- ## the `p`-group homomorphism `U →* P` is the restriction `res k K`
  -- (defined on the nose, so that the induced action on `M` is *definitionally* the canonical one)
  let act' : ↥U →* ↥P :=
    { toFun := fun u => ⟨SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω),
        by rw [← hactres u]; exact (act u).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u w => Subtype.ext (by simp) }
  haveI hPcomm : SMulCommClass ↥P (ZMod p) M :=
    ⟨fun q c m => by
      show ((q : ↥P) : K ≃ₐ[k] K) • (c • m) = c • (((q : ↥P) : K ≃ₐ[k] K) • m)
      rw [smul_comm]⟩
  -- ## the action of `U` is discrete: it factors through the finite group `P`
  have hdiscU : Work.AbsoluteKummer.IsDiscreteModule ↥U M := by
    intro m
    refine Subgroup.isOpen_mono (show ((K.fixingSubgroup).subgroupOf
      (SSGRoute.decomp k A)).subgroupOf U ≤ MulAction.stabilizer ↥U m from ?_)
      (Subgroup.subgroupOf_isOpen _ _ (Subgroup.subgroupOf_isOpen _ _
        (IntermediateField.fixingSubgroup_isOpen K)))
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    have hu' : SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) = 1 := by
      have h2 : ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := hu
      have h3 : ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
        rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
          IntermediateField.restrictNormalHom_ker K]
        exact h2
      simpa using h3
    have h4 : ((act' u : ↥P) : K ≃ₐ[k] K) = 1 := by
      rw [show ((act' u : ↥P) : K ≃ₐ[k] K)
        = SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) from rfl, hu']
    rw [show u • m = ((act' u : ↥P) : K ≃ₐ[k] K) • m from rfl, h4, one_smul]
  -- ## dévissage: `H³(U, M) = 0` from `H³(U, 𝔽_p) = 0` and the `p`-group action
  have hdevU : Subsingleton (Work.SSGRoute.H3 (M := M) ↥U) :=
    Work.SSGRoute.PTembedding.h3_subsingleton_of_pgroup_action p hP act' hdiscU hbaseU
  -- ## the transfer back to `D_A` (index of `U` prime to `p`)
  have hD : Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A)) :=
    Work.SSGRoute.EulerSymm.subsingleton_H3_decomp_of_subsingleton_H3_subgroup p k Ω K A hA
      U hUopen hcop M hdiscU hdevU
  -- ## the model bridge `H³ ↦ H3loc`
  exact (Work.SSGRoute.PTCore.subsingleton_h3loc_iff_subsingleton_H3 p k Ω K M
    (SSGRoute.decomp k A)
    (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A)
    (fun h m => Work.SSGRoute.decomp_smul_eq_res K M A h m)).mpr hD

/-- **The residue-characteristic case** of the target, recorded as such (the `hp` hypothesis is
not used: the `p`-Sylow argument of `h3loc_decomp_subsingleton_of_finPlace` is uniform in the
residue characteristic). -/
theorem h3loc_decomp_subsingleton_of_residueChar
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hp : A.valuation ((p : ℚ) : Ω) < 1) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) :=
  h3loc_decomp_subsingleton_of_finPlace p k Ω K A hA

/-- **`H³` of the decomposition group at a finite place vanishes on finite coefficient modules**
(`cd_p(G_{k_v}) ≤ 2`; Serre, *Cohomologie galoisienne*, II §5; Neukirch–Schmidt–Wingberg 7.1.8). -/
theorem h3loc_decomp_subsingleton
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) :=
  h3loc_decomp_subsingleton_of_finPlace p k Ω K A hA

end Work.SSGRoute.PT
