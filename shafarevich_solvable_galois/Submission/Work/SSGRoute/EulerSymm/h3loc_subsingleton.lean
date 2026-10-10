import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.EulerSymm.sylow_datum
import Submission.Work.SSGRoute.PT.shapiro_H3_coind
import Submission.Work.SSGRoute.PTCore.h3loc_decomp_subsingleton
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_finiteIndex_subgroup
import Submission.Work.SSGRoute.PTfin.subsingleton_H3_of_isPGroup_action
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The third local cohomology of the decomposition group vanishes on finite coefficient modules

This file proves `Work.SSGRoute.EulerSymm.h3loc_subsingleton` (`cd_p(G_{k_v}) ≤ 2`), by the
`p`-Sylow route of `EULER_DESIGN` (nodes A2-A6), using the degree-three arithmetic and Shapiro
machinery of the `PT`/`PTembedding` lanes:

* `Work.SSGRoute.PTembedding.h3_triv_subsingleton_decomp` (via
  `Work.SSGRoute.EulerSymm.h3triv_subsingleton_fixingSubgroup`) — the local vanishing
  `H³(F, 𝔽_p) = 0` at a number field `F` containing `ζ_p`;
* `Work.SSGRoute.PTembedding.h3_subsingleton_of_pgroup_action` — the dévissage of `H³` from the
  trivial module over a finite `p`-group;
* `Work.SSGRoute.PTembedding.h3_subsingleton_of_finiteIndex_subgroup` — the transfer of
  `H³`-vanishing from an open subgroup of index prime to `p`;
* `Work.SSGRoute.PT.shapiro_H3_coind` — Shapiro's isomorphism in degree three;
* `Work.SSGRoute.EulerSymm.exists_sylowDatum` — the `p`-Sylow datum of the decomposition group.

The reduction `h3loc_subsingleton_of_sylowDatum` proves the target from that datum.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

open Work.SSGRoute
open scoped Pointwise

/-- **Sub-singleton transfer for `H³` along a homeomorphic group isomorphism** with a compatible
coefficient isomorphism. -/
theorem subsingleton_H3_of_homeomorph {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (h : Subsingleton (Work.SSGRoute.H3 (M := M') G')) :
    Subsingleton (Work.SSGRoute.H3 (M := M) G) := by
  refine ⟨fun a b => ?_⟩
  have h2 : (Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ).symm a
      = (Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ).symm b := h.elim _ _
  simpa using congrArg (fun x => (Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ) x) h2

/-- **Sub-singleton transfer for `H³` along a homeomorphic group isomorphism**, in the reverse
direction (from the codomain of `Φ` to its domain). -/
theorem subsingleton_H3_of_homeomorph' {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (h : Subsingleton (Work.SSGRoute.H3 (M := M) G)) :
    Subsingleton (Work.SSGRoute.H3 (M := M') G') := by
  refine ⟨fun a b => ?_⟩
  exact (Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ).injective
    (h.elim ((Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ) a)
      ((Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ) b))

/-- The canonical action of the decomposition group commutes with the `𝔽_p`-scalars. -/
theorem smulCommClass_decomp (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
    SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) M := by
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
  refine ⟨fun g c m => ?_⟩
  show SSGRoute.res k K ((g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • (c • m)
    = c • (SSGRoute.res k K ((g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • m)
  rw [smul_comm]

/-- **The reduction of the target to the `p`-Sylow datum of the decomposition group.** -/
theorem h3loc_subsingleton_of_sylowDatum (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (U : Subgroup ↥(SSGRoute.decomp k A))
    (hUopen : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    (hUfi : Subgroup.FiniteIndex U)
    (hUcop : Nat.Coprime U.index p)
    (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p ↥P) (act : ↥U →* ↥P)
    (hactres : ∀ u : ↥U, ((act u : ↥P) : K ≃ₐ[k] K)
      = SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω))
    (hdisc : letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
      Work.AbsoluteKummer.IsDiscreteModule ↥U M)
    (hbaseU : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥U)) :
    Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  classical
  haveI : Subgroup.FiniteIndex U := hUfi
  haveI : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp
      (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A).isCompact
  haveI : CompactSpace ↥U :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen U hUopen).isCompact
  -- the canonical action of `D_A`, and the `p`-group action on the coefficients
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
  haveI hcommD : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) M :=
    smulCommClass_decomp p k Ω K A M
  letI hPact : DistribMulAction ↥P M := DistribMulAction.compHom M (Subgroup.subtype P)
  haveI hcommP : SMulCommClass ↥P (ZMod p) M := ⟨fun g c m => by
    show ((g : ↥P) : K ≃ₐ[k] K) • (c • m) = c • (((g : ↥P) : K ≃ₐ[k] K) • m)
    rw [smul_comm]⟩
  have hact : ∀ (g : ↥U) (m : M), g • m = act g • m := fun g m => by
    change SSGRoute.res k K ((g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • m
      = ((act g : ↥P) : K ≃ₐ[k] K) • m
    rw [hactres g]
  -- the dévissage at `U`
  have hdev : Subsingleton (Work.SSGRoute.H3 (M := M) ↥U) :=
    Work.SSGRoute.PTfin.subsingleton_H3_of_isPGroup_action p hP act hact hdisc hbaseU
  -- Shapiro's isomorphism and the transfer `U ≤ D_A`
  have hshapiro : Nonempty (Work.SSGRoute.H3
      (M := Work.SSGRoute.PT.Coind ↥(SSGRoute.decomp k A) U M) ↥(SSGRoute.decomp k A) ≃+
      Work.SSGRoute.H3 (M := M) ↥U) :=
    Work.SSGRoute.PT.shapiro_H3_coind (G := ↥(SSGRoute.decomp k A)) U hUopen hdisc
  have hD : Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A)) :=
    Work.SSGRoute.PTembedding.h3_subsingleton_of_finiteIndex_subgroup p U hUopen
      hUcop hshapiro hdev
  -- the model bridge
  exact (Work.SSGRoute.PTCore.subsingleton_h3loc_iff_subsingleton_H3 p k Ω K M
    (SSGRoute.decomp k A)
    (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A)
    (fun h m => Work.SSGRoute.decomp_smul_eq_res K M A h m)).mpr hD

/-- The third local cohomology of the decomposition group at a finite place vanishes on finite
coefficient modules: `cd_p(G_{k_v}) ≤ 2` (Serre, Cohomologie galoisienne II.5; NSW 7.1.8). Same
statement as the filed `Work.SSGRoute.PTCore.h3loc_decomp_subsingleton`.

Route (EULER_DESIGN nodes A2-A6): let `L = K^Q · k(ζ_p)` where `Q` is the image in `Gal(K/k)` of a
Sylow `p`-subgroup of the image of `res k K : D_A →* Gal(K/k)`. Then `U = Gal(Ω/L) ∩ D_A` is open
of index prime to `p` in `D_A`, maps into the `p`-group `Q`, and has `H³(U, 𝔽_p) = 0` because `L`
is a number field containing `ζ_p` (`h3triv_subsingleton_fixingSubgroup`). The dévissage
`h3_subsingleton_of_pgroup_action` gives `H³(U,M) = 0` for every finite `𝔽_p[Gal(K/k)]`-module `M`,
and the Shapiro/transfer step `h3_subsingleton_of_finiteIndex_subgroup` transports this to
`H³(D_A, M) = 0`; `PTCore.subsingleton_h3loc_iff_subsingleton_H3` converts this into the statement
about `H3loc`. The datum is provided by `Work.SSGRoute.EulerSymm.exists_sylowDatum`. -/
theorem h3loc_subsingleton
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  obtain ⟨U, P, act, hP, hUopen, hUfi, hUcop, hactres, hdisc, hbaseU⟩ :=
    exists_sylowDatum p k Ω K A hA
  exact fun M _ _ _ _ _ => h3loc_subsingleton_of_sylowDatum p k Ω K A hA M U hUopen hUfi
    hUcop P hP act hactres (hdisc M) hbaseU

end Work.SSGRoute.EulerSymm
