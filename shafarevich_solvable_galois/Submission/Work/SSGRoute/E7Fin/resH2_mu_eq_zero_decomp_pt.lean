import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7Fin.kummerUnitsTransfer
import Submission.Work.SSGRoute.E7Fin.rootsOfUnity_adjoinLocalEquiv_any
import Submission.Work.SSGRoute.LTD02Proved.comap_index_iso
import Submission.Work.SSGRoute.PT.resH2_eq_zero_of_index_nsmul_eq_zero
import Submission.Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup

/-!
# `res` kills the index-torsion of `H²(D_A, μ_n)`: the transport from the completion

`Work.SSGRoute.E7Fin.resH2_mu_eq_zero_decomp_pt` is the local-global transport of the *proved*
local statement `Work.SSGRoute.PT.local_resH2_mu_eq_zero` (restriction kills the index-torsion of
`H²(G_𝔨, μ_n)` for the completion `𝔨 = k_𝔭` of a number field at a finite prime `𝔭`):

for a finite place `A` of `Ω` over a number field `k`, an open finite-index subgroup
`U ≤ D_A = decomp k A` and every `n ≥ 1`, restriction kills the index-torsion of
`H²(D_A, μ_n(Ω))`.

The transport is along

* the homeomorphic group isomorphism `Φ : G_𝔨 ≃* D_A` built from `NK.Mine.adjoinLocalEquiv` and
  the comparison `AlgEquiv.autCongr` of two separable closures of `𝔨`, and
* the equivariant coefficient isomorphism `Ψ : μ_n(𝔨̄) ≃+ μ_n(Ω)` built from
  `PTembedding.rootsOfUnity_autCongr_equiv` and the proved
  `E7Fin.rootsOfUnity_adjoinLocalEquiv_any`,

using the naturality `PT.resH2_h2Transfer` of restriction under `PT.h2Transfer` and the
subgroup bookkeeping `LTD02Proved.comap_index_iso`.

This is the missing half of Milne, *ADT*, (1.1b) for the local class formation `(D_A, Ωˣ)`:
combined with the Kummer sequence `1 → μ_n → Ωˣ → Ωˣ → 1` it gives that restriction kills the
index-torsion of `H²(D_A, Ωˣ)`, which is `PT.resH2_kill_index_torsion`.
-/

open SSGRoute

namespace Work.SSGRoute.E7Fin

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **A primitive `n`-th root of unity in an algebraic closure of a number field**: an algebraic
closure of a field of characteristic `0` contains primitive `n`-th roots of unity for every
`n ≠ 0` (a separably closed field has enough roots of unity). -/
theorem primitiveRoot_of_isAlgClosure_pt (n : ℕ) [NeZero n] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI hcz : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
  haveI hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hSepC : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  haveI hNnz : NeZero ((n : ℕ) : Ω) := inferInstance
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

/-! ## Naturality of `resH2` under a transfer of `H²`

The two statements below are copies (under `_pt` names) of `PT.resH2_h2TransferAddHom` and
`PT.resH2_h2Transfer`.  They are reproduced here because the file holding them cannot be imported
together with the proved local statement `PT.local_resH2_mu_eq_zero` (both define
`PT.resH2_mapH2`). -/

/-- **Naturality of the restriction under a transfer of `H²` along a homeomorphic isomorphism of
groups, at the level of the underlying additive maps.** -/
theorem resH2_h2TransferAddHom_pt {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
    [DistribMulAction G' M'] (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (U : Subgroup G) (U' : Subgroup G') (e : ↥U' ≃* ↥U)
    (hec : Continuous (e.symm : ↥U → ↥U'))
    (hcoe : ∀ u' : ↥U', ((e u' : ↥U) : G) = Φ (u' : G'))
    (hΨ' : ∀ (g' : ↥U') (m' : M'), Ψ (g' • m') = e g' • Ψ m')
    (x : Work.AbsoluteKummer.H2 G' M') :
    Work.SSGRoute.PT.resH2 U (Work.SSGRoute.PT.h2TransferAddHom Φ hΦc Ψ hΨ x)
      = Work.SSGRoute.PT.h2TransferAddHom e hec Ψ hΨ' (Work.SSGRoute.PT.resH2 U' x) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G' M').comap (Work.AbsoluteKummer.Z2 G' M').subtype) x
  have hc' : x = Work.AbsoluteKummer.H2π G' M' c := hc.symm
  rw [hc']
  have h1 : Work.SSGRoute.PT.h2TransferAddHom Φ hΦc Ψ hΨ (Work.AbsoluteKummer.H2π G' M' c)
      = Work.AbsoluteKummer.H2π G M (Work.SSGRoute.PT.z2Transfer Φ hΦc Ψ hΨ c) :=
    Work.SSGRoute.PT.h2TransferAddHom_mk Φ hΦc Ψ hΨ c
  have h3 : Work.SSGRoute.PT.h2TransferAddHom e hec Ψ hΨ'
        (Work.SSGRoute.PT.resH2 U' (Work.AbsoluteKummer.H2π G' M' c))
      = Work.AbsoluteKummer.H2π ↥U M
          (Work.SSGRoute.PT.z2Transfer e hec Ψ hΨ' (Work.SSGRoute.PT.resZ2 U' c)) := by
    rw [Work.SSGRoute.PT.resH2_H2π (A := M') U' c]
    exact Work.SSGRoute.PT.h2TransferAddHom_mk e hec Ψ hΨ' (Work.SSGRoute.PT.resZ2 U' c)
  rw [h1, Work.SSGRoute.PT.resH2_H2π (A := M) U (Work.SSGRoute.PT.z2Transfer Φ hΦc Ψ hΨ c), h3]
  exact congrArg (Work.AbsoluteKummer.H2π ↥U M) (by
    apply Subtype.ext
    funext p
    obtain ⟨p1, p2⟩ := p
    have key1 : ((e.symm p1 : ↥U') : G') = Φ.symm (p1 : G) := by
      have h : Φ (((e.symm p1 : ↥U') : G')) = ((p1 : ↥U) : G) := by
        rw [← hcoe (e.symm p1), MulEquiv.apply_symm_apply]
      rw [← h, MulEquiv.symm_apply_apply]
    have key2 : ((e.symm p2 : ↥U') : G') = Φ.symm (p2 : G) := by
      have h : Φ (((e.symm p2 : ↥U') : G')) = ((p2 : ↥U) : G) := by
        rw [← hcoe (e.symm p2), MulEquiv.apply_symm_apply]
      rw [← h, MulEquiv.symm_apply_apply]
    simp only [Work.SSGRoute.PT.resZ2_coe, Work.SSGRoute.PT.z2Transfer_coe,
      Work.SSGRoute.PT.cochainTransfer2_apply, key1, key2])

/-- **Naturality of the restriction under a transfer of `H²` along a homeomorphic isomorphism of
groups.** -/
theorem resH2_h2Transfer_pt {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
    [DistribMulAction G' M'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (U : Subgroup G) (U' : Subgroup G') (e : ↥U' ≃* ↥U)
    (he : IsHomeomorph (e : ↥U' → ↥U))
    (hcoe : ∀ u' : ↥U', ((e u' : ↥U) : G) = Φ (u' : G'))
    (hΨ' : ∀ (g' : ↥U') (m' : M'), Ψ (g' • m') = e g' • Ψ m')
    (x : Work.AbsoluteKummer.H2 G' M') :
    Work.SSGRoute.PT.resH2 U (Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ x)
      = Work.SSGRoute.PT.h2Transfer e he Ψ hΨ' (Work.SSGRoute.PT.resH2 U' x) :=
  resH2_h2TransferAddHom_pt Φ
    (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ U U' e
    (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv e he) hcoe hΨ' x

/-! ## The local `μ_n`-statement at the completion

The two statements below are copies (under `_pt` names) of the auxiliary results of
`PT/local_resH2_mu_eq_zero.lean`, together with the local statement itself
`local_resH2_mu_eq_zero_pt`.  They are reproduced here because the file holding them cannot be
imported together with the transfer file `PT/corH2_injective_on_ptorsion_localTransport` (both
define `PT.resH2_mapH2`), while the latter is needed elsewhere in this workspace. -/

open Work.AbsoluteKummer

/-- The continuity condition `IsDiscreteModule` on the action of `Γ` restricts to any subgroup. -/
theorem isDiscreteModule_subgroup_pt {Γ : Type*} [TopologicalSpace Γ] [Group Γ] {M : Type*}
    [AddCommGroup M] [DistribMulAction Γ M] (h : IsDiscreteModule Γ M) (U : Subgroup Γ) :
    IsDiscreteModule ↥U M := by
  intro m
  show IsOpen (MulAction.stabilizer ↥U m : Set ↥U)
  have hG : IsOpen (MulAction.stabilizer Γ m : Set Γ) := h m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U) =
      Subtype.val ⁻¹' (MulAction.stabilizer Γ m : Set Γ) := by
    ext u
    simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def]
  rw [hset]
  exact hG.preimage continuous_subtype_val

/-- **The Kummer injection `H²(U, μ_n) ↪ H²(U, F̄ˣ)` at an open subgroup.** -/
theorem kummerIota_mapH2_injective_openSubgroup_pt (F : Type) [Field F] [CharZero F]
    (n : ℕ) [NeZero n] (U : Subgroup (G F)) (hU : IsOpen (U : Set (G F))) :
    Function.Injective (mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a)) := by
  haveI : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F _
  have hMn : IsDiscreteModule ↥U (Additive (rootsOfUnity n (AlgebraicClosure F))) :=
    isDiscreteModule_subgroup_pt (isDiscreteModule_addRootsOfUnity F n) U
  have hNu : IsDiscreteModule ↥U (Additive (AlgebraicClosure F)ˣ) :=
    isDiscreteModule_subgroup_pt (isDiscreteModule_addUnits F) U
  let S : ShortExactSeq ↥U (Additive (rootsOfUnity n (AlgebraicClosure F)))
      (Additive (AlgebraicClosure F)ˣ) (Additive (AlgebraicClosure F)ˣ) :=
    { iota := Kummer.kummerIota (k := F) n
      pi := Kummer.kummerPi (k := F) n
      iota_equivariant := fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a
      pi_equivariant := fun u a => Kummer.kummerPi_equivariant (k := F) n (u : G F) a
      iota_injective := Kummer.kummerIota_injective (k := F) n
      pi_surjective := Kummer.kummerPi_surjective (k := F) n
      range_iota_eq_ker_pi := Kummer.kummerIota_range_eq_ker_pi (k := F) n
      isDiscreteM := hMn
      isDiscreteN := hNu
      isDiscreteP := hNu }
  have hsub : Subsingleton (H1 ↥U (Additive (AlgebraicClosure F)ˣ)) :=
    Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup (k := F) (Ω := AlgebraicClosure F) U hU
  have hker : (mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S]
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [show z = 0 from Subsingleton.elim z 0, map_zero]
    simp
  have hmaps : (mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a))
      = (mapH2 S.iota S.iota_equivariant) := rfl
  rw [hmaps]
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hker

/-- **Restriction kills the index-torsion of `H²(G_𝔨, μ_n)`** for the completion `𝔨 = K_Q` of a
number field at a finite prime: the local-field statement, obtained from the units form
`PT.local_resH2_eq_zero_of_index_nsmul_eq_zero` along the Kummer injection. -/
theorem local_resH2_mu_eq_zero_pt {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) [NeZero n]
    (U' : Subgroup (Work.AbsoluteKummer.G (Q.adicCompletion K)))
    (hU' : IsOpen (U' : Set (Work.AbsoluteKummer.G (Q.adicCompletion K))))
    [U'.FiniteIndex] [Fintype (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U')]
    (x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
        (Additive (rootsOfUnity n (AlgebraicClosure (Q.adicCompletion K))))) :
    Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U') • x = 0 →
      Work.SSGRoute.PT.resH2 U' x = 0 := by
  intro hx
  haveI hcz : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  haveI hgal : IsGalois (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)) :=
    IsAlgClosure.isGalois _ _
  have hinj := kummerIota_mapH2_injective_openSubgroup_pt (Q.adicCompletion K) n U' hU'
  have hmap : Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U') •
      (mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
        (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hres := Work.SSGRoute.PT.local_resH2_eq_zero_of_index_nsmul_eq_zero (K := K) Q
    (mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
      (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) U' hU' hmap
  have hnat := Work.SSGRoute.E7Fin.resH2_mapH2
    (G := Work.AbsoluteKummer.G (Q.adicCompletion K)) U'
    (Kummer.kummerIota (k := Q.adicCompletion K) n)
    (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x
  exact hinj (hnat.symm.trans hres)

/-- **Transport of "restriction kills the index-torsion" along a homeomorphic isomorphism of
topological groups and an equivariant identification of coefficient modules.**

If the statement holds for every open finite-index subgroup of `G'`, then it holds for every open
finite-index subgroup of `G`: a class `x` of index-torsion is transported by `PT.h2Transfer` to a
class `x'` of index-torsion over the preimage subgroup `Φ ⁻¹' U` (whose index equals that of `U`,
`LTD02Proved.comap_index_iso`), and the conclusion is pulled back along
`resH2_h2Transfer_pt`. -/
theorem resH2_index_torsion_transport_pt {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
    [DistribMulAction G' M'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (hloc : ∀ (U' : Subgroup G') (_ : IsOpen (U' : Set G')) [U'.FiniteIndex]
      [Fintype (G' ⧸ U')] (x' : Work.AbsoluteKummer.H2 G' M'),
      Nat.card (G' ⧸ U') • x' = 0 → Work.SSGRoute.PT.resH2 U' x' = 0) :
    ∀ x : Work.AbsoluteKummer.H2 G M, Nat.card (G ⧸ U) • x = 0 →
      Work.SSGRoute.PT.resH2 U x = 0 := by
  intro x hx
  let U' : Subgroup G' := U.comap (Φ : G' →* G)
  obtain ⟨e, he, hval, hU'open, hindex⟩ :=
    Work.SSGRoute.LTD02Proved.comap_index_iso Φ hΦ U hU
  have hindex' : U'.index = U.index := hindex
  haveI hFinI : U'.FiniteIndex := ⟨by
    rw [hindex']
    exact Subgroup.index_ne_zero_of_finite (H := U)⟩
  have hcard : Nat.card (G' ⧸ U') = Nat.card (G ⧸ U) := by
    rw [← Subgroup.index_eq_card U', hindex', Subgroup.index_eq_card U]
  haveI hFinQ : Fintype (G' ⧸ U') := by
    haveI : Finite (G' ⧸ U') := Nat.finite_of_card_ne_zero (by
      rw [hcard, ← Subgroup.index_eq_card U]
      exact Subgroup.index_ne_zero_of_finite (H := U))
    exact Fintype.ofFinite _
  let T := Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ
  have hx'' : Nat.card (G' ⧸ U') • T.symm x = 0 := by
    rw [hcard]
    apply T.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero]
    exact hx
  have hloc0 : Work.SSGRoute.PT.resH2 U' (T.symm x) = 0 := hloc U' hU'open (T.symm x) hx''
  have hΨ' : ∀ (g' : ↥U') (m' : M'), Ψ (g' • m') = e g' • Ψ m' := by
    intro g' m'
    have h := hΨ (g' : G') m'
    rw [← hval g'] at h
    exact h
  have hnat := resH2_h2Transfer_pt (Φ := Φ) hΦ Ψ hΨ U U' e he hval hΨ' (T.symm x)
  calc Work.SSGRoute.PT.resH2 U x
      = Work.SSGRoute.PT.resH2 U (Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ (T.symm x)) := by
          rw [AddEquiv.apply_symm_apply]
    _ = Work.SSGRoute.PT.h2Transfer e he Ψ hΨ'
          (Work.SSGRoute.PT.resH2 U' (T.symm x)) := hnat
    _ = 0 := by rw [hloc0, map_zero]

/-- **`res` kills the index-torsion of `H²(D_A, μ_n)`.**

For a finite place `A` of `Ω` over the number field `k`, an open subgroup `U ≤ D_A` of finite index
and `n ≥ 1`, every class of `H²(D_A, μ_n(Ω))` annihilated by the index `[D_A : U]` restricts to
zero on `U`.

This is the transport of the proved local statement `PT.local_resH2_mu_eq_zero` from the
completion `𝔨 = k_𝔭` to the decomposition group `D_A` along a homeomorphic group isomorphism and an
equivariant identification of the `n`-th roots of unity. -/
theorem resH2_mu_eq_zero_decomp_pt (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (rootsOfUnity n Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 → Work.SSGRoute.PT.resH2 U x = 0 := by
  classical
  -- ## a primitive `n`-th root of unity in `Ω`
  obtain ⟨ζ, hζ⟩ := primitiveRoot_of_isAlgClosure_pt n k Ω
  -- ## the ambient local data at the prime `𝔭` of `k` below `A`
  let 𝔭 := Submission.NeukirchUchida.primeOf A hA
  have hspec : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 :=
    Submission.NeukirchUchida.primeOf_spec A hA
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec).toAlgebra
  have halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭,
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec z := fun _ => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k 𝔭 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A hspec
  haveI hSep : IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A hspec halg
  -- ## the comparison of the two separable closures of `𝔨`
  let e2 : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭]
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) :=
    IsSepClosure.equiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))
  obtain ⟨Ψ2, hΨ2⟩ := Work.SSGRoute.PTembedding.rootsOfUnity_autCongr_equiv
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭) e2 n
  -- ## the coefficient identification `μ_n(𝔨·Ω) ≃ μ_n(Ω)`
  obtain ⟨Ψ0, hΨ0⟩ := rootsOfUnity_adjoinLocalEquiv_any n k Ω A hA halg hW ζ hζ
  -- ## the group identification `G_𝔨 ≃* D_A` and the coefficient identification `μ_n(𝔨̄) ≃ μ_n(Ω)`
  let Φ3 : ((↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭]
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) ≃* ↥(SSGRoute.decomp k A) :=
    (NK.Mine.adjoinLocalEquiv 𝔭 A hspec halg hW).symm
  have hΦ3 : IsHomeomorph (Φ3 : ((↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭]
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))) → ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_symm _
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A hspec halg hW)
  have hadj : ∀ w : ((↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A)) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭]
      (↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A))),
      NK.Mine.adjoinLocalEquiv 𝔭 A hspec halg hW (Φ3 w) = w := by
    intro w
    exact MulEquiv.apply_symm_apply (NK.Mine.adjoinLocalEquiv 𝔭 A hspec halg hW) w
  let Φ : Work.AbsoluteKummer.G (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭) ≃*
      ↥(SSGRoute.decomp k A) := (AlgEquiv.autCongr e2).trans Φ3
  have hΦ : IsHomeomorph (Φ : Work.AbsoluteKummer.G
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭) → ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_trans (AlgEquiv.autCongr e2) Φ3 (NK.Mine.isHomeomorph_autCongr e2) hΦ3
  let Ψ : Additive (rootsOfUnity n (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))) ≃+
      Additive (rootsOfUnity n Ω) := Ψ2.trans Ψ0
  have hΨ : ∀ (g' : Work.AbsoluteKummer.G
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))
      (m' : Additive (rootsOfUnity n (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)))),
      Ψ (g' • m') = Φ g' • Ψ m' := by
    intro g' m'
    have h1 := hΨ2 g' m'
    have h2 := hΨ0 (Φ3 (AlgEquiv.autCongr e2 g')) (Ψ2 m')
    rw [hadj] at h2
    rw [AddEquiv.trans_apply, h1]
    exact h2
  -- ## the transport of the local statement
  refine resH2_index_torsion_transport_pt Φ hΦ Ψ hΨ U hU
    (fun (U'' : Subgroup (Work.AbsoluteKummer.G
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)))
        (hU'' : IsOpen (U'' : Set (Work.AbsoluteKummer.G
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))))
        [U''.FiniteIndex]
        [Fintype (Work.AbsoluteKummer.G
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭) ⧸ U'')]
        (x'' : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))
          (Additive (rootsOfUnity n (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭))))) =>
      local_resH2_mu_eq_zero_pt (K := k) 𝔭 n U'' hU'' x'')

end

end Work.SSGRoute.E7Fin
