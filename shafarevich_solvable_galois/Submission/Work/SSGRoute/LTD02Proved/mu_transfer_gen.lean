import Mathlib
import Submission.Work.SSGRoute.LTD02Proved.comap_index_iso
import Submission.Work.SSGRoute.PT.H2Transfer
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.PT.resH2_eq_zero_of_index_nsmul_eq_zero
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.AbsoluteKummer.Kummer.kummerSES
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv_general
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_autCongr_equiv
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
import Submission.NK.Mine.AdjoinLocalGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `μ_n`-transport of the local restriction statement to the decomposition group

The chain of transports

`H²(G_κ, μ_n(κ̄)) ≅ H²(Gal(M/𝔨), μ_n(M)) ≅ H²(D_A, μ_n(K))`

(two `h2Transfer`s, along `AlgEquiv.autCongr` of a `𝔨`-algebra isomorphism `κ̄ ≅ M` and along
`NK.Mine.adjoinLocalEquiv`), together with the naturality of `resH2` under a transfer and the local
statement `PT.local_resH2_mu_eq_zero` at the corresponding open subgroup, gives

`ltdResH2_mu_eq_zero_decomp_gen`: `resH2 U` kills the index-torsion of `H²(D_A, μ_n(K))`.
-/

open Classical
open scoped Pointwise

namespace Work.SSGRoute.LTD02Proved

open Work.AbsoluteKummer

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-! ## Restriction is natural in the coefficient module, and the local `μ_n`-statement -/

/-- The continuity condition `IsDiscreteModule` on the action of `G` restricts to any subgroup. -/
theorem ltdIsDiscreteModule_subgroup {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
    {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (h : Work.AbsoluteKummer.IsDiscreteModule G M) :
    Work.AbsoluteKummer.IsDiscreteModule ↥U M := by
  intro m
  show IsOpen (MulAction.stabilizer ↥U m : Set ↥U)
  have hG : IsOpen (MulAction.stabilizer G m : Set G) := h m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U) =
      Subtype.val ⁻¹' (MulAction.stabilizer G m : Set G) := by
    ext u
    simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def]
  rw [hset]
  exact hG.preimage continuous_subtype_val

/-- **Naturality of the restriction `H²(G,A) → H²(U,A)` in the coefficient module.** -/
theorem ltdResH2_mapH2 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] (U : Subgroup G)
    (f : A →+ B) (hf : Work.GroupCohomology.IsEquivariant G f) (x : Work.AbsoluteKummer.H2 G A) :
    Work.SSGRoute.PT.resH2 U (Work.AbsoluteKummer.mapH2 f hf x)
      = Work.AbsoluteKummer.mapH2 (G := ↥U) f (fun u a => hf (u : G) a)
          (Work.SSGRoute.PT.resH2 U x) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G A).comap (Work.AbsoluteKummer.Z2 G A).subtype) x
  rw [show x = Work.AbsoluteKummer.H2π G A c from hc.symm]
  rw [Work.AbsoluteKummer.mapH2_H2π (G := G) f hf c]
  rw [Work.SSGRoute.PT.resH2_H2π U (Work.AbsoluteKummer.mapZ2 f hf c)]
  rw [Work.SSGRoute.PT.resH2_H2π U c]
  rw [Work.AbsoluteKummer.mapH2_H2π (G := ↥U) f (fun u a => hf (u : G) a)
    (Work.SSGRoute.PT.resZ2 U c)]
  exact congrArg (Work.AbsoluteKummer.H2π ↥U B) (by ext p; rfl)

/-- **The Kummer injection `H²(U, μ_n) ↪ H²(U, F̄ˣ)` at an open subgroup.** -/
theorem ltdKummerIota_mapH2_injective (F : Type) [Field F] [CharZero F]
    (n : ℕ) [NeZero n] (U : Subgroup (Work.AbsoluteKummer.G F))
    (hU : IsOpen (U : Set (Work.AbsoluteKummer.G F))) :
    Function.Injective (Work.AbsoluteKummer.mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : Work.AbsoluteKummer.G F) a)) := by
  haveI : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F _
  have hMn : IsDiscreteModule ↥U (Additive (rootsOfUnity n (AlgebraicClosure F))) :=
    ltdIsDiscreteModule_subgroup (G := Work.AbsoluteKummer.G F) (U := U)
      (isDiscreteModule_addRootsOfUnity F n)
  have hNu : IsDiscreteModule ↥U (Additive (AlgebraicClosure F)ˣ) :=
    ltdIsDiscreteModule_subgroup (G := Work.AbsoluteKummer.G F) (U := U)
      (isDiscreteModule_addUnits F)
  let S : Work.AbsoluteKummer.ShortExactSeq ↥U (Additive (rootsOfUnity n (AlgebraicClosure F)))
      (Additive (AlgebraicClosure F)ˣ) (Additive (AlgebraicClosure F)ˣ) :=
    { iota := Kummer.kummerIota (k := F) n
      pi := Kummer.kummerPi (k := F) n
      iota_equivariant := fun u a => Kummer.kummerIota_equivariant (k := F) n
        (u : Work.AbsoluteKummer.G F) a
      pi_equivariant := fun u a => Kummer.kummerPi_equivariant (k := F) n
        (u : Work.AbsoluteKummer.G F) a
      iota_injective := Kummer.kummerIota_injective (k := F) n
      pi_surjective := Kummer.kummerPi_surjective (k := F) n
      range_iota_eq_ker_pi := Kummer.kummerIota_range_eq_ker_pi (k := F) n
      isDiscreteM := hMn
      isDiscreteN := hNu
      isDiscreteP := hNu }
  have hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (AlgebraicClosure F)ˣ)) :=
    Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup (k := F) (Ω := AlgebraicClosure F) U hU
  have hker : (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S]
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [show z = 0 from Subsingleton.elim z 0, map_zero]
    simp
  have hmaps : (Work.AbsoluteKummer.mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : Work.AbsoluteKummer.G F) a))
      = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant) := rfl
  rw [hmaps]
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hker

/-- **The local statement with `μ_n`-coefficients** (the `μ_n`-coefficient form of
`PT.local_resH2_eq_zero_of_index_nsmul_eq_zero`). -/
theorem ltdLocalResH2MulEqZero {K : Type} [Field K] [NumberField K]
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
  have hinj := ltdKummerIota_mapH2_injective (Q.adicCompletion K) n U' hU'
  have hmap : Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U') •
      (Work.AbsoluteKummer.mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
        (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hres := Work.SSGRoute.PT.local_resH2_eq_zero_of_index_nsmul_eq_zero (K := K) Q
    (Work.AbsoluteKummer.mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
      (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) U' hU' hmap
  have hnat := ltdResH2_mapH2 (G := Work.AbsoluteKummer.G (Q.adicCompletion K)) U'
    (Kummer.kummerIota (k := Q.adicCompletion K) n)
    (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x
  exact hinj (hnat.symm.trans hres)

/-! ## Naturality of `resH2` under a transfer -/

theorem ltdResCochain2_cochainTransfer2 {G G' : Type*} [Group G] [Group G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (Ψ : M' ≃+ M) (H : Subgroup G) (H' : Subgroup G')
    (ΦH : ↥H' ≃* ↥H) (hΦH : ∀ h' : ↥H', ((ΦH h' : ↥H) : G) = Φ (h' : G'))
    (c : G' × G' → M') :
    (Work.SSGRoute.PT.resCochain2 H (Work.SSGRoute.PT.cochainTransfer2 Φ Ψ c))
      = Work.SSGRoute.PT.cochainTransfer2 ΦH Ψ (Work.SSGRoute.PT.resCochain2 H' c) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  simp only [Work.SSGRoute.PT.resCochain2_apply, Work.SSGRoute.PT.cochainTransfer2_apply]
  refine congrArg (fun q => Ψ (c q)) (Prod.ext ?_ ?_)
  · exact Φ.injective (by
      rw [Φ.apply_symm_apply, ← hΦH (ΦH.symm p1), ΦH.apply_symm_apply])
  · exact Φ.injective (by
      rw [Φ.apply_symm_apply, ← hΦH (ΦH.symm p2), ΦH.apply_symm_apply])

theorem ltdResZ2_z2Transfer {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G')) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (H : Subgroup G) (H' : Subgroup G') (ΦH : ↥H' ≃* ↥H)
    (hΦHc : Continuous (ΦH.symm : ↥H → ↥H'))
    (hΦHa : ∀ h' : ↥H', ((ΦH h' : ↥H) : G) = Φ (h' : G'))
    (hΨH : ∀ (h' : ↥H') (m' : M'), Ψ (h' • m') = ΦH h' • Ψ m')
    (c : Work.AbsoluteKummer.Z2 G' M') :
    Work.SSGRoute.PT.resZ2 H (Work.SSGRoute.PT.z2Transfer Φ hΦc Ψ hΨ c)
      = Work.SSGRoute.PT.z2Transfer ΦH hΦHc Ψ hΨH (Work.SSGRoute.PT.resZ2 H' c) :=
  Subtype.ext (ltdResCochain2_cochainTransfer2 Φ Ψ H H' ΦH hΦHa (c : G' × G' → M'))

/-- **Naturality of the restriction under a transfer of `H²`.** -/
theorem ltdResH2_h2Transfer {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (H : Subgroup G) (H' : Subgroup G') (ΦH : ↥H' ≃* ↥H)
    (hΦH : IsHomeomorph (ΦH : ↥H' → ↥H))
    (hΦHa : ∀ h' : ↥H', ((ΦH h' : ↥H) : G) = Φ (h' : G'))
    (hΨH : ∀ (h' : ↥H') (m' : M'), Ψ (h' • m') = ΦH h' • Ψ m')
    (x : Work.AbsoluteKummer.H2 G' M') :
    Work.SSGRoute.PT.resH2 H (Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ x)
      = Work.SSGRoute.PT.h2Transfer ΦH hΦH Ψ hΨH (Work.SSGRoute.PT.resH2 H' x) := by
  classical
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G' M').comap (Work.AbsoluteKummer.Z2 G' M').subtype) x
  set hΦc : Continuous (Φ.symm : G → G') :=
    Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ with hhΦc
  set hΦHc : Continuous (ΦH.symm : ↥H → ↥H') :=
    Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv ΦH hΦH with hhΦHc
  show Work.SSGRoute.PT.resH2 H (Work.SSGRoute.PT.h2TransferAddHom Φ hΦc Ψ hΨ
        (Work.AbsoluteKummer.H2π G' M' c))
      = Work.SSGRoute.PT.h2TransferAddHom ΦH hΦHc Ψ hΨH
          (Work.SSGRoute.PT.resH2 H' (Work.AbsoluteKummer.H2π G' M' c))
  rw [Work.SSGRoute.PT.h2TransferAddHom_mk, Work.SSGRoute.PT.resH2_H2π,
      Work.SSGRoute.PT.resH2_H2π, Work.SSGRoute.PT.h2TransferAddHom_mk,
      ltdResZ2_z2Transfer Φ hΦc Ψ hΨ H H' ΦH hΦHc hΦHa hΨH c]

/-! ## The action of the decomposition group on `μ_n(K)` -/

/-- The action of the decomposition group of `A` on `μ_n ⊆ K`, through the restriction `res k K`
(the general exponent version of `PTembedding.MupCard.instDistribMulActionDecompMuAdd`). -/
noncomputable def ltdMuAddDecompAction (n : ℕ) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) :
    DistribMulAction ↥(SSGRoute.decomp k A) (Work.SSGRoute.PTembedding.MupCard.MuAdd n K) :=
  SSGRoute.decompDistribMulAction K (Work.SSGRoute.PTembedding.MupCard.MuAdd n K) A

attribute [local instance] ltdMuAddDecompAction

/-- `M = 𝔨·Ω ⊆ placeCompletion A`, the model of the separable closure of `𝔨 = k_𝔭` at which the
decomposition group acts. -/
abbrev ltdAdjoinField (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (NK.NeukirchUchida.placeCompletion A)] : Type :=
  ↥(NK.NeukirchUchida.adjoinPlaceCompletion (Submission.NeukirchUchida.primeOf A hA) A)

/-- **The `μ_n`-transport of the local restriction statement to `D_A`.** -/
theorem ltdResH2_mu_eq_zero_decomp_gen
    (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k
        (Submission.NeukirchUchida.primeOf A hA)) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k
        (Submission.NeukirchUchida.primeOf A hA),
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion k
          (Submission.NeukirchUchida.primeOf A hA))
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k
        (Submission.NeukirchUchida.primeOf A hA))
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.PTembedding.MupCard.MuAdd n K),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 →
        Work.SSGRoute.PT.resH2 U x = 0 := by
  intro x hx
  classical
  -- ### the two models of the local closure
  haveI hCharZero : CharZero (Work.SSGRoute.PTembedding.localFieldOf k A hA) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion (Submission.NeukirchUchida.primeOf A hA)
  haveI hSep : IsSepClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (ltdAdjoinField k Ω A hA) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion (Submission.NeukirchUchida.primeOf A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg
  haveI hGalM : IsGalois (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (ltdAdjoinField k Ω A hA) := hSep.isGalois
  haveI hGalCl : IsGalois (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)) :=
    IsAlgClosure.isGalois _ _
  -- ### the coefficient isomorphisms
  let e2 : AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃ₐ[
      Work.SSGRoute.PTembedding.localFieldOf k A hA] (ltdAdjoinField k Ω A hA) :=
    IsSepClosure.equiv (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)) (ltdAdjoinField k Ω A hA)
  obtain ⟨Ψ2, hΨ2⟩ := Work.SSGRoute.PTembedding.rootsOfUnity_autCongr_equiv
    (Work.SSGRoute.PTembedding.localFieldOf k A hA) e2 n
  obtain ⟨Ψ3, hΨ3⟩ := Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv_general
    n k Ω A hA halg hW K ζ hζ hζK
  -- ### the group isomorphism `D_A ≅ Gal(M/𝔨)`
  let Φ3 : Gal(ltdAdjoinField k Ω A hA / Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃*
      ↥(SSGRoute.decomp k A) :=
    (NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg hW).symm
  have hΦ3 : IsHomeomorph (Φ3 : Gal(ltdAdjoinField k Ω A hA /
      Work.SSGRoute.PTembedding.localFieldOf k A hA) → ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_symm _
      (NK.Mine.isHomeomorph_adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW)
  have hadj : ∀ g' : Gal(ltdAdjoinField k Ω A hA / Work.SSGRoute.PTembedding.localFieldOf k A hA),
      NK.Mine.adjoinLocalEquiv (Submission.NeukirchUchida.primeOf A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW (Φ3 g') = g' := by
    intro g'
    change Φ3.symm (Φ3 g') = g'
    exact MulEquiv.symm_apply_apply Φ3 g'
  have hΨ3' : ∀ (g' : Gal(ltdAdjoinField k Ω A hA /
        Work.SSGRoute.PTembedding.localFieldOf k A hA))
      (m' : Additive (rootsOfUnity n (ltdAdjoinField k Ω A hA))),
      Ψ3 (g' • m') = Φ3 g' • Ψ3 m' := by
    intro g' m'
    have h := hΨ3 (Φ3 g') m'
    rwa [hadj g'] at h
  -- ### the composite group isomorphism `G_κ ≅ D_A`
  let Φ2 : Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃*
      Gal(ltdAdjoinField k Ω A hA / Work.SSGRoute.PTembedding.localFieldOf k A hA) :=
    AlgEquiv.autCongr e2
  have hΦ2 : IsHomeomorph (Φ2 :
      Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) →
      Gal(ltdAdjoinField k Ω A hA / Work.SSGRoute.PTembedding.localFieldOf k A hA)) :=
    NK.Mine.isHomeomorph_autCongr e2
  let Φ : Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) ≃* ↥(SSGRoute.decomp k A) :=
    Φ2.trans Φ3
  have hΦ : IsHomeomorph (Φ :
      Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) → ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_trans Φ2 Φ3 hΦ2 hΦ3
  -- ### the composite coefficient isomorphism
  let Ψ : Additive (rootsOfUnity n
        (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA))) ≃+
      Additive (rootsOfUnity n K) := Ψ2.trans Ψ3
  have hΨ : ∀ (g' : Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA))
      (m' : Additive (rootsOfUnity n
        (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)))),
      Ψ (g' • m') = Φ g' • Ψ m' := by
    intro g' m'
    show Ψ3 (Ψ2 (g' • m')) = Φ3 (Φ2 g') • Ψ3 (Ψ2 m')
    exact (congrArg (fun z => Ψ3 z) (hΨ2 g' m')).trans (hΨ3' (Φ2 g') (Ψ2 m'))
  -- ### the composite transfer and the transported class
  let htr : Work.AbsoluteKummer.H2
        (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
          Work.SSGRoute.PTembedding.localFieldOf k A hA))
        (Additive (rootsOfUnity n
          (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)))) ≃+
      Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (rootsOfUnity n K)) :=
    Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ
  let y : Work.AbsoluteKummer.H2
        (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
          Work.SSGRoute.PTembedding.localFieldOf k A hA))
        (Additive (rootsOfUnity n
          (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)))) := htr.symm x
  have hxy : htr y = x := AddEquiv.apply_symm_apply htr x
  -- ### the corresponding open subgroup and its bookkeeping
  let U' : Subgroup (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA)) :=
    U.comap (Φ : _ →* ↥(SSGRoute.decomp k A))
  obtain ⟨e, heHomeo, hcoe, hU'open, hU'index⟩ :
      ∃ (e : ↥U' ≃* ↥U),
        IsHomeomorph (e : ↥U' → ↥U) ∧
        (∀ x : ↥U', ((e x : ↥U) : ↥(SSGRoute.decomp k A)) = Φ (x :
          Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
            Work.SSGRoute.PTembedding.localFieldOf k A hA))) ∧
        IsOpen ((U' : Set (Gal(AlgebraicClosure
            (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
          Work.SSGRoute.PTembedding.localFieldOf k A hA)))) ∧
        U'.index = U.index :=
    comap_index_iso Φ hΦ U hU
  haveI hU'fi : U'.FiniteIndex :=
    (Subgroup.finiteIndex_iff (H := U')).mpr (by
      rw [hU'index]
      exact (Subgroup.finiteIndex_iff (H := U)).mp inferInstance)
  have hcard : Nat.card (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) ⧸ U') =
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) := hU'index
  haveI hU'fintype : Fintype (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
      Work.SSGRoute.PTembedding.localFieldOf k A hA) ⧸ U') := by
    have hne : Nat.card (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) ⧸ U') ≠ 0 := by
      rw [hcard, Nat.card_eq_fintype_card]
      exact Fintype.card_ne_zero
    exact Fintype.ofFinite _
  -- ### the transported class is still killed by the index
  have hy : Nat.card (Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
        Work.SSGRoute.PTembedding.localFieldOf k A hA) ⧸ U') • y = 0 := by
    have h1 : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • y = 0 := by
      refine htr.injective ?_
      rw [map_nsmul, hxy, hx, map_zero]
    rw [hcard]
    exact h1
  -- ### the local statement
  have hres' : Work.SSGRoute.PT.resH2 U' y = 0 :=
    ltdLocalResH2MulEqZero (K := k) (Q := Submission.NeukirchUchida.primeOf A hA) n U' hU'open y hy
  -- ### the subgroup-level equivariance
  have hΨ' : ∀ (h' : ↥U') (m' : Additive (rootsOfUnity n
        (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA)))),
      Ψ (h' • m') = e h' • Ψ m' := by
    intro h' m'
    calc Ψ ((h' : Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
          Work.SSGRoute.PTembedding.localFieldOf k A hA)) • m')
        = Φ (h' : Gal(AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA) /
          Work.SSGRoute.PTembedding.localFieldOf k A hA)) • Ψ m' := hΨ (h' : _) m'
      _ = ((e h' : ↥U) : ↥(SSGRoute.decomp k A)) • Ψ m' := by rw [← hcoe h']
      _ = e h' • Ψ m' := rfl
  -- ### naturality of the restriction under the transfer
  have hnat := ltdResH2_h2Transfer Φ hΦ Ψ hΨ U U' e heHomeo hcoe hΨ' y
  rw [hxy, hres', map_zero] at hnat
  exact hnat

end

end Work.SSGRoute.LTD02Proved
