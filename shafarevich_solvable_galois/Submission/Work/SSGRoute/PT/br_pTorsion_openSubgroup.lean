import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.PT.h2_equiv_of_equiv
import Submission.Work.SSGRoute.PT.isSolvable_algEquiv_of_finiteDimensional
import Submission.Work.SSGRoute.PTfin.exists_superlevel_p_dvd_index_finiteExtension
import Submission.Work.SSGRoute.PTfin.levelH2_cyclic_finiteExtension

namespace Work.SSGRoute.PT


/-- Build-speed: `IsAlgClosure k Ω` in the `variable` lines below needs
`Module.IsTorsionFree k Ω`, and the variables are re-elaborated for every declaration (about 2 s of
instance search each time). This file-local instance answers it directly. -/
private theorem file_isTorsionFree_fast {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] file_isTorsionFree_fast


open Work.AbsoluteKummer

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-! ## Transport of subgroups along a homeomorphic isomorphism -/

section SubgroupTransport

variable {G Γ : Type*} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ]

/-- The restriction of a bijective homomorphism `Φ : G ≃* Γ` to a subgroup `U ≤ Γ`, i.e. the
canonical isomorphism `Φ⁻¹(U) ≃* U`. -/
noncomputable def bropenSubgroupComapEquiv (Φ : G ≃* Γ) (U : Subgroup Γ) :
    ↥(U.comap Φ.toMonoidHom) ≃* ↥U where
  toFun x := ⟨Φ x.1, x.2⟩
  invFun y := ⟨Φ.symm y.1, by
    show Φ (Φ.symm y.1) ∈ U
    rw [MulEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul Φ x.1 y.1)

/-- An open subgroup of a topological group is closed. -/
theorem bropenIsClosedOfIsOpenSubgroup [IsTopologicalGroup Γ] (U : Subgroup Γ)
    (hU : IsOpen (U : Set Γ)) : IsClosed (U : Set Γ) :=
  Subgroup.isClosed_of_isOpen U hU

/-- The canonical isomorphism `Φ⁻¹(U) ≃* U` is a homeomorphism when `Φ` is one and `U` is open. -/
theorem bropenIsHomeomorphSubgroupComapEquiv [CompactSpace G] [T2Space Γ] [IsTopologicalGroup Γ]
    (Φ : G ≃* Γ) (hΦ : IsHomeomorph (Φ : G → Γ)) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) :
    IsHomeomorph (bropenSubgroupComapEquiv Φ U : ↥(U.comap Φ.toMonoidHom) → ↥U) := by
  have hclosed : IsClosed ((U.comap Φ.toMonoidHom : Subgroup G) : Set G) :=
    (bropenIsClosedOfIsOpenSubgroup U hU).preimage hΦ.continuous
  haveI : CompactSpace ↥(U.comap Φ.toMonoidHom) := isCompact_iff_compactSpace.mp hclosed.isCompact
  refine (isHomeomorph_iff_continuous_bijective).mpr
    ⟨?_, (bropenSubgroupComapEquiv Φ U).bijective⟩
  show Continuous fun x : ↥(U.comap Φ.toMonoidHom) => (⟨Φ x.1, x.2⟩ : ↥U)
  exact Continuous.subtype_mk (hΦ.continuous.comp continuous_subtype_val) (fun x => x.2)

end SubgroupTransport

section SubgroupImage

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The canonical isomorphism between a subgroup `U ≤ ↥D` of a subgroup `D` and its image in the
ambient group. -/
noncomputable def bropenSubgroupMapValEquiv (D : Subgroup G) (U : Subgroup ↥D) :
    ↥U ≃* ↥(U.map (Subgroup.subtype D)) :=
  { Equiv.ofBijective
      (fun x : ↥U => (⟨(x.1 : G), ⟨x.1, x.2, rfl⟩⟩ : ↥(U.map (Subgroup.subtype D))))
      ⟨fun x y h => by
          have h1 : (x.1 : G) = (y.1 : G) := by
            simpa using congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h1),
        fun y => by
          obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨u, hu⟩, Subtype.ext huy⟩⟩ with
    map_mul' := fun x y => Subtype.ext rfl }

/-- The image in the ambient group of a closed subgroup of a closed subgroup is closed. -/
theorem bropenIsClosedMapSubtype (D : Subgroup G) (hD : IsClosed (D : Set G)) (U : Subgroup ↥D)
    (hU : IsClosed (U : Set ↥D)) :
    IsClosed ((U.map (Subgroup.subtype D) : Subgroup G) : Set G) := by
  have h := hD.isClosedMap_subtype_val (U : Set ↥D) hU
  have h2 : (Subtype.val : ↥D → G) '' (U : Set ↥D) = (⇑(Subgroup.subtype D)) '' (U : Set ↥D) :=
    Set.image_congr (fun x _ => rfl)
  rw [Subgroup.coe_map, ← h2]
  exact h

/-- `bropenSubgroupMapValEquiv` is a homeomorphism (compact source, Hausdorff target). -/
theorem bropenIsHomeomorphSubgroupMapValEquiv [CompactSpace G] [T2Space G] (D : Subgroup G)
    (hD : IsClosed (D : Set G)) (U : Subgroup ↥D) (hU : IsClosed (U : Set ↥D)) :
    IsHomeomorph (bropenSubgroupMapValEquiv D U : ↥U → ↥(U.map (Subgroup.subtype D))) := by
  haveI : CompactSpace ↥D := isCompact_iff_compactSpace.mp hD.isCompact
  haveI : CompactSpace ↥U := isCompact_iff_compactSpace.mp hU.isCompact
  refine (isHomeomorph_iff_continuous_bijective).mpr
    ⟨?_, (bropenSubgroupMapValEquiv D U).bijective⟩
  show Continuous fun x : ↥U =>
    (⟨(x.1 : G), ⟨x.1, x.2, rfl⟩⟩ : ↥(U.map (Subgroup.subtype D)))
  exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
    (fun x => ⟨x.1, x.2, rfl⟩)

end SubgroupImage

/-- **Hilbert 90 at a closed subgroup of an absolute Galois group**: `H¹(H, Ωˣ) = 0`. -/
theorem bropenHilbert90ClosedSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [IsAlgClosure k Ω] [CharZero k]
    (H : Subgroup Gal(Ω/k)) (hH : IsClosed (H : Set Gal(Ω/k))) :
    Subsingleton (Work.AbsoluteKummer.H1 ↥H (Additive (Units Ω))) := by
  let M : IntermediateField k Ω := IntermediateField.fixedField H
  have hL : M.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩
  haveI hAlgM : Algebra.IsAlgebraic ↥M Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := ↥M) (A := Ω)
  haveI : IsAlgClosure ↥M Ω := ⟨IsAlgClosure.isAlgClosed k, hAlgM⟩
  haveI : IsGalois ↥M Ω := IsAlgClosure.isGalois ↥M Ω
  haveI : CharZero ↥M := inferInstance
  haveI : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥M] Ω) (Additive (Units Ω))) :=
    ⟨fun a b => by
      rw [Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥M Ω a,
        Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥M Ω b]⟩
  haveI : CompactSpace ↥(M.fixingSubgroup) := by
    have hclosed : IsClosed ((M.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
      rw [hL]; exact hH
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space (Ω ≃ₐ[↥M] Ω) := krullTopology_t2 (K := ↥M) (L := Ω)
  have hΦ : IsHomeomorph ((IntermediateField.fixingSubgroupEquiv M :
      ↥(M.fixingSubgroup) → (Ω ≃ₐ[↥M] Ω))) :=
    (isHomeomorph_iff_continuous_bijective).mpr
      ⟨PTembedding.MupCard.continuous_fixingSubgroupEquiv_of_charZero (k := k) (Ω := Ω) M,
        (IntermediateField.fixingSubgroupEquiv M).bijective⟩
  have h := Work.SSGRoute.PT.h1Transfer (G := Ω ≃ₐ[↥M] Ω) (G' := ↥(M.fixingSubgroup))
    (M := Additive (Units Ω)) (M' := Additive (Units Ω))
    (IntermediateField.fixingSubgroupEquiv M) hΦ (AddEquiv.refl (Additive (Units Ω)))
    (fun g' m' => rfl)
  have hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥H (Additive (Units Ω))) :=
    hL ▸ (⟨fun a b => h.injective (Subsingleton.elim _ _)⟩ :
      Subsingleton (Work.AbsoluteKummer.H1 ↥(M.fixingSubgroup) (Additive (Units Ω))))
  exact hsub

/-- **The Kummer step at an arbitrary subgroup of a decomposition group**: the `p`-torsion of
`H²(H, Ωˣ)` is `H²(H, μ_p)`, the Hilbert 90 input being a hypothesis. -/
theorem bropenKummerCardSubgroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (H : Subgroup ↥(SSGRoute.decomp k A))
    (hH1 : Subsingleton (Work.AbsoluteKummer.H1 ↥H (Additive (Units Ω)))) :
    Nat.card {x : Work.AbsoluteKummer.H2 ↥H (Additive (Units Ω)) // p • x = 0} =
      Nat.card (Work.AbsoluteKummer.H2 ↥H (Work.SSGRoute.PTembedding.MupCard.MuAdd p K)) := by
  classical
  haveI : IsTopologicalGroup ↥H := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hMU : Work.GroupCohomology.IsEquivariant ↥H
      (PTembedding.MupCard.muIota (p := p) (K := K)) :=
    fun h m => PTembedding.MupCard.muIota_equivariant (K := K) hζ hζK A
      (h : ↥(SSGRoute.decomp k A)) m
  have hPU : Work.GroupCohomology.IsEquivariant ↥H
      (PTembedding.MupCard.powPi (p := p) (Ω := Ω)) :=
    fun h u => PTembedding.MupCard.powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A)
      (h : ↥(SSGRoute.decomp k A)) u
  have hDM : Work.AbsoluteKummer.IsDiscreteModule ↥H (PTembedding.MupCard.MuAdd p K) := by
    intro m
    have hDA : IsOpen (MulAction.stabilizer ↥(SSGRoute.decomp k A) m :
        Set ↥(SSGRoute.decomp k A)) :=
      PTembedding.MupCard.isDiscreteModule_decomp_muAdd (K := K) hζ hζK A m
    have hset : (MulAction.stabilizer ↥H m : Set ↥H) =
        Subtype.val ⁻¹' (MulAction.stabilizer ↥(SSGRoute.decomp k A) m :
          Set ↥(SSGRoute.decomp k A)) := by
      ext h
      show h • m = m ↔ (h : ↥(SSGRoute.decomp k A)) • m = m
      rfl
    exact hset ▸ hDA.preimage continuous_subtype_val
  have hDN : Work.AbsoluteKummer.IsDiscreteModule ↥H (Additive (Units Ω)) := by
    intro m
    have hDA : IsOpen (MulAction.stabilizer ↥(SSGRoute.decomp k A) m :
        Set ↥(SSGRoute.decomp k A)) :=
      PTembedding.MupCard.isDiscreteModule_decomp_addUnits (k := k) (Ω := Ω) A m
    have hset : (MulAction.stabilizer ↥H m : Set ↥H) =
        Subtype.val ⁻¹' (MulAction.stabilizer ↥(SSGRoute.decomp k A) m :
          Set ↥(SSGRoute.decomp k A)) := by
      ext h
      show h • m = m ↔ (h : ↥(SSGRoute.decomp k A)) • m = m
      rfl
    exact hset ▸ hDA.preimage continuous_subtype_val
  let S : Work.AbsoluteKummer.ShortExactSeq ↥H (PTembedding.MupCard.MuAdd p K)
      (Additive (Units Ω)) (Additive (Units Ω)) :=
    { iota := PTembedding.MupCard.muIota (p := p) (K := K)
      pi := PTembedding.MupCard.powPi (p := p) (Ω := Ω)
      iota_equivariant := hMU
      pi_equivariant := hPU
      iota_injective := PTembedding.MupCard.muIota_injective (p := p) (K := K)
      pi_surjective := PTembedding.MupCard.powPi_surjective (p := p) (Ω := Ω)
      range_iota_eq_ker_pi := PTembedding.MupCard.range_muIota_eq_ker_powPi (K := K) hζ hζK
      isDiscreteM := hDM
      isDiscreteN := hDN
      isDiscreteP := hDN }
  have hPi : ∀ u : Additive (Units Ω), S.pi u = p • u := fun u =>
    PTembedding.MupCard.powPi_eq_nsmul (p := p) (Ω := Ω) u
  have hrange : (mapH2 S.iota S.iota_equivariant).range =
      (nsmulHom p (H2 ↥H (Additive (Units Ω)))).ker :=
    range_mapH2_eq_ker_nsmul p S hPi
  have hker : (mapH2 S.iota S.iota_equivariant).ker = ⊥ :=
    ker_mapH2_eq_bot_of_subsingleton p S hH1
  have hinj : Function.Injective (mapH2 S.iota S.iota_equivariant) := by
    rw [← AddMonoidHom.ker_eq_bot_iff]; exact hker
  let F : H2 ↥H (PTembedding.MupCard.MuAdd p K) →+ PTor p (H2 ↥H (Additive (Units Ω))) :=
    { toFun := fun x => ⟨mapH2 S.iota S.iota_equivariant x, by
        have hmem : mapH2 S.iota S.iota_equivariant x ∈
            (nsmulHom p (H2 ↥H (Additive (Units Ω)))).ker := by
          rw [← hrange]
          exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
        simpa [AddMonoidHom.mem_ker] using hmem⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hbij : Function.Bijective F := by
    refine ⟨fun x y hxy => hinj (Subtype.ext_iff.mp hxy), fun y => ?_⟩
    have hy : y.1 ∈ (mapH2 S.iota S.iota_equivariant).range := by
      rw [hrange, AddMonoidHom.mem_ker, nsmulHom_apply]
      exact (mem_PTor).mp y.2
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hcard : Nat.card (H2 ↥H (PTembedding.MupCard.MuAdd p K))
      = Nat.card (PTor p (H2 ↥H (Additive (Units Ω)))) :=
    Nat.card_congr (AddEquiv.ofBijective F hbij).toEquiv
  exact (show Nat.card {x : H2 ↥H (Additive (Units Ω)) // p • x = 0}
      = Nat.card (PTor p (H2 ↥H (Additive (Units Ω)))) from rfl).trans hcard.symm

/-- **The `p`-torsion of the local Brauer group of a finite extension of a `ℚ_p`-field**:
`#H²(G_F, μ_p) = p` for a finite extension `F` of the `Q`-adic completion of a number field `K`.
This is a copy of `PTdualControl.natCard_H2_rootsOfUnity_adicCompletion` with the level inputs
replaced by the finite-extension forms `levelH2_cyclic_finiteExtension` and
`PTfin.exists_superlevel_p_dvd_index_finiteExtension`. -/
theorem bropenNatCardH2RootsOfUnityFiniteExtension
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F : Type} [Field F] [Algebra (Q.adicCompletion K) F] [FiniteDimensional (Q.adicCompletion K) F] :
    Nat.card (Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
      (Additive (rootsOfUnity p (AlgebraicClosure F)))) = p := by
  classical
  haveI hk : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ (Q.adicCompletion K)))
  have hInj : Function.Injective (algebraMap (Q.adicCompletion K) F) :=
    RingHom.injective (algebraMap (Q.adicCompletion K) F)
  haveI hFc : CharZero F :=
    CharZero.of_addMonoidHom (algebraMap (Q.adicCompletion K) F).toAddMonoidHom (by simp) hInj
  haveI hgal : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F (AlgebraicClosure F)
  obtain ⟨eK⟩ := PTdualControl.H2_rootsOfUnity_equiv_ptorsion_units (k := F) p
  obtain ⟨φ, hφinj, hφmono, hφcov⟩ := PTCore.H2_units_level_structure (F := F)
  set W := Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
    (Additive (AlgebraicClosure F)ˣ) with hW
  -- the level maps, relabelled so that they start on the cocycle model `LevelH2 L`
  let ψ : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      PTCore.LevelH2 L →+ W :=
    fun L => (φ L).comp ((PTCore.h2LevelEquiv L).symm).toAddMonoidHom
  have hψ_apply : ∀ (L) (x : PTCore.LevelH2 L),
      ψ L x = φ L ((PTCore.h2LevelEquiv L).symm x) := fun L x => rfl
  have hψrange : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      Set.range (ψ L) = Set.range (φ L) := by
    intro L
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(PTCore.h2LevelEquiv L).symm x, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨PTCore.h2LevelEquiv L w, by rw [hψ_apply, AddEquiv.symm_apply_apply]⟩
  have hψinj : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      Function.Injective (ψ L) := fun L =>
    (hφinj L).comp (AddEquiv.injective (PTCore.h2LevelEquiv L).symm)
  have hψmono : ∀ (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F)),
      L.toIntermediateField ≤ L'.toIntermediateField → Set.range (ψ L) ⊆ Set.range (ψ L') := by
    intro L L' h
    rw [hψrange L, hψrange L']
    exact hφmono L L' h
  have hψcov : ∀ x : W, ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      x ∈ Set.range (ψ L) := by
    intro x
    obtain ⟨L, hL⟩ := hφcov x
    obtain ⟨z, hz⟩ := hL
    refine ⟨L, PTCore.h2LevelEquiv L z, ?_⟩
    show ψ L (PTCore.h2LevelEquiv L z) = x
    rw [hψ_apply, AddEquiv.symm_apply_apply, hz]
  set T : AddSubgroup W :=
    (Work.AbsoluteKummer.mapH2 (Kummer.kummerPi (k := F) p)
      (Kummer.kummerPi_equivariant (k := F) p)).ker with hT
  have hTmem : ∀ x : W, x ∈ T ↔ p • x = 0 := by
    intro x
    rw [hT, AddMonoidHom.mem_ker, PTdualControl.mapH2_kummerPi_eq_nsmul F p x]
  haveI : Module (ZMod p) ↥T := AddCommGroup.zmodModule (n := p) (G := ↥T) (fun x : ↥T => by
    refine Subtype.ext ?_
    simpa using (hTmem x.1).mp x.2)
  have hcyc : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      ∃ w : W, Set.range (ψ L) ⊆ AddSubgroup.zmultiples w := by
    intro L
    obtain ⟨u, hgen, -⟩ := levelH2_cyclic_finiteExtension (K := K) Q L
    refine ⟨ψ L u, ?_⟩
    rintro _ ⟨y, hy⟩
    have hy' : y ∈ AddSubgroup.zmultiples u := by rw [hgen]; trivial
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hy'
    exact ⟨m, by rw [← hy, ← hm, map_zsmul]⟩
  have hdep : ∀ x y : ↥T, ∃ c d : ZMod p, (c, d) ≠ 0 ∧ c • x + d • y = 0 := by
    intro x y
    have hpx : p • (x : W) = 0 := (hTmem x.1).mp x.2
    have hpy : p • (y : W) = 0 := (hTmem y.1).mp y.2
    obtain ⟨Lx, hLx⟩ := hψcov x.1
    obtain ⟨Ly, hLy⟩ := hψcov y.1
    have hxr : x.1 ∈ Set.range (ψ (Lx ⊔ Ly)) := by
      refine hψmono Lx (Lx ⊔ Ly) ?_ hLx
      exact le_sup_left
    have hyr : y.1 ∈ Set.range (ψ (Lx ⊔ Ly)) := by
      refine hψmono Ly (Lx ⊔ Ly) ?_ hLy
      exact le_sup_right
    obtain ⟨w, hw⟩ := hcyc (Lx ⊔ Ly)
    obtain ⟨m, n, hmn, hsum⟩ :=
      PTCore.zmultiples_pTorsion_int_dependent p w x.1 y.1 (hw hxr) (hw hyr) hpx hpy
    refine ⟨(m : ZMod p), (n : ZMod p), ?_, ?_⟩
    · intro h0
      exact hmn ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp (congrArg Prod.fst h0),
        (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp (congrArg Prod.snd h0)⟩
    · refine Subtype.ext ?_
      rw [Int.cast_smul_eq_zsmul (ZMod p) m x, Int.cast_smul_eq_zsmul (ZMod p) n y]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero, AddSubgroup.coe_zsmul]
      exact hsum
  have hne : ∃ z : ↥T, z ≠ 0 := by
    obtain ⟨L, -, hdvd⟩ := PTfin.exists_superlevel_p_dvd_index_finiteExtension (K := K) p Q
      (⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    obtain ⟨u, hgen, hord⟩ := levelH2_cyclic_finiteExtension (K := K) Q L
    have hbot : Module.finrank F
        ↥((⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
          IntermediateField F (AlgebraicClosure F)) = 1 := by
      rw [show ((⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
        IntermediateField F (AlgebraicClosure F)) = ⊥ from rfl]
      exact IntermediateField.finrank_bot
    rw [hbot, one_mul] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hn0 : Module.finrank F ↥(L : IntermediateField F (AlgebraicClosure F)) ≠ 0 :=
      ne_of_gt ((Module.finrank_pos_iff_of_free F
        ↥(L : IntermediateField F (AlgebraicClosure F))).mpr inferInstance)
    have hpu : p • (m • u) = 0 := by
      rw [← mul_nsmul' u p m, ← hm, ← hord]
      exact addOrderOf_nsmul_eq_zero u
    have hne0 : m • u ≠ 0 := by
      intro h0
      have hd : Module.finrank F ↥(L : IntermediateField F (AlgebraicClosure F)) ∣ m := by
        rw [← hord, addOrderOf_dvd_iff_nsmul_eq_zero]
        exact h0
      have hmp : m ≠ 0 := by
        intro h0'
        apply hn0
        calc Module.finrank F ↥(L : IntermediateField F (AlgebraicClosure F)) = p * m := hm
          _ = 0 := by rw [h0', mul_zero]
      have hmlt : m < Module.finrank F ↥(L : IntermediateField F (AlgebraicClosure F)) := by
        rw [hm]
        simpa using Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt
          (Nat.pos_of_ne_zero hmp)
      have hm0 : m = 0 := Nat.eq_zero_of_dvd_of_lt hd hmlt
      apply hn0
      calc Module.finrank F ↥(L : IntermediateField F (AlgebraicClosure F)) = p * m := hm
        _ = 0 := by rw [hm0, mul_zero]
    refine ⟨⟨ψ L (m • u), ?_⟩, ?_⟩
    · rw [hTmem, ← map_nsmul, hpu, map_zero]
    · intro hz
      have h1 : ψ L (m • u) = 0 := congrArg Subtype.val hz
      exact hne0 (hψinj L (by rw [h1, map_zero]))
  have hTcard : Nat.card ↥T = p := PTCore.card_eq_prime_of_pairwise_dependent p hdep hne
  exact (Nat.card_congr eK.toEquiv).trans hTcard

/-- **The `p`-torsion of the local Brauer group at an arbitrary open subgroup of a local Galois
group** — the level-wise class-formation axiom Milne, *ADT*, (1.1b): for the class formation
`(D_A, \bar k_v^×)` the invariant map `H²(U, \bar k_v^×) ≅ ℚ/ℤ` is compatible for every open
subgroup `U ≤ D_A`, so its `p`-torsion is `ℤ/p`.

`U` here is an arbitrary open subgroup of the decomposition group `D_A` (not merely the
decomposition group of a finite level `L/k` of number fields).  The statement is the general form
of `Work.SSGRoute.Nakayama.br_pTorsion` (which is the case `U = D_A`), and it is the arithmetic
input of the injectivity of the corestriction `cor : H²(U,C) → H²(G,C)` on `p`-torsion, hence of
the base case of Milne's dévissage of Theorem I.1.8.

Mathematically: `U ≅ G_M` for the local field `M = (Ω)^U` (a finite extension of `k_v`, by the
Galois correspondence for the profinite group `D_A`), and `Ω = M̄`, so
`H²(U, Ωˣ) = H²(G_M, M̄ˣ) = Br(M) = ℚ/ℤ`, whose `p`-torsion is `ℤ/p`.  Two proof routes:

* direct: re-run the nested-cyclic-level argument of `br_pTorsion` with the arbitrary `p`-adic
  base field `M` (its inputs — the level structure `H²(Gal(L/M), Lˣ) ≅ ℤ/[L:M]`
  (`PT/levelH2_structure.lean`), the level maps `psiTilde` (`PT/psiTilde_*`), the
  degree-divisibility statement (`PT/local_exists_degree_mul_level.lean`) — are level statements
  of local class field theory and hold for an arbitrary `p`-adic base; the statements in the tree
  are phrased for `Q.adicCompletion K`, so they must be instantiated or transported);
* via number fields: `M` is isomorphic to `L_w` for a suitable number field `L` (Krasner), and
  one transfers `br_pTorsion p L Ω' A'` along the corresponding homeomorphic group isomorphism
  `U ≅ decomp L A` using `PT.h2Transfer`. -/
theorem br_pTorsion_openSubgroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) :
    Nat.card {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} = p := by
  classical
  -- ### compactness bookkeeping
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  have hDAclosed : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := PTembedding.isClosed_decomp' k Ω A
  haveI : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp hDAclosed.isCompact
  haveI : IsTopologicalGroup ↥(SSGRoute.decomp k A) := inferInstance
  have hUclosed : IsClosed (U : Set ↥(SSGRoute.decomp k A)) :=
    bropenIsClosedOfIsOpenSubgroup U hU
  haveI : CompactSpace ↥U := isCompact_iff_compactSpace.mp hUclosed.isCompact
  -- ### a cyclotomic level
  obtain ⟨K, ζ, hζ, hζK, hKfin, hKgal⟩ := PTembedding.exists_galois_adjoin_primitiveRoot p k Ω
  haveI := hKfin
  haveI := hKgal
  -- ### Step 1: the Kummer reduction at `U`
  have hH1U : Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) := by
    have hU'closed : IsClosed ((U.map ((SSGRoute.decomp k A).subtype) :
        Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      bropenIsClosedMapSubtype (SSGRoute.decomp k A) hDAclosed U hUclosed
    have h1 : Subsingleton (Work.AbsoluteKummer.H1
        ↥(U.map ((SSGRoute.decomp k A).subtype)) (Additive (Units Ω))) :=
      bropenHilbert90ClosedSubgroup (U.map ((SSGRoute.decomp k A).subtype)) hU'closed
    have hΦ : IsHomeomorph (bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U :
        ↥U → ↥(U.map ((SSGRoute.decomp k A).subtype))) :=
      bropenIsHomeomorphSubgroupMapValEquiv (SSGRoute.decomp k A) hDAclosed U hUclosed
    have htr := h1Transfer (Φ := bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U) hΦ
      (AddEquiv.refl (Additive (Units Ω))) (fun g m => rfl)
    exact ⟨fun a b => htr.injective (Subsingleton.elim _ _)⟩
  rw [bropenKummerCardSubgroup p k Ω K ζ hζ hζK A U hH1U]
  -- ### the local picture
  let 𝔨 := PTembedding.localFieldOf k A hA
  letI : Algebra 𝔨 (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (PTCore.h2PrimeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  have halg : ∀ z : 𝔨,
      (algebraMap 𝔨 (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion (PTCore.h2PrimeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) z := fun _ => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion (PTCore.h2PrimeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k (PTCore.h2PrimeUnder k A hA) :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (PTCore.h2PrimeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
  haveI hSepM : IsSepClosure 𝔨 (PTCore.h2AdjoinField k Ω A hA) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion (PTCore.h2PrimeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg
  haveI hGalM : IsGalois 𝔨 (PTCore.h2AdjoinField k Ω A hA) := hSepM.isGalois
  haveI hAlgClM : IsAlgClosure 𝔨 (PTCore.h2AdjoinField k Ω A hA) :=
    IsSepClosure.isAlgClosure_of_perfectField 𝔨 _
  haveI hCharK : CharZero 𝔨 :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion (PTCore.h2PrimeUnder k A hA)
  -- ### the identification `D_A ≃* Gal(M/𝔨)` and the open subgroup `U₀`, the field `N`
  let Φ3 : Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨) ≃* ↥(SSGRoute.decomp k A) :=
    (NK.Mine.adjoinLocalEquiv (PTCore.h2PrimeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) halg hW).symm
  have hΦ3 : IsHomeomorph (Φ3 : Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨) →
      ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_symm _
      (NK.Mine.isHomeomorph_adjoinLocalEquiv (PTCore.h2PrimeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW)
  let U₀ : Subgroup Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨) := U.comap Φ3.toMonoidHom
  have hU₀open : IsOpen (U₀ : Set Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨)) :=
    hU.preimage hΦ3.continuous
  have hU₀closed : IsClosed (U₀ : Set Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨)) := by
    haveI : IsTopologicalGroup Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨) := inferInstance
    exact bropenIsClosedOfIsOpenSubgroup U₀ hU₀open
  let N : IntermediateField 𝔨 (PTCore.h2AdjoinField k Ω A hA) :=
    IntermediateField.fixedField U₀
  have hNfix : N.fixingSubgroup = U₀ :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U₀, hU₀closed⟩
  haveI hNfin : FiniteDimensional 𝔨 ↥N :=
    PT.finiteDimensional_fixedField_of_isOpen U₀ hU₀open
  -- ### Step 2: transfer `↥U ≅ ↥U₀` together with the `μ_p` coefficient
  obtain ⟨Ψ3, hΨ3⟩ :=
    PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv p k Ω A hA halg hW K ζ hζ hζK
  have hadj : ∀ g' : Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨),
      NK.Mine.adjoinLocalEquiv (PTCore.h2PrimeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) halg hW (Φ3 g') = g' := by
    intro g'
    change Φ3.symm (Φ3 g') = g'
    exact MulEquiv.symm_apply_apply Φ3 g'
  have hΨ3' : ∀ (g' : Gal(PTCore.h2AdjoinField k Ω A hA / 𝔨))
      (m' : Additive (rootsOfUnity p (PTCore.h2AdjoinField k Ω A hA))),
      Ψ3 (g' • m') = Φ3 g' • Ψ3 m' := by
    intro g' m'
    have h := hΨ3 (Φ3 g') m'
    rwa [hadj g'] at h
  have hΦ3U : IsHomeomorph (bropenSubgroupComapEquiv Φ3 U : ↥U₀ → ↥U) :=
    bropenIsHomeomorphSubgroupComapEquiv Φ3 hΦ3 U hU
  have hΨ3U : ∀ (g' : ↥U₀)
      (m' : Additive (rootsOfUnity p (PTCore.h2AdjoinField k Ω A hA))),
      Ψ3 (g' • m') = (bropenSubgroupComapEquiv Φ3 U g') • Ψ3 m' :=
    fun g' m' => hΨ3' g'.1 m'
  have htr2 := h2Transfer (Φ := bropenSubgroupComapEquiv Φ3 U) hΦ3U Ψ3 hΨ3U
  -- ### Step 3: `↥U₀ ≅ ↥(N.fixingSubgroup) ≅ Gal(M/↥N)`, the coefficient unchanged
  let ι : ↥U₀ ≃* ↥(N.fixingSubgroup) :=
    { toFun := fun x => (⟨x.1, (SetLike.ext_iff.mp hNfix x.1).mpr x.2⟩ : ↥(N.fixingSubgroup))
      invFun := fun y => (⟨y.1, (SetLike.ext_iff.mp hNfix y.1).mp y.2⟩ : ↥U₀)
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hιHomeo : IsHomeomorph (ι : ↥U₀ → ↥(N.fixingSubgroup)) := by
    haveI : CompactSpace ↥U₀ := isCompact_iff_compactSpace.mp hU₀closed.isCompact
    refine (isHomeomorph_iff_continuous_bijective).mpr ⟨?_, ι.bijective⟩
    exact Continuous.subtype_mk continuous_subtype_val _
  have htr3a := h2Transfer (Φ := ι) hιHomeo
    (AddEquiv.refl (Additive (rootsOfUnity p (PTCore.h2AdjoinField k Ω A hA))))
    (fun g' m' => rfl)
  have htr3b := h2Transfer (Φ := IntermediateField.fixingSubgroupEquiv N)
    (PT.isHomeomorph_fixingSubgroupEquiv 𝔨 (PTCore.h2AdjoinField k Ω A hA) N)
    (AddEquiv.refl (Additive (rootsOfUnity p (PTCore.h2AdjoinField k Ω A hA))))
    (fun g' m' => rfl)
  have htr3 := htr3a.trans htr3b
  -- ### Step 4: `Gal(M/↥N) ≅ G_N`, coefficients via the separable closure isomorphism
  haveI hAlgN : IsAlgClosure ↥N (PTCore.h2AdjoinField k Ω A hA) :=
    ⟨hAlgClM.isAlgClosed, Algebra.IsAlgebraic.tower_top (K := 𝔨) (L := ↥N)
      (A := (PTCore.h2AdjoinField k Ω A hA))⟩
  haveI hSepN : IsSepClosure ↥N (PTCore.h2AdjoinField k Ω A hA) := inferInstance
  haveI hGalN : IsGalois ↥N (PTCore.h2AdjoinField k Ω A hA) := hAlgN.isGalois
  let e : AlgebraicClosure ↥N ≃ₐ[↥N] (PTCore.h2AdjoinField k Ω A hA) :=
    IsSepClosure.equiv ↥N (AlgebraicClosure ↥N) (PTCore.h2AdjoinField k Ω A hA)
  have hAutHomeo : IsHomeomorph (AlgEquiv.autCongr e :
      (AlgebraicClosure ↥N ≃ₐ[↥N] AlgebraicClosure ↥N) →
        ((PTCore.h2AdjoinField k Ω A hA) ≃ₐ[↥N] (PTCore.h2AdjoinField k Ω A hA))) :=
    NK.Mine.isHomeomorph_autCongr e
  obtain ⟨Ψ4, hΨ4⟩ := PTembedding.rootsOfUnity_autCongr_equiv ↥N e p
  have htr4 := h2Transfer (Φ := e.autCongr) hAutHomeo Ψ4 hΨ4
  -- ### assembly
  rw [Nat.card_congr (htr2.symm.trans (htr3.trans htr4.symm)).toEquiv]
  exact bropenNatCardH2RootsOfUnityFiniteExtension p (Submission.NeukirchUchida.primeOf A hA)


end Work.SSGRoute.PT
