import Mathlib
import Submission.Work.SSGRoute.NodeShim.perfectRightBricks
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_p_dvd_stab
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_ge_p_dvd_stab
import Submission.Work.SSGRoute.local_duality_ext_in
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.g1plus_finHalf
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
import Submission.Work.SSGRoute.E7cOmega.card_stab_eq_of_liesOver
import Submission.Work.SSGRoute.E7cOmega.card_stab_dvd_of_tower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (4)-right of `G1⁺`: perfectness of the finite half in the second variable

The local pairing at a finite place `A` (`pair (decomp k A)`, given abstractly with its value formula
`hpair` in terms of the local dictionary `βl`) is perfect in its *second* variable: a locally
constant `M^∨(1)`-cocycle `b` which pairs to zero with every locally constant `M`-cocycle is a
coboundary on `decomp k A`.

Route (as in the docstring of the interface): if `b` is not a coboundary, pass to a level `L ≥ L₀`
through which `b|decomp k A` factors and at which the decomposition group of the place of `L` under
`A` has order divisible by `p` (`PT.G1plusOwn.exists_level_ge_p_dvd_stab`).  At that level the
`p`-torsion of `H²(D_{w'}, L_{w'}ˣ)` is one-dimensional, so `χ ∘ ι_w` detects `p`-torsion local
classes (`NodeShim.perfectRightBricks.chi_iota_ne_zero_of_ptorsion_ne_zero`).  The value formula
`hpair` turns the vanishing hypothesis (which ranges over `im βl = Ext¹`, by the surjectivity clause
`hβl_onto`) into the vanishing of the level pairing of `finZH b` against *every* class of `Ext¹`,
whence `finZH b = 0` by the right detection of the local Yoneda pairing
(`SSGRoute.local_duality_ext_detect_h`).  Finally `finZH b = 0` is read off as a coboundary
witness: the level class is the `H¹`-class of the factorised cocycle `b₀` under the degree-one
bridge `ExtH1.gammaHom`, whose kernel is `B¹` (`ExtH1.gammaZ1_eq_zero_iff`), and a `B¹`-witness on
`D_{w'}` restricts to a coboundary witness on `decomp k A` (`finZF_spec`, `galRes_trans`).
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT.G1plusOwn

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Helpers

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- In a `ZMod p`-module, `p • x = 0`. -/
theorem g1r_nsmul_p_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod p) V] (x : V) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]

/-- The `𝔽_p`-dual of `M ⊗ T` is finite (the `[Finite M]` input at the Tate dual
`M^∨(1) = DualMod p (M ⊗ T)`). -/
theorem g1r_finite_dualMod_tensor (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := by
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (R := ZMod p) (M := T) (by rw [hT.1]; exact Nat.one_pos)
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  haveI hTfin : Finite T := Finite.of_injective u u.injective
  let isoE : M ≃ₗ[ZMod p] (M ⊗[ZMod p] T) :=
    (TensorProduct.rid (ZMod p) M).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod p) M) u).symm)
  haveI hMT : Finite (M ⊗[ZMod p] T) := Finite.of_injective isoE.symm isoE.symm.injective
  exact Finite.of_injective
    (fun f : Work.SSGRoute.DualMod p (M ⊗[ZMod p] T) => (f : (M ⊗[ZMod p] T) → ZMod p))
    (fun f g h => LinearMap.ext (fun x => congrFun h x))

/-- **The inverse of the coboundary witness**: if the factorised cocycle `b₀` is the coboundary of
`m` for the `D_w`-action pulled back along the place glue `finZF`, then `b` is a coboundary on
`decomp k A`. -/
theorem g1r_isCoboundaryOn_of_finZF_d0
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hm : ∀ g : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))),
      b₀ (g : ↥L ≃ₐ[k] ↥L)
        = ((Work.SSGRoute.PT.finZF hKL A hA g :
              ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) :
            ↥K ≃ₐ[k] ↥K) • m - m) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b := by
  refine ⟨m, fun σ hσ => ?_⟩
  have hg : (SSGRoute.res k L σ) ∈
      Subgroup.map (SSGRoute.res k L) (SSGRoute.decomp k A) :=
    Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
  rw [Work.SSGRoute.PT.finQW_glue L A hA] at hg
  have h1 : b₀ ((SSGRoute.res k L σ) : ↥L ≃ₐ[k] ↥L)
      = ((Work.SSGRoute.PT.finZF hKL A hA ⟨SSGRoute.res k L σ, hg⟩ :
            ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) :
          ↥K ≃ₐ[k] ↥K) • m - m :=
    hm ⟨SSGRoute.res k L σ, hg⟩
  have hcoe : ((Work.SSGRoute.PT.finZF hKL A hA ⟨SSGRoute.res k L σ, hg⟩ :
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) :
      ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K σ := by
    rw [Work.SSGRoute.PT.finZF_spec hKL A hA]
    exact SSGRoute.PTExt.galRes_trans σ
  rw [hb₀ σ hσ, h1, hcoe]

/-- **Detection**: the level class `finZH` vanishes as soon as `χ ∘ ι_w` kills the level pairing of
`finZH` against every class of `Ext¹`, provided the decomposition group of the level's place has
order divisible by `p`. -/
theorem g1r_finZH_eq_zero_of_forall_chi_levelPair
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hp : p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))))
    (hzero : ∀ x : Abelian.Ext
        (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
          (modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1,
        χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
            (Work.SSGRoute.PT.finZI hKL A hA) x
            (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))) = 0) :
    Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ = 0 := by
  classical
  haveI hXfin := g1r_finite_dualMod_tensor (M := M) (hT := hT)
  haveI hMr : Module (ZMod p) ↥(modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) :=
    inferInstanceAs (Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  haveI hMf : Finite ↥(modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) := hXfin
  have hX : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 :=
    fun x => g1r_nsmul_p_eq_zero p x
  have hpZH : p • Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hX _
  by_contra hne
  have hw' : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) :=
    NK.GlobalCFT.Place.liesOver_ofFinite
      (Work.SSGRoute.PT.finQW_liesOver (L := K) (L' := L) A hA hKL)
  have hζi : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
      (RingHom.injective _)
  obtain ⟨y, hy⟩ := Work.SSGRoute.local_duality_ext_detect_h p k ↥K (⟨ζ, hζK⟩ : ↥K) hζi
    (modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
    (fun x => g1r_nsmul_p_eq_zero p x)
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) ↥L
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) hw'
    (Work.SSGRoute.PT.finZF hKL A hA) (Work.SSGRoute.PT.finZF_spec hKL A hA)
    (Work.SSGRoute.PT.finZI hKL A hA)
    (fun u => Work.SSGRoute.PT.localUnitsMapAt_spec k ↥K ↥L
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      ((Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
        (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA)
        (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1)
      (Work.SSGRoute.PT.finZF hKL A hA) (Work.SSGRoute.PT.finZF_spec hKL A hA) u)
    hp (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀) hne
  refine absurd (hzero y) ?_
  have hpt : p • SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZI hKL A hA) y
      (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀) = 0 := by
    rw [← Work.SSGRoute.PT.levelPair_nsmul_snd, hpZH, Work.SSGRoute.levelPair_zero_h]
  exact Work.SSGRoute.PT.chi_iota_ne_zero_of_ptorsion_ne_zero p k Ω K T χ hχinj L hKL
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) _ hpt hy

/-- **The converse of the coboundary clause**: a vanishing level class forces `b` to be a
coboundary on `decomp k A`. -/
theorem g1r_isCoboundaryOn_of_finZH_eq_zero
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (h : Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b := by
  classical
  let X := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  let D := ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)))
  let φ₀ : D →* (↥K ≃ₐ[k] ↥K) :=
    (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype.comp
      (Work.SSGRoute.PT.finZF hKL A hA)
  letI : DistribMulAction D X := DistribMulAction.compHom X φ₀
  let hcr := Work.SSGRoute.PT.factorised_isCrossedHom p k Ω K L hKL A hA
    (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
    (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)
    (Work.SSGRoute.PT.finQW_glue L A hA) X b hb b₀ hb₀
  let ψ : ↥(Work.GroupCohomology.Z1 D X) :=
    ⟨fun σ => b₀ (σ : ↥L ≃ₐ[k] ↥L), by
      rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
      intro g h
      rw [hcr g h]
      show b₀ (g : ↥L ≃ₐ[k] ↥L)
          + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L)
        = (((Work.SSGRoute.PT.finZF hKL A hA g :
              ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) :
            ↥K ≃ₐ[k] ↥K)) • b₀ (h : ↥L ≃ₐ[k] ↥L)
          + b₀ (g : ↥L ≃ₐ[k] ↥L)
      rw [Work.SSGRoute.PT.finZF_spec hKL A hA g]
      abel⟩
  have hZH : (Work.SSGRoute.PT.finLevelClass p k Ω K T M L (Work.SSGRoute.PT.finQ K A hA)
      (Work.SSGRoute.PT.finQW L A hA) (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZF_spec hKL A hA) b₀ hcr : extH (modRep D X) 1) = 0 := h
  have hgamma : Work.SSGRoute.ExtH1.gammaHom D X (Work.SSGRoute.augSES_shortExact D)
      (Work.GroupCohomology.H1π D X ψ) = 0 := hZH
  have hH1 : Work.GroupCohomology.H1π D X ψ = 0 :=
    Work.SSGRoute.ExtH1.gammaHom_injective D X (Work.SSGRoute.augSES_shortExact D)
      (by rw [hgamma, map_zero])
  have hB1 : (ψ : D → X) ∈ Work.GroupCohomology.B1 D X :=
    (Work.SSGRoute.ExtH1.H1π_eq_zero_iff D X ψ).mp hH1
  obtain ⟨m, hm⟩ := (Work.GroupCohomology.mem_B1_iff D X (ψ : D → X)).mp hB1
  refine g1r_isCoboundaryOn_of_finZF_d0 (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
    (L := L) (hKL := hKL) (A := A) (hA := hA) (b := b) (b₀ := b₀) (hb₀ := hb₀) (m := m)
    (fun g => ?_)
  have h1 : (Work.GroupCohomology.d0 D X m) g = b₀ (g : ↥L ≃ₐ[k] ↥L) := congrFun hm g
  exact (h1 : ((Work.SSGRoute.PT.finZF hKL A hA g :
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) :
      ↥K ≃ₐ[k] ↥K) • m - m = b₀ (g : ↥L ≃ₐ[k] ↥L)).symm

end Helpers

theorem g1FinHalf_perfect_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcomp : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (h : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
      pair (SSGRoute.decomp k A) a b = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b := by
  classical
  obtain ⟨L₀, hfd₀, hnorm₀, hKL₀, b₀, hb₀⟩ :=
    Work.SSGRoute.PT.exists_level_factors_locConstOn p k Ω K
      (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (SSGRoute.decomp k A) b hlb
  letI : FiniteDimensional k L₀ := hfd₀
  letI : Normal k L₀ := hnorm₀
  letI : IsGalois k L₀ := inferInstance
  letI : NumberField L₀ := inferInstance
  obtain ⟨L, hfdL, hgalL, hnfL, hL₀L, hp⟩ :=
    Work.SSGRoute.PT.G1plusOwn.exists_level_ge_p_dvd_stab p k Ω K A hA L₀ hKL₀
  letI : FiniteDimensional k L := hfdL
  letI : IsGalois k L := hgalL
  letI : NumberField L := hnfL
  have hKL : K ≤ L := le_trans hKL₀ hL₀L
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI hst1 : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hst2 : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥L₀ ↥L := (IntermediateField.inclusion hL₀L).toAlgebra
  haveI hst3 : IsScalarTower k ↥L₀ ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hst4 : IsScalarTower ↥L₀ ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let b₀L : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T) :=
    fun τ => b₀ (AlgEquiv.restrictNormalHom ↥L₀ τ)
  have hb₀L : ∀ σ ∈ SSGRoute.decomp k A,
      b σ = b₀L (AlgEquiv.restrictNormalHom L σ) := by
    intro σ hσ
    rw [hb₀ σ hσ]
    exact congrArg b₀ (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥L₀ ↥L σ)
  -- ## the value of the pairing vanishes for every `a`
  have hkey : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀L hb₀L))) = 0 := by
    intro a hca hla
    have h1 : pair (SSGRoute.decomp k A) a b = χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀L hb₀L))) :=
      hpair A hA a b hla hlb hb L hKL b₀L hb₀L
    rw [← h1]
    exact h a ⟨hca, hla⟩
  -- ## hence also for every class of `Ext¹` (surjectivity of `βl`)
  have hzero : ∀ x : Abelian.Ext
      (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
        (modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
      (localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1,
      χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA) x
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀L hb₀L))) = 0 := by
    intro x
    obtain ⟨a, hca, hla, hfax⟩ := hβl_onto A hA x
    have h1 := hkey a hca hla
    rw [hfax] at h1
    exact h1
  have hZH : Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀L hb₀L = 0 :=
    g1r_finZH_eq_zero_of_forall_chi_levelPair (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (hζK := hζK) (T := T) (hT := hT) (χ := χ) (hχinj := hχinj) (M := M) (L := L)
      (hKL := hKL) (A := A) (hA := hA) (b := b) (hb := hb) (b₀ := b₀L) (hb₀ := hb₀L)
      (hp := hp) (hzero := hzero)
  exact g1r_isCoboundaryOn_of_finZH_eq_zero (k := k) (Ω := Ω) (K := K) (T := T)
    (M := M) (L := L) (hKL := hKL) (A := A) (hA := hA) (b := b) (hb := hb) (b₀ := b₀L)
    (hb₀ := hb₀L) (h := hZH)

end Work.SSGRoute.PT.G1plusOwn
