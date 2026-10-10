import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair
import Submission.Work.SSGRoute.PT.G1plusOwn.pushSpelling
import Submission.Work.SSGRoute.PT.G1plusOwn.unramifiedPairClause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the finite-place reciprocity of `G1⁺` (clause (7))

The target `G1pOwn.g1FinHalf_reciprocity` is proved by choosing *one* global finite Galois level
`L ⊇ K` at which the cocycle `b` factors (`b = b₀ ∘ res_L`), evaluating every term of the sum at `L`
(`G1pOwn.g1FinHalf_hpair`), replacing the local dictionary `finZB` by the localisation of the global
dictionary `finZBg` (`finZB_square`), and reading the resulting sum as `χ` of a single global class
`Y = levelPair (galRes) (idleRepMap) (extToIdeles (finZBg … a)) hL`.

Two inputs are not yet available in the workspace, and are stated here:

* `hClass` / `finZZ_eq_extLoc`: the comparison of the *concrete* level class `finZZ` (built from the
  place-glue `finZF`, the local units map `finZI` and the local level class `finZH`) with the
  localisation `extLoc w (levelPair (galRes) (idleRepMap) (extToIdeles (finZBg … a)) hL)` of the
  single global class `Y`;
* `exists_good_level`: a common factorisation level `L` of `a` and `b` which is moreover
  **unramified at every finite place outside the conjugacy classes of `S'`** (so that clause (6)
  kills the off-`S'` terms of the reciprocity sum).
-/

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

noncomputable section

namespace Work.SSGRoute.PT.G1plusOwn

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

/-- **The global class of a cocycle on `Gal(L/k)`** (the level-`L` partner of `finZH`): the image of
the cohomology class of `b₀` under the degree-one bridge `H¹ ≅ Ext¹(ℤ, ·)`
(`ExtH1.gammaHom`), with the `Gal(L/k)`-action on `DualMod p (M ⊗ T)` obtained by restricting the
`Gal(K/k)`-action along `galRes k K L`. -/
noncomputable def hClass {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L]
    [IsGalois k L] [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ g h : (↥L ≃ₐ[k] ↥L),
      b₀ (g * h) = (galRes k K L g) • b₀ h + b₀ g) :
    extH (Rep.res (galRes k K L)
      (modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T)))) 1 := by
  letI hAct : DistribMulAction (↥L ≃ₐ[k] ↥L) (DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom (DualMod p (M ⊗[ZMod p] T)) (galRes k K L)
  haveI hCommZK : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCK : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  haveI hCommCL : SMulCommClass (↥L ≃ₐ[k] ↥L) Coeff (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm (galRes k K L g) c.down m⟩
  have h1 : Work.GroupCohomology.IsCrossedHom (↥L ≃ₐ[k] ↥L)
      (DualMod p (M ⊗[ZMod p] T)) b₀ := hb₀
  exact Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (DualMod p (M ⊗[ZMod p] T))
    (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
    (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (DualMod p (M ⊗[ZMod p] T)) ⟨b₀, h1⟩)

/-- **The level class `finZZ` is the localisation of the single global class `Y`.**

For a finite place `A` of `Ω`, a level `L ⊇ K` and a factorisation `b = b₀ ∘ res_L` of `b` at `L`,
the concrete level class
`finZZ = levelPair (finZF …) (finZI …) (finZB … a) (finZH … b …)` equals the `w_A`-component of the
global class
`Y = levelPair (galRes k K L) (idleRepMap k K L) (extToIdeles (finZBg … a)) (hClass … b₀ …)`.

This is the comparison of the two presentations of the local pairing at `w_A`: `finZF` is the
place-glue `decompKRestrict` (`PT.finZF_spec`), `finZI` is the canonical local-units embedding
(`PT.localUnitsMapAt_spec`), `finZH` is the restriction of `hClass` to the decomposition group
(`ExtH1.gammaHom` naturality, `Work.SSGRoute.extHMap_gammaHom_eq`), and `finZB a` is
`extLoc q (extToIdeles (finZBg a))` (`PT.finZB_square`). -/
theorem finZZ_eq_extLoc
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀h : ∀ g h : (↥L ≃ₐ[k] ↥L),
      b₀ (g * h) = (galRes k K L g) • b₀ h + b₀ g) :
    Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀
      = extLoc (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
            (extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
            (hClass p k Ω K T M (L := L) b₀ hb₀h)) := by
  exact Work.SSGRoute.PT.G1plusOwn.finZZ_eq_extLoc_of_bricks p k Ω K T M L hKL A hA ζ hζ hζK hT
    a b b₀ hb hb₀ hb₀h
    (Work.SSGRoute.PT.G1plusOwn.finZF_eq_dkrg hKL A hA)
    (Work.SSGRoute.PT.G1plusOwn.finZI_eq_localUnitsMap hKL A hA
      (Work.SSGRoute.PT.G1plusOwn.finZF_eq_dkrg hKL A hA))
    (Work.SSGRoute.PT.G1plusOwn.finZH_eq_extHRestrict p k Ω K T M L hKL A hA b b₀ hb hb₀ hb₀h
      (Work.SSGRoute.PT.G1plusOwn.finZF_eq_dkrg hKL A hA))
    (Work.SSGRoute.PT.G1plusOwn.finZB_square p K ζ hζ hζK T hT M A hA a ha1 ha2)

/-- **A common factorisation level of `a` and `b`, unramified outside `S'` — `Ω`-side form.**

This is the *provable* half of `exists_good_level`: the unramifiedness is asked in the `Ω`-side form
`¬ SSGRoute.IsRamifiedIn k L B` (i.e. every element of the inertia subgroup `I_B(Ω)` fixes `L`
pointwise), which is what the natural construction gives.  The passage to the level-`L` form
`∀ σ : ↥L ≃ₐ[k] ↥L, IsInertiaAt (finQW L B hB) σ → σ = 1` (the form consumed by
`PT.levelPair_unramified_eq_zero`) is the *converse* of inertia restriction, `exists_good_level`'s
second conjunct; the forward direction is the proved
`Work.SSGRoute.E9Nodes.e9_inertia_restrict`.

Route (all pieces located).
* `U`: a normal open subgroup of `Gal(Ω/k)` on which both `a` and `b` vanish.  From
  `ha2 : IsLocConstOn ⊤ a` (`Interfaces.lean`) one gets an open subgroup `U_a` with
  `a (g * u) = a g`; an open subgroup has finite index, so its normal core is open normal; and on a
  *constancy* subgroup `U` one has `a u = a (1 * u) = a 1 = 0` (the crossed-hom identity at `(1,1)`
  gives `a 1 = 0`, from `ha1`).  Intersect with the same for `b`.
* `N := Subgroup.closure (↑U ∪ ⋃_{B ∉ S'} ↑(Work.SSGRoute.inertiaSub k Ω B))`, a subgroup of
  `Gal(Ω/k)`; its generating set is conjugation-invariant (`U` is normal; the conjugate of
  `inertiaSub B` is `inertiaSub (σ • B)` by `Work.SSGRoute.isInertia_conj`, and `IsConjPlace` is
  conjugation-invariant), so `Subgroup.closure_induction` gives normality.  `N` contains the open
  `U`, hence is open (and closed).
* `L := IntermediateField.fixedField N`.  `K ≤ L` by `IntermediateField.le_iff_le` from
  `¬ IsRamifiedIn k K B` (which *is* `inertiaSub B ≤ K.fixingSubgroup`) and `U ≤ K.fixingSubgroup`;
  `FiniteDimensional k L` and `IsGalois k L` from
  `InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`) together with
  `InfiniteGalois.fixingSubgroup_fixedField` (closed `N`).
* `¬ IsRamifiedIn k L B` for `B ∉ S'`: for `σ ∈ inertiaSub k Ω B`, `res σ ∈ N` by construction and
  `N = L.fixingSubgroup`, so `σ ∈ L.fixingSubgroup`.
* factorisation: `a` is constant on right cosets of `N` because `a` vanishes on every generator of
  `N` (`U` and all `inertiaSub B`, the latter by `hgood`) and vanishing is preserved by products and
  inverses through the crossed-hom identity; hence `a` descends along
  `Gal(Ω/k) → Gal(Ω/k)/N ≅ Gal(L/k)` (`InfiniteGalois.normalAutEquivQuotient`).  Same for `b`. -/
theorem exists_good_level_unramified
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hgood : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) :
    ∃ (L : IntermediateField k Ω) (_ : NumberField L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L),
      K ≤ L ∧
      (∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsRamifiedIn k L B) ∧
      (∃ a₀ : (↥L ≃ₐ[k] ↥L) → M,
        ∀ σ : (Ω ≃ₐ[k] Ω), a σ = a₀ (AlgEquiv.restrictNormalHom L σ)) ∧
      (∃ b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T),
        ∀ σ : (Ω ≃ₐ[k] Ω), b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) := by
  classical
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- the crossed-homomorphism identity at `(1,1)` gives `a 1 = b 1 = 0`
  have haz : a 1 = 0 := by
    have h := ha1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    simp only [mul_one, map_one, one_smul] at h
    have h2 : a 1 + a 1 = a 1 + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h2
  have hbz : b 1 = 0 := by
    have h := hb1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    simp only [mul_one, map_one, one_smul] at h
    have h2 : b 1 + b 1 = b 1 + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h2
  -- openness of the local constancy subgroups of `a` and `b`
  obtain ⟨Ua, hUaopen, hUa⟩ := ha2
  obtain ⟨Ub, hUbopen, hUb⟩ := hb2
  have hUav : ∀ u ∈ Ua, a u = 0 := fun u hu => by
    have h := hUa 1 (Subgroup.mem_top 1) u hu (Subgroup.mem_top u)
    rw [one_mul] at h
    exact h.trans haz
  have hUbv : ∀ u ∈ Ub, b u = 0 := fun u hu => by
    have h := hUb 1 (Subgroup.mem_top 1) u hu (Subgroup.mem_top u)
    rw [one_mul] at h
    exact h.trans hbz
  -- a finite normal level `L₀` whose fixing subgroup lies in `Ua ⊓ Ub ⊓ K.fixingSubgroup`
  have hUopen : IsOpen (((Ua ⊓ Ub) ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := (hUaopen.inter hUbopen).inter K.fixingSubgroup_isOpen
  obtain ⟨L₀, hL₀fd, hL₀n, hKL₀, hL₀le⟩ :=
    Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K
      ((Ua ⊓ Ub) ⊓ K.fixingSubgroup) hUopen
  letI : FiniteDimensional k L₀ := hL₀fd
  letI : Normal k L₀ := hL₀n
  letI : IsGalois k L₀ := inferInstance
  haveI hWopen : IsOpen ((L₀.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen L₀
  haveI hWnorm : (L₀.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois L₀
  have hWa : ∀ x ∈ L₀.fixingSubgroup, a x = 0 := fun x hx => hUav x (hL₀le hx).1.1
  have hWb : ∀ x ∈ L₀.fixingSubgroup, b x = 0 := fun x hx => hUbv x (hL₀le hx).1.2
  -- the normal subgroup generated by `W = L₀.fixingSubgroup` and the inertia subgroups
  -- of the finite places outside the classes of `S'`
  let N : Subgroup (Ω ≃ₐ[k] Ω) :=
    Subgroup.closure ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
      {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B})
  have hWN : (L₀.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ N := fun x hx =>
    Subgroup.subset_closure (Or.inl hx)
  have hNopen : IsOpen (N : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isOpen_mono hWN hWopen
  have hIN : ∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → Work.SSGRoute.inertiaSub k Ω B ≤ N :=
    fun B hB hnot σ hσ => Subgroup.subset_closure (Or.inr ⟨B, hB, hnot, hσ⟩)
  -- the generating set is conjugation-invariant
  have hconjU : ∀ x ∈ ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
      {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B}),
      ∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
      {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B}) := by
    intro x hx g
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx ⊢
    rcases hx with hx | ⟨B, hB, hnot, hxI⟩
    · exact Or.inl (hWnorm.conj_mem x hx g)
    · refine Or.inr ⟨g • B, (SSGRoute.isFinPlace_smul_iff B g).mpr hB, ?_, ?_⟩
      · intro A hA hconj
        obtain ⟨σ, hσ⟩ := hconj
        exact hnot A hA ⟨g⁻¹ * σ, by rw [mul_smul, hσ, inv_smul_smul]⟩
      · exact (Work.SSGRoute.isInertia_conj B g x).mpr hxI
  have hconjN : ∀ n ∈ N, ∀ g : Ω ≃ₐ[k] Ω, g * n * g⁻¹ ∈ N := by
    intro n hn
    exact Subgroup.closure_induction
      (k := ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
        {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B}))
      (p := fun n _ => ∀ g : Ω ≃ₐ[k] Ω, g * n * g⁻¹ ∈ N)
      (fun x hx g => Subgroup.subset_closure (hconjU x hx g))
      (fun g => by simpa using N.one_mem)
      (fun x y hx hy ihx ihy g => by
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) from by group]
        exact N.mul_mem (ihx g) (ihy g))
      (fun x hx ihx g => by
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ from by group]
        exact N.inv_mem (ihx g))
      hn
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hconjN y hy g
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * x * g, hconjN x hx g⁻¹, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  haveI := hNnormal
  -- every generator of `N` lies in `K.fixingSubgroup`
  have hSK : ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
      {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B})
      ⊆ (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) := by
    rintro x (hx | ⟨B, hB, hnot, hxI⟩)
    · exact (hL₀le hx).2
    · by_contra hxnot
      exact (hgood B hB hnot).2.1 ⟨x, (Work.SSGRoute.mem_inertiaSub k Ω B x).mp hxI, hxnot⟩
  have hKN : N ≤ K.fixingSubgroup := (Subgroup.closure_le (K.fixingSubgroup)).mpr hSK
  -- the level: the fixed field of `N`
  let L : IntermediateField k Ω := IntermediateField.fixedField N
  have hLfd : FiniteDimensional k L := Work.SSGRoute.PT.finiteDimensional_fixedField_of_isOpen N hNopen
  have hLfix : L.fixingSubgroup = N := Work.SSGRoute.PT.fixingSubgroup_fixedField_of_isOpen N hNopen
  letI : FiniteDimensional k L := hLfd
  haveI : IsGalois k L := IsGalois.of_fixedField_normal_subgroup N
  have hLnf : NumberField L := NumberField.of_module_finite k L
  -- `a` and `b` vanish on `N`
  have haN : ∀ n ∈ N, a n = 0 := by
    intro n hn
    exact Subgroup.closure_induction
      (k := ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
        {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B}))
      (p := fun n _ => a n = 0)
      (fun x hx => by
        simp only [Set.mem_union, Set.mem_setOf_eq] at hx
        rcases hx with hx | ⟨B, hB, hnot, hxI⟩
        · exact hWa x hx
        · exact ((hgood B hB hnot).2.2 x ((Work.SSGRoute.mem_inertiaSub k Ω B x).mp hxI)).1)
      haz
      (fun x y hx hy ihx ihy => by
        rw [ha1 x (Subgroup.mem_top x) y (Subgroup.mem_top y), ihx, ihy, smul_zero, add_zero])
      (fun x hx ihx => by
        have h := ha1 x (Subgroup.mem_top x) x⁻¹ (Subgroup.mem_top x⁻¹)
        rw [mul_inv_cancel, ihx, zero_add] at h
        have h' : SSGRoute.res k K x • a x⁻¹ = 0 := by rw [← h]; exact haz
        calc a x⁻¹ = (SSGRoute.res k K x)⁻¹ • (SSGRoute.res k K x • a x⁻¹) := by
              rw [smul_smul, inv_mul_cancel, one_smul]
          _ = 0 := by rw [h', smul_zero])
      hn
  have hbN : ∀ n ∈ N, b n = 0 := by
    intro n hn
    exact Subgroup.closure_induction
      (k := ((↑(L₀.fixingSubgroup) : Set (Ω ≃ₐ[k] Ω)) ∪
        {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ σ ∈ Work.SSGRoute.inertiaSub k Ω B}))
      (p := fun n _ => b n = 0)
      (fun x hx => by
        simp only [Set.mem_union, Set.mem_setOf_eq] at hx
        rcases hx with hx | ⟨B, hB, hnot, hxI⟩
        · exact hWb x hx
        · exact ((hgood B hB hnot).2.2 x ((Work.SSGRoute.mem_inertiaSub k Ω B x).mp hxI)).2)
      hbz
      (fun x y hx hy ihx ihy => by
        rw [hb1 x (Subgroup.mem_top x) y (Subgroup.mem_top y), ihx, ihy, smul_zero, add_zero])
      (fun x hx ihx => by
        have h := hb1 x (Subgroup.mem_top x) x⁻¹ (Subgroup.mem_top x⁻¹)
        rw [mul_inv_cancel, ihx, zero_add] at h
        have h' : SSGRoute.res k K x • b x⁻¹ = 0 := by rw [← h]; exact hbz
        calc b x⁻¹ = (SSGRoute.res k K x)⁻¹ • (SSGRoute.res k K x • b x⁻¹) := by
              rw [smul_smul, inv_mul_cancel, one_smul]
          _ = 0 := by rw [h', smul_zero])
      hn
  -- the descent of `a` and `b` to `Gal(L/k)`
  have key : ∀ σ : Ω ≃ₐ[k] Ω, (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
        (AlgEquiv.restrictNormalHom ↥L σ)))⁻¹ * σ ∈ N := by
    intro σ
    have hspec : AlgEquiv.restrictNormalHom ↥L
        (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
          (AlgEquiv.restrictNormalHom ↥L σ))) = AlgEquiv.restrictNormalHom ↥L σ :=
      Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
        (AlgEquiv.restrictNormalHom ↥L σ))
    have h1 : AlgEquiv.restrictNormalHom ↥L
        ((Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
          (AlgEquiv.restrictNormalHom ↥L σ)))⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, hspec, inv_mul_cancel]
    have h2 : (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
          (AlgEquiv.restrictNormalHom ↥L σ)))⁻¹ * σ
        ∈ (AlgEquiv.restrictNormalHom ↥L).ker := MonoidHom.mem_ker.mpr h1
    rwa [IntermediateField.restrictNormalHom_ker, hLfix] at h2
  have descent_a : ∃ a₀ : (↥L ≃ₐ[k] ↥L) → M,
      ∀ σ : (Ω ≃ₐ[k] Ω), a σ = a₀ (AlgEquiv.restrictNormalHom ↥L σ) := by
    refine ⟨fun τ => a (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω τ)),
      fun σ => ?_⟩
    have hcst : ∀ σ n : Ω ≃ₐ[k] Ω, n ∈ N → a (σ * n) = a σ := by
      intro σ n hn
      rw [ha1 σ (Subgroup.mem_top σ) n (Subgroup.mem_top n), haN n hn, smul_zero, add_zero]
    have h3 := hcst (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
        (AlgEquiv.restrictNormalHom ↥L σ))) _ (key σ)
    simpa only [mul_inv_cancel_left] using h3
  have descent_b : ∃ b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T),
      ∀ σ : (Ω ≃ₐ[k] Ω), b σ = b₀ (AlgEquiv.restrictNormalHom ↥L σ) := by
    refine ⟨fun τ => b (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω τ)),
      fun σ => ?_⟩
    have hcst : ∀ σ n : Ω ≃ₐ[k] Ω, n ∈ N → b (σ * n) = b σ := by
      intro σ n hn
      rw [hb1 σ (Subgroup.mem_top σ) n (Subgroup.mem_top n), hbN n hn, smul_zero, add_zero]
    have h3 := hcst (Classical.choose (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) Ω
        (AlgEquiv.restrictNormalHom ↥L σ))) _ (key σ)
    simpa only [mul_inv_cancel_left] using h3
  refine ⟨L, hLnf, hLfd, inferInstance, ?_, ?_, descent_a, descent_b⟩
  · exact (IntermediateField.le_iff_le N K).mpr hKN
  · intro B hB hnot
    rintro ⟨σ, hσI, hσnot⟩
    exact hσnot (by rw [hLfix]; exact (hIN B hB hnot) hσI)

/-- **A common factorisation level of `a` and `b`, unramified outside `S'`.**

There exists a finite Galois level `L ⊇ K` through which both `a` and `b` factor and which is
unramified at every finite place of `Ω` outside the conjugacy classes of `S'`.

This is `exists_good_level_unramified` (the `Ω`-side unramifiedness) together with the bridge from
`¬ SSGRoute.IsRamifiedIn k L B` to the level-`L` inertia form
`∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L B hB) σ → σ = 1`
(the converse of inertia restriction: a level-`L` inertia element lifts to an `Ω`-inertia element;
the forward direction is the proved `Work.SSGRoute.E9Nodes.e9_inertia_restrict`).  The level-`L`
form is the hypothesis consumed by `PT.levelPair_unramified_eq_zero`, hence by the off-`S'`
vanishing in the reciprocity assembly. -/
theorem exists_good_level
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hgood : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) :
    ∃ (L : IntermediateField k Ω) (_ : NumberField L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L),
      K ≤ L ∧
      (∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : ↥L ≃ₐ[k] ↥L,
          SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L B hB) σ → σ = 1) ∧
      (∃ a₀ : (↥L ≃ₐ[k] ↥L) → M,
        ∀ σ : (Ω ≃ₐ[k] Ω), a σ = a₀ (AlgEquiv.restrictNormalHom L σ)) ∧
      (∃ b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T),
        ∀ σ : (Ω ≃ₐ[k] Ω), b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) := by
  classical
  obtain ⟨L, hLnf, hLfd, hLgal, hKL, hunr, ha₀, hb₀⟩ :=
    exists_good_level_unramified p k Ω K T M a b ha1 ha2 hb1 hb2 S' hS'fin hgood
  letI : NumberField L := hLnf
  letI : FiniteDimensional k L := hLfd
  letI : IsGalois k L := hLgal
  refine ⟨L, hLnf, hLfd, hLgal, hKL, ?_, ha₀, hb₀⟩
  intro B hB hnot σ hσ
  refine isInertiaAt_eq_one_of_inertiaSub_le k Ω B hB L ?_ σ hσ
  intro x hx
  by_contra hx'
  exact (hunr B hB hnot) ⟨x, (Work.SSGRoute.mem_inertiaSub k Ω B x).mp hx, hx'⟩

end Work.SSGRoute.PT.G1plusOwn
