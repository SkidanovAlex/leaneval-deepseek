import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.ResidueFrob.inertia_of_levels_of_tameData
import Submission.NK.ResidueFrob.isClosed_setOf_isTrivialOnResidueAtLevel
import Submission.NK.ResidueFrob.isTrivialOnResidueAtLevel_of_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inertia subgroups are the images of the inertia subgroup at the place

This file contains the proof of

`NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel`:

if `g ∈ Gal(K'/K)` lies in the decomposition group of a place `A` of the separable closure `K'` of
a number field `K` and acts trivially on the residue field of a finite normal level `L ⊆ K'` at the
prime below `A`, then `g` agrees on `L` with an element `δ` of the decomposition group that fixes
`L` pointwise and such that `δ * g` acts trivially on the residue field of **every** finite normal
level: `δ` is the element carrying the residue automorphism `ρ(g)⁻¹` of the residue field of `A`,
and its existence is the surjectivity of the map "place inertia ↠ level inertia".

## The mathematics

**Step 1 (`NK.ResidueFrob.exists_lift_fixing_aux`, proved here).**  For finite normal levels
`L ≤ M` and `g ∈ D_A` acting trivially on the residue field of `L`, there is `σ ∈ D_A` fixing `L`
pointwise with `σ * g` acting trivially on the residue field of `M`.  The proof is the classical
Fourier–Hilbert statement that the inertia subgroup of the level `M` surjects onto the inertia
subgroup of the sublevel `L`, made explicit as follows.

Let `γ = g|_M` and let `γbar` be the action of `γ` on the residue field `κ_M = 𝓞M/P_M` over
`κ_K = 𝓞K/𝔭`.  The hypothesis at the level `L` says exactly that `γbar` is `κ_L`-linear, so
`γbar` is an element of `Aut(κ_M/κ_L)`; the residue field is finite, so this group is cyclic, and
the residue action map
`Aut(κ_M/κ_L) ← D_{P_M}(M/L)`, i.e. `stabilizerHom (M/L, P_M/P_L)`, is **surjective** by
Mathlib's `Ideal.Quotient.stabilizerHom_surjective` (a finite-group instance of the theorem that
`D_P/I_P ≅ Gal(κ_P/κ_p)`).  Choosing `τ ∈ Gal(M/L) ∩ D_{P_M}` with `γbarL(τ) = γbar⁻¹` and
lifting it to `σ ∈ D_A` by `Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`
(transitivity of the Galois action on the primes above `P_M`) gives an element with `σ|_L = 1`
and `σ * g` residue-trivial at `M`.

**Step 2 (compactness).**  The family of conditions
`t M = {σ : σ ∈ D_A, σ|_L = 1, σ * g residue-trivial at M}` is a *directed* family of nonempty
closed subsets of the compact group `Gal(K'/K)` (Krull topology): directedness uses the
monotonicity of the level condition
(`NK.ResidueFrob.isTrivialOnResidueAtLevel_of_le`) and nonemptiness Step 1, while closedness
uses that the condition depends only on the restriction to the finite level `M`
(`NK.ResidueFrob.isClosed_setOf_isTrivialOnResidueAtLevel`).  Compactness
(`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) then produces a single `δ`
satisfying all the level conditions simultaneously, which is the statement.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The condition which the compactness argument in
`NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel` intersects: an element `σ` of
`Gal(K'/K)` which lies in the decomposition group of `A`, fixes the level `L` pointwise, and is
such that `σ * g` acts trivially on the residue field of the level `N`. -/
def TrivSet (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] (g : Gal(K'/K))
    (N : IntermediateField K K') [FiniteDimensional K N] [Normal K N] [NumberField ↥N] :
    Set Gal(K'/K) :=
  {σ : Gal(K'/K) |
    σ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ∧
    AlgEquiv.restrictNormalHom L σ = 1 ∧
    NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N (σ * g)}

/-- **`TrivSet` is closed** in the Krull topology: the decomposition group is closed
(`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring`), fixing `L` pointwise is a
closed condition (the restriction map to the finite group `Gal(↥L/K)` is continuous), and the
level condition depends only on the restriction to `N`
(`NK.ResidueFrob.isClosed_setOf_isTrivialOnResidueAtLevel`). -/
theorem isClosed_trivSet (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] (g : Gal(K'/K))
    (N : IntermediateField K K') [FiniteDimensional K N] [Normal K N] [NumberField ↥N] :
    IsClosed (TrivSet A L g N) := by
  have hEq : TrivSet A L g N =
      ((MulAction.stabilizer (K' ≃ₐ[K] K') A.1 : Subgroup Gal(K'/K)) : Set Gal(K'/K)) ∩
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) ⁻¹' ({1} : Set (↥L ≃ₐ[K] ↥L))) ∩
      ((fun σ : Gal(K'/K) => σ * g) ⁻¹'
        {h : Gal(K'/K) | NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N h}) := by
    ext σ
    simp only [TrivSet, Submission.NeukirchUchida.decompositionGroup, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hEq]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A.1
  · exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous L) (isClosed_discrete _)
  · exact IsClosed.preimage (Homeomorph.mulRight g).continuous
      (isClosed_setOf_isTrivialOnResidueAtLevel A N)

theorem exists_lift_fixing_aux (A : NK.FrobeniusBridge.FinitePlaceOf K K') {L M : IntermediateField K K'}
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M] (hLM : L ≤ M) (g : Gal(K'/K))
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hgtriv : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g) :
    ∃ σ : Gal(K'/K),
      σ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ∧
      AlgEquiv.restrictNormalHom L σ = 1 ∧
      NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A M (σ * g) := by
  classical
  -- ===== setup =====
  letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI hST1 : IsScalarTower K ↥L ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hST2 : IsScalarTower ↥L ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hfdLM : FiniteDimensional ↥L ↥M := Module.Finite.of_restrictScalars_finite K ↥L ↥M
  haveI hgalKM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hgalLM : IsGalois ↥L ↥M := IsGalois.tower_top_of_isGalois K ↥L ↥M
  let PL := NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  let PM := NK.Reconstruct.primeOfLevel A.1 M (NK.Reconstruct.comap_level_ne_top A.2 M)
  let pK := Submission.NeukirchUchida.primeOf A.1 A.2
  have hspecM : A.1.comap (algebraMap ↥M K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM :=
    NK.Reconstruct.primeOfLevel_spec A.1 M _
  have hunder : PL = PM.under (𝓞 ↥L) := NK.FrobeniusBridge.primeOfLevel_under hLM A
  haveI hliesLM : PM.asIdeal.LiesOver PL.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [hunder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  have hliesKM : PM.asIdeal.LiesOver pK.asIdeal := NK.ResidueFrob.primeOfLevel_liesOver A M
  -- ===== the ambient (base K) residue action and γ =====
  letI actK : MulSemiringAction (Gal(↥M/K)) (𝓞 ↥M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K ↥M (𝓞 ↥M)
  haveI hcommK : SMulCommClass (Gal(↥M/K)) (𝓞 K) (𝓞 ↥M) := ⟨fun gg a x => by
    change galRestrict (𝓞 K) K ↥M (𝓞 ↥M) gg (algebraMap (𝓞 K) (𝓞 ↥M) a * x) =
      algebraMap (𝓞 K) (𝓞 ↥M) a * galRestrict (𝓞 K) K ↥M (𝓞 ↥M) gg x
    rw [map_mul, AlgEquiv.commutes]⟩
  haveI hInvK : Algebra.IsInvariant (𝓞 K) (𝓞 ↥M) (Gal(↥M/K)) :=
    Algebra.isInvariant_of_isGalois (𝓞 K) K ↥M (𝓞 ↥M)
  let γ : Gal(↥M/K) := AlgEquiv.restrictNormalHom M g
  have hgz : g • A.1 = A.1 := (MulAction.mem_stabilizer_iff).mp hg
  have hγV : γ ∈ MulAction.stabilizer (Gal(↥M/K))
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM) := by
    rw [← hspecM]
    exact Commons.FieldTheory.Galois.restrictNormalHom_smul_comap_eq_of_smul_eq A.1 g hgz M
  have hγD : γ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) PM :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      (K := K) (L := ↥M) PM γ).mp hγV
  have hγstab : γ ∈ MulAction.stabilizer (Gal(↥M/K)) PM.asIdeal := by
    rw [MulAction.mem_stabilizer_iff]
    exact (Submission.NeukirchUchida.Local.mem_decompositionSubgroup_iff_smul
      (K := K) (L := ↥M) PM γ).mp hγD
  let γbar : (𝓞 ↥M ⧸ PM.asIdeal) ≃ₐ[𝓞 K ⧸ pK.asIdeal] (𝓞 ↥M ⧸ PM.asIdeal) :=
    Ideal.Quotient.stabilizerHom PM.asIdeal pK.asIdeal (Gal(↥M/K)) ⟨γ, hγstab⟩
  -- ===== the tower (base L) residue action and its surjectivity =====
  letI actL : MulSemiringAction (Gal(↥M/↥L)) (𝓞 ↥M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 ↥L) ↥L ↥M (𝓞 ↥M)
  haveI hcommL : SMulCommClass (Gal(↥M/↥L)) (𝓞 ↥L) (𝓞 ↥M) := ⟨fun gg a x => by
    change galRestrict (𝓞 ↥L) ↥L ↥M (𝓞 ↥M) gg (algebraMap (𝓞 ↥L) (𝓞 ↥M) a * x) =
      algebraMap (𝓞 ↥L) (𝓞 ↥M) a * galRestrict (𝓞 ↥L) ↥L ↥M (𝓞 ↥M) gg x
    rw [map_mul, AlgEquiv.commutes]⟩
  haveI hInvL : Algebra.IsInvariant (𝓞 ↥L) (𝓞 ↥M) (Gal(↥M/↥L)) :=
    Algebra.isInvariant_of_isGalois (𝓞 ↥L) ↥L ↥M (𝓞 ↥M)
  have hsurj : Function.Surjective (Ideal.Quotient.stabilizerHom PM.asIdeal PL.asIdeal
      (Gal(↥M/↥L))) :=
    Ideal.Quotient.stabilizerHom_surjective (Gal(↥M/↥L)) PL.asIdeal PM.asIdeal
  -- ===== the κ_L-structure on γbar =====
  have hfixL : ∀ a : 𝓞 ↥L ⧸ PL.asIdeal,
      γbar (algebraMap (𝓞 ↥L ⧸ PL.asIdeal) (𝓞 ↥M ⧸ PM.asIdeal) a) =
        algebraMap (𝓞 ↥L ⧸ PL.asIdeal) (𝓞 ↥M ⧸ PM.asIdeal) a := by
    intro a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [show γbar (Ideal.Quotient.mk PM.asIdeal (algebraMap (𝓞 ↥L) (𝓞 ↥M) y)) =
        Ideal.Quotient.mk PM.asIdeal
          (galRestrict (𝓞 K) K ↥M (𝓞 ↥M) γ (algebraMap (𝓞 ↥L) (𝓞 ↥M) y)) from
      Ideal.Quotient.stabilizerHom_apply _ _ _ _ _]
    rw [← NK.Chebotarev.algebraMap_galRestrict_restrictNormalHom_le L M hLM γ y]
    have hcomp : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) L γ =
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L g := by
      rw [show γ = AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M g from rfl,
        NK.Chebotarev.restrictNormalHom_le_comp L M hLM g]
    rw [hcomp]
    rw [Ideal.Quotient.eq]
    have hmem : galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L g) y - y ∈ PL.asIdeal := hgtriv y
    have hunder' : Ideal.under (𝓞 ↥L) PM.asIdeal = PL.asIdeal := by
      rw [← IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hunder.symm
    rw [← map_sub]
    exact (Ideal.mem_under (𝓞 ↥L) PM.asIdeal).mp (hunder' ▸ hmem)
  -- ===== the κ_L-AlgEquiv structure on γbar
  let γbarL : (𝓞 ↥M ⧸ PM.asIdeal) ≃ₐ[𝓞 ↥L ⧸ PL.asIdeal] (𝓞 ↥M ⧸ PM.asIdeal) :=
    { γbar with commutes' := hfixL }
  -- ===== the corrected element
  obtain ⟨τ₀, hτ₀⟩ := hsurj (γbarL⁻¹)
  let τ : Gal(↥M/K) := AlgEquiv.restrictScalars K (τ₀ : Gal(↥M/↥L))
  -- the actions of `τ₀` (over `L`) and `τ` (over `K`) agree
  have hact : ∀ x : 𝓞 ↥M, galRestrict (𝓞 K) K ↥M (𝓞 ↥M) τ x =
      galRestrict (𝓞 ↥L) ↥L ↥M (𝓞 ↥M) (τ₀ : Gal(↥M/↥L)) x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 ↥M) ↥M (galRestrict (𝓞 K) K ↥M (𝓞 ↥M) τ x) =
      algebraMap (𝓞 ↥M) ↥M (galRestrict (𝓞 ↥L) ↥L ↥M (𝓞 ↥M) (τ₀ : Gal(↥M/↥L)) x)
    rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    rfl
  -- ===== the triviality at the level `M`
  have hkey : ∀ x : 𝓞 ↥M, Ideal.Quotient.mk PM.asIdeal
      (galRestrict (𝓞 K) K ↥M (𝓞 ↥M) (τ * γ) x) = Ideal.Quotient.mk PM.asIdeal x := by
    intro x
    set y : 𝓞 ↥M := galRestrict (𝓞 K) K ↥M (𝓞 ↥M) γ x with hy
    have h1 : galRestrict (𝓞 K) K ↥M (𝓞 ↥M) (τ * γ) x =
        galRestrict (𝓞 K) K ↥M (𝓞 ↥M) τ y := by
      rw [map_mul]
      rfl
    rw [h1, hact]
    have h3 : Ideal.Quotient.mk PM.asIdeal
          (galRestrict (𝓞 ↥L) ↥L ↥M (𝓞 ↥M) (τ₀ : Gal(↥M/↥L)) y)
        = (Ideal.Quotient.stabilizerHom PM.asIdeal PL.asIdeal (Gal(↥M/↥L))) τ₀
            (Ideal.Quotient.mk PM.asIdeal y) := by
      rw [Ideal.Quotient.stabilizerHom_apply]
      rfl
    have h4 : Ideal.Quotient.mk PM.asIdeal y = γbarL (Ideal.Quotient.mk PM.asIdeal x) := by
      have h5 : γbar (Ideal.Quotient.mk PM.asIdeal x) = Ideal.Quotient.mk PM.asIdeal y := by
        rw [Ideal.Quotient.stabilizerHom_apply]
        rfl
      rw [show γbarL (Ideal.Quotient.mk PM.asIdeal x) = γbar (Ideal.Quotient.mk PM.asIdeal x)
        from rfl, h5]
    rw [h3, h4, hτ₀]
    exact AlgEquiv.symm_apply_apply γbarL (Ideal.Quotient.mk PM.asIdeal x)
  -- ===== lifting `τ` to `D_A`
  have hτ₀V : (τ₀ : Gal(↥M/↥L)) ∈ MulAction.stabilizer (Gal(↥M/↥L))
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM) :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      (K := ↥L) (L := ↥M) PM (τ₀ : Gal(↥M/↥L))).mpr
      ((Submission.NeukirchUchida.Local.mem_decompositionSubgroup_iff_smul
        (K := ↥L) (L := ↥M) PM (τ₀ : Gal(↥M/↥L))).mpr τ₀.2)
  have hτV : τ ∈ MulAction.stabilizer (Gal(↥M/K))
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM) := by
    have hVeq : (τ • (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM)) =
        ((τ₀ : Gal(↥M/↥L)) •
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M PM)) := by
      ext z
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def]
      congr 1
      rfl
    rw [MulAction.mem_stabilizer_iff, hVeq]
    exact (MulAction.mem_stabilizer_iff).mp hτ₀V
  obtain ⟨σ, hσmem, hσres⟩ :=
    Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq (F := K) A.1 A.2 M τ
      (by rw [hspecM]; exact hτV)
  -- `σ` fixes `L` pointwise
  have hσfixL : ∀ x ∈ L, σ x = x := by
    intro x hx
    have hxM : x ∈ M := hLM hx
    have h2 : σ (((⟨x, hxM⟩ : ↥M) : K')) = (((τ ⟨x, hxM⟩ : ↥M)) : K') := by
      rw [← AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := K') M σ ⟨x, hxM⟩]
      rw [hσres]
    have h3 : τ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
      have h := AlgEquiv.commutes (τ₀ : Gal(↥M/↥L)) (⟨x, hx⟩ : ↥L)
      rwa [show (algebraMap ↥L ↥M (⟨x, hx⟩ : ↥L)) = (⟨x, hxM⟩ : ↥M) from rfl] at h
    have h1 : (((⟨x, hxM⟩ : ↥M)) : K') = x := rfl
    rw [← h1, h2, h3]
  refine ⟨σ, hσmem, ?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact hσfixL x x.2
  · intro x
    rw [show AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M (σ * g) =
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M σ *
          AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M g from map_mul _ _ _]
    rw [hσres, show AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M g = γ from rfl]
    exact (Ideal.Quotient.eq).mp (hkey x)



/-- **The main theorem, with the level `L` and the element `g` as variables.** -/
theorem exists_inertia_aux (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K))
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hgtriv : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g) :
    ∃ δ : Gal(K'/K),
      δ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ∧
      AlgEquiv.restrictNormalHom L δ = 1 ∧
      ∀ (N : IntermediateField K K') [FiniteDimensional K N] [Normal K N] [NumberField ↥N],
        NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N (δ * g) := by
  classical
  -- The index set: the finite normal intermediate fields which are number fields.
  haveI hneι : Nonempty
      {N : IntermediateField K K' // FiniteDimensional K N ∧ Normal K N ∧ NumberField ↥N} :=
    ⟨⟨⊥, inferInstance, inferInstance, inferInstance⟩⟩
  -- The family of level conditions.
  let t : {N : IntermediateField K K' // FiniteDimensional K N ∧ Normal K N ∧ NumberField ↥N} →
      Set Gal(K'/K) := fun N => by
    haveI h1 : FiniteDimensional K N.1 := N.2.1
    haveI h2 : Normal K N.1 := N.2.2.1
    haveI h3 : NumberField ↥N.1 := N.2.2.2
    exact TrivSet A L g N.1
  -- Each member of the family is closed.
  have hcl : ∀ N : {N : IntermediateField K K' //
      FiniteDimensional K N ∧ Normal K N ∧ NumberField ↥N}, IsClosed (t N) := by
    intro N
    haveI h1 : FiniteDimensional K N.1 := N.2.1
    haveI h2 : Normal K N.1 := N.2.2.1
    haveI h3 : NumberField ↥N.1 := N.2.2.2
    exact isClosed_trivSet A L g N.1
  -- Each member of the family is nonempty: correct `g` on a level containing both `L` and `N`.
  have hne : ∀ N : {N : IntermediateField K K' //
      FiniteDimensional K N ∧ Normal K N ∧ NumberField ↥N}, (t N).Nonempty := by
    intro N
    haveI h1 : FiniteDimensional K N.1 := N.2.1
    haveI h2 : Normal K N.1 := N.2.2.1
    haveI h3 : NumberField ↥N.1 := N.2.2.2
    let M : IntermediateField K K' := L ⊔ N.1
    haveI hMa : FiniteDimensional K M := inferInstance
    haveI hMb : Normal K M := inferInstance
    haveI hMc : NumberField ↥M :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K') M
    obtain ⟨σ, hσ, hfix, htr⟩ :=
      exists_lift_fixing_aux (K := K) (K' := K') A (L := L) (M := M)
        le_sup_left g hg hgtriv
    refine ⟨σ, hσ, hfix, ?_⟩
    exact isTrivialOnResidueAtLevel_of_le A (L := N.1) (N := M) le_sup_right (σ * g) htr
  -- The family is directed: the condition at the compositum implies the conditions at the factors.
  have hdir : Directed (· ⊇ ·) t := by
    intro N₁ N₂
    haveI h1a : FiniteDimensional K N₁.1 := N₁.2.1
    haveI h1b : Normal K N₁.1 := N₁.2.2.1
    haveI h1c : NumberField ↥N₁.1 := N₁.2.2.2
    haveI h2a : FiniteDimensional K N₂.1 := N₂.2.1
    haveI h2b : Normal K N₂.1 := N₂.2.2.1
    haveI h2c : NumberField ↥N₂.1 := N₂.2.2.2
    let M : IntermediateField K K' := N₁.1 ⊔ N₂.1
    haveI hMa : FiniteDimensional K M := inferInstance
    haveI hMb : Normal K M := inferInstance
    haveI hMc : NumberField ↥M :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K') M
    refine ⟨⟨M, hMa, hMb, hMc⟩, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      exact ⟨h1, h2,
        isTrivialOnResidueAtLevel_of_le A (L := N₁.1) (N := M) le_sup_left (σ * g) h3⟩
    · intro σ hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      exact ⟨h1, h2,
        isTrivialOnResidueAtLevel_of_le A (L := N₂.1) (N := M) le_sup_right (σ * g) h3⟩
  -- Compactness of the Krull topology: the intersection of the family is nonempty.
  obtain ⟨δ, hδ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
      (fun N => (hcl N).isCompact) hcl
  have hδL : δ ∈ TrivSet A L g L :=
    Set.mem_iInter.mp hδ ⟨L, inferInstance, inferInstance, inferInstance⟩
  refine ⟨δ, hδL.1, hδL.2.1, ?_⟩
  intro N hfin hnorm hnf
  haveI h1 : FiniteDimensional K N := hfin
  haveI h2 : Normal K N := hnorm
  haveI h3 : NumberField ↥N := hnf
  exact (Set.mem_iInter.mp hδ ⟨N, hfin, hnorm, hnf⟩).2.2

/-- **The inertia half of the local–global dictionary at a finite level.**

If `g : Gal(K'/K)` lies in the decomposition group of a place `A` of the separable closure `K'` of
a number field `K` and acts trivially on the residue field of the finite normal level `L ⊆ K'` at
the prime of `𝓞 L` below `A`, then there is `δ` in the decomposition group of `A` with

* `δ` fixes `L` pointwise, and
* `δ * g` acts trivially on the residue field of **every** finite normal level `N ⊆ K'`.

Equivalently: the place inertia subgroup `I_A ≅ I_κ` of the decomposition group surjects onto the
level inertia subgroup of `L`; but the statement is formulated without any local field theory,
purely in terms of the level residue fields. -/
theorem exists_inertia_of_isTrivialOnResidueAtLevel {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K))
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hgtriv : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g) :
    ∃ δ : Gal(K'/K),
      δ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ∧
      AlgEquiv.restrictNormalHom L δ = 1 ∧
      ∀ (N : IntermediateField K K') [FiniteDimensional K N] [Normal K N] [NumberField ↥N],
        NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N (δ * g) :=
  exists_inertia_aux A L g hg hgtriv

end NK.ResidueFrob
