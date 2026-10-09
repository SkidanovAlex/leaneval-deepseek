import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_hom
import Submission.Work.SSGRoute.Sha2Lib.ext_comp_mk0_ne_zero_of_section
import Submission.Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial
import Submission.Work.E7cOmega.functional_of_ext_nonzero
import Submission.Work.E7cOmega.ext_one_unitRep_iso_divRep
import Submission.Work.Sha2Lib.rankOneLevelCocycleRoute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick of node `C6`, proved

This file proves `Work.Sha2Lib.rankOneBrickProved`, the detector for the permutation module
`Ind_N^{Γ} 𝔽_p`, i.e. the last arithmetic brick isolated by
`Work.SSGRoute.PTdualControl.unramifiedDetector_of_rankOneBrick`.
-/

namespace Work.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1
attribute [local instance] Classical.propDecidable

noncomputable section

set_option linter.style.haveILetI false

/-- **The detector is insensitive to an isomorphism of coefficient modules.** -/
theorem rankOne_isUnramifiedDetector_of_iso {p : ℕ} [Fact p.Prime] {k K : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {w : NK.GlobalCFT.Place K}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {hwq : w = NK.GlobalCFT.Place.ofFinite q}
    {N M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (e : N ≅ M)
    (h : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq N) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  intro φ hφ
  refine Work.SSGRoute.Sha2Lib.detectsAt_of_hom p k K Ω w q hwq N M h e.hom φ ?_
  refine Work.SSGRoute.Sha2Lib.ext_comp_mk0_ne_zero_of_section
    (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype e.hom)
    (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype e.inv) ?_ hφ
  show Rep.resMap _ e.inv ≫ Rep.resMap _ e.hom = 𝟙 _
  show (Rep.resFunctor _).map e.inv ≫ (Rep.resFunctor _).map e.hom
    = 𝟙 ((Rep.resFunctor _).obj M)
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- It suffices to prove the detector for the *coinduced* module. -/
theorem rankOne_isUnramifiedDetector_of_coind (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal] (W : Rep.{0} SSGRoute.PTExt.Coeff N)
    (h : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq (Rep.coind N.subtype W)) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq (Rep.ind N.subtype W) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  haveI : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  haveI : N.FiniteIndex := inferInstance
  exact rankOne_isUnramifiedDetector_of_iso (Rep.indCoindIso W).symm h

/-- The coefficient scalar `p` kills every element of `𝔽_p`. -/
theorem rankOne_coeff_smul_p_eq_zero (p : ℕ) [NeZero p] (y : ZMod p) :
    (p : SSGRoute.PTExt.Coeff) • y = 0 := by
  show ((p : ℤ) • y : ZMod p) = 0
  rw [zsmul_eq_mul]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

/-- The coinduced module of the trivial `𝔽_p`-module of `N` is killed by `p`. -/
theorem rankOne_coind_pTorsion (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    ∀ m : Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)), p • m = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro m
  rw [← Nat.cast_smul_eq_nsmul SSGRoute.PTExt.Coeff]
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_zero]
  funext g
  rw [Pi.smul_apply]
  exact rankOne_coeff_smul_p_eq_zero p _

/-- The coinduced module of the trivial `𝔽_p`-module of `N` is finite. -/
theorem rankOne_coind_finite (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    Finite (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- **The functional form of the rank-one brick.**

For a nonzero `D_w`-equivariant functional `μ` on the restriction of the coinduced module
`M = coInd_N^{Γ} 𝔽_p`, the class `φ = δ(μ)` is detected.  This is the arithmetic core: Grünwald
over `K^N` produces a finite Galois level `L ⊇ K`, a place `q' | q` with `e(q'|q)` prime to `p`, and
a Shapiro class `h ∈ H¹(Gal(L/k), res M)` unramified at `q'` whose `μ`-value is nonzero. -/
theorem rankOne_functionalDetection (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
      ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
            (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1)) := by
  sorry

/-- **The rank-one brick**: the detector for the permutation module `Ind_N^{Γ} 𝔽_p`, for a normal
subgroup `N ⊴ Gal(K/k)` containing the inertia at `q ∤ p` and fixing a primitive `p`-th root of
unity `ζ ∈ K`. -/
theorem rankOneBrickProved (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  refine rankOne_isUnramifiedDetector_of_coind p k K Ω w q hwq N _ ?_
  intro φ hφ
  haveI : Finite (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) :=
    rankOne_coind_finite p k K N
  obtain ⟨μ, hμne, hφμ⟩ := Work.E7cOmega.functional_of_ext_nonzero p k K
    (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
    (rankOne_coind_pTorsion p k K N) w φ hφ
  rw [hφμ]
  exact rankOne_functionalDetection p k K Ω w q hwq hpq N hNI ζ hζ hNζ μ hμne

end

end Work.Sha2Lib
