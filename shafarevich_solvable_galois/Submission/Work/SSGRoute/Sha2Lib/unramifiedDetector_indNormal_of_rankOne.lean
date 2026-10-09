import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_hom
import Submission.Work.SSGRoute.Sha2Lib.rankOneDescentAux
import Submission.Work.SSGRoute.rightDetect_quotient_step
import Submission.Work.SSGRoute.local_duality_ext_realization_of_detection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The equivariant multi-generator descent** (first sub-step of node `C6` in the form
`unramifiedDetector_indNormal`, `_lead_design/ssg_pt_design_1002/DESIGN.md` §2 A1).

`N ⊴ Gal(K/k)` contains every inertia element at `q` and fixes a primitive `p`-th root of unity
`ζ ∈ K`.  `W` is a finite *trivial* `N`-module killed by `p`.

The hypothesis `hrankOne` is the rank-one (`W = 𝔽_p`) case of the node, for every admissible `N` and
`ζ`; the conclusion is the node for an arbitrary finite trivial `p`-torsion `W`: detection of every
nonzero `φ ∈ Ext¹_{D_w}(res (Ind_N^Γ W), ℤ)` (i.e. `Sha2Lib.DetectsAt` at `φ`, which is the
`IsUnramifiedDetector` predicate of `Sha2Lib.detectorInterface`).

Reduction: a finite trivial `p`-torsion `W` is a finite direct sum of copies of `𝔽_p`; `Ind_N^Γ`
preserves finite biproducts, and `Ext¹_{D_w}(·, ℤ)` and `H¹(Gal(L/k), ·)` are additive in finite
direct sums, so a nonzero `φ` has a nonzero component `φ_i`; `hrankOne` at `φ_i` gives `L, q', h_i`
with `⟨φ_i, h_i⟩ ≠ 0` and `p ∤ e(q'|q)`, and testing `φ` against the class whose only nonzero
component is `i` (additivity of `levelPair` in the `H¹`-variable, `levelPair_add_h`) gives the same
nonzero value, with `h` still unramified at `q'`.  Known on-disk helpers:
`Sha2Lib.detectsAt_of_coeff_surjection` (pushing detection along a coefficient surjection),
`Work.SSGRoute.levelPair_add_h` (additivity of the pairing in the `H¹`-variable),
`Sha2Lib.unramifiedDetector_trivial` (the `𝔽_p`-module pattern). -/
theorem unramifiedDetector_indNormal_of_rankOne (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hrankOne : ∀ (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
      (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
      (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ),
      Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
        (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (W : Rep.{0} SSGRoute.PTExt.Coeff N) [Finite W] (hWp : ∀ x : W, p • x = 0)
    (hWtriv : ∀ (n : N) (x : W), W.ρ n x = x) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq (Rep.ind N.subtype W) := by
  classical
  have hmain : ∀ (m : ℕ) (W : Rep.{0} SSGRoute.PTExt.Coeff N) (hfin : Finite ↥W),
      Nat.card ↥W = m →
      (∀ x : W, p • x = 0) → (∀ (n : N) (x : W), W.ρ n x = x) →
      IsUnramifiedDetector p k K Ω w q hwq (Rep.ind N.subtype W) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m' ih
    intro W hfin hcard hWp hWtriv
    haveI hfin' : Finite ↥W := hfin
    by_cases htriv : ∀ x : W, x = 0
    · have hsub : Subsingleton ↥W := ⟨fun a b => by rw [htriv a, htriv b]⟩
      have hsubInd : Subsingleton ↥(Rep.ind N.subtype W) := subsingleton_ind _ N W hsub
      haveI : Subsingleton (CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype (Rep.ind N.subtype W))
          (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1) :=
        Work.SSGRoute.ExtChain.subsingleton_ext_of_subsingleton_V
          (H := ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w))
          (X := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
            (Rep.ind N.subtype W))
          hsubInd
          (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 0
      intro φ hφ
      exact absurd (Subsingleton.elim φ 0) hφ
    · push_neg at htriv
      obtain ⟨x₀, hx₀⟩ := htriv
      obtain ⟨π, s, hπx, hsπ⟩ := exists_rankOne_functional_and_section p W hWp hWtriv x₀ hx₀
      have hπsurj : Function.Surjective ⇑(Rep.Hom.hom π) := by
        intro y
        exact ⟨(Rep.Hom.hom s) y, by
          have := congrArg (fun (f : Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p) ⟶
            Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)) => (Rep.Hom.hom f) y) hsπ
          simpa using this⟩
      have hπ0 : π ≠ 0 := by
        intro h
        exact hπx (by rw [h]; rfl)
      obtain ⟨V, hVfin, hVp, hVtriv, ι, h0, hcardV, hSES⟩ :=
        exists_kernelRep_shortExact p W hWp hWtriv π hπsurj hπ0
      haveI hVfin' : Finite ↥V := hVfin
      have hdetV : IsUnramifiedDetector p k K Ω w q hwq (Rep.ind N.subtype V) :=
        ih (Nat.card ↥V) (by rw [hcard] at hcardV; exact hcardV) V hVfin rfl hVp hVtriv
      have hdetA : IsUnramifiedDetector p k K Ω w q hwq
          (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) :=
        hrankOne N hNI ζ hζ hNζ
      let SN : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff N) :=
        CategoryTheory.ShortComplex.mk ι π h0
      have hSΓ : (SN.map (Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype)).ShortExact :=
        hSES.map_of_exact _
      have hSD : ((SN.map (Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype)).map
          (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype)).ShortExact :=
        (Rep.shortExact_res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype).mpr hSΓ
      let SD : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff
          (SSGRoute.PTExt.decompK (k := k) (K := K) w)) :=
        (SN.map (Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype)).map
          (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype)
      have hSD' : SD.ShortExact := hSD
      have hf_eq : SD.f
          = Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
              ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map ι) := rfl
      have hg_eq : SD.g
          = Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
              ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map π) := rfl
      have hvu : Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
            ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map s) ≫ SD.g = 𝟙 _ := by
        have h1 : ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map s) ≫
            ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map π) = 𝟙 _ := by
          rw [← CategoryTheory.Functor.map_comp, hsπ, CategoryTheory.Functor.map_id]
        rw [hg_eq]
        show (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype).map
            ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map s) ≫
          (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype).map
            ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map π) = 𝟙 _
        rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_id]
      intro φ hφ
      by_cases hcase : (CategoryTheory.Abelian.Ext.mk₀ SD.f).comp φ (zero_add 1) = 0
      · obtain ⟨φA, hφA⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂ hSD'
          (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) φ hcase
        have hφA_ne : φA ≠ 0 := by
          intro h0'
          apply hφ
          rw [← hφA, h0']
          exact CategoryTheory.Abelian.Ext.comp_zero (CategoryTheory.Abelian.Ext.mk₀ SD.g)
            (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1 1 (zero_add 1)
        have hsec := mk0_comp_eq_of_comp_eq_id SD.g
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
            ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map s)) hvu φ φA hφA
        refine detectsAt_of_hom p k K Ω w q hwq
          (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
          (Rep.ind N.subtype W) hdetA
          ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map s) φ ?_
        intro hzero
        exact hφA_ne (hsec.symm.trans hzero)
      · have hcaseA : (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
              ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map ι))).comp φ (zero_add 1) ≠ 0 := by
          intro hzero
          exact hcase (by rw [hf_eq]; exact hzero)
        exact detectsAt_of_hom p k K Ω w q hwq (Rep.ind N.subtype V) (Rep.ind N.subtype W)
          hdetV ((Rep.indFunctor SSGRoute.PTExt.Coeff N.subtype).map ι) φ hcaseA
  exact hmain (Nat.card ↥W) W inferInstance rfl hWp hWtriv

end Work.SSGRoute.Sha2Lib
