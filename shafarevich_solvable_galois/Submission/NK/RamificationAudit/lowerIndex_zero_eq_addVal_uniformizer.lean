import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.RamificationAudit.perfectField_residueField_comap
import Submission.NK.RamificationDeep.algebra_isIntegral_inertiaField_comap
import Submission.NK.RamificationDeep.algebra_isIntegral_comap
import Submission.NK.RamificationDeep.isIntegralClosure_comap
import Submission.NK.RamificationDeep.isNoetherianRing_comap
import Submission.NK.RamificationAudit.Vocab
import Submission.NK.RamificationDeep.comapHom_mem_maximalIdeal_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The zeroth lower index is the ramification index: `g_0 = e`

For `L/K` a Galois extension, `M : IntermediateField K L`, `A : ValuationSubring L` a discrete
valuation ring stable under all of `Gal(L/K)` (`A.decompositionSubgroup K = ⊤`) with perfect
residue field, and `ϖ` a uniformizer of the ring `B = A ∩ M = A.comap (algebraMap ↥M L)`, the
zeroth lower index of the ramification filtration computed over the base `↥M` is the ramification
index:

  `g_0 = #G_0(L/M) = e(L/M) = addVal_A(ϖ)`.

The classical input `#(inertia subgroup) = ramification index` is Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn`, applied to the local ring extension `B ⊆ A`; the
identification of the ramification index with `addVal` of a uniformizer is
`Ideal.ramificationIdx'_spec`.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise
open NK.RamificationDeep

namespace NK.RamificationAudit


theorem lowerIndex_zero_eq_addVal_uniformizer {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (M : IntermediateField K L) [IsGalois K ↥M] [IsGalois K L]
    [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    [PerfectField (IsLocalRing.ResidueField A)]
    (ϖ : ↥(A.comap (algebraMap ↥M L)))
    (hϖ : IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M L)) = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) :
    NK.Ramification.lowerIndex (K := ↥M) A 0
      = (IsDiscreteValuationRing.addVal A ⟨(ϖ : ↥M), ϖ.2⟩).toNat := by
  -- ======================= setup =======================
  have hAM : A.decompositionSubgroup ↥M = ⊤ := decompositionSubgroup_restrict_eq_top A M hA
  haveI hfinK : Finite (L ≃ₐ[K] L) := finite_galoisGroup A hA
  haveI hfdKL : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite K L
  haveI hfdKM : FiniteDimensional K ↥M := finiteDimensional_intermediateField hfinK M
  haveI hfdML : FiniteDimensional ↥M L := Module.Finite.of_restrictScalars_finite K ↥M L
  haveI hfinML : Fintype (L ≃ₐ[↥M] L) := AlgEquiv.fintype ↥M L
  haveI hHfin : Finite ↥(A.decompositionSubgroup ↥M) := inferInstance
  haveI hintMA : Algebra.IsIntegral ↥(A.comap (algebraMap ↥M L)) ↥A :=
    algebra_isIntegral_comap (K := ↥M) A hAM
  haveI hICMA : IsIntegralClosure ↥A ↥(A.comap (algebraMap ↥M L)) L :=
    isIntegralClosure_comap A hintMA
  haveI hnoethMB : IsNoetherianRing ↥(A.comap (algebraMap ↥M L)) := isNoetherianRing_comap A
  have hnfMB : ¬ IsField ↥(A.comap (algebraMap ↥M L)) := fun hf =>
    IsDiscreteValuationRing.not_isField ↥A
      (isField_of_isIntegral_of_isField' (R := ↥(A.comap (algebraMap ↥M L))) (S := ↥A) (hR := hf))
  have hVRMB : ValuationRing ↥(A.comap (algebraMap ↥M L)) := inferInstance
  haveI hBdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M L)) :=
    (IsDiscreteValuationRing.TFAE ↥(A.comap (algebraMap ↥M L)) hnfMB).out 1 2 |>.mpr hVRMB
  haveI hBintcl : IsIntegrallyClosed ↥(A.comap (algebraMap ↥M L)) := inferInstance
  haveI hBdom : IsDomain ↥(A.comap (algebraMap ↥M L)) := inferInstance
  haveI hAdom : IsDomain ↥A := inferInstance
  haveI hAded : IsDedekindDomain ↥A := inferInstance
  haveI hBded : IsDedekindDomain ↥(A.comap (algebraMap ↥M L)) := inferInstance
  haveI hfinBA : Module.Finite ↥(A.comap (algebraMap ↥M L)) ↥A :=
    IsIntegralClosure.finite ↥(A.comap (algebraMap ↥M L)) ↥M L ↥A
  haveI htorsBA : Module.IsTorsionFree ↥(A.comap (algebraMap ↥M L)) ↥A :=
    ⟨fun {r} hr => by
      intro m₁ m₂ hm
      have hr0 : r ≠ 0 := by
        intro h0
        have h1 : (0 : ↥(A.comap (algebraMap ↥M L))) * 1
            = (0 : ↥(A.comap (algebraMap ↥M L))) * 0 := by simp
        exact one_ne_zero (hr.left (by simpa [h0] using h1))
      have hmap0 : algebraMap ↥(A.comap (algebraMap ↥M L)) ↥A r ≠ 0 := by
        intro h
        have h1 : algebraMap ↥M L (r : ↥M) = 0 := by
          have := congrArg (fun x : ↥A => (x : L)) h
          simpa [NK.RamificationDeep.coe_algebraMap_comap_apply] using this
        exact hr0 (Subtype.ext (by simpa using h1))
      exact mul_left_cancel₀ hmap0 (by simpa [Algebra.smul_def] using hm)⟩
  haveI hflatBA : Module.Flat ↥(A.comap (algebraMap ↥M L)) ↥A := inferInstance
  -- ======================= the pair (𝔪_B, 𝔪_A) =======================
  haveI hLies : (IsLocalRing.maximalIdeal ↥A).LiesOver
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) := by
    refine ⟨?_⟩
    ext b
    rw [Ideal.mem_comap, NK.RamificationDeep.algebraMap_comap_apply]
    exact (NK.RamificationDeep.comapHom_mem_maximalIdeal_iff A b).symm
  haveI hperfB : PerfectField (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L))) :=
    perfectField_residueField_comap A M hA
  haveI hperf : PerfectField (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).ResidueField := by
    haveI hloc : IsLocalization
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).primeCompl
        ↥(A.comap (algebraMap ↥M L)) :=
      IsLocalization.of_le_isUnit (fun x hx =>
        not_not.mp (fun h => hx ((IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr h))))
    haveI hlocL : IsLocalization
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).primeCompl
        (Localization.AtPrime (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L)))) :=
      Localization.isLocalization
    let e : ↥(A.comap (algebraMap ↥M L)) ≃+*
        Localization.AtPrime (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) :=
      (IsLocalization.algEquiv (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).primeCompl
        ↥(A.comap (algebraMap ↥M L))
        (Localization.AtPrime (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))))).toRingEquiv
    haveI := hperfB
    exact PerfectField.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)
  -- ======================= IsGaloisGroup =======================
  haveI hgal : IsGaloisGroup ↥(A.decompositionSubgroup ↥M)
      ↥(A.comap (algebraMap ↥M L)) ↥A :=
    { faithful := ⟨fun {σ τ} h => by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        have hjk : (σ : L →+* L) = (τ : L →+* L) := by
          refine IsLocalization.ringHom_ext (nonZeroDivisors ↥A) ?_
          ext a
          have h2 := congrArg (fun y : ↥A => (y : L)) (h a)
          rw [NK.Ramification.coe_smul, NK.Ramification.coe_smul] at h2
          simpa using h2
        exact DFunLike.congr_fun hjk x⟩
      commutes := ⟨fun σ b a => by
        show σ • (algebraMap ↥(A.comap (algebraMap ↥M L)) ↥A b * a)
          = algebraMap ↥(A.comap (algebraMap ↥M L)) ↥A b * (σ • a)
        rw [smul_mul']
        congr 1
        apply Subtype.ext
        rw [NK.Ramification.coe_smul]
        exact AlgEquiv.commutes (σ : L ≃ₐ[↥M] L) (b : ↥M)⟩
      isInvariant := ⟨fun a ha => by
        have hfix : ∀ g : L ≃ₐ[↥M] L, g (a : L) = (a : L) := by
          intro g
          have hg : g ∈ A.decompositionSubgroup ↥M := by rw [hAM]; trivial
          have h2 := congrArg (fun y : ↥A => (y : L)) (ha ⟨g, hg⟩)
          rwa [NK.Ramification.coe_smul] at h2
        obtain ⟨m, hm⟩ := Algebra.IsInvariant.isInvariant (A := ↥M) (B := L)
          (G := L ≃ₐ[↥M] L) (a : L)
          (fun g => by rw [AlgEquiv.smul_def]; exact hfix g)
        exact ⟨⟨m, by rw [ValuationSubring.mem_comap, hm]; exact a.2⟩, by
          apply Subtype.ext
          simpa [NK.RamificationDeep.comapHom_apply] using hm⟩⟩ }
  -- ======================= the card identity =======================
  have hcard : Nat.card ↥(Ideal.inertia ↥(A.decompositionSubgroup ↥M)
        (IsLocalRing.maximalIdeal ↥A))
      = (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).ramificationIdxIn ↥A :=
    Ideal.card_inertia_eq_ramificationIdxIn
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) (IsLocalRing.maximalIdeal ↥A)
  -- ======================= the ramification index =======================
  have hpow : ∀ {n : ℕ} {x : ↥A},
      x ∈ IsLocalRing.maximalIdeal ↥A ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal A x := by
    intro n x
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
    have hmax : IsLocalRing.maximalIdeal ↥A = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_eq_mul, mul_one]
  have hu0 : (⟨(ϖ : ↥M), ϖ.2⟩ : ↥A) ≠ 0 := by
    intro h
    have h1 : algebraMap ↥M L (ϖ : ↥M) = 0 := by
      have h2 : ((⟨(ϖ : ↥M), ϖ.2⟩ : ↥A) : L) = ((0 : ↥A) : L) :=
        congrArg (fun y : ↥A => (y : L)) h
      simpa using h2
    exact hϖ0 (Subtype.ext (FaithfulSMul.algebraMap_injective ↥M L h1))
  have huval : IsDiscreteValuationRing.addVal A (⟨(ϖ : ↥M), ϖ.2⟩ : ↥A) ≠ ⊤ := by
    rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hu0
  have hspec : (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).ramificationIdxIn ↥A
      = (IsDiscreteValuationRing.addVal A ⟨(ϖ : ↥M), ϖ.2⟩).toNat := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) (IsLocalRing.maximalIdeal ↥A)
      ↥(A.decompositionSubgroup ↥M)]
    have hmapspan : Ideal.map (algebraMap ↥(A.comap (algebraMap ↥M L)) ↥A)
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) = Ideal.span {⟨(ϖ : ↥M), ϖ.2⟩} := by
      rw [hϖ, Ideal.map_span, Set.image_singleton]
      congr 1
    have hne : Ideal.map (algebraMap ↥(A.comap (algebraMap ↥M L)) ↥A)
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) ≠ ⊥ := by
      rw [hmapspan, ne_eq, Ideal.span_singleton_eq_bot]
      exact hu0
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx'
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))) (IsLocalRing.maximalIdeal ↥A) hne]
    refine Ideal.ramificationIdx'_spec ?_ ?_
    · rw [hmapspan, Ideal.span_le, Set.singleton_subset_iff]
      exact hpow.mpr (by rw [ENat.natCast_toNat huval])
    · intro hle
      rw [hmapspan, Ideal.span_le, Set.singleton_subset_iff] at hle
      refine absurd (hpow.mp hle) ?_
      rw [← ENat.natCast_toNat huval]
      exact not_le.mpr (by exact_mod_cast Nat.lt_succ_self _)
  -- ======================= assembly =======================
  have hsub : NK.Ramification.ramificationSubgroup (K := ↥M) A 0
      = Ideal.inertia ↥(A.decompositionSubgroup ↥M) (IsLocalRing.maximalIdeal ↥A) := by
    ext σ
    rw [NK.Ramification.mem_ramificationSubgroup_iff, AddSubgroup.mem_inertia]
    simp
  calc NK.Ramification.lowerIndex (K := ↥M) A 0
      = Nat.card ↥(Ideal.inertia ↥(A.decompositionSubgroup ↥M) (IsLocalRing.maximalIdeal ↥A)) := by
        rw [NK.Ramification.lowerIndex, hsub]
    _ = (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥M L))).ramificationIdxIn ↥A := hcard
    _ = (IsDiscreteValuationRing.addVal A ⟨(ϖ : ↥M), ϖ.2⟩).toNat := hspec

end NK.RamificationAudit

