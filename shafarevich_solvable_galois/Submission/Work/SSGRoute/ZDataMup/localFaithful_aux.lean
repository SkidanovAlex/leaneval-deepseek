import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.NUV2.kernelCondition_all
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local faithfulness of the abelian Artin map at one place

Milne, *CFT*, V.5.3(a): for a finite abelian extension `L / K` of number fields, a one-place idèle
`onePlace v a` lying in `N_{L/K} 𝕀_L · Kˣ` already lies in `N_{L/K} 𝕀_L`.

The proof reduces to the abelian "one place omitted" form of Hilbert reciprocity
(`lfab_hilbertReciprocity_abelian`), which in turn follows from the cyclic case
(`NK.CFTLib.hilbertReciprocity_onePlace_aux`) together with the *local intersection identity*: the
local norm subgroup at a place is the intersection of the local norm subgroups of the finite cyclic
intermediate extensions.  That identity is proved here for finite places (via local class field
theory at the completion, `normGroup_eq_iInf_of_iSup_eq_top`, and the fact that the completions of
the cyclic intermediate fields generate the completion of `L`, `iSup_localFieldImage_eq_top`) and
for infinite places (where the local norm subgroup is `⊤` or the positive reals, detected by the
existence of a complex place above the real place).
-/

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

set_option maxHeartbeats 8000000


set_option maxHeartbeats 8000000


/-- `IsReal` of a complex embedding depends only on the place it defines. -/
theorem lfab_isReal_of_mk_eq {K : Type} [Field K] {φ ψ : K →+* ℂ}
    (h : NumberField.InfinitePlace.mk φ = NumberField.InfinitePlace.mk ψ) :
    NumberField.ComplexEmbedding.IsReal φ ↔ NumberField.ComplexEmbedding.IsReal ψ := by
  rcases NumberField.InfinitePlace.mk_eq_iff.mp h with h' | h'
  · rw [h']
  · rw [← h', NumberField.ComplexEmbedding.isReal_conjugate_iff]

/-- **The local norm subgroup at a finite place is the intersection of the local norm subgroups of
the finite cyclic intermediate extensions.** -/
theorem localNormSubgroup_iInf_cyclic_ofFinite
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) =
      ⨅ (M : {M : IntermediateField K L // IsCyclic (↥M ≃ₐ[K] ↥M)}),
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M.1) (Place.ofFinite Q) := by
  classical
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  haveI hfdE : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgalE : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  have hcommE : ∀ a b : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      a * b = b * a := by
    intro a b
    let e := (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      Q q hq).symm
    refine e.injective ?_
    rw [map_mul, map_mul]
    exact Subtype.ext (hcomm (e a).1 (e b).1)
  obtain ⟨D⟩ := NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion Q
    (Classical.choice (NK.NUV2.kernelCondition_all K Q))
  let N : {M : IntermediateField K L // IsCyclic (↥M ≃ₐ[K] ↥M)} →
      IntermediateField (Q.adicCompletion K) (q.adicCompletion L) :=
    fun M => localFieldImage Q q hq M.1
  have htop : ⨆ M, N M = ⊤ := iSup_localFieldImage_eq_top hcomm Q q hq
  have hdata : ∀ M : {M : IntermediateField K L // IsCyclic (↥M ≃ₐ[K] ↥M)},
      (FiniteDimensional (Q.adicCompletion K) ↥(N M)) ∧
      (Normal (Q.adicCompletion K) ↥(N M)) ∧
      (NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(N M) =
        @NK.LocalReciprocity.normGroup (Q.adicCompletion K)
          ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) _ _
          (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
            (Submission.NeukirchUchida.Local.placeUnder M.1 q)
            (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q))) := by
    intro M
    haveI : IsGalois K ↥M.1 := isGalois_intermediateField_of_comm hcomm M.1
    letI : Algebra (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
        (Submission.NeukirchUchida.Local.placeUnder M.1 q)
        (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q)
    haveI hfinA : FiniteDimensional (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) :=
      Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q
        (Submission.NeukirchUchida.Local.placeUnder M.1 q)
        (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q)
    haveI hgalA : IsGalois (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) :=
      Submission.NeukirchUchida.Local.isGalois_adicCompletion Q
        (Submission.NeukirchUchida.Local.placeUnder M.1 q)
        (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q)
    have hfinj : Function.Injective (adjCompletionHom Q q hq M.1) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
        (Submission.NeukirchUchida.Local.placeUnder M.1 q) q
        (Ideal.LiesOver.mk (by rw [Submission.NeukirchUchida.Local.placeUnder_asIdeal]))
    have e : ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) ≃ₐ[Q.adicCompletion K]
        ↥(N M) :=
      (IntermediateField.topEquiv (F := Q.adicCompletion K)
          (E := (Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1)).symm.trans
        (Subalgebra.equivMapOfInjective
          (⊤ : IntermediateField (Q.adicCompletion K)
            ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1)).toSubalgebra
          (adjCompletionHom Q q hq M.1) hfinj)
    exact ⟨e.toLinearEquiv.finiteDimensional, Normal.of_algEquiv (F := Q.adicCompletion K) e,
      (NK.LocalReciprocity.normGroup_eq_of_algEquiv e).symm⟩
  have hfd : ∀ M, FiniteDimensional (Q.adicCompletion K) ↥(N M) := fun M => (hdata M).1
  have hnorm : ∀ M, Normal (Q.adicCompletion K) ↥(N M) := fun M => (hdata M).2.1
  have hnormG : ∀ M, NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(N M) =
      @NK.LocalReciprocity.normGroup (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M.1 q).adicCompletion ↥M.1) _ _
        (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
          (Submission.NeukirchUchida.Local.placeUnder M.1 q)
          (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q)) := fun M => (hdata M).2.2
  have h := normGroup_eq_iInf_of_iSup_eq_top (B := Q.adicCompletion K) D hcommE N hfd hnorm htop
  rw [localNormSubgroup_ofFinite_eq_normGroup (K := K) (L := L) Q q hq]
  rw [h]
  refine iInf_congr fun M => ?_
  haveI : IsGalois K ↥M.1 := isGalois_intermediateField_of_comm hcomm M.1
  rw [localNormSubgroup_ofFinite_eq_normGroup (K := K) (L := ↥M.1) Q
    (Submission.NeukirchUchida.Local.placeUnder M.1 q)
    (Submission.NeukirchUchida.Local.liesOver_placeUnder M.1 q Q)]
  exact hnormG M


section ArchimedeanAux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Transitivity of the local norm subgroup at an infinite place -/

/-- **Transitivity of the local norm subgroup at an infinite place**: for `K ⊆ M ⊆ L` and an
infinite place `w` of `K`, the local norm subgroup of `L` is contained in that of `M`. -/
theorem lfab_localNormSubgroup_ofInfinite_le_of_le {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (M : IntermediateField K L) (w : InfinitePlace K) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M)
        (NK.GlobalCFT.Place.ofInfinite w) := by
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite (K := K) (L := L),
    NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite (K := K) (L := ↥M)]
  refine iSup_le fun w'' => ?_
  haveI hw'' : w''.1.LiesOver w := w''.2
  set w' : InfinitePlace ↥M := w''.1.comap (algebraMap ↥M L) with hw'def
  haveI hle : w''.1.LiesOver w' :=
    NK.GlobalCFT.Norm.liesOver_comap_self (K := ↥M) (L := L) w''.1
  have hrel : w'.LiesOver w :=
    (NK.GlobalCFT.Norm.liesOver_comap_trans (K := K) (L := ↥M) (M := L) w''.1 w).mpr hw''
  haveI := hrel
  refine le_iSup_of_le ⟨w', hrel⟩ ?_
  rintro z ⟨y, rfl⟩
  exact ⟨NK.GlobalCFT.Place.localNormInfinite w''.1 w' y,
    NK.GlobalCFT.Norm.localNormInfinite_trans (K := K) (L := ↥M) (M := L)
      (v := w) (w := w') (w' := w''.1) y⟩

/-! ## The archimedean step: a cyclic subextension which is complex at a real place -/

/-- If `w` is a real place of `K`, `L / K` is a finite Galois extension, and **every** place of
`L` above `w` is complex, then some cyclic intermediate field `M` has a complex place above `w`.

Proof sketch: choose a complex place `w''` of `L` above `w` and let `ψ = w''.embedding`.  The
`K`-conjugate embedding `conj ∘ ψ` is `ψ ∘ σ` for an involution `σ ∈ Gal(L/K)` (the local complex
conjugation), and `σ ≠ 1` because `ψ` is not real.  If every cyclic `M` were real at `w`, then
`ψ|_M` would be real for every such `M`, i.e. `σ` would fix `M`, whence `σ` would fix
`L = ⨆ M`, contradicting `σ ≠ 1`. -/
theorem lfab_exists_isCyclic_isComplex_at {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (w : InfinitePlace K) (hwR : w.IsReal)
    (hwc : ∀ w' : InfinitePlace L, w'.LiesOver w → w'.IsComplex) :
    ∃ M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)},
      ∃ w'M : InfinitePlace ↥M.1, w'M.LiesOver w ∧ w'M.IsComplex := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ M w'M, w'M.LiesOver w → ¬ w'M.IsComplex`
  obtain ⟨w'', hw''⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
  haveI hw''LO : w''.LiesOver w := hw''
  have hw''C : w''.IsComplex := hwc w'' hw''
  have hw''nR : ¬ NumberField.ComplexEmbedding.IsReal w''.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp hw''C
  -- the restriction of `ψ = w''.embedding` to `K` is real
  have hψK_real : NumberField.ComplexEmbedding.IsReal
      (w''.embedding.comp (algebraMap K L)) := by
    have hmkw : NumberField.InfinitePlace.mk (w''.embedding.comp (algebraMap K L)) = w := by
      rw [← NumberField.InfinitePlace.comap_mk (φ := w''.embedding) (f := algebraMap K L)]
      rw [NumberField.InfinitePlace.mk_embedding]
      rw [NumberField.InfinitePlace.LiesOver.comap_eq w'' w]
    have hmk : NumberField.InfinitePlace.mk (w''.embedding.comp (algebraMap K L))
        = NumberField.InfinitePlace.mk (NumberField.InfinitePlace.embedding w) := by
      rw [hmkw]
      rw [NumberField.InfinitePlace.mk_embedding]
    exact (lfab_isReal_of_mk_eq hmk).mpr (NumberField.InfinitePlace.isReal_iff.mp hwR)
  -- the local complex conjugation `σ`
  have hconj : (NumberField.ComplexEmbedding.conjugate w''.embedding).comp (algebraMap K L)
      = w''.embedding.comp (algebraMap K L) := by
    rw [NumberField.ComplexEmbedding.conjugate_comp]
    exact NumberField.ComplexEmbedding.isReal_iff.mp hψK_real
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
    (K := L) (k := K) (NumberField.ComplexEmbedding.conjugate w''.embedding) w''.embedding hconj
  have hσ1 : ∀ x : L, w''.embedding (σ x) = star (w''.embedding x) := by
    intro x
    have hx := RingHom.congr_fun hσ (σ x)
    simp only [RingHom.comp_apply] at hx
    rw [show (↑σ.symm : L →+* L) (σ x) = x from AlgEquiv.symm_apply_apply σ x,
      NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply] at hx
    exact hx.symm
  have hσne : σ ≠ 1 := by
    intro h1
    apply hw''nR
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    have hx := hσ1 x
    rw [h1] at hx
    simpa using hx.symm
  -- `σ` fixes every cyclic intermediate field
  have hMfix : ∀ M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)},
      σ ∈ M.1.fixingSubgroup := by
    intro M
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hrealM : NumberField.ComplexEmbedding.IsReal
        (w''.embedding.comp (algebraMap ↥M.1 L)) := by
      have hlies : (w''.comap (algebraMap ↥M.1 L)).LiesOver w :=
        (NK.GlobalCFT.Norm.liesOver_comap_trans (K := K) (L := ↥M.1) (M := L) w'' w).mpr hw''
      have hreal : (w''.comap (algebraMap ↥M.1 L)).IsReal :=
        NumberField.InfinitePlace.not_isComplex_iff_isReal.mp
          (hcon M (w''.comap (algebraMap ↥M.1 L)) hlies)
      have hmk : NumberField.InfinitePlace.mk (w''.embedding.comp (algebraMap ↥M.1 L))
          = NumberField.InfinitePlace.mk
            (NumberField.InfinitePlace.embedding (w''.comap (algebraMap ↥M.1 L))) := by
        rw [← NumberField.InfinitePlace.comap_mk (φ := w''.embedding) (f := algebraMap ↥M.1 L)]
        rw [NumberField.InfinitePlace.mk_embedding]
        rw [NumberField.InfinitePlace.mk_embedding]
      exact (lfab_isReal_of_mk_eq hmk).mpr (NumberField.InfinitePlace.isReal_iff.mp hreal)
    have hxstar : star (w''.embedding x) = w''.embedding x := by
      have h := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp hrealM)
        (⟨x, hx⟩ : ↥M.1)
      simpa only [RingHom.comp_apply, NumberField.ComplexEmbedding.conjugate_coe_eq,
        IntermediateField.algebraMap_apply, starRingEnd_apply] using h
    exact w''.embedding.injective ((hσ1 x).trans hxstar)
  have hmem : σ ∈ ⨅ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}),
      M.1.fixingSubgroup := Subgroup.mem_iInf.mpr hMfix
  have hbot : (⨅ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1.fixingSubgroup)
      = ⊥ := by
    rw [← fixingSubgroup_iSup_eq_iInf'
        (fun M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)} => M.1),
      isCyclic_intermediateField_iSup_eq_top (K := K) (L := L) hcomm,
      IntermediateField.fixingSubgroup_top]
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hσne hmem

/-- **The one-place step at an infinite place from the cyclic case.** -/
theorem lfab_localImage_mem_localNormSubgroup_ofInfinite
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (x : Kˣ) (w : InfinitePlace K)
    (hM : ∀ M : IntermediateField K L, IsCyclic (M ≃ₐ[K] M) →
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M)
          (NK.GlobalCFT.Place.ofInfinite w)) :
    NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  by_cases hwC : w.IsComplex
  · obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
    haveI : w'.LiesOver w := hw'
    have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) = ⊤ :=
      NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := L)
        (v := w) (w₀ := w')
        (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
          (K := K) (L := L) (v := w) (w := w') hwC
          (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' hwC))
    rw [htop]
    exact Subgroup.mem_top _
  · have hwR : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hwC
    by_cases hre : ∃ w' : InfinitePlace L, w'.LiesOver w ∧ w'.IsReal
    · obtain ⟨w', hw', hw'R⟩ := hre
      haveI : w'.LiesOver w := hw'
      have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
          (NK.GlobalCFT.Place.ofInfinite w) = ⊤ :=
        NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := L)
          (v := w) (w₀ := w')
          (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real
            (K := K) (L := L) (v := w) (w := w') hwR hw'R)
      rw [htop]
      exact Subgroup.mem_top _
    · have hwc : ∀ w' : InfinitePlace L, w'.LiesOver w → w'.IsComplex :=
        fun w' h => NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
          (fun hR => hre ⟨w', h, hR⟩)
      obtain ⟨M, w'M, hw'M, hw'MC⟩ :=
        lfab_exists_isCyclic_isComplex_at (K := K) (L := L) hcomm w hwR hwc
      obtain ⟨w'', hw''⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
      haveI : w''.LiesOver w := hw''
      haveI hMgal : IsGalois K ↥M.1 := isGalois_intermediateField_of_comm hcomm M.1
      let E : (w.Completion)ˣ →* ℝˣ :=
        Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toMulEquiv.toMonoidHom
      have hMv : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M.1)
          (NK.GlobalCFT.Place.ofInfinite w) = (Units.posSubgroup ℝ).comap E :=
        NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap (K := K) (L := ↥M.1)
          (v := w) (w₀ := w'M) hw'M hwR hw'MC
      have hLv : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
          (NK.GlobalCFT.Place.ofInfinite w) = (Units.posSubgroup ℝ).comap E :=
        NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap (K := K) (L := L)
          (v := w) (w₀ := w'') hw'' hwR (hwc w'' hw'')
      have hmem : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x
          ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M.1)
            (NK.GlobalCFT.Place.ofInfinite w) := hM M.1 M.2
      rw [hMv] at hmem
      rw [hLv]
      exact hmem


end ArchimedeanAux

