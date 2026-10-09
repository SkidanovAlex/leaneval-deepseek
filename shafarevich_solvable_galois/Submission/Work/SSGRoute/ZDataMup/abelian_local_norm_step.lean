import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux
import Submission.Work.SSGRoute.ZDataMup.ssg_cyclic_quotient_separates
import Submission.NK.NUV2.ARL.HR.CyclotomicTransferAux
import Submission.NeukirchUchida.Local.LocalTransfer
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Work.SSGRoute.ZDataMup.normGroup_eq_iInf_of_iSup_eq_top
import Submission.Work.SSGRoute.ZDataMup.exists_isCyclic_fixingSubgroup_notMem
import Submission.Work.SSGRoute.ZDataMup.mem_fixingSubgroup_of_mem_localFieldImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZDataMup

/-! ## The local field of an intermediate field inside the local field of the top field -/

/-- The image of the completion of an intermediate field in the completion of the top field,
as the `fieldRange` of `adjCompletionHom` (propositionally equal to `localFieldImage`, but
definitionally in the `fieldRange` normal form used by `AlgHom.equivFieldRange`). -/
noncomputable def localFieldRange {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (M : IntermediateField K L) :
    IntermediateField (Q.adicCompletion K) (q.adicCompletion L) :=
  letI : Algebra (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
      (Submission.NeukirchUchida.Local.placeUnder M q)
      (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
  (adjCompletionHom Q q hq M).fieldRange

lemma localFieldRange_eq_localFieldImage {K : Type} [Field K] [NumberField K] {L : Type}
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (M : IntermediateField K L) :
    localFieldRange Q q hq M = localFieldImage Q q hq M := by
  letI : Algebra (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
      (Submission.NeukirchUchida.Local.placeUnder M q)
      (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
  rw [localFieldRange, localFieldImage, AlgHom.fieldRange_eq_map]

/-- Every finite place of the base field has a finite place of the extension above it. -/
lemma exists_heightOneSpectrum_liesOver {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : HeightOneSpectrum (𝓞 K)) :
    ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal := by
  obtain ⟨P⟩ := (inferInstance : Nonempty ↑(Q.asIdeal.primesOver (𝓞 L)))
  exact ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver Q.ne_bot P.2⟩, P.2.2⟩

theorem finite_case_of_datum {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (D : NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))
    {x : Kˣ}
    (h : ∀ (M : IntermediateField K L), IsCyclic (↥M ≃ₐ[K] ↥M) →
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M)
          (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite Q) := by
  classical
  haveI hMC : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  haveI hAG : IsAbelianGalois K L := ⟨⟩
  letI hAlgB : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  haveI hFD : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hGal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  have hcommE : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a := by
    intro a b
    let e := Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      Q q hq
    have hinner : e.symm a * e.symm b = e.symm b * e.symm a := by
      refine Subtype.ext ?_
      exact hcomm _ _
    calc a * b = e (e.symm a) * e (e.symm b) := by rw [e.apply_symm_apply, e.apply_symm_apply]
      _ = e (e.symm a * e.symm b) := by rw [map_mul]
      _ = e (e.symm b * e.symm a) := by rw [hinner]
      _ = b * a := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
  let N : {M : IntermediateField K L // IsCyclic (↥M ≃ₐ[K] ↥M)} →
      IntermediateField (Q.adicCompletion K) (q.adicCompletion L) :=
    fun i => localFieldRange Q q hq i.1
  have htop : ⨆ i, N i = ⊤ := by
    have hbot : (⨅ i, (N i).fixingSubgroup) = ⊥ := by
      rw [eq_bot_iff]
      intro χ hχ
      by_contra hne
      let e := Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q hq
      have hσne : (e.symm χ).1 ≠ 1 := by
        intro h1
        apply hne
        have heq : χ = 1 := by
          rw [← e.apply_symm_apply χ, show e.symm χ = 1 from Subtype.ext h1, map_one]
        exact Subgroup.mem_bot.mpr heq
      obtain ⟨M, hMcyc, hMfix⟩ :=
        exists_isCyclic_fixingSubgroup_notMem (K := K) (L := L) hcomm (e.symm χ).1 hσne
      haveI hAGM : IsAbelianGalois K ↥M := inferInstance
      haveI hNM : Normal K ↥M := inferInstance
      have hχmem : χ ∈ (localFieldImage Q q hq M).fixingSubgroup := by
        rw [← localFieldRange_eq_localFieldImage Q q hq M]
        exact iInf_le (fun i : {M : IntermediateField K L // IsCyclic (↥M ≃ₐ[K] ↥M)} =>
          (N i).fixingSubgroup) ⟨M, hMcyc⟩ hχ
      rw [← e.apply_symm_apply χ] at hχmem
      exact hMfix (mem_fixingSubgroup_of_mem_localFieldImage Q q hq M (e.symm χ) hχmem)
    have hfix : (⨆ i, N i).fixingSubgroup = ⊥ :=
      le_bot_iff.mp (le_trans
        (le_iInf fun i => IntermediateField.fixingSubgroup_le (le_iSup N i))
        (le_of_eq hbot))
    have hmain : IntermediateField.fixedField ((⨆ i, N i).fixingSubgroup) = ⨆ i, N i :=
      IsGalois.fixedField_fixingSubgroup (⨆ i, N i)
    rw [hfix, IntermediateField.fixedField_bot] at hmain
    exact hmain.symm
  have hdim : ∀ i, FiniteDimensional (Q.adicCompletion K) ↥(N i) := by
    rintro ⟨M, hM⟩
    haveI hAGM : IsAbelianGalois K ↥M := inferInstance
    haveI hNM : Normal K ↥M := inferInstance
    letI hAlgM : Algebra (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)
    haveI hFDm : FiniteDimensional (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
      Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)
    exact (AlgHom.equivFieldRange (adjCompletionHom Q q hq M)).toLinearEquiv.finiteDimensional
  have hnorm : ∀ i, Normal (Q.adicCompletion K) ↥(N i) := by
    rintro ⟨M, hM⟩
    haveI hAGM : IsAbelianGalois K ↥M := inferInstance
    haveI hNM : Normal K ↥M := inferInstance
    letI hAlgM : Algebra (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)
    haveI hGalm : IsGalois (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
      Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)
    have hgal : IsGalois (Q.adicCompletion K) ↥((adjCompletionHom Q q hq M).fieldRange) :=
      (AlgHom.equivFieldRange (adjCompletionHom Q q hq M)).transfer_galois.mp inferInstance
    exact hgal.to_normal
  have hmem : ∀ i, NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(N i) := by
    rintro ⟨M, hMcyc⟩
    haveI hAGM : IsAbelianGalois K ↥M := inferInstance
    haveI hNM : Normal K ↥M := inferInstance
    letI hAlgM : Algebra (Q.adicCompletion K)
        ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion ↥M) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)
    have h1 := h M hMcyc
    rw [localNormSubgroup_ofFinite_eq_normGroup (Q := Q)
      (q := Submission.NeukirchUchida.Local.placeUnder M q)
      (hq := Submission.NeukirchUchida.Local.placeUnder_liesOver' M Q q hq)] at h1
    have h2 : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
        NK.LocalReciprocity.normGroup (Q.adicCompletion K)
          ↥((adjCompletionHom Q q hq M).fieldRange) :=
      ((NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (AlgHom.equivFieldRange (adjCompletionHom Q q hq M))).symm ▸ h1)
    exact h2
  have hcore := normGroup_eq_iInf_of_iSup_eq_top (B := Q.adicCompletion K)
    (E := q.adicCompletion L) D hcommE N hdim hnorm htop
  have hmemall : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) := by
    rw [hcore]
    exact Subgroup.mem_iInf.mpr hmem
  rw [localNormSubgroup_ofFinite_eq_normGroup (Q := Q) (q := q) (hq := hq)]
  exact hmemall

theorem infinite_case {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (v : InfinitePlace K) {x : Kˣ}
    (h : ∀ (M : IntermediateField K L), IsCyclic (↥M ≃ₐ[K] ↥M) →
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite v) x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M)
          (NK.GlobalCFT.Place.ofInfinite v)) :
    NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite v) x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite v) := by
  classical
  haveI hMC : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  haveI hAG : IsAbelianGalois K L := ⟨⟩
  obtain ⟨w₀, hw₀⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) v
  haveI hw₀I : w₀.LiesOver v := hw₀
  by_cases hvR : v.IsReal
  · by_cases hw₀R : w₀.IsReal
    · have hrange : (NK.GlobalCFT.Place.localNormInfinite w₀ v).range = ⊤ := by
        rw [show NK.GlobalCFT.Place.localNormInfinite w₀ v
            = Units.map (Algebra.norm v.Completion : w₀.Completion →* v.Completion) from rfl]
        exact NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real hvR hw₀R
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top hrange]
      exact Subgroup.mem_top _
    · have hw₀C : w₀.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw₀R
      obtain ⟨δ, hδne, -, hδconj⟩ :=
        NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
          (K := K) (L := L) w₀ v hvR hw₀C
      obtain ⟨M, hMcyc, hMfix⟩ :=
        exists_isCyclic_fixingSubgroup_notMem (K := K) (L := L) hcomm δ hδne
      haveI hAGM : IsAbelianGalois K ↥M := inferInstance
      let wM : InfinitePlace ↥M := w₀.comap (algebraMap ↥M L)
      have hwMlies : w₀.LiesOver wM :=
        (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w₀ wM).mpr rfl
      haveI hwMliesI : w₀.LiesOver wM := hwMlies
      have hwMunder : wM.LiesOver v :=
        (NK.GlobalCFT.Norm.liesOver_comap_trans (K := K) (L := ↥M) (M := L) w₀ v).mpr hw₀
      haveI hwMunderI : wM.LiesOver v := hwMunder
      have hwMC : wM.IsComplex := by
        rw [← InfinitePlace.not_isReal_iff_isComplex]
        intro hwMR
        apply hMfix
        have hreal : ComplexEmbedding.IsReal (w₀.embedding.comp (algebraMap ↥M L)) := by
          have h1 : ComplexEmbedding.IsReal
              (InfinitePlace.mk (w₀.embedding.comp (algebraMap ↥M L))).embedding := by
            rw [InfinitePlace.LiesOver.mk_embedding_comp w₀ wM]
            exact (InfinitePlace.isReal_iff (w := wM)).mp hwMR
          rcases InfinitePlace.embedding_mk_eq (w₀.embedding.comp (algebraMap ↥M L)) with h | h
          · rwa [h] at h1
          · rw [h] at h1
            rwa [ComplexEmbedding.isReal_conjugate_iff] at h1
        have hfix : ∀ y : ↥M, star ((w₀.embedding.comp (algebraMap ↥M L)) y)
            = (w₀.embedding.comp (algebraMap ↥M L)) y := by
          intro y
          have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hreal) y
          simpa [ComplexEmbedding.conjugate, RingHom.star_apply] using h2
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        apply w₀.embedding.injective
        rw [hδconj.eq y]
        simpa using hfix ⟨y, hy⟩
      have hmem := h M hMcyc
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap (K := K) (L := ↥M)
        (v := v) (w₀ := wM) hwMunder hvR hwMC] at hmem
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap (K := K) (L := L)
        (v := v) (w₀ := w₀) hw₀ hvR hw₀C]
      exact hmem
  · have hvC : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hvR
    have hw₀C : w₀.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hvC
    have hrange : (NK.GlobalCFT.Place.localNormInfinite w₀ v).range = ⊤ := by
      rw [show NK.GlobalCFT.Place.localNormInfinite w₀ v
          = Units.map (Algebra.norm v.Completion : w₀.Completion →* v.Completion) from rfl]
      exact NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hvC hw₀C
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top hrange]
    exact Subgroup.mem_top _


/-- **Shrink-to-cyclic for the local norm group of an abelian extension.**

If `x : Kˣ` is a local norm at the single place `v₀` from *every* cyclic intermediate extension
`M/K` of an abelian extension `L/K`, then `x` is a local norm at `v₀` from `L/K`.

Route (all inputs that exist in the workspace are listed):
* reduce to the completion: `B = K_{v₀}`, `E = L_{w₀}` (`w₀ | v₀`), with
  `localNormSubgroup K L v₀ = NK.LocalReciprocity.normGroup B E` — see
  `Work.SSGRoute.ZDataMup.localNormSubgroup_ofFinite_eq_normGroup` (finite places);
* the local reciprocity datum `D : NK.LocalCFT.ArtinReciprocity B (SeparableClosure B)` comes from
  `NK.NUV2.kernelCondition_all K Q` together with
  `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` (finite `v₀`); for an archimedean
  `v₀` use `NK.LocalCFT.Instance.artinReciprocity_complex`;
* embed `E` into `B^{ab}` with `Work.SSGRoute.ZDataMup.exists_level_realization`, and let
  `Λ_M ≤ Λ` be the images of the completions `(M)_{v₀ ∩ M}`;
* the hypothesis gives `x ∈ NK.LocalReciprocity.normGroup B Λ_M` (invariance of the norm group
  under a `B`-algebra isomorphism: `NK.LocalReciprocity.normGroup_eq_of_algEquiv`);
* `NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup` rewrites each norm group as the
  preimage of the fixing subgroup, and `Work.SSGRoute.ZDataMup.normGroup_iSup_eq_iInf` (or directly
  the join of the fixing subgroups) reduces the intersection to `N_{Λ/B}`;
* finally `⊔_M Λ_M = Λ`: an element `σ` of `Gal(Λ/B)` fixing every `Λ_M` already fixes every
  cyclic `M`, hence is `1` by `Work.SSGRoute.ZDataMup.ssg_cyclic_quotient_separates` applied to
  `Gal(E/K_{v₀}) ≅ D_{w₀} ≤ Gal(L/K)` (use
  `Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois`). -/
theorem abelian_local_norm_step {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {v₀ : NK.GlobalCFT.Place K} {x : Kˣ}
    (h : ∀ (M : IntermediateField K L), IsCyclic (↥M ≃ₐ[K] ↥M) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M) v₀) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  revert h
  cases v₀ with
  | inl w =>
      intro h
      exact infinite_case (K := K) (L := L) hcomm w h
  | inr Q =>
      intro h
      obtain ⟨q, hq⟩ := exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
      exact finite_case_of_datum (K := K) (L := L) hcomm Q q hq
        (Classical.choice (NK.NUV2.ARL.HR.artinReciprocity_adicCompletion Q)) h

end Work.SSGRoute.ZDataMup
