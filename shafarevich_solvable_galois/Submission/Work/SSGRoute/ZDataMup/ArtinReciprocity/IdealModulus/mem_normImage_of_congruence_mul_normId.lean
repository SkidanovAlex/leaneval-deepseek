import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.AdjustId
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.GlobalCFT

/-- **An idèle with trivial attached ideal which is congruent to `1` modulo an admissible modulus
after multiplication by a norm is itself a norm.**

Under the local–global principle for norms of idèles
(`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`) it suffices to prove that `z` is a local norm
at every place `v` of `K`.  At a finite place `Q`:

* if `Q | 𝔪`, the hypothesis `hcong` and admissibility `hadm` show that the component
  `z_Q · N(y)_Q` of `z · N(y)` is a local norm; since `N(y)_Q` is a norm (a product of local norms
  `N_{L_{q'}/K_Q}`, whose images all agree by Galois conjugation,
  `NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver`), so is `z_Q = (z_Q · N(y)_Q)·N(y)_Q⁻¹`;
* if `Q ∤ 𝔪`, then `Q` is unramified by `hram`, and `z_Q` is a local unit because `z.idealOf = 1`
  (`NK.GlobalCFT.Idele.idealOf_eq_one_iff`); for an unramified local extension the norm on units is
  surjective (`KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one`).

At an archimedean place `v` one chooses `w | v`.  If either place is complex the local norm is onto;
if `v` and `w` are both real it is an isomorphism; if `v` is real and `w` complex, the local norm is
`z ↦ |z|²`, whose image is the positive units.  In the last case positivity of `z_v` follows from
`hpos` (positivity of `z_v · N(y)_v`) and the fact that `N(y)_v` is positive, because the local
norm subgroup at a real place above a complex place is exactly the positive subgroup
(`NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap`). -/
theorem mem_normImage_of_congruence_mul_normId
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪)
    (z : NK.GlobalCFT.Idele K) (y : NK.GlobalCFT.Idele L)
    (hz : z.idealOf = 1)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 →
        NK.CFTLib.ArtinReciprocityIdeal.CongrAtId 𝔭 𝔪
          (z (NK.GlobalCFT.Place.ofFinite 𝔭) *
            NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofFinite 𝔭)))
    (hpos : ∀ w : NumberField.InfinitePlace K,
      NK.CFTLib.Arl.PosAtReal w
        (z (NK.GlobalCFT.Place.ofInfinite w) *
          NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofInfinite w))) :
    z ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L) z]
  intro v
  cases v with
  | inl v =>
      -- ## The archimedean places
      obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace L,
          w.comap (algebraMap K L) = v :=
        NumberField.InfinitePlace.comap_surjective v
      have hwl : w.LiesOver v := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v).mpr hw
      haveI : w.LiesOver v := hwl
      have hdef : Place.localNormInfinite w v
          = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
      have hzu : z (Place.ofInfinite v) ∈ (Place.localNormInfinite w v).range := by
        rw [hdef]
        rcases InfinitePlace.isReal_or_isComplex v with hvR | hvC
        · rcases InfinitePlace.isReal_or_isComplex w with hwR | hwC
          · -- both real: the local norm is onto
            rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
            exact Subgroup.mem_top _
          · -- `v` real, `w` complex: the local norm is onto the positive units
            have hNmem : Idele.normIdeleFun K L y (Place.ofInfinite v) ∈
                NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
                  (Place.ofInfinite v) :=
              NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y _
            have hNpos : (0 : ℝ) <
                (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
                  (((Idele.normIdeleFun K L y (Place.ofInfinite v) : (v.Completion)ˣ) :
                    v.Completion)) := by
              rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap hwl hvR hwC,
                Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map] at hNmem
              exact hNmem
            have hprod : (0 : ℝ) <
                (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
                  (((z (Place.ofInfinite v) * Idele.normIdeleFun K L y (Place.ofInfinite v) :
                    (v.Completion)ˣ) : v.Completion)) := hpos v hvR
            rw [Units.val_mul, map_mul] at hprod
            have hzpos : (0 : ℝ) <
                (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
                  (((z (Place.ofInfinite v) : (v.Completion)ˣ) : v.Completion)) := by
              rcases mul_pos_iff.mp hprod with ⟨ha, _⟩ | ⟨hb, hb2⟩
              · exact ha
              · exact absurd hNpos (not_lt.mpr hb2.le)
            have hmem : z (Place.ofInfinite v) ∈ Subgroup.comap
                (Units.map
                  ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom) :
                    (v.Completion)ˣ →* ℝˣ) (Units.posSubgroup ℝ) := by
              rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
              exact hzpos
            exact NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
              (v := v) (w := w) hvR hwC hmem
        · -- `v` complex: the local norm is onto
          have hwC : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
          rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
          exact Subgroup.mem_top _
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hzu
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofInfinite w) u, ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v w u]
      exact hu.symm
  | inr Q =>
      -- ## The nonarchimedean places
      obtain ⟨q, hq⟩ : ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
      have hzu : z (Place.ofFinite Q) ∈ (Place.localNormFinite q Q hq).range := by
        by_cases hQ : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 Q
        · -- `Q | 𝔪`: use admissibility on the congruent product and divide by the norm
          have h1 : (z * Idele.normIdeleHom K L y) (Place.ofFinite Q) ∈
              (Place.localNormFinite q Q hq).range := by
            have hx : NK.CFTLib.ArtinReciprocityIdeal.CongrAtId Q 𝔪
                ((z * Idele.normIdeleHom K L y) (Place.ofFinite Q)) := by
              rw [Idele.mul_apply, Idele.normIdeleHom_apply]
              exact hcong Q hQ
            exact hadm Q hQ q hq _ hx
          have h2 : Idele.normIdeleFun K L y (Place.ofFinite Q) ∈
              (Place.localNormFinite q Q hq).range := by
            rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup
              (K := K) (L := L) Q q hq]
            exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y _
          have hzeq : z (Place.ofFinite Q)
              = (z * Idele.normIdeleHom K L y) (Place.ofFinite Q)
                * (Idele.normIdeleFun K L y (Place.ofFinite Q))⁻¹ := by
            rw [Idele.mul_apply, Idele.normIdeleHom_apply]
            group
          rw [hzeq]
          exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
        · -- `Q ∤ 𝔪`: the place is unramified and `z_Q` is a local unit
          have hramQ : Q.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
            by_contra hc
            exact hQ (hram Q hc)
          have hunrq : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
            haveI : q.asIdeal.IsPrime := q.isPrime
            haveI : q.asIdeal.LiesOver Q.asIdeal := hq
            rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L)
              Q.asIdeal q.asIdeal (L ≃ₐ[K] L)]
            exact hramQ
          have hzunit : z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q) :=
            (Idele.mem_integralIdeles.mp ((Idele.idealOf_eq_one_iff z).mp hz))
              (Place.ofFinite Q) (Place.isFinite_ofFinite Q)
          obtain ⟨u, -, hu⟩ :=
            NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
              Q q hq hunrq (z (Place.ofFinite Q)) hzunit
          exact ⟨u, hu⟩
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hzu
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) u, ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u]
      exact hu.symm

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
