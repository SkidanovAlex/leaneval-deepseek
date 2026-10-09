import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.CFTLib.IdeleHasse.ideleGluing
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
import Submission.NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_decompositionSubgroup_ofInfinite_eq_finrank
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global Artin map `Φ = ∏_v λ_v`

This module assembles the local–global Artin map of a finite extension `L / K` of number fields as
the finite product of its local factors:

* the local factors at the finite places are supplied by `exists_localMap_ofFinite` (the local
  Artin map of local class field theory, Frobenius-normalised at unramified primes);
* the archimedean factors are constructed here (`exists_localMap_ofInfinite`): the trivial map when
  the local norm is onto, the sign character when `K_w = ℝ` and every place of `L` above `w` is
  complex;
* the gluing of the local factors into a single homomorphism `𝕀[K] →* Gal(L/K)` is
  `NK.CFTLib.IdeleHasse.ideleHomOfLocal` (a finite product, well defined because an idèle is a
  local unit at all but finitely many places).

The main result is `NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap'`, the four clauses
(norm-killing, surjectivity, one-place faithfulness, Frobenius normalisation) that make `Φ` the
canonical local–global Artin map.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField NumberField.LiesOver RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT


open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- In the archimedean real/complex case the range of the local norm is the subgroup of positive
reals. -/
theorem range_localNormInfinite_of_real_complex {w : InfinitePlace K} {w' : InfinitePlace L}
    [hw' : w'.LiesOver w] (hvR : w.IsReal) (hwC : w'.IsComplex) :
    (Place.localNormInfinite w' w).range =
      (Units.posSubgroup ℝ).comap (Units.map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rintro u ⟨z, rfl⟩
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      (Algebra.norm w.Completion (z : w'.Completion))
    rw [NK.NUV2.ArtinBridge.localNormInfinite_norm_eq_real_complex hvR hwC (z : w'.Completion)]
    exact Complex.normSq_pos.mpr (fun h => z.ne_zero
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).injective
        (by rw [h, map_zero])))
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    exact NK.NUV2.ArtinBridge.localNormInfinite_posSubgroup_le_range_of_real_complex hvR hwC hu

/-- **The archimedean local factor of the local–global Artin map.**  For an infinite place `w`
of `K` there is a homomorphism `K_wˣ →* Gal(L/K)` whose kernel is the local norm subgroup:
the trivial map when the local norm is onto (`K_w = ℂ`, or `K_w = ℝ` with a real place of `L`
above it), and the sign character when `K_w = ℝ` and every place of `L` above `w` is complex. -/
theorem exists_localMap_ofInfinite (hcyc : IsCyclic (L ≃ₐ[K] L)) (w : InfinitePlace K) :
    ∃ F : (w.Completion)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) := by
  classical
  let w₀ : InfinitePlace L := Classical.choose (InfinitePlace.comap_surjective (k := K) (K := L) w)
  have hw₀ : w₀.LiesOver w := (Norm.liesOver_iff_comap_eq w₀ w).mpr
    (Classical.choose_spec (InfinitePlace.comap_surjective (k := K) (K := L) w))
  haveI : w₀.LiesOver w := hw₀
  by_cases hwc : w.IsComplex
  · -- `K_w = ℂ`: the local norm is onto
    refine ⟨1, ?_⟩
    rw [MonoidHom.ker_one]
    refine le_antisymm ?_ le_top
    rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
    refine le_trans (le_of_eq ?_) (le_iSup_of_le ⟨w₀, hw₀⟩ le_rfl)
    exact (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
      (v := w) (w := w₀) hwc (InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hwc)).symm
  · have hwR : w.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hwc
    by_cases hre : ∃ w' : InfinitePlace L, w'.LiesOver w ∧ w'.IsReal
    · -- a real place above a real place: the local norm is onto
      obtain ⟨w₁, hw₁, hw₁R⟩ := hre
      refine ⟨1, ?_⟩
      rw [MonoidHom.ker_one]
      refine le_antisymm ?_ le_top
      rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
      refine le_trans (le_of_eq ?_) (le_iSup_of_le ⟨w₁, hw₁⟩ le_rfl)
      exact (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real
        (v := w) (w := w₁) hwR hw₁R).symm
    · -- every place of `L` above `w` is complex: the local norm is the positive reals
      have hcomp : ∀ (w' : InfinitePlace L) (h : w'.LiesOver w), w'.IsComplex :=
        fun w' h => InfinitePlace.not_isReal_iff_isComplex.mp fun hR => hre ⟨w', h, hR⟩
      -- an element of order two
      have hstab : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w₀) = 2 := by
        refine NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.mp ?_
        rw [NumberField.InfinitePlace.isUnramified_iff]
        refine not_or.mpr ⟨?_, ?_⟩
        · exact fun hR => InfinitePlace.not_isReal_iff_isComplex.mpr (hcomp w₀ hw₀) hR
        · rw [InfinitePlace.LiesOver.comap_eq w₀ w]
          exact InfinitePlace.not_isComplex_iff_isReal.mpr hwR
      have hcard : Fintype.card ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀) = 2 := by
        rw [← Nat.card_eq_fintype_card]; exact hstab
      obtain ⟨x, hx⟩ : ∃ x : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀), x ≠ 1 :=
        Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num)
          (1 : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀))
      have hx2 : x ^ 2 = 1 := by
        have hdiv : orderOf x ∣ 2 := by
          have := orderOf_dvd_natCard x
          rwa [hstab] at this
        have hne : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
        rw [← pow_orderOf_eq_one x]
        congr 1
        rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
        · exact absurd h hne
        · exact h.symm
      set σ : L ≃ₐ[K] L := (x : L ≃ₐ[K] L) with hσdef
      have hσne : σ ≠ 1 := fun h => hx (Subtype.ext h)
      have hσ2 : σ * σ = 1 := by
        have h := congrArg (fun y : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀) => (y : L ≃ₐ[K] L)) hx2
        simpa [hσdef, pow_two] using h
      -- the sign character
      have hsgn : ∀ a : ℝˣ, (if 0 < (a : ℝ) then (1 : L ≃ₐ[K] L) else σ) = 1 ↔ 0 < (a : ℝ) := by
        intro a
        by_cases ha : 0 < (a : ℝ)
        · rw [if_pos ha]; exact ⟨fun _ => ha, fun _ => rfl⟩
        · have ha' : (a : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp ha) (Units.ne_zero a)
          rw [if_neg ha]
          exact ⟨fun h => absurd h hσne, fun h => absurd h (not_lt.mpr ha'.le)⟩
      have hmul : ∀ a b : ℝˣ, (if 0 < ((a * b : ℝˣ) : ℝ) then (1 : L ≃ₐ[K] L) else σ)
          = (if 0 < (a : ℝ) then 1 else σ) * (if 0 < (b : ℝ) then 1 else σ) := by
        intro a b
        have ha : (a : ℝ) < 0 ∨ 0 < (a : ℝ) :=
          lt_or_gt_of_ne (a := (a : ℝ)) (b := 0) (Units.ne_zero a)
        have hb : (b : ℝ) < 0 ∨ 0 < (b : ℝ) :=
          lt_or_gt_of_ne (a := (b : ℝ)) (b := 0) (Units.ne_zero b)
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · rw [Units.val_mul, if_pos (mul_pos_of_neg_of_neg ha hb),
            if_neg (not_lt.mpr ha.le), if_neg (not_lt.mpr hb.le), hσ2]
        · rw [Units.val_mul, if_neg (not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le),
            if_neg (not_lt.mpr ha.le), if_pos hb, mul_one]
        · rw [Units.val_mul, if_neg (not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le),
            if_pos ha, if_neg (not_lt.mpr hb.le), one_mul]
        · rw [Units.val_mul, if_pos (mul_pos ha hb), if_pos ha, if_pos hb, mul_one]
      let sgn : ℝˣ →* (L ≃ₐ[K] L) :=
        { toFun := fun a => if 0 < (a : ℝ) then 1 else σ
          map_one' := by simp
          map_mul' := hmul }
      have hker_sgn : MonoidHom.ker sgn = Units.posSubgroup ℝ := by
        ext a
        rw [MonoidHom.mem_ker, Units.mem_posSubgroup]
        change (if 0 < (a : ℝ) then (1 : L ≃ₐ[K] L) else σ) = 1 ↔ 0 < (a : ℝ)
        exact hsgn a
      -- the subgroup of local norms is the subgroup of positive reals
      have hsub : localNormSubgroup (K := K) (L := L) (Place.ofInfinite w)
          = (Units.posSubgroup ℝ).comap (Units.map
              (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toMulEquiv.toMonoidHom) := by
        rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
        refine le_antisymm (iSup_le fun w' => ?_) ?_
        · rw [range_localNormInfinite_of_real_complex (w := w) (w' := w'.1) (hw' := w'.2) hwR
            (hcomp w'.1 w'.2)]
        · exact le_iSup_of_le ⟨w₀, hw₀⟩ (le_of_eq (range_localNormInfinite_of_real_complex
            (w := w) (w' := w₀) (hw' := hw₀) hwR (hcomp w₀ hw₀)).symm)
      refine ⟨sgn.comp (Units.map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toMulEquiv.toMonoidHom), ?_⟩
      rw [hsub]
      ext a
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker (f := sgn), hker_sgn,
        Subgroup.mem_comap]




open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Auxiliary lemmas -/

/-- The `v`-component of the norm idèle lies in the local norm subgroup. -/
theorem normIdeleFun_mem_localNormSubgroup (y : Idele L) (v : Place K) :
    Idele.normIdeleFun K L y v ∈ localNormSubgroup (K := K) (L := L) v := by
  classical
  cases v with
  | inl w =>
      rw [Idele.normIdeleFun_ofInfinite, localNormSubgroup_ofInfinite (K := K) (L := L)]
      refine Subgroup.prod_mem _ fun w' _ => ?_
      exact Subgroup.mem_iSup_of_mem
        ⟨w'.1, (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2⟩
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  | inr Q =>
      rw [Idele.normIdeleFun_ofFinite, localNormSubgroup_ofFinite (K := K) (L := L)]
      refine Subgroup.prod_mem _ fun q' _ => ?_
      exact Subgroup.mem_iSup_of_mem
        ⟨q'.1, (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2⟩
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

/-- At an unramified finite place the local units are local norms. -/
theorem localUnits_le_localNormSubgroup_of_unramified (Q : HeightOneSpectrum (𝓞 K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    Place.localUnits K (Place.ofFinite Q) ≤
      localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  have he : q.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr q hq
  intro a ha
  obtain ⟨u, _hu, hua⟩ :=
    NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one
      q Q hq he a ha
  rw [← hua, ← range_localNormFinite_eq_localNormSubgroup Q q hq]
  exact MonoidHom.mem_range.mpr ⟨u, rfl⟩

/-- The `ofFinite Q`-component of the prime idèle at `Q`. -/
@[simp] theorem ideleOfPrime_apply_ofFinite_self (Q : HeightOneSpectrum (𝓞 K)) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofFinite Q) = IdeleClassGroup.unifUnit K Q := by
  classical
  rw [NK.HeckeL.ideleOfPrime]
  change IdeleClassGroup.unifUnit K Q ^ (if Q = Q then (1 : ℤ) else 0) =
    IdeleClassGroup.unifUnit K Q
  rw [if_pos rfl, zpow_one]

/-- The `ofFinite q`-component of the prime idèle at `Q ≠ q`. -/
theorem ideleOfPrime_apply_ofFinite_ne_setup {q Q : HeightOneSpectrum (𝓞 K)} (h : q ≠ Q) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofFinite q) = 1 := by
  classical
  rw [NK.HeckeL.ideleOfPrime]
  change IdeleClassGroup.unifUnit K q ^ (if q = Q then (1 : ℤ) else 0) = 1
  rw [if_neg h, zpow_zero]

/-- The archimedean components of a prime idèle are trivial. -/
@[simp] theorem ideleOfPrime_apply_ofInfinite (Q : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofInfinite w) = 1 := rfl

/-! ## The local–global Artin map -/

/-- **The local–global Artin map** `Φ = ∏_v λ_v`: the product of the local Artin maps, with

* `Φ` surjective and killing the idèle norms;
* `Φ` faithful on the one-place idèles: `Φ (onePlace v a) = 1` iff `a` is a local norm at `v`;
* `Φ` normalised by the Frobenius elements at the unramified primes. -/
theorem exists_localGlobalArtinMap' (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    ∃ Φ : Idele K →* (L ≃ₐ[K] L), Function.Surjective Φ ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      (∀ (v : Place K) (a : (Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  haveI : IsCyclic (L ≃ₐ[K] L) := hcyc
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  let Ffin : (Q : HeightOneSpectrum (𝓞 K)) → (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    fun Q => Classical.choose (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)
  have hFfin_ker : ∀ Q, MonoidHom.ker (Ffin Q) =
      localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) :=
    fun Q => (Classical.choose_spec (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)).1
  have hFfin_unif : ∀ (Q : HeightOneSpectrum (𝓞 K))
      (hu : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q),
      Ffin Q (IdeleClassGroup.unifUnit K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q :=
    fun Q hu => (Classical.choose_spec (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)).2 hu
  let Finf : (w : InfinitePlace K) → (w.Completion)ˣ →* (L ≃ₐ[K] L) :=
    fun w => Classical.choose (exists_localMap_ofInfinite (K := K) (L := L) hcyc w)
  have hFinf_ker : ∀ w, MonoidHom.ker (Finf w) =
      localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) :=
    fun w => Classical.choose_spec (exists_localMap_ofInfinite (K := K) (L := L) hcyc w)
  let F : ∀ v : Place K, (Place.localField K v)ˣ →* (L ≃ₐ[K] L) := fun v =>
    match v with
    | Sum.inl w => Finf w
    | Sum.inr Q => Ffin Q
  have hF_ker : ∀ v : Place K, MonoidHom.ker (F v) =
      localNormSubgroup (K := K) (L := L) v := by
    intro v; cases v with
    | inl w => exact hFinf_ker w
    | inr Q => exact hFfin_ker Q
  have hF_ker_apply : ∀ (v : Place K) (a : (Place.localField K v)ˣ), F v a = 1 ↔
      a ∈ localNormSubgroup (K := K) (L := L) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hF_ker v]
  have hsupport : ∀ y : Idele K, {v : Place K | F v (y v) ≠ 1}.Finite := by
    intro y
    have hInf : ({v : Place K | Place.IsInfinite v} : Set (Place K)).Finite := by
      refine (Finset.finite_toSet (Finset.univ.image (Place.ofInfinite (K := K)))).subset ?_
      intro v hv
      obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp hv
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ w))
    have hNu : ({v : Place K | y v ∉ Place.localUnits K v} : Set (Place K)).Finite :=
      Filter.eventually_cofinite.mp y.2
    have hRam : ({v : Place K | ∃ q : HeightOneSpectrum (𝓞 L),
        q.asIdeal.ramificationIdx (𝓞 K) ≠ 1 ∧
          NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q) = v}
        : Set (Place K)).Finite := by
      have hq := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)
      refine (hq.image (fun q : HeightOneSpectrum (𝓞 L) =>
        NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q))).subset ?_
      rintro v ⟨q, hqe, hqeq⟩
      exact ⟨q, hqe, hqeq⟩
    refine Set.Finite.subset (hInf.union (hNu.union hRam)) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hnot
    push_neg at hnot
    obtain ⟨h1, h2, h3⟩ := hnot
    obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp h1
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
      intro q hq
      by_contra hqe
      exact h3 q hqe
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver
          (Place.liesOver_ofFinite hq))
    exact hv ((hF_ker_apply (Place.ofFinite Q) (y (Place.ofFinite Q))).mpr
      (localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L) Q hunr h2))
  let Φ : Idele K →* (L ≃ₐ[K] L) := ideleHomOfLocal hcomm F hsupport
  have hΦ : ∀ y : Idele K, Φ y = cprod hcomm (hsupport y).toFinset (fun v => F v (y v)) := by
    intro y
    dsimp only [Φ]
    rw [ideleHomOfLocal_apply]
  have hΦ_onePlace : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = F v a := by
    intro v a
    exact ideleHomOfLocal_apply_onePlace hcomm F hsupport v a
  have h4 : ∀ (Q : HeightOneSpectrum (𝓞 K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hunr
    rw [hΦ]
    have hsingle := cprod_eq_single (hcomm := hcomm)
      (s := (hsupport (NK.HeckeL.ideleOfPrime K Q)).toFinset)
      (f := fun v => F v ((NK.HeckeL.ideleOfPrime K Q) v)) (Place.ofFinite Q)
      (fun b _ hb => by
        cases b with
        | inl w => rw [ideleOfPrime_apply_ofInfinite, map_one]
        | inr q =>
            have hqQ : q ≠ Q := fun h => hb (by rw [h])
            rw [ideleOfPrime_apply_ofFinite_ne_setup hqQ, map_one])
      (fun hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))
    rw [hsingle, ideleOfPrime_apply_ofFinite_self]
    exact hFfin_unif Q hunr
  have h1 : ∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hΦ]
    refine cprod_eq_one hcomm fun v _ => ?_
    rw [Idele.normIdeleHom_apply]
    exact (hF_ker_apply v _).mpr (normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y v)
  have h3' : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L := by
    intro v a
    rw [hΦ_onePlace v a, hF_ker_apply v a]
    exact (onePlace_mem_normImage_iff (K := K) (L := L) v a).symm
  have h2 : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top]
    let T : Finset (HeightOneSpectrum (𝓞 K)) :=
      ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)).toFinset.image (fun q : HeightOneSpectrum (𝓞 L) =>
          HeightOneSpectrum.under (𝓞 K) q))
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L) T
      Φ.range ?_
    intro p hp σ hσ
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
      intro q hq
      by_contra hqe
      have hmem : p ∈ T := by
        refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
        · rw [Set.Finite.mem_toFinset]; exact hqe
        · exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])
      exact hp hmem
    rw [NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ] at hσ
    exact ⟨NK.HeckeL.ideleOfPrime K p, by rw [h4 p hunr, hσ]⟩
  exact ⟨Φ, h2, h1, h3', h4⟩



end NK.CFTLib.IdeleHasse
