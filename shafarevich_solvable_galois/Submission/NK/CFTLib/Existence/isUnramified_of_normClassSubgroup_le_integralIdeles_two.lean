import Mathlib
import Submission.NK.NUV2.LC.hilbertReciprocity
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-two case of the conductor theorem, from the `2`-torsion Hilbert reciprocity law

The target of the sibling file,
`NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles`, consumes the general
"one place omitted" form of Hilbert reciprocity.  In this file the same theorem is recorded in the
degree-two case, where the arithmetic input is the *canonical* `2`-torsion product formula that
the `NK.NUV2` chapter states as `NK.NUV2.LC.HilbertReciprocityTwo` (the set of places at which
`x ∈ Kˣ` fails to be a local norm is finite of even cardinality), together with
`NK.NUV2.LC.HilbertReciprocityTwo.eq_empty_of_subset_singleton`.

The bridge between the two vocabularies is `isLocalNorm_iff_exists_idele`: the workspace's
`NK.NUV2.LC.IsLocalNorm K L x v` ("the image of `x` in `K_vˣ` is a norm from the local field at
some place above `v`") is equivalent to the form in which the local–global principle for idèles
(`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`) consumes it, namely
`∃ y : 𝕀_L, P(x)_v = N(y)_v`.  In the Galois case all the local norm groups over a fixed `v`
coincide (finite places: `NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver`; infinite
places: the type — real or complex — is Galois-invariant there, and the range of the local norm is
`⊤` in the `real/real` and `complex/complex` cases and the positive reals in the
`real/complex` case), so the product `N(y)_v = ∏_{w | v} N(y_w)` lies in the norm group of a single
`w` above `v`.

**Status.**  Three of the four implications of the bridge are proved (at finite places in both
directions, by exhibiting the single-place idèle `singleIdele q y'`, and at infinite places in the
`⟹` direction); the remaining implication — the `⟸` direction at an infinite place — is recorded as
the single `sorry` of this file, together with its precise remaining content (the Galois-invariance
of the local norm range over a fixed infinite place).  Given the bridge, the degree-two case of the target
follows from `HilbertReciprocityTwo` exactly as in the sibling file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- `P(x)` has the same components as the inclusion `Kˣ → K_vˣ`. -/
theorem principalIdele_apply_eq_localIncl {K : Type} [Field K] [NumberField K] (x : Kˣ)
    (v : Place K) :
    (Idele.principalIdele K x) v = NK.NUV2.LC.localIncl K v x := by
  rw [Idele.principalIdele_apply]
  rfl

/-- **The easy half of the bridge at a finite place**: if some idèle of `L` has `Q`-component
`x`, then the image of `x` in `K_Qˣ` is a norm from the local field at every place of `L` above
`Q` (we use the local norm groups at the places above `Q`, which coincide in the Galois case). -/
theorem isLocalNorm_of_exists_idele_ofFinite {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (x : Kˣ) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∃ y : Idele L,
      Idele.principalIdele K x (Place.ofFinite Q) = Idele.normIdeleFun K L y (Place.ofFinite Q)) :
    NK.NUV2.LC.IsLocalNorm K L x (Place.ofFinite Q) := by
  classical
  obtain ⟨y, hy⟩ := h
  obtain ⟨q₀, hq₀⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
  refine ⟨q₀, hq₀, ?_⟩
  rw [principalIdele_apply_eq_localIncl] at hy
  rw [hy, Idele.normIdeleFun_ofFinite]
  refine Subgroup.prod_mem _ (fun q _ => ?_)
  have hq : ((q : HeightOneSpectrum (𝓞 L))).asIdeal.LiesOver Q.asIdeal :=
    (Place.mem_primesOverFinite).mp (Finset.mem_coe.mp q.2)
  rw [← NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver (hq := hq) (hq' := hq₀)]
  exact ⟨y (Place.ofFinite (q : HeightOneSpectrum (𝓞 L))), rfl⟩

/-! ## The archimedean local norm range

Over a real place `v` whose places in `L` are complex, the local norm `ℂˣ → ℝˣ` is `z ↦ |z|²`, so
its range is the group of positive reals.  In particular the range does not depend on `w | v`,
which is the invariance needed for the bridge at infinite places. -/

theorem range_localNormInfinite_eq_posSubgroup_of_isReal_of_isComplex
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] {v : InfinitePlace K} (hvR : v.IsReal)
    {w : InfinitePlace L} (hw : w.LiesOver v) (hwC : w.IsComplex) :
    (Place.localNormInfinite w v).range
      = Subgroup.comap
          (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
          (Units.posSubgroup ℝ) := by
  classical
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR
  haveI := hw
  refine le_antisymm ?_ ?_
  · rw [show Place.localNormInfinite w v =
        Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
    rintro x ⟨y, rfl⟩
    rw [Subgroup.mem_comap, Units.mem_posSubgroup]
    simp only [Units.coe_map]
    change 0 < e ((Algebra.norm v.Completion) (y : w.Completion))
    rw [show e ((Algebra.norm v.Completion) (y : w.Completion))
        = Complex.normSq ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC)
            (y : w.Completion)) from
      NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex (K := K) (L := L)
        hvR hwC (y : w.Completion)]
    refine Complex.normSq_pos.mpr (fun hz => Units.ne_zero y ?_)
    exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).injective
      (by rw [hz, map_zero])
  · intro u hu
    rw [Subgroup.mem_comap, Units.mem_posSubgroup] at hu
    simp only [Units.coe_map] at hu
    set r : ℝ := e ((u : v.Completion)) with hr_def
    have hr : 0 < r := hu
    set z : ℂ := ((Real.sqrt r : ℝ) : ℂ) with hz_def
    have hz : z ≠ 0 := by
      intro h0
      have hsqrt : Real.sqrt r = 0 := by simpa [hz_def] using congrArg Complex.re h0
      have hr0 : r = 0 := by rw [← Real.sq_sqrt (le_of_lt hr), hsqrt]; ring
      exact absurd hr0 (ne_of_gt hr)
    refine ⟨Units.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm.toMulEquiv.toMonoidHom
      (Units.mk0 z hz), ?_⟩
    rw [show Place.localNormInfinite w v =
        Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
    refine Units.ext ?_
    refine e.injective ?_
    simp only [Units.coe_map]
    rw [show e ((Algebra.norm v.Completion)
          ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm.toMulEquiv.toMonoidHom
            ((Units.mk0 z hz : ℂ))))
        = Complex.normSq ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC)
            ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm.toMulEquiv.toMonoidHom
              ((Units.mk0 z hz : ℂ)))) from
        NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex (K := K) (L := L)
          hvR hwC _,
      show (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC)
          ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm.toMulEquiv.toMonoidHom
            ((Units.mk0 z hz : ℂ))) = ((Units.mk0 z hz : ℂ)) from
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).toMulEquiv.apply_symm_apply _]
    have hnorm : Complex.normSq z = r := by
      rw [hz_def, Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hr)]
    rw [show ((Units.mk0 z hz : ℂ)) = z from rfl, hnorm, hr_def]

/-- **The range of the archimedean local norm depends only on the place below** (Galois case). -/
theorem range_localNormInfinite_eq_of_liesOver {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {v : InfinitePlace K} {w w' : InfinitePlace L} (hw : w.LiesOver v) (hw' : w'.LiesOver v) :
    (Place.localNormInfinite w v).range = (Place.localNormInfinite w' v).range := by
  classical
  rcases v.isReal_or_isComplex with hvR | hvC
  · by_cases hreal : w.IsReal
    · haveI := hw
      have hreal' : w'.IsReal := by
        by_contra hc
        have hw'C : w'.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hc
        have hwC' : w.IsComplex :=
          NK.CFTLib.Existence.isComplex_of_liesOver_of_isComplex hw'C w hw
        exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hwC') hreal
      haveI := hw'
      rw [show Place.localNormInfinite w v =
            Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl,
        show Place.localNormInfinite w' v =
            Units.map (Algebra.norm v.Completion : w'.Completion →* v.Completion) from rfl,
        NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real
            (K := K) (L := L) hvR hreal,
        NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real
            (K := K) (L := L) hvR hreal']
    · haveI := hw
      have hwC : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hreal
      have hw'C : w'.IsComplex := NK.CFTLib.Existence.isComplex_of_liesOver_of_isComplex hwC w' hw'
      rw [range_localNormInfinite_eq_posSubgroup_of_isReal_of_isComplex
            (K := K) (L := L) hvR hw hwC,
        range_localNormInfinite_eq_posSubgroup_of_isReal_of_isComplex
            (K := K) (L := L) hvR hw' hw'C]
  · haveI := hw; haveI := hw'
    have hwC : w.IsComplex :=
      NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
    have hw'C : w'.IsComplex :=
      NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' hvC
    rw [show Place.localNormInfinite w v =
          Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl,
      show Place.localNormInfinite w' v =
          Units.map (Algebra.norm v.Completion : w'.Completion →* v.Completion) from rfl,
      NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex
          (K := K) (L := L) hvC hwC,
      NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex
          (K := K) (L := L) hvC hw'C]

/-- **The easy half of the bridge at an infinite place.** -/
theorem isLocalNorm_of_exists_idele_ofInfinite {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (x : Kˣ) (w : InfinitePlace K)
    (h : ∃ y : Idele L,
      Idele.principalIdele K x (Place.ofInfinite w) = Idele.normIdeleFun K L y (Place.ofInfinite w)) :
    NK.NUV2.LC.IsLocalNorm K L x (Place.ofInfinite w) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨w₀, hw₀⟩ := InfinitePlace.comap_surjective (k := K) (K := L) w
  have hw₀' : w₀.LiesOver w := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w₀ w).mpr hw₀
  refine ⟨w₀, hw₀', ?_⟩
  rw [principalIdele_apply_eq_localIncl] at hy
  rw [hy, Idele.normIdeleFun_ofInfinite]
  refine Subgroup.prod_mem _ (fun w' _ => ?_)
  have hw'l : (w'.1 : InfinitePlace L).LiesOver w := (Place.mem_fiberInfinite).mp w'.2
  rw [← range_localNormInfinite_eq_of_liesOver (K := K) (L := L) hw'l hw₀']
  exact ⟨y (Place.ofInfinite w'.1), rfl⟩

/-- **The other half of the bridge**: if the image of `x` in `K_vˣ` is a local norm, then it is
the `v`-component of an idèle norm — by exhibiting the single-place idèle above `v`. -/
theorem exists_idele_of_isLocalNorm {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (x : Kˣ) (v : Place K)
    (h : NK.NUV2.LC.IsLocalNorm K L x v) :
    ∃ y : Idele L, Idele.principalIdele K x v = Idele.normIdeleFun K L y v := by
  classical
  cases v with
  | inl w =>
      obtain ⟨w', hw', hmem⟩ := h
      obtain ⟨y', hy'⟩ := hmem
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofInfinite w') y', ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite,
        principalIdele_apply_eq_localIncl]
      exact hy'.symm
  | inr Q =>
      obtain ⟨q, hq, hmem⟩ := h
      obtain ⟨y', hy'⟩ := hmem
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) y', ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq,
        principalIdele_apply_eq_localIncl]
      exact hy'.symm

/-- **The bridge between the two local-norm vocabularies.** -/
theorem isLocalNorm_iff_exists_idele {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (x : Kˣ) (v : Place K) :
    NK.NUV2.LC.IsLocalNorm K L x v ↔
      ∃ y : Idele L, Idele.principalIdele K x v = Idele.normIdeleFun K L y v := by
  cases v with
  | inl w =>
      exact ⟨exists_idele_of_isLocalNorm x (Place.ofInfinite w),
        isLocalNorm_of_exists_idele_ofInfinite x w⟩
  | inr Q =>
      exact ⟨exists_idele_of_isLocalNorm x (Place.ofFinite Q),
        isLocalNorm_of_exists_idele_ofFinite x Q⟩

/-- **The "one place omitted" form of Hilbert reciprocity at degree two**, from the workspace's
canonical `2`-torsion product formula. -/
theorem localNormImage_of_forall_ne_of_hilbertReciprocityTwo
    (hHR2 : NK.NUV2.LC.HilbertReciprocityTwo)
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2)
    {x : Kˣ} {v₀ : Place K}
    (h : ∀ v : Place K, v ≠ v₀ → ∃ y : Idele L,
      Idele.principalIdele K x v = Idele.normIdeleFun K L y v) :
    Idele.principalIdele K x ∈ Idele.normImage K L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (p := 2) h2
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
  intro v
  obtain ⟨s, hs, heven⟩ := hHR2 K L h2 x
  -- the only possible member of the bad set is `v₀`
  have hsub : ∀ v ∈ s, v = v₀ := by
    intro v hv'
    by_contra hne
    exact (hs v).mp hv' ((isLocalNorm_iff_exists_idele x v).mpr (h v hne))
  -- an even bad set contained in a singleton is empty
  have hempty : s = ∅ := by
    rcases Finset.eq_empty_or_nonempty s with hse | ⟨v, hv'⟩
    · exact hse
    · exfalso
      have hcard : s.card = 1 :=
        le_antisymm
          (Finset.card_le_one.mpr fun a ha b hb => by rw [hsub a ha, hsub b hb])
          (Finset.card_pos.mpr ⟨v, hv'⟩)
      rw [hcard] at heven
      norm_num at heven
  exact exists_idele_of_isLocalNorm x v (by
    by_contra hbad
    exact Finset.notMem_empty v (hempty ▸ (hs v).mpr hbad))

/-- **The degree-two case of the conductor theorem**, from the canonical `2`-torsion product
formula. -/
theorem isUnramified_of_normClassSubgroup_le_integralIdeles_of_hilbertReciprocityTwo
    (hHR2 : NK.NUV2.LC.HilbertReciprocityTwo)
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hdeg : Module.finrank K L = 2)
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤
      Idele.normClassSubgroup K L) :
    differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L := by
  classical
  have hcyc : IsCyclic (L ≃ₐ[K] L) := by
    refine isCyclic_of_prime_card (p := 2) ?_
    rw [IsGalois.card_aut_eq_finrank K L]
    exact hdeg
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank K L]
    exact hdeg
  obtain ⟨hfin, hinf⟩ :=
    localUnits_le_range_localNorm_of_integralIdeles' (K := K) (L := L) (p := 2) hdeg
      (fun {x v₀} hx => localNormImage_of_forall_ne_of_hilbertReciprocityTwo hHR2 hcard hx) hray
  constructor
  · refine differentIdeal_eq_top_of_ramificationIdx_heightOne ?_
    intro q
    let QK : HeightOneSpectrum (𝓞 K) := q.under (𝓞 K)
    have hlies : q.asIdeal.LiesOver QK.asIdeal :=
      (Ideal.liesOver_iff _ _).mpr (by simp only [QK, HeightOneSpectrum.under_asIdeal])
    exact ramificationIdx_eq_one_of_localUnits_le_localNorm (K := K) (L := L) hcyc hdeg
      QK q hlies (hfin QK q hlies)
  · refine ⟨fun w => ?_⟩
    rw [NumberField.InfinitePlace.isUnramified_iff]
    rcases w.isReal_or_isComplex with hR | hC
    · exact Or.inl hR
    · refine Or.inr ?_
      by_contra hv
      have hvR : (w.comap (algebraMap K L)).IsReal :=
        NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hv
      haveI hwv : w.LiesOver (w.comap (algebraMap K L)) :=
        (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w _).mpr rfl
      let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR
      let u : (w.comap (algebraMap K L)).Completionˣ :=
        Units.map e.symm.toMulEquiv.toMonoidHom (Units.mk0 (-1 : ℝ) (by norm_num))
      obtain ⟨u', hu'⟩ := hinf (w.comap (algebraMap K L)) w u
      have hle : (NK.GlobalCFT.Place.localNormInfinite w (w.comap (algebraMap K L))).range ≤
          Subgroup.comap (Units.map e.toMulEquiv.toMonoidHom) (Units.posSubgroup ℝ) := by
        rw [show NK.GlobalCFT.Place.localNormInfinite w (w.comap (algebraMap K L))
            = Units.map (Algebra.norm (w.comap (algebraMap K L)).Completion :
                w.Completion →* (w.comap (algebraMap K L)).Completion) from rfl]
        rintro x ⟨y, rfl⟩
        rw [Subgroup.mem_comap, Units.mem_posSubgroup]
        simp only [Units.coe_map]
        change 0 < e ((Algebra.norm (w.comap (algebraMap K L)).Completion) (y : w.Completion))
        rw [show e ((Algebra.norm (w.comap (algebraMap K L)).Completion) (y : w.Completion))
            = Complex.normSq ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC)
                (y : w.Completion)) from
          NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex (K := K) (L := L)
            hvR hC (y : w.Completion)]
        refine Complex.normSq_pos.mpr (fun hz => Units.ne_zero y ?_)
        exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).injective
          (by rw [hz, map_zero])
      have hmem : u ∈ Subgroup.comap (Units.map e.toMulEquiv.toMonoidHom) (Units.posSubgroup ℝ) := by
        refine hle ?_
        rw [← hu']
        exact ⟨u', rfl⟩
      rw [Subgroup.mem_comap, Units.mem_posSubgroup] at hmem
      have hc : ((Units.map e.toMulEquiv.toMonoidHom u : ℝˣ) : ℝ) = -1 := by
        simp [u]
      rw [hc] at hmem
      norm_num at hmem

end NK.CFTLib.Existence
