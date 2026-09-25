import Mathlib
import Submission.NK.CFTLib.roquetteDefs
import Submission.NK.CFTLib.roquette_plan
import Submission.NK.CFTLib.normPrincipalDefs
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd
import Submission.NK.CFTLib.NormPrincipal.dvd_expUnit_of_eq_normIdeleFun
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq

/-!
# `x ∈ Fˣ ∩ N_{K/F} 𝕀_K` iff the inertia degrees divide the valuations

Let `K / F` be a finite Galois extension of number fields which is unramified at every place
(`CFTLib.IsUnramified F K`).  We prove

`x ∈ normPrincipalPreimage F K ↔ ∀ v finite, f_v ∣ v(x)`,

where `normPrincipalPreimage F K = (N_{K/F} 𝕀_K).comap (principalIdele F)` is the set of elements
of `Fˣ` whose principal idèle is a norm of an idèle of `K`, `f_v = Ideal.inertiaDegIn v (𝓞 K)`
is the inertia degree of `v` in `K` and `v(x) = NK.GlobalCFTdeep.expUnit v x` is the `v`-adic
valuation of `x`.

## Strategy

* **(⇒)** If the principal idèle of `x` is a norm of an idèle `y` of `K`, then at a finite place
  `Q` of `F` we have `x_Q = ∏_{q | Q} N_{K_q/F_Q}(y_q)`.  The local norm multiplies the valuation
  by the inertia degree, so `v_Q(x) = f_Q · Σ_q v_q(y_q)`; this is
  `NK.CFTLib.NormPrincipal.dvd_expUnit_of_eq_normIdeleFun`.

* **(⇐)** If `f_Q ∣ v_Q(x)` at every finite place, then each component of the principal idèle is a
  local norm: at a finite place `Q` this is
  `NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd` (unramifiedness makes the
  local norm on units surjective), and at an infinite place the local norm is surjective because
  the extension is unramified there.  The idèle `y` realising all the local conditions at once is
  constructed by `NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage`, applied to the finite
  set of places at which `x` is not a local unit.

## Main result

* `NK.CFTLib.normPrincipalPreimage_iff_expUnit`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

section Helpers

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]

/-- A chosen infinite place of `K` above a given infinite place of `F`. -/
noncomputable def placeAboveInf (w : InfinitePlace F) : InfinitePlace K :=
  Classical.choose (InfinitePlace.comap_surjective (k := F) (K := K) w)

theorem placeAboveInf_spec (w : InfinitePlace F) :
    (placeAboveInf F K w).comap (algebraMap F K) = w :=
  Classical.choose_spec (InfinitePlace.comap_surjective (k := F) (K := K) w)

theorem liesOver_placeAboveInf (w : InfinitePlace F) : (placeAboveInf F K w).LiesOver w :=
  (NK.GlobalCFT.Norm.liesOver_iff_comap_eq _ _).mpr (placeAboveInf_spec F K w)

/-- A chosen prime of `𝓞 K` above a given prime of `𝓞 F`. -/
noncomputable def placeAboveFin (Q : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 K) :=
  Classical.choose (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := F) (L := K) Q)

theorem placeAboveFin_spec (Q : HeightOneSpectrum (𝓞 F)) :
    (placeAboveFin F K Q).asIdeal.LiesOver Q.asIdeal :=
  Classical.choose_spec (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := F) (L := K) Q)

/-- A place of `K` above a given place of `F`. -/
noncomputable def placeAbove (v : NK.GlobalCFT.Place F) : NK.GlobalCFT.Place K :=
  match v with
  | Sum.inl w => Sum.inl (placeAboveInf F K w)
  | Sum.inr Q => Sum.inr (placeAboveFin F K Q)

theorem liesOver_placeAbove (v : NK.GlobalCFT.Place F) :
    NK.GlobalCFT.Place.LiesOver (placeAbove F K v) v := by
  cases v with
  | inl w => exact NK.GlobalCFT.Place.liesOver_ofInfinite (liesOver_placeAboveInf F K w)
  | inr Q => exact NK.GlobalCFT.Place.liesOver_ofFinite (placeAboveFin_spec F K Q)

/-- The local norm at the chosen place above `v`, as an explicit homomorphism. -/
noncomputable def localNormAtPlace (v : NK.GlobalCFT.Place F) :
    (NK.GlobalCFT.Place.localField K (placeAbove F K v))ˣ →*
      (NK.GlobalCFT.Place.localField F v)ˣ :=
  match v with
  | Sum.inl w =>
      letI : (placeAboveInf F K w).LiesOver w := liesOver_placeAboveInf F K w
      NK.GlobalCFT.Place.localNormInfinite (placeAboveInf F K w) w
  | Sum.inr Q =>
      NK.GlobalCFT.Place.localNormFinite (placeAboveFin F K Q) Q (placeAboveFin_spec F K Q)

theorem localNormAtPlace_spec (v : NK.GlobalCFT.Place F)
    (u : (NK.GlobalCFT.Place.localField K (placeAbove F K v))ˣ) :
    NK.GlobalCFT.Idele.normIdeleFun F K
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (placeAbove F K v) u) v =
      localNormAtPlace F K v u := by
  cases v with
  | inl w =>
      haveI : (placeAboveInf F K w).LiesOver w := liesOver_placeAboveInf F K w
      exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite
        w (placeAboveInf F K w) u
  | inr Q =>
      exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q _ _ u

/-- The finite set of finite places of `F` at which the unit `x` is not a local unit. -/
noncomputable def badPlaces (x : Fˣ) : Finset (NK.GlobalCFT.Place F) :=
  ((NK.GlobalCFT.Idele.finite_setOf_valuation_ne_one x).image
    NK.GlobalCFT.Place.ofFinite).toFinset

theorem mem_badPlaces {x : Fˣ} {Q : HeightOneSpectrum (𝓞 F)} :
    NK.GlobalCFT.Place.ofFinite Q ∈ badPlaces F x ↔ Q.valuation F (x : F) ≠ 1 := by
  rw [badPlaces, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨Q', hQ', h⟩
    rw [NK.GlobalCFT.Place.ofFinite_inj] at h
    subst h
    exact hQ'
  · intro h
    exact ⟨Q, h, rfl⟩

/-- At an infinite place of `F` the value of the principal idèle is a local norm. -/
theorem mem_range_localNormAtPlace_ofInfinite (x : Fˣ) (w : InfinitePlace F)
    (hunr : IsUnramifiedAtInfinitePlaces F K) :
    (NK.GlobalCFT.Idele.principalIdele F x) (Sum.inl w) ∈
      (localNormAtPlace F K (Sum.inl w)).range := by
  haveI : IsUnramifiedAtInfinitePlaces F K := hunr
  haveI : (placeAboveInf F K w).LiesOver w := liesOver_placeAboveInf F K w
  show (NK.GlobalCFT.Idele.principalIdele F x) (Sum.inl w) ∈
    (NK.GlobalCFT.Place.localNormInfinite (placeAboveInf F K w) w).range
  rw [NK.CFTLib.localNormInfinite_range_eq_top_of_isUnramified (K := F) (L := K)
    (v := w) (w := placeAboveInf F K w) (hunr.isUnramified (placeAboveInf F K w))]
  exact Subgroup.mem_top _

/-- At a finite place `Q` at which the inertia degree divides the valuation of `x`, the value of
the principal idèle of `x` is a local norm. -/
theorem mem_range_localNormAtPlace_ofFinite (x : Fˣ) (Q : HeightOneSpectrum (𝓞 F))
    (hfin : differentIdeal (𝓞 F) (𝓞 K) = ⊤)
    (hdiv : (Ideal.inertiaDegIn Q.asIdeal (𝓞 K) : ℤ) ∣ NK.GlobalCFTdeep.expUnit Q x) :
    (NK.GlobalCFT.Idele.principalIdele F x) (Sum.inr Q) ∈
      (localNormAtPlace F K (Sum.inr Q)).range := by
  have hq := placeAboveFin_spec F K Q
  have hf : ((placeAboveFin F K Q).asIdeal.inertiaDeg (𝓞 F) : ℤ) =
      (Ideal.inertiaDegIn Q.asIdeal (𝓞 K) : ℤ) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal (placeAboveFin F K Q) (K ≃ₐ[F] K)]
  have hz : ((placeAboveFin F K Q).asIdeal.inertiaDeg (𝓞 F) : ℤ) ∣
      finVal F Q ((NK.GlobalCFT.Idele.principalIdele F x) (Sum.inr Q)) := by
    rw [finVal_principalIdele (K := K), hf]
    exact hdiv
  obtain ⟨y, hy⟩ := (@NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd
    F K _ _ _ _ _ _ _ hfin Q (placeAboveFin F K Q) hq
    ((NK.GlobalCFT.Idele.principalIdele F x) (Sum.inr Q))).mpr hz
  exact MonoidHom.mem_range.mpr ⟨y, hy⟩

/-- The unit-surjectivity outside the exceptional set. -/
theorem hunit_badPlaces (x : Fˣ) (hfin : differentIdeal (𝓞 F) (𝓞 K) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces F K) :
    ∀ (v : NK.GlobalCFT.Place F), v ∉ badPlaces F x → ∀ a ∈ NK.GlobalCFT.Place.localUnits F v,
      ∃ u ∈ NK.GlobalCFT.Place.localUnits K (placeAbove F K v),
        localNormAtPlace F K v u = a := by
  intro v hv a ha
  cases v with
  | inl w =>
      haveI : IsUnramifiedAtInfinitePlaces F K := hinf
      haveI : (placeAboveInf F K w).LiesOver w := liesOver_placeAboveInf F K w
      have htop : (NK.GlobalCFT.Place.localNormInfinite (placeAboveInf F K w) w).range = ⊤ :=
        NK.CFTLib.localNormInfinite_range_eq_top_of_isUnramified (K := F) (L := K)
          (v := w) (w := placeAboveInf F K w)
          (hinf.isUnramified (placeAboveInf F K w))
      have hmem : a ∈ (NK.GlobalCFT.Place.localNormInfinite
          (placeAboveInf F K w) w).range := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨u, hu⟩ := hmem
      refine ⟨u, Subgroup.mem_top _, ?_⟩
      show NK.GlobalCFT.Place.localNormInfinite (placeAboveInf F K w) w u = a
      exact hu
  | inr Q =>
      have hq := placeAboveFin_spec F K Q
      have hram : (placeAboveFin F K Q).asIdeal.ramificationIdx (𝓞 F) = 1 :=
        NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top hfin (placeAboveFin F K Q)
      obtain ⟨u, hu, hnorm⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q (placeAboveFin F K Q) hq hram a ha
      refine ⟨u, hu, ?_⟩
      show NK.GlobalCFT.Place.localNormFinite (placeAboveFin F K Q) Q hq u = a
      exact hnorm


end Helpers

theorem normPrincipalPreimage_iff_expUnit (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hunr : _root_.CFTLib.IsUnramified F K) (x : Fˣ) :
    x ∈ NK.CFTLib.normPrincipalPreimage F K ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        (Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers K) : ℤ) ∣
          NK.GlobalCFTdeep.expUnit v x := by
  classical
  constructor
  · intro hx Q
    have hmem : NK.GlobalCFT.Idele.principalIdele F x ∈ NK.GlobalCFT.Idele.normImage F K := by
      simpa only [normPrincipalPreimage, Subgroup.mem_comap] using hx
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem
    exact NK.CFTLib.NormPrincipal.dvd_expUnit_of_eq_normIdeleFun Q x y
      (hy (NK.GlobalCFT.Place.ofFinite Q))
  · intro hdiv
    have hmem : NK.GlobalCFT.Idele.principalIdele F x ∈ NK.GlobalCFT.Idele.normImage F K := by
      have hxmem : NK.GlobalCFT.Idele.principalIdele F x ∈ NK.GlobalCFTdeep.constrainedE
          (badPlaces F x) (fun v => (localNormAtPlace F K (v : NK.GlobalCFT.Place F)).range) := by
        rw [NK.GlobalCFTdeep.mem_constrainedE]
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · obtain ⟨v, hv⟩ := v
          cases v with
          | inl w => exact mem_range_localNormAtPlace_ofInfinite F K x w hunr.2
          | inr Q => exact mem_range_localNormAtPlace_ofFinite F K x Q hunr.1 (hdiv Q)
        · cases v with
          | inl w =>
              rw [NK.GlobalCFT.Place.localUnits_ofInfinite]
              exact Subgroup.mem_top _
          | inr Q =>
              rw [← finVal_eq_zero_iff_mem_localUnits, finVal_principalIdele (K := K),
                NK.GlobalCFTdeep.expUnit]
              have h1 : Q.valuation F (x : F) = 1 := by
                by_contra h
                exact hv ((mem_badPlaces F).mpr h)
              rw [h1, WithZero.log_one, neg_zero]
      exact NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage (S := badPlaces F x)
        (A := fun v => (localNormAtPlace F K (v : NK.GlobalCFT.Place F)).range)
        (g := placeAbove F K) (hg := liesOver_placeAbove F K) (Φ := localNormAtPlace F K)
        (hbridge := localNormAtPlace_spec F K) (hA := fun v => le_refl _)
        (hunit := hunit_badPlaces F K x hunr.1 hunr.2) hxmem
    simpa only [normPrincipalPreimage, Subgroup.mem_comap] using hmem

end NK.CFTLib
