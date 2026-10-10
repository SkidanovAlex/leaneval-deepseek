import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage_of_kummerData
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_eq_one_of_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

variable {K : Type} [Field K] [NumberField K]

/-- Points of an idèle power: `𝕀 K` carries the pointwise group structure, so powers are
computed componentwise. -/
@[simp] theorem Idele.pow_apply_eq (x : Idele K) (p : ℕ) (v : Place K) :
    (x ^ p) v = (x v) ^ p := rfl

/-- **Milne 6.7, the easy inclusion.**  The `p`-th powers of the `(S ∪ T)`-units, viewed as
principal idèles, lie in `Kˣ ∩ E`: a `p`-th power of an `S ∪ T`-unit is a `p`-th power at every
place of `S` (indeed at every place), and it is a local unit at every place outside `S ∪ T`. -/
theorem tUnitsPowIdele_le_principal_inf_kummerE (p : ℕ) (S : Finset (Place K))
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    tUnitsPowIdele (K := K) p
        ((S : Set (Place K)) ∪ (((T.map (placeOfFiniteEmb K)) : Finset (Place K)) : Set (Place K)))
      ≤ Idele.principalSubgroup K ⊓ kummerE (K := K) p S (T.map (placeOfFiniteEmb K)) := by
  intro x hx
  simp only [tUnitsPowIdele] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(powMonoidHom p) u, rfl⟩, ?_⟩
  · change Idele.principalIdele K ((powMonoidHom p) u) ∈
        kummerE (K := K) p S (T.map (placeOfFiniteEmb K))
    rw [mem_kummerE]
    refine ⟨fun v _ => ?_, fun v hvS hvT => ?_⟩
    · refine ⟨Idele.principalIdele K u v, ?_⟩
      simp only [powMonoidHom_apply, Idele.principalIdele_apply, map_pow, Idele.pow_apply_eq]
    · have hv : v ∉ (S : Set (Place K)) ∪
          (((T.map (placeOfFiniteEmb K)) : Finset (Place K)) : Set (Place K)) := by
        simp only [Set.mem_union, not_or]
        exact ⟨hvS, hvT⟩
      have hu' := (NK.GlobalCFTdeep.mem_TUnits.mp hu) v hv
      rw [show Idele.principalIdele K ((powMonoidHom p) u) v =
          (Idele.principalIdele K u v) ^ p by
        simp only [powMonoidHom_apply, Idele.principalIdele_apply, map_pow,
          Idele.pow_apply_eq]]
      exact Subgroup.pow_mem (Place.localUnits K v) hu' p

/-- A `p`-th root of a local unit is a local unit. -/
theorem mem_localUnits_of_pow_mem_localUnits_aux {v : Place K} {p : ℕ} (hp : p ≠ 0)
    {y : (Place.localField K v)ˣ} (h : y ^ p ∈ Place.localUnits K v) :
    y ∈ Place.localUnits K v := by
  cases v with
  | inl w => exact Place.mem_localUnits_ofInfinite
  | inr q =>
    rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h ⊢
    have h' : (Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((y : (q.adicCompletion K)ˣ)) : q.adicCompletion K)) ^ p = 1 := by
      rw [← map_pow]
      simpa only [Units.val_pow_eq_pow_val] using h
    refine pow_left_injective (M := WithZero (Multiplicative ℤ)) hp ?_
    simpa using h'

/-- **Milne 6.7, the hard inclusion** (assembled here from the delegated local norm
computation and Milne's 4.5). -/
theorem principal_inf_kummerE_le_tUnitsPow_assembly {K : Type} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → Place.ofFinite q ∈ S)
    (hSgen : (⊤ : Subgroup (Idele K)) =
      Idele.principalSubgroup K ⊔ TIdeles (S : Set (Place K)))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hTdisj : ∀ q ∈ T, Place.ofFinite q ∉ S)
    (hsurj : ∀ x : Idele K, x ∈ TIdeles (S : Set (Place K)) →
      ∃ u : TUnits (S : Set (Place K)),
        ∀ q ∈ T, ∃ c : (q.adicCompletionIntegers K)ˣ,
          x (Place.ofFinite q) *
            (Idele.principalIdele K (u : Kˣ) (Place.ofFinite q))⁻¹
            = ((c : q.adicCompletionIntegers K) : q.adicCompletion K) ^ p) :
    Idele.principalSubgroup K ⊓ kummerE (K := K) p S (T.map (placeOfFiniteEmb K))
      ≤ tUnitsPowIdele (K := K) p
          ((S : Set (Place K)) ∪
            ((T.map (placeOfFiniteEmb K) : Finset (Place K)) : Set (Place K))) := by
  classical
  set T' : Finset (Place K) := T.map (placeOfFiniteEmb K) with hT'def
  set Tset : Set (Place K) := (S : Set (Place K)) ∪ (T' : Set (Place K)) with hTsetdef
  intro x hx
  obtain ⟨hxP, hxE⟩ := hx
  obtain ⟨b, hb⟩ := Idele.mem_principalSubgroup.mp hxP
  change x ∈ kummerE (K := K) p S T' at hxE
  rw [mem_kummerE] at hxE
  obtain ⟨hbSpow, hbSunit⟩ := hxE
  have hbS : ∀ v ∈ S, Idele.principalIdele K b v ∈ localPow (K := K) p v := by
    intro v hv
    rw [hb]
    exact hbSpow v hv
  have hbSu : ∀ v : Place K, v ∉ S → v ∉ T' →
      Idele.principalIdele K b v ∈ Place.localUnits K v := by
    intro v hvS hvT
    rw [hb]
    exact hbSunit v hvS (by rwa [hT'def] at hvT)
  by_cases hbpow : b ∈ NK.LocalAnabelian.powSubgroup p K
  · -- `b` is a global `p`-th power
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hbpow
    rw [powMonoidHom_apply] at hu
    have huT : u ∈ TUnits Tset := by
      rw [NK.GlobalCFTdeep.mem_TUnits]
      intro w hw
      have hbw : Idele.principalIdele K b w ∈ Place.localUnits K w := by
        refine hbSu w ?_ ?_
        · intro hwS
          exact hw (by rw [hTsetdef]; exact Set.mem_union_left _ hwS)
        · intro hwT
          exact hw (by rw [hTsetdef]; exact Set.mem_union_right _ hwT)
      have hpow : (Idele.principalIdele K u) ^ p = Idele.principalIdele K b := by
        rw [← map_pow, hu]
      have hpow_w : (Idele.principalIdele K u w) ^ p = Idele.principalIdele K b w := by
        rw [← KummerCase.Idele.pow_apply_eq, hpow]
      rw [← hpow_w] at hbw
      exact mem_localUnits_of_pow_mem_localUnits_aux hp.ne_zero hbw
    refine Subgroup.mem_map.mpr ⟨(powMonoidHom p) u, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨u, huT, rfl⟩
    · rw [← hb, ← hu, powMonoidHom_apply]
  · -- `b` is not a global `p`-th power: Milne 6.10 applies and gives a contradiction
    let Ω := AlgebraicClosure K
    haveI hsep : IsSepClosure K Ω := inferInstance
    haveI hfd : FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) :=
      NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) hp hζ b
    haveI hnf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := Ω)
        (NK.LocalAnabelian.kummerField (K' := Ω) p b)
    haveI hgal : IsGalois K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) :=
      NK.GlobalCFTdeep.SecondInequality.isGalois_kummerField (K' := Ω) hp hζ b
    have hfr : Module.finrank K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) = p :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p hp hζ b hbpow).2
    have hcard : Nat.card (↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) ≃ₐ[K]
        ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) = p := by
      rw [IsGalois.card_aut_eq_finrank K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
      exact hfr
    haveI : Fact p.Prime := ⟨hp⟩
    haveI hcyc : IsCyclic (↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) ≃ₐ[K]
        ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) :=
      isCyclic_of_card_dvd_prime (p := p) (hcard.symm ▸ dvd_rfl)
    have hdisj : Disjoint S T' := by
      refine Finset.disjoint_left.mpr fun v hvS hvT => ?_
      rw [hT'def] at hvT
      obtain ⟨q, hqT, hq⟩ := Finset.mem_map.mp hvT
      exact hTdisj q hqT (by rwa [← hq] at hvS)
    have hD : kummerE (K := K) p T' S ≤
        Idele.normImage K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) :=
      kummerE_le_normImage_of_kummerData (Ω := Ω) hp hζ b hcard S T' hdisj hSinf
        (fun q hq => Or.inl (hSp q hq)) (fun v hv => hbS v hv) hbSu
    have htop : Idele.principalSubgroup K ⊔ kummerE (K := K) p T' S = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hxsup : x ∈ Idele.principalSubgroup K ⊔ TIdeles (S : Set (Place K)) := by
        rw [← hSgen]
        exact Subgroup.mem_top x
      obtain ⟨a₁, ha₁, y, hy, hxy⟩ := Subgroup.mem_sup.mp hxsup
      obtain ⟨u, hu⟩ := hsurj y hy
      refine Subgroup.mem_sup.mpr
        ⟨a₁ * Idele.principalIdele K (u : Kˣ), ?_,
         y * (Idele.principalIdele K (u : Kˣ))⁻¹, ?_, ?_⟩
      · exact Subgroup.mul_mem _ ha₁ (MonoidHom.mem_range.mpr ⟨u, rfl⟩)
      · rw [mem_kummerE]
        refine ⟨fun v hv => ?_, fun v hvT' hvS' => ?_⟩
        · rw [hT'def] at hv
          obtain ⟨q, hqT, hq⟩ := Finset.mem_map.mp hv
          obtain ⟨c, hc⟩ := hu q hqT
          rw [← hq]
          simp only [placeOfFiniteEmb_apply]
          refine ⟨Units.map (↑(algebraMap (q.adicCompletionIntegers K) (q.adicCompletion K)) :
            (q.adicCompletionIntegers K) →* (q.adicCompletion K)) c, ?_⟩
          rw [Idele.mul_apply, Idele.inv_apply]
          apply Units.ext
          simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.coe_map,
            Units.val_inv_eq_inv_val]
          exact hc.symm
        · rw [Idele.mul_apply, Idele.inv_apply]
          refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ?_)
          · exact (NK.GlobalCFTdeep.mem_TIdeles.mp hy) v (by simpa using hvS')
          · exact (NK.GlobalCFTdeep.mem_TUnits.mp u.2) v (by simpa using hvS')
      · rw [← hxy]
        simp only [mul_assoc]
        congr 1
        rw [mul_comm y, ← mul_assoc, mul_inv_cancel, one_mul]
    have h1 : Module.finrank K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) = 1 :=
      NK.GlobalCFTdeep.SecondInequality.finrank_eq_one_of_le_normImage (K := K)
        (E := ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b))
        (kummerE (K := K) p T' S) hD htop
    exact absurd (hfr ▸ h1) hp.ne_one


theorem principal_inf_kummerE_eq_tUnitsPow {K : Type} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (hSgen : (⊤ : Subgroup (NK.GlobalCFT.Idele K)) =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K)))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hTdisj : ∀ q ∈ T, NK.GlobalCFT.Place.ofFinite q ∉ S)
    (hsurj : ∀ x : NK.GlobalCFT.Idele K, x ∈ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K)) →
      ∃ u : NK.GlobalCFTdeep.TUnits (S : Set (NK.GlobalCFT.Place K)),
        ∀ q ∈ T, ∃ c : (q.adicCompletionIntegers K)ˣ,
          x (NK.GlobalCFT.Place.ofFinite q) *
            (NK.GlobalCFT.Idele.principalIdele K (u : Kˣ) (NK.GlobalCFT.Place.ofFinite q))⁻¹
            = ((c : q.adicCompletionIntegers K) : q.adicCompletion K) ^ p) :
    NK.GlobalCFT.Idele.principalSubgroup K ⊓
        KummerCase.kummerE (K := K) p S (T.map (KummerCase.placeOfFiniteEmb K))
      = KummerCase.tUnitsPowIdele (K := K) p
          ((S : Set (NK.GlobalCFT.Place K)) ∪
            ((T.map (KummerCase.placeOfFiniteEmb K) : Finset (NK.GlobalCFT.Place K)) : Set (NK.GlobalCFT.Place K))) := by
  refine le_antisymm ?_ (tUnitsPowIdele_le_principal_inf_kummerE p S T)
  exact principal_inf_kummerE_le_tUnitsPow_assembly hp hζ S hSinf hSp hSgen T hTdisj hsurj

end NK.GlobalCFTdeep.SecondInequality.KummerCase
