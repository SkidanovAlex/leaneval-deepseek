import Mathlib
import Submission.Commons.RingTheory.Valuation.eq_of_comap_eq_of_center_eq
import Submission.Commons.RingTheory.Valuation.hasExtension_comap_of_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

open ValuationSubring

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]

/-- Integrality over `O` is the same as integrality over the image of `O` in `L`. -/
private lemma isIntegral_image_iff (O : ValuationSubring F) (x : L) :
    IsIntegral O x ↔ IsIntegral (Subring.map (algebraMap F L) O.toSubring) x := by
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  let φ : ↥O.toSubring ≃+* ↥(Subring.map (algebraMap F L) O.toSubring) :=
    Subring.equivMapOfInjective O.toSubring (algebraMap F L) hinj
  have h : (algebraMap ↥(Subring.map (algebraMap F L) O.toSubring) L).comp φ.toRingHom
      = algebraMap ↥O.toSubring L := by
    ext o
    rfl
  exact RingEquiv.isIntegral_iff φ h x

/-- An element integral over a subring `S` of a valuation subring `W` lies in `W`. -/
private lemma mem_of_isIntegral_of_le {L : Type*} [Field L] (S : Subring L)
    (W : ValuationSubring L) (hSW : S ≤ W.toSubring) {b : L} (hb : IsIntegral ↥S b) : b ∈ W := by
  haveI : IsIntegrallyClosedIn ↥W.toSubring L :=
    Subring.isIntegrallyClosedIn_iff.mpr
      (fun _ hz => LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz)
  have hle : (integralClosure ↥S L).toSubring ≤ W.toSubring :=
    (Subring.integralClosure_subring_le_iff (S := S) (T := W.toSubring)).mpr hSW
  exact hle ((mem_integralClosure_iff (R := ↥S) (A := L)).mpr hb)

/-- The image of `O` in `L` is contained in any valuation subring whose comap is `O`. -/
private lemma image_le (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) :
    Subring.map (algebraMap F L) O.toSubring ≤ W.toSubring := by
  intro z hz
  rw [Subring.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [ValuationSubring.mem_toSubring]
  have hy' : y ∈ O := (ValuationSubring.mem_toSubring O y).mp hy
  have : y ∈ W.comap (algebraMap F L) := by rw [hW]; exact hy'
  rwa [ValuationSubring.mem_comap] at this

/-- Every element integral over `O` lies in a valuation subring whose comap is `O`. -/
private lemma mem_integralClosure_of_comap_eq (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) {x : L} (hx : x ∈ integralClosure O L) : x ∈ W := by
  rw [mem_integralClosure_iff (R := O) (A := L)] at hx
  exact mem_of_isIntegral_of_le _ W (image_le O W hW) ((isIntegral_image_iff O x).mp hx)

/-- The canonical ring hom from the integral closure of `O` in `L` to `W`. -/
private noncomputable def toW (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : ↥(integralClosure O L) →+* ↥W where
  toFun x := ⟨(x : L), mem_integralClosure_of_comap_eq O W hW x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intro a b; ext; rfl
  map_zero' := by ext; rfl
  map_add' := by intro a b; ext; rfl

/-- The inclusion `O → W`. -/
private noncomputable def toOW (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : O →+* ↥W where
  toFun o := ⟨algebraMap F L (o : F), by
    have : (o : F) ∈ W.comap (algebraMap F L) := by rw [hW]; exact o.2
    rwa [ValuationSubring.mem_comap] at this⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp
  map_zero' := by ext; simp
  map_add' := by intro a b; ext; simp

/-- The ideal of the integral closure cut out by the maximal ideal of `W`. -/
private noncomputable def P (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : Ideal ↥(integralClosure O L) :=
  Ideal.comap (toW O W hW) (IsLocalRing.maximalIdeal ↥W)

private lemma mem_P_iff (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) (x : L) (hx : x ∈ integralClosure O L) :
    (⟨x, hx⟩ : ↥(integralClosure O L)) ∈ P O W hW ↔ W.valuation x < 1 := by
  rw [P, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

private lemma comap_toOW_eq (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) :
    Ideal.comap (toOW O W hW) (IsLocalRing.maximalIdeal ↥W) = IsLocalRing.maximalIdeal O := by
  haveI hExt : O.valuation.HasExtension W.valuation := hasExtension_comap_of_comap_eq W O hW
  ext o
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.valuation_lt_one_iff]
  exact Valuation.HasExtension.val_map_lt_one_iff O.valuation W.valuation (o : F)

private lemma comap_base_eq (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) :
    Ideal.comap (algebraMap O ↥(integralClosure O L)) (P O W hW) = IsLocalRing.maximalIdeal O := by
  have hcomp : (toW O W hW).comp (algebraMap O ↥(integralClosure O L)) = toOW O W hW := by
    ext o; rfl
  rw [P, Ideal.comap_comap, hcomp]
  exact comap_toOW_eq O W hW

/-- The ideal `P O W hW` is maximal. -/
private lemma isMaximal_P (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : (P O W hW).IsMaximal := by
  haveI hprime : (P O W hW).IsPrime :=
    Ideal.comap_isPrime (toW O W hW) (IsLocalRing.maximalIdeal ↥W)
  have hbase := comap_base_eq O W hW
  have hfield : IsField (O ⧸ Ideal.comap (algebraMap O ↥(integralClosure O L)) (P O W hW)) := by
    rw [hbase]
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  haveI : Algebra.IsIntegral (O ⧸ Ideal.comap (algebraMap O ↥(integralClosure O L)) (P O W hW))
      (↥(integralClosure O L) ⧸ P O W hW) := inferInstance
  exact Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField'
      (R := O ⧸ Ideal.comap (algebraMap O ↥(integralClosure O L)) (P O W hW))
      (S := ↥(integralClosure O L) ⧸ P O W hW) hfield)

theorem exists_add_eq_one_of_comap_eq_ne {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (O : ValuationSubring F) (C C' : ValuationSubring L)
    (hC : C.comap (algebraMap F L) = O) (hC' : C'.comap (algebraMap F L) = O) (hne : C ≠ C') :
    ∃ x y : L, C.valuation x < 1 ∧ C'.valuation y < 1 ∧ IsIntegral O x ∧ IsIntegral O y ∧
      x + y = 1 := by
  have hmaxC : (P O C hC).IsMaximal := isMaximal_P O C hC
  have hmaxC' : (P O C' hC').IsMaximal := isMaximal_P O C' hC'
  have hneP : P O C hC ≠ P O C' hC' := by
    intro heq
    apply hne
    refine eq_of_comap_eq_of_center_eq C C' (by rw [hC, hC']) ?_
    intro x hxA
    have hxA' : IsIntegral (Subring.map (algebraMap F L) O.toSubring) x := by
      have h := hxA
      rw [hC] at h
      exact h
    have hxO : IsIntegral O x := (isIntegral_image_iff O x).mpr hxA'
    have hxD : x ∈ integralClosure O L := (mem_integralClosure_iff (R := O) (A := L)).mpr hxO
    have h1 : (⟨x, hxD⟩ : ↥(integralClosure O L)) ∈ P O C hC ↔
        (⟨x, hxD⟩ : ↥(integralClosure O L)) ∈ P O C' hC' := by rw [heq]
    rw [mem_P_iff O C hC x hxD, mem_P_iff O C' hC' x hxD] at h1
    exact h1
  have hcm : P O C hC ⊔ P O C' hC' = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne hmaxC hmaxC' hneP
  obtain ⟨a, haP, b, hbP, hab⟩ := Submodule.mem_sup.mp
    (show (1 : ↥(integralClosure O L)) ∈ P O C hC ⊔ P O C' hC' by rw [hcm]; trivial)
  refine ⟨(a : L), (b : L), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mem_P_iff O C hC (a : L) a.2]; exact haP
  · rw [← mem_P_iff O C' hC' (b : L) b.2]; exact hbP
  · exact (mem_integralClosure_iff (R := O) (A := L)).mp a.2
  · exact (mem_integralClosure_iff (R := O) (A := L)).mp b.2
  · have h := congrArg (fun z : ↥(integralClosure O L) => (z : L)) hab
    simpa using h

end Commons.RingTheory.Valuation
