import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_add_eq_one_of_comap_eq_ne

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

open ValuationSubring

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-! ## Elementary transfer lemmas for the action of `Gal(L/F)` on `ValuationSubring L` -/

/-- **The norm formula for the action on a valuation subring.** -/
theorem norm_valuation_eq_prod_aut (C : ValuationSubring L) (x : L) :
    C.valuation (algebraMap F L (Algebra.norm F x)) = ∏ σ : L ≃ₐ[F] L, C.valuation (σ x) := by
  rw [Algebra.norm_eq_prod_automorphisms F x, map_prod]

/-- The comap along `algebraMap F L` is invariant under conjugation. -/
private lemma comap_smul_eq (P : ValuationSubring L) (σ : L ≃ₐ[F] L) :
    (σ • P).comap (algebraMap F L) = P.comap (algebraMap F L) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    show σ⁻¹ • (algebraMap F L x) = σ⁻¹ (algebraMap F L x) from rfl,
    (σ⁻¹).commutes x]

private lemma val_eq_one_iff' (A : ValuationSubring L) (y : L) :
    A.valuation y = 1 ↔ A.valuation y ≤ 1 ∧ ¬ A.valuation y < 1 := by
  refine ⟨fun h => by rw [h]; exact ⟨le_rfl, lt_irrefl 1⟩,
    fun ⟨h1, h2⟩ => le_antisymm h1 (le_of_not_gt h2)⟩

/-- Conjugation transports the nonunits. -/
private lemma mem_nonunits_smul_iff (P : ValuationSubring L) (σ : L ≃ₐ[F] L) (y : L) :
    σ y ∈ P.nonunits ↔ y ∈ (σ⁻¹ • P).nonunits := by
  have hmem : ∀ z : L, (z ∈ σ⁻¹ • P) ↔ σ z ∈ P :=
    fun z => (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ⁻¹) (S := P))
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  constructor
  · rintro (h | h)
    · left; exact σ.injective (by rw [h, map_zero])
    · right
      intro hy
      apply h
      simpa [map_inv₀] using (hmem (y⁻¹)).mp hy
  · rintro (h | h)
    · left; rw [h, map_zero]
    · right
      intro hy
      apply h
      exact (hmem (y⁻¹)).mpr (by simpa [map_inv₀] using hy)

/-- **Transfer of `valuation = 1` across conjugation.** -/
private lemma val_smul_eq_one (P : ValuationSubring L) (σ : L ≃ₐ[F] L) (y : L) :
    P.valuation (σ y) = 1 ↔ (σ⁻¹ • P).valuation y = 1 := by
  have hmem : σ y ∈ P ↔ y ∈ σ⁻¹ • P :=
    (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ⁻¹) (S := P)).symm
  rw [val_eq_one_iff', val_eq_one_iff', ValuationSubring.valuation_le_one_iff,
    ValuationSubring.valuation_le_one_iff, ← ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.mem_nonunits_iff, hmem, mem_nonunits_smul_iff]

/-- **Transfer of `valuation < 1` across conjugation.** -/
private lemma val_smul_lt_one (P : ValuationSubring L) (σ : L ≃ₐ[F] L) (y : L) :
    P.valuation (σ y) < 1 ↔ (σ⁻¹ • P).valuation y < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    mem_nonunits_smul_iff]

/-- **Transfer of `valuation = 1` along the base change `F → L`.** -/
private lemma val_comap_eq_one (P : ValuationSubring L) (y : F) :
    (P.comap (algebraMap F L)).valuation y = 1 ↔ P.valuation (algebraMap F L y) = 1 := by
  have hlt : (P.comap (algebraMap F L)).valuation y < 1 ↔ P.valuation (algebraMap F L y) < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff]
    simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
    rw [map_eq_zero_iff (algebraMap F L) (algebraMap F L).injective]
  rw [val_eq_one_iff', val_eq_one_iff', ValuationSubring.valuation_le_one_iff,
    ValuationSubring.valuation_le_one_iff, hlt, ValuationSubring.mem_comap]

/-! ## The ideal of the integral closure cut out by the maximal ideal of a prolongation -/

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

private lemma mem_of_isIntegral_of_le {L' : Type*} [Field L'] (S : Subring L')
    (W : ValuationSubring L') (hSW : S ≤ W.toSubring) {b : L'} (hb : IsIntegral ↥S b) : b ∈ W := by
  haveI : IsIntegrallyClosedIn ↥W.toSubring L' :=
    Subring.isIntegrallyClosedIn_iff.mpr
      (fun _ hz => LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz)
  have hle : (integralClosure ↥S L').toSubring ≤ W.toSubring :=
    (Subring.integralClosure_subring_le_iff (S := S) (T := W.toSubring)).mpr hSW
  exact hle ((mem_integralClosure_iff (R := ↥S) (A := L')).mpr hb)

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

private lemma mem_integralClosure_of_comap_eq (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) {x : L} (hx : x ∈ integralClosure O L) : x ∈ W := by
  rw [mem_integralClosure_iff (R := O) (A := L)] at hx
  exact mem_of_isIntegral_of_le _ W (image_le O W hW) ((isIntegral_image_iff O x).mp hx)

/-- The canonical ring hom from the integral closure of `O` in `L` to `W`. -/
private noncomputable def toC (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : ↥(integralClosure O L) →+* ↥W where
  toFun x := ⟨(x : L), mem_integralClosure_of_comap_eq O W hW x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intro a b; ext; rfl
  map_zero' := by ext; rfl
  map_add' := by intro a b; ext; rfl

/-- The ideal of the integral closure cut out by the maximal ideal of `W`. -/
private noncomputable def pId (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) : Ideal ↥(integralClosure O L) :=
  Ideal.comap (toC O W hW) (IsLocalRing.maximalIdeal ↥W)

private lemma mem_pId_iff (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) (x : ↥(integralClosure O L)) :
    x ∈ pId O W hW ↔ W.valuation (x : L) < 1 := by
  rw [pId, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

/-- Distinct prolongations of the same valuation ring have comaximal primes in the integral
closure. -/
private lemma isCoprime_pId (O : ValuationSubring F) (C C' : ValuationSubring L)
    (hC : C.comap (algebraMap F L) = O) (hC' : C'.comap (algebraMap F L) = O) (hne : C ≠ C') :
    IsCoprime (pId O C hC) (pId O C' hC') := by
  obtain ⟨x, y, hx, hy, hix, hiy, hxy⟩ :=
    exists_add_eq_one_of_comap_eq_ne O C C' hC hC' hne
  have hxR : x ∈ integralClosure O L := (mem_integralClosure_iff (R := O) (A := L)).mpr hix
  have hyR : y ∈ integralClosure O L := (mem_integralClosure_iff (R := O) (A := L)).mpr hiy
  refine Ideal.isCoprime_iff_exists.mpr ⟨⟨x, hxR⟩, ?_, ⟨y, hyR⟩, ?_, ?_⟩
  · rw [mem_pId_iff O C hC ⟨x, hxR⟩]; simpa using hx
  · rw [mem_pId_iff O C' hC' ⟨y, hyR⟩]; simpa using hy
  · ext; simpa using hxy

/-- A product of finitely many elements `< 1` of a linearly ordered commutative monoid with zero
is `< 1`. -/
private lemma finset_prod_lt_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → Γ) (h : ∀ i ∈ s, f i < 1) :
    ∏ i ∈ s, f i < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      rcases t.eq_empty_or_nonempty with rfl | ht
      · simpa using h a (Finset.mem_insert_self a ∅)
      · have h1 : f a < 1 := h a (Finset.mem_insert_self a t)
        have h2 : ∏ i ∈ t, f i < 1 := ih ht (fun i hi => h i (Finset.mem_insert_of_mem hi))
        calc f a * ∏ i ∈ t, f i ≤ f a * 1 :=
              mul_le_mul_right (le_of_lt h2) (f a)
          _ = f a := mul_one (f a)
          _ < 1 := h1

/-! ## The main theorem -/

/-- **Transitivity of the Galois action on the extensions of a valuation** (finite Galois case).

Let `L/F` be a finite Galois extension and let `P`, `Q` be valuation subrings of `L` with the same
trace on `F`.  Then `P` and `Q` are conjugate under `Gal(L/F)`.

The proof is by contradiction: if `Q` is not conjugate to `P`, the ideals of the integral closure
cut out by the maximal ideals of the conjugates of `P` and `Q` are pairwise comaximal, so by the
Chinese remainder theorem there is `β` in the integral closure with `β ≡ 1` at every conjugate of
`P` and `β ∈ 𝔪` at every conjugate of `Q`.  The norm identity
`v(Algebra.norm F β) = ∏_σ v(σ β)` then computes the value of the norm as `1` using the
`P`-conjugates and as `< 1` using the `Q`-conjugates: a contradiction. -/
theorem exists_smul_eq_of_comap_eq_of_finite {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (P Q : ValuationSubring L)
    (h : P.comap (algebraMap F L) = Q.comap (algebraMap F L)) :
    ∃ σ : L ≃ₐ[F] L, σ • P = Q := by
  classical
  by_contra hcon
  have hcon' : ∀ σ : L ≃ₐ[F] L, σ • P ≠ Q := fun σ hσ => hcon ⟨σ, hσ⟩
  let O : ValuationSubring F := P.comap (algebraMap F L)
  have hP : P.comap (algebraMap F L) = O := rfl
  have hQ : Q.comap (algebraMap F L) = O := h.symm
  let SP : Finset (ValuationSubring L) := Finset.univ.image (fun σ : L ≃ₐ[F] L => σ • P)
  let SQ : Finset (ValuationSubring L) := Finset.univ.image (fun σ : L ≃ₐ[F] L => σ • Q)
  let S : Finset (ValuationSubring L) := SP ∪ SQ
  have hcomap : ∀ C : ↥S, C.1.comap (algebraMap F L) = O := by
    intro C
    rcases Finset.mem_union.mp C.2 with hC | hC
    · obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hC
      rw [← hσ, comap_smul_eq P σ, hP]
    · obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hC
      rw [← hσ, comap_smul_eq Q σ, hQ]
  have hdisj : ∀ σ τ : L ≃ₐ[F] L, σ • P ≠ τ • Q := by
    intro σ τ hστ
    exact hcon' (τ⁻¹ * σ) (by rw [mul_smul, hστ, inv_smul_smul])
  have hcop : Pairwise (fun C C' : ↥S => IsCoprime (pId O C.1 (hcomap C)) (pId O C'.1 (hcomap C'))) := by
    intro C C' hne
    exact isCoprime_pId O C.1 C'.1 (hcomap C) (hcomap C') (fun hcc => hne (Subtype.ext hcc))
  let a : ↥S → ↥(integralClosure O L) := fun C => if C.1 ∈ SP then 1 else 0
  have haP : ∀ C : ↥S, C.1 ∈ SP → a C = 1 := by
    intro C hC
    show (if C.1 ∈ SP then (1 : ↥(integralClosure O L)) else 0) = 1
    rw [if_pos hC]
  have haQ : ∀ C : ↥S, C.1 ∈ SQ → a C = 0 := by
    intro C hC
    have hnot : C.1 ∉ SP := by
      intro hc
      obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hc
      obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp hC
      exact hdisj σ τ (by rw [hσ, hτ])
    show (if C.1 ∈ SP then (1 : ↥(integralClosure O L)) else 0) = 0
    rw [if_neg hnot]
  obtain ⟨β, hβ⟩ := Ideal.exists_forall_sub_mem_ideal (R := ↥(integralClosure O L))
    (I := fun C : ↥S => pId O C.1 (hcomap C)) hcop a
  have hcondP : ∀ σ : L ≃ₐ[F] L, (σ⁻¹ • P).valuation (β : L) = 1 := by
    intro σ
    have hmem : (σ⁻¹ • P) ∈ SP := Finset.mem_image.mpr ⟨σ⁻¹, Finset.mem_univ _, rfl⟩
    let C₁ : ↥S := ⟨σ⁻¹ • P, Finset.mem_union_left SQ hmem⟩
    have hb : β - a C₁ ∈ pId O C₁.1 (hcomap C₁) := hβ C₁
    have ha : a C₁ = 1 := haP C₁ hmem
    rw [ha] at hb
    have hlt : (σ⁻¹ • P).valuation ((β : L) - 1) < 1 := by
      have h2 := (mem_pId_iff O (σ⁻¹ • P) (hcomap C₁) (β - 1)).mp hb
      simpa using h2
    have hkey : (σ⁻¹ • P).valuation ((1 : L) + ((β : L) - 1)) =
        (σ⁻¹ • P).valuation (1 : L) :=
      Valuation.map_add_eq_of_lt_left ((σ⁻¹ • P).valuation) (by
        rw [Valuation.map_one]; exact hlt)
    have hβ1 : (σ⁻¹ • P).valuation (β : L) = 1 := by
      have hβeq : (1 : L) + ((β : L) - 1) = (β : L) := by ring
      rw [hβeq, Valuation.map_one] at hkey
      exact hkey
    exact hβ1
  have hcondQ : ∀ σ : L ≃ₐ[F] L, (σ⁻¹ • Q).valuation (β : L) < 1 := by
    intro σ
    have hmem : (σ⁻¹ • Q) ∈ SQ := Finset.mem_image.mpr ⟨σ⁻¹, Finset.mem_univ _, rfl⟩
    let C₁ : ↥S := ⟨σ⁻¹ • Q, Finset.mem_union_right SP hmem⟩
    have hb : β - a C₁ ∈ pId O C₁.1 (hcomap C₁) := hβ C₁
    have ha : a C₁ = 0 := haQ C₁ hmem
    rw [ha, sub_zero] at hb
    have h2 := (mem_pId_iff O (σ⁻¹ • Q) (hcomap C₁) β).mp hb
    simpa using h2
  have hP1 : P.valuation (algebraMap F L (Algebra.norm F (β : L))) = 1 := by
    rw [norm_valuation_eq_prod_aut]
    refine Finset.prod_eq_one fun σ _ => ?_
    rw [val_smul_eq_one]
    exact hcondP σ
  have hQ1 : Q.valuation (algebraMap F L (Algebra.norm F (β : L))) < 1 := by
    rw [norm_valuation_eq_prod_aut]
    refine finset_prod_lt_one Finset.univ Finset.univ_nonempty _ (fun σ _ => ?_)
    rw [val_smul_lt_one]
    exact hcondQ σ
  have hN : Q.valuation (algebraMap F L (Algebra.norm F (β : L))) = 1 := by
    rw [← val_comap_eq_one (P := Q), hQ.trans hP.symm, val_comap_eq_one (P := P)]
    exact hP1
  exact absurd hN (ne_of_lt hQ1)

end Commons.RingTheory.Valuation
