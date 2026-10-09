import Mathlib
import Submission.Commons.RingTheory.Valuation.henselianLocalRing_of_unique_extension
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.RingTheory.Polynomial.isRoot_eq_of_sub_mem_maximalIdeal
import Submission.Commons.RingTheory.Valuation.ValuationSubring.isUnit_comap_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise

set_option linter.style.haveILetI false

private theorem eval_sub_mem_of_sub_mem {R : Type*} [CommRing R] (I : Ideal R) (p : Polynomial R)
    {x y : R} (h : x - y ∈ I) : p.eval x - p.eval y ∈ I := by
  have hq : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := Ideal.Quotient.eq.mpr h
  have h2 : Ideal.Quotient.mk I (p.eval x) = Ideal.Quotient.mk I (p.eval y) := by
    rw [← Polynomial.eval₂_at_apply (Ideal.Quotient.mk I) x,
      ← Polynomial.eval₂_at_apply (Ideal.Quotient.mk I) y, hq]
  exact Ideal.Quotient.eq.mp h2

private theorem isUnit_eval_of_sub_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (p : Polynomial R) {x y : R} (h : x - y ∈ IsLocalRing.maximalIdeal R)
    (hu : IsUnit (p.eval y)) : IsUnit (p.eval x) := by
  by_contra hx
  have hmem : p.eval x ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hx)
  have hd : p.eval x - p.eval y ∈ IsLocalRing.maximalIdeal R := eval_sub_mem_of_sub_mem _ p h
  have hmem' : p.eval y ∈ IsLocalRing.maximalIdeal R := by
    have h : p.eval y = p.eval x - (p.eval x - p.eval y) := by ring
    rw [h]
    exact sub_mem hmem hd
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem')) hu

private theorem henselianLocalRing_of_isSepClosed (E : Type*) [Field E] [IsSepClosed E]
    (A : ValuationSubring E) : HenselianLocalRing A := by
  haveI : IsSepClosure E E := IsSepClosure.self_of_isSepClosed E
  refine Commons.RingTheory.Valuation.henselianLocalRing_of_unique_extension A A ?_ ?_
  · rw [Algebra.algebraMap_self]
    ext x
    simp [ValuationSubring.mem_comap]
  · intro W' hW'
    rw [Algebra.algebraMap_self] at hW'
    have h : W'.comap (RingHom.id E) = W' := by
      ext x
      simp [ValuationSubring.mem_comap]
    rwa [h] at hW'

private theorem henselianLocalRing_comap_fixedField_stabilizer_aux {F E : Type*} [Field F] [Field E] [Algebra F E] (A : ValuationSubring E)
    [HenselianLocalRing A] :
    HenselianLocalRing (A.comap (algebraMap (IntermediateField.fixedField (MulAction.stabilizer (E ≃ₐ[F] E) A)) E)) := by
  set G : Subgroup (E ≃ₐ[F] E) := MulAction.stabilizer (E ≃ₐ[F] E) A with hG
  set K : IntermediateField F E := IntermediateField.fixedField G with hK
  let V : ValuationSubring ↥K := A.comap (algebraMap ↥K E)
  have hφmem : ∀ x : V, algebraMap ↥K E (x : ↥K) ∈ A := fun x => (ValuationSubring.mem_comap).mp x.2
  let φ : V →+* A := ((algebraMap ↥K E).comp (algebraMap V ↥K)).codRestrict A hφmem
  have hφ_coe : ∀ x : V, ((φ x : A) : E) = algebraMap ↥K E (x : ↥K) := fun x => rfl
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h : algebraMap ↥K E (x : ↥K) = algebraMap ↥K E (y : ↥K) := by
      rw [← hφ_coe x, ← hφ_coe y, hxy]
    exact Subtype.ext ((algebraMap ↥K E).injective h)
  have hφunit : ∀ x : V, IsUnit (φ x) ↔ IsUnit x := by
    intro x
    rw [show φ x = ⟨algebraMap ↥K E (x : ↥K), hφmem x⟩ from rfl]
    exact (Commons.RingTheory.Valuation.ValuationSubring.isUnit_comap_iff A x).symm
  have hmap_eval : ∀ (p : Polynomial V) (x : V), (p.map φ).eval (φ x) = φ (p.eval x) := by
    intro p x
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply φ x
  constructor
  intro f hf a₀ h1 h2
  have hF0 : (f.map φ).eval (φ a₀) ∈ IsLocalRing.maximalIdeal A := by
    rw [hmap_eval f a₀, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    exact fun hu => h1 ((hφunit (f.eval a₀)).mp hu)
  have hFderiv : IsUnit ((f.map φ).derivative.eval (φ a₀)) := by
    rw [Polynomial.derivative_map, hmap_eval]
    exact h2.map φ
  obtain ⟨b, hbroot, hbsub⟩ :=
    HenselianLocalRing.is_henselian (f.map φ) (hf.map φ) (φ a₀) hF0 hFderiv
  have hbsubnu : ¬ IsUnit (b - φ a₀) :=
    fun h => (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hbsub)) h
  have hfixK : ∀ (x : ↥K), ∀ σ ∈ G, σ (algebraMap ↥K E x) = algebraMap ↥K E x := by
    intro x σ hσ
    have hx : (algebraMap ↥K E x) ∈ IntermediateField.fixedField G := by
      rw [← hK]
      exact x.2
    exact (IntermediateField.mem_fixedField_iff G _).mp hx σ hσ
  have hbK : (b : E) ∈ K := by
    rw [hK, IntermediateField.mem_fixedField_iff]
    intro σ hσG
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) A := hG ▸ hσG
    have hmem : ∀ x : E, x ∈ A ↔ σ x ∈ A :=
      (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A σ).mp hσ
    let σA : A ≃+* A :=
      { toFun := fun x => ⟨σ (x : E), (hmem (x : E)).mp x.2⟩
        invFun := fun x => ⟨σ.symm (x : E),
          (hmem (σ.symm (x : E))).mpr (by rw [σ.apply_symm_apply]; exact x.2)⟩
        left_inv := fun x => by ext; simp
        right_inv := fun x => by ext; simp
        map_mul' := fun x y => by ext; simp
        map_add' := fun x y => by ext; simp }
    have hunitσA : ∀ x : A, IsUnit (σA x) ↔ IsUnit x := by
      intro x
      constructor
      · intro h
        have h' := h.map (σA.symm : A →+* A)
        simpa using h'
      · intro h
        exact h.map (σA : A →+* A)
    have hb0fix : σ (((φ a₀ : A) : E)) = ((φ a₀ : A) : E) := by
      rw [hφ_coe a₀]
      exact hfixK ((a₀ : V) : ↥K) σ hσG
    have hφa0fix : σA (φ a₀) = φ a₀ := Subtype.ext hb0fix
    have hz1 : σA (b - φ a₀) = σA b - φ a₀ := by rw [map_sub, hφa0fix]
    have hsubA : σA b - φ a₀ ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [← hz1]
      exact fun h => hbsubnu ((hunitσA (b - φ a₀)).mp h)
    have hrootσ : (f.map φ).IsRoot (σA b) := by
      have hrootE : ((f.map φ).map (algebraMap A E)).IsRoot (algebraMap A E b) :=
        Polynomial.IsRoot.map (x := b) (p := f.map φ) (f := algebraMap A E) hbroot
      have hcoeff : ∀ i, ((f.map φ).map (algebraMap A E)).coeff i =
          algebraMap ↥K E (((f.coeff i : V)) : ↥K) := by
        intro i
        rw [Polynomial.coeff_map, Polynomial.coeff_map]
        exact hφ_coe (f.coeff i)
      have hfix : ((f.map φ).map (algebraMap A E)).map (σ : E →+* E) =
          ((f.map φ).map (algebraMap A E)) := by
        ext i
        rw [Polynomial.coeff_map, hcoeff i]
        exact hfixK _ σ hσG
      have h1 : ((f.map φ).map (algebraMap A E)).IsRoot (σ (algebraMap A E b)) := by
        have := Polynomial.IsRoot.map (f := (σ : E →+* E)) hrootE
        rwa [hfix] at this
      have h2 : σ (algebraMap A E b) = algebraMap A E (σA b) := rfl
      rw [h2] at h1
      exact Polynomial.IsRoot.of_map h1 (fun x y hxy => Subtype.ext hxy)
    have hunitb : IsUnit ((f.map φ).derivative.eval b) :=
      isUnit_eval_of_sub_mem_maximalIdeal _ hbsub hFderiv
    have hsubA2 : σA b - b ∈ IsLocalRing.maximalIdeal A := by
      have e : σA b - b = (σA b - φ a₀) - (b - φ a₀) := by ring
      rw [e]
      exact sub_mem hsubA hbsub
    have hfin : σA b = b :=
      Commons.RingTheory.Polynomial.isRoot_eq_of_sub_mem_maximalIdeal hrootσ hbroot hsubA2 hunitb
    exact congrArg (fun z : A => (z : E)) hfin
  let ã : V := ⟨⟨(b : E), hbK⟩, by show (b : E) ∈ A; exact b.2⟩
  have hφã : φ ã = b := Subtype.ext rfl
  refine ⟨ã, ?_, ?_⟩
  · have hroot : φ (f.eval ã) = 0 := by
      rw [← hmap_eval f ã, hφã]
      exact hbroot
    exact hφ_inj (by rw [hroot, map_zero])
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hφsub : φ (ã - a₀) = b - φ a₀ := by rw [map_sub, hφã]
    exact hbsubnu (by rw [← hφsub]; exact (hφunit (ã - a₀)).mpr hu)

/-- **The decomposition field of a valuation is henselian.**

Let `E` be a separable closure of `F` and `A` a valuation subring of `E`.  The *decomposition
field* of `A` is the fixed field `K` of the stabiliser `G` of `A` in `Gal(E/F)`, and the
restriction `A ∩ K` of `A` to `K` is a henselian local ring.

Proof sketch: `A` is henselian because `E` is separably closed (a separably closed field is its
own separable closure, so there is no extension to extend to).  Given a Hensel datum over `V =
A ∩ K`, Hensel's lemma in `A` produces a root `b` of the reduced polynomial.  Every `σ ∈ G`
fixes `K` pointwise — in particular the coefficients of the polynomial — and preserves `A` and
its maximal ideal, so `σ b` is a root congruent to `b` modulo the maximal ideal; uniqueness of
the Hensel root in a local ring gives `σ b = b`.  Hence `b ∈ E^G = K`, so `b ∈ A ∩ K = V` and
the Hensel datum is satisfied in `V`. -/
theorem henselianLocalRing_comap_decompositionField {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsSepClosure F E] (A : ValuationSubring E) :
    HenselianLocalRing (A.comap (algebraMap (IntermediateField.fixedField (MulAction.stabilizer (E ≃ₐ[F] E) A)) E)) := by
  haveI : IsSepClosed E := IsSepClosure.sep_closed F
  haveI : HenselianLocalRing A := henselianLocalRing_of_isSepClosed E A
  exact henselianLocalRing_comap_fixedField_stabilizer_aux A

end Commons.RingTheory.Valuation
