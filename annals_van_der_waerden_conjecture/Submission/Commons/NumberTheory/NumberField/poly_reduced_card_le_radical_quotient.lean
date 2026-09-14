import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.PicardGroup

open scoped BigOperators NumberField
open Polynomial

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.NumberField

noncomputable section

/-! # Cardinality of the reduced quotient vs. the radical quotient

`poly_reduced_card_le_radical_quotient`: for `θ ∈ 𝓞 K` with minimal polynomial
`f = minpoly ℤ θ`, the size of the reduced 𝔽_p-algebra
`(𝔽_p[X]/(f mod p))/nilradical` is at most the size of `𝓞K / rad(p·𝓞K)`.

Strategy: identify the left hand side with the radical quotient
`ℤ[θ] / rad(p·ℤ[θ])`, and use the fact that the extension
`ℤ[θ] ⊆ 𝓞K` is integral: extending an ideal and contracting its radical
recovers the original radical (`comap_radical_map_eq_radical_of_isIntegral`),
which yields an injection of the quotients by radicals.
-/

/-! ## Generic radical/quotient lemmas -/

section RadicalQuotients

variable {R : Type*} [CommRing R]

/-- The nilradical of `R ⧸ I` is the image of the radical of `I`. -/
lemma nilradical_quotient_eq_map_radical (I : Ideal R) :
    (I.radical).map (Ideal.Quotient.mk I) = nilradical (R ⧸ I) := by
  symm
  rw [Ideal.map_radical_of_surjective (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (I := I) (by simp)]
  rw [Ideal.map_quotient_self]
  rfl

/-- Quotienting by the nilradical of `R ⧸ I` gives the same cardinality as
quotienting `R` by the radical of `I`. -/
theorem natCard_quotient_nilradical_eq (I : Ideal R) :
    Nat.card ((R ⧸ I) ⧸ nilradical (R ⧸ I)) = Nat.card (R ⧸ I.radical) := by
  have hmap : (I.radical).map (Ideal.Quotient.mk I) = nilradical (R ⧸ I) :=
    nilradical_quotient_eq_map_radical I
  calc
    Nat.card ((R ⧸ I) ⧸ nilradical (R ⧸ I))
        = Nat.card ((R ⧸ I) ⧸ ((I.radical).map (Ideal.Quotient.mk I))) := by
            exact Nat.card_congr ((Ideal.quotEquivOfEq hmap.symm).toEquiv)
    _ = Nat.card (R ⧸ I.radical) := by
            exact Nat.card_congr
              ((DoubleQuot.quotQuotEquivQuotOfLE (R := R) (I := I) (J := I.radical)
                (Ideal.le_radical)).toEquiv)

/-- Ring isomorphisms preserve the cardinality of quotients by nilradicals. -/
theorem natCard_nilradical_quotient_congr {S : Type*} [CommRing S] (e : R ≃+* S) :
    Nat.card (R ⧸ nilradical R) = Nat.card (S ⧸ nilradical S) := by
  classical
  have hIJ : nilradical S = (nilradical R).map (e : R →+* S) := by
    ext y
    constructor
    · intro hy
      rw [Ideal.mem_map_iff_of_surjective (f := (e : R →+* S)) e.surjective]
      refine ⟨e.symm y, ?_, by simp⟩
      rw [mem_nilradical]
      rcases (mem_nilradical.mp hy) with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hmap : e.symm (y ^ n) = (0 : R) := by
        rw [hn]
        exact map_zero (e.symm : S →+* R)
      simpa using hmap
    · intro hy
      rw [Ideal.mem_map_iff_of_surjective (f := (e : R →+* S)) e.surjective] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [mem_nilradical] at hx
      rcases hx with ⟨n, hn⟩
      rw [mem_nilradical (R := S)]
      refine ⟨n, ?_⟩
      have hmap : e (x ^ n) = (0 : S) := by
        rw [hn]
        exact map_zero (e : R →+* S)
      simpa using hmap
  exact Nat.card_congr ((Ideal.quotientEquiv (nilradical R) (nilradical S) e hIJ).toEquiv)

end RadicalQuotients

section IntegralExtension

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

/-- In an integral extension `A → B`, an element of `A` lying in the extension
ideal `I·B` lies in the radical of `I`. -/
lemma comap_map_le_radical_of_isIntegral [Algebra.IsIntegral A B] [FaithfulSMul A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) ≤ I.radical := by
  classical
  intro x hx
  by_contra hxn
  have hxnot : x ∉ sInf {J : Ideal A | I ≤ J ∧ Ideal.IsPrime J} := by
    rwa [Ideal.radical_eq_sInf] at hxn
  rw [Submodule.mem_sInf] at hxnot
  push Not at hxnot
  obtain ⟨P, hPmem, hxP⟩ := hxnot
  rcases hPmem with ⟨hIleP, hPprime⟩
  haveI : Ideal.IsPrime P := hPprime
  have hIP : (⊥ : Ideal B).comap (algebraMap A B) ≤ P := by
    intro y hy
    have hy0 : algebraMap A B y = 0 := (Submodule.mem_bot _).mp ((Ideal.mem_comap (f := algebraMap A B)).mp hy)
    have hy' : y = 0 := (FaithfulSMul.algebraMap_injective A B) (by simpa using hy0)
    simp [hy']
  obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) P (⊥ : Ideal B) hIP
  have hmap_le_Q : I.map (algebraMap A B) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQcomap]
    exact hIleP
  have hfxQ : algebraMap A B x ∈ Q := hmap_le_Q hx
  have hxP' : x ∈ P := by
    rw [← hQcomap]
    exact hfxQ
  exact hxP hxP'

/-- For an integral extension `A → B`, extending an ideal `I` to `B` and
contracting its radical back gives exactly the radical of `I`. -/
lemma comap_radical_map_eq_radical_of_isIntegral [Algebra.IsIntegral A B] [FaithfulSMul A B]
    (I : Ideal A) :
    (I.map (algebraMap A B)).radical.comap (algebraMap A B) = I.radical := by
  apply le_antisymm
  · rw [Ideal.comap_radical]
    calc
      ((I.map (algebraMap A B)).comap (algebraMap A B)).radical
          ≤ I.radical.radical := Ideal.radical_mono (comap_map_le_radical_of_isIntegral (A := A) (B := B) I)
      _ = I.radical := Ideal.radical_idem I
  · exact (Ideal.map_le_iff_le_comap (f := algebraMap A B) (I := I.radical)
      (K := (I.map (algebraMap A B)).radical)).mp (Ideal.map_radical_le (algebraMap A B) (I := I))

/-- If `B` is an integral `A`-algebra, then `A / rad I` injects into
`B / rad (I·B)`, so its cardinality is at most that of the latter. -/
theorem natCard_quotient_radical_le_of_isIntegral [Algebra.IsIntegral A B] [FaithfulSMul A B]
    (I : Ideal A) [Finite (B ⧸ (I.map (algebraMap A B)).radical)] :
    Nat.card (A ⧸ I.radical) ≤ Nat.card (B ⧸ (I.map (algebraMap A B)).radical) := by
  classical
  let f : A →+* B ⧸ (I.map (algebraMap A B)).radical :=
    (Ideal.Quotient.mk ((I.map (algebraMap A B)).radical)).comp (algebraMap A B)
  have H : ∀ a : A, a ∈ I.radical → f a = 0 := by
    intro a ha
    change (Ideal.Quotient.mk ((I.map (algebraMap A B)).radical) (algebraMap A B a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (Ideal.map_radical_le (algebraMap A B) (I := I)) (Ideal.mem_map_of_mem (algebraMap A B) ha)
  have hker : RingHom.ker f ≤ I.radical := by
    intro a ha
    have ha0 : f a = 0 := (RingHom.mem_ker.mp ha)
    have ha' : algebraMap A B a ∈ (I.map (algebraMap A B)).radical := by
      change (Ideal.Quotient.mk ((I.map (algebraMap A B)).radical) (algebraMap A B a)) = 0 at ha0
      rw [Ideal.Quotient.eq_zero_iff_mem] at ha0
      exact ha0
    rw [← comap_radical_map_eq_radical_of_isIntegral (A := A) (B := B) I]
    exact (Ideal.mem_comap (f := algebraMap A B)).2 ha'
  have hinj : Function.Injective (Ideal.Quotient.lift (I := I.radical) f H) := by
    exact RingHom.lift_injective_of_ker_le_ideal (R := A) (S := B ⧸ (I.map (algebraMap A B)).radical)
      (I := I.radical) H hker
  exact Nat.card_le_card_of_injective (Ideal.Quotient.lift (I := I.radical) f H) hinj

end IntegralExtension

/-! ## The order `ℤ[θ]` inside `𝓞 K` and the main cardinality inequality -/

section NumberFieldAdjoin

variable {K : Type*} [Field K] [NumberField K]

/-- The order `ℤ[θ]` as a subalgebra of the ring of integers. -/
def adjoinOrder (θ : 𝓞 K) : Subalgebra ℤ (𝓞 K) :=
  Algebra.adjoin ℤ ({θ} : Set (𝓞 K))

/-- The canonical power basis of `ℤ[θ]` generated by `θ`. -/
noncomputable def adjoinOrderPB (θ : 𝓞 K) : PowerBasis ℤ (adjoinOrder θ) :=
  Algebra.adjoin.powerBasis' (S := 𝓞 K) (θ.isIntegral)

/-- The minimal polynomial of the power-basis generator is `minpoly ℤ θ`. -/
lemma adjoinOrderPB_minpoly (θ : 𝓞 K) :
    minpoly ℤ (adjoinOrderPB θ).gen = minpoly ℤ θ :=
  (Algebra.adjoin.powerBasis'_minpoly_gen (S := 𝓞 K) (θ.isIntegral)).symm

/-- The extension `ℤ[θ] ⊆ 𝓞 K` is integral. -/
lemma adjoinOrder_isIntegral (θ : 𝓞 K) : Algebra.IsIntegral (adjoinOrder θ) (𝓞 K) := by
  refine ⟨fun x : 𝓞 K => ?_⟩
  exact IsIntegral.tower_top (R := ℤ) (A := adjoinOrder θ) (B := 𝓞 K) x.isIntegral

/-- Polynomial ring equivalence induced by a ring equivalence of the coefficients. -/
noncomputable def polyCongr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    R[X] ≃+* S[X] :=
  RingEquiv.ofBijective (Polynomial.mapRingHom (e : R →+* S))
    ⟨Polynomial.map_injective (e : R →+* S) e.injective,
     Polynomial.map_surjective (e : R →+* S) e.surjective⟩

@[simp]
lemma polyCongr_apply {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : R[X]) :
    polyCongr e p = p.map (e : R →+* S) := by
  rfl

/-- The ℤ[θ]-side quotient `ℤ[θ] / p·ℤ[θ]` is ring-isomorphic to
`(ZMod p)[X] / (f mod p)` where `f = minpoly ℤ θ`. -/
noncomputable def quotient_iso_zmod (θ : 𝓞 K) (p : ℕ) :
    ((adjoinOrder θ) ⧸ ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (adjoinOrder θ)))) ≃+*
      (ZMod p)[X] ⧸ Ideal.span
        ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X]) := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let A := adjoinOrder θ
  let pb := adjoinOrderPB θ
  have e1 : (A ⧸ pZ.map (algebraMap ℤ A)) ≃+*
      (ℤ ⧸ pZ)[X] ⧸ Ideal.span
        ({(minpoly ℤ pb.gen).map (Ideal.Quotient.mk pZ)} : Set (ℤ ⧸ pZ)[X]) := by
    exact (pb.quotientEquivQuotientMinpolyMap pZ).toRingEquiv
  let eZ : ℤ ⧸ pZ ≃+* ZMod p := Int.quotientSpanNatEquivZMod p
  let psi : (ℤ ⧸ pZ)[X] ≃+* (ZMod p)[X] := polyCongr eZ
  have hcomp : (eZ : (ℤ ⧸ pZ) →+* ZMod p).comp (Ideal.Quotient.mk pZ) =
      Int.castRingHom (ZMod p) := by
    exact Int.quotientSpanNatEquivZMod_comp_Quotient_mk p
  have hPs : psi ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk pZ)) =
      (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) := by
    calc
      psi ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk pZ))
          = ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk pZ)).map
              (eZ : (ℤ ⧸ pZ) →+* ZMod p) := by
              rw [polyCongr_apply]
      _ = (minpoly ℤ pb.gen).map ((eZ : (ℤ ⧸ pZ) →+* ZMod p).comp (Ideal.Quotient.mk pZ)) := by
              rw [Polynomial.map_map]
      _ = (minpoly ℤ pb.gen).map (Int.castRingHom (ZMod p)) := by rw [hcomp]
      _ = (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) := by rw [adjoinOrderPB_minpoly θ]
  let I1 : Ideal (ℤ ⧸ pZ)[X] := Ideal.span
        ({(minpoly ℤ pb.gen).map (Ideal.Quotient.mk pZ)} : Set (ℤ ⧸ pZ)[X])
  let J1 : Ideal (ZMod p)[X] := Ideal.span
        ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])
  have hIJ : J1 = I1.map (psi : (ℤ ⧸ pZ)[X] →+* (ZMod p)[X]) := by
    dsimp [J1, I1]
    rw [Ideal.map_span]
    congr 1
    simp [hPs]
  have e2 : ((ℤ ⧸ pZ)[X] ⧸ I1) ≃+* (ZMod p)[X] ⧸ J1 :=
    Ideal.quotientEquiv I1 J1 psi hIJ
  exact e1.trans e2

/-- The cardinality of the reduced quotient of `(ZMod p)[X] / (f mod p)` equals
the cardinality of `ℤ[θ] / rad(p·ℤ[θ])`. -/
lemma natCard_zmod_poly_nilrad_eq_adjoin_rad (θ : 𝓞 K) (p : ℕ) :
    Nat.card (((ZMod p)[X] ⧸ Ideal.span
        ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])) ⧸
      nilradical ((ZMod p)[X] ⧸ Ideal.span
        ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X]))) =
    Nat.card ((adjoinOrder θ) ⧸
      ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (adjoinOrder θ))).radical) := by
  let A := adjoinOrder θ
  let pA : Ideal A := (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ A)
  calc
    Nat.card (((ZMod p)[X] ⧸ Ideal.span
          ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])) ⧸
        nilradical ((ZMod p)[X] ⧸ Ideal.span
          ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])))
        = Nat.card ((A ⧸ pA) ⧸ nilradical (A ⧸ pA)) := by
            exact (natCard_nilradical_quotient_congr (quotient_iso_zmod θ p)).symm
    _ = Nat.card (A ⧸ pA.radical) := natCard_quotient_nilradical_eq (R := A) pA

/-- The cardinality of `ℤ[θ] / rad(p·ℤ[θ])` is at most that of
`𝓞K / rad(p·𝓞K)`. -/
theorem natCard_adjoin_rad_le_ringOfIntegers_rad (θ : 𝓞 K) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card ((adjoinOrder θ) ⧸
      ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (adjoinOrder θ))).radical) ≤
    Nat.card ((𝓞 K) ⧸
      ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))).radical) := by
  classical
  let A := adjoinOrder θ
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let pA : Ideal A := pZ.map (algebraMap ℤ A)
  let pB : Ideal (𝓞 K) := pZ.map (algebraMap ℤ (𝓞 K))
  have hpmap : pA.map (algebraMap A (𝓞 K)) = pB := by
    dsimp [pA, pB, pZ]
    rw [Ideal.map_map]
    congr 1
  have hBne : pB ≠ ⊥ := by
    intro h
    have hmem : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ pB := by
      dsimp [pB]
      exact Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) (Ideal.mem_span_singleton_self (p : ℤ))
    have hz : algebraMap ℤ (𝓞 K) (p : ℤ) = 0 := (Submodule.mem_bot _).mp (by
      rw [← h]
      exact hmem)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := FaithfulSMul.algebraMap_injective ℤ (𝓞 K)
    have h' : (p : ℤ) = 0 := hinj (by simpa using hz)
    exact (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)) (by exact_mod_cast h')
  have hJne : (pA.map (algebraMap A (𝓞 K))).radical ≠ ⊥ := by
    intro h
    apply hBne
    rw [← hpmap]
    exact le_bot_iff.mp (by
      calc
        pA.map (algebraMap A (𝓞 K))
            ≤ (pA.map (algebraMap A (𝓞 K))).radical := Ideal.le_radical
        _ = ⊥ := h)
  haveI : Finite ((𝓞 K) ⧸ (pA.map (algebraMap A (𝓞 K))).radical) := by
    exact Ring.HasFiniteQuotients.finiteQuotient (R := 𝓞 K)
      (I := (pA.map (algebraMap A (𝓞 K))).radical) hJne
  haveI : Algebra.IsIntegral A (𝓞 K) := adjoinOrder_isIntegral θ
  have hle := natCard_quotient_radical_le_of_isIntegral (A := A) (B := 𝓞 K) pA
  calc
    Nat.card (A ⧸ pA.radical) ≤ Nat.card ((𝓞 K) ⧸ (pA.map (algebraMap A (𝓞 K))).radical) := hle
    _ = Nat.card ((𝓞 K) ⧸ pB.radical) := by
        have hJeq : (pA.map (algebraMap A (𝓞 K))).radical = pB.radical := by
          rw [hpmap]
        exact Nat.card_congr ((Ideal.quotEquivOfEq hJeq).toEquiv)



end NumberFieldAdjoin
/-- The size of the reduced `𝔽_p`-algebra `(𝔽_p[X]/(f mod p))/nilradical`
(with `f = minpoly ℤ θ`) is at most the size of `𝓞K / rad(p·𝓞K)`. -/
theorem poly_reduced_card_le_radical_quotient {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
      (((ZMod p)[X] ⧸ Ideal.span
          ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])) ⧸
        nilradical ((ZMod p)[X] ⧸ Ideal.span
          ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X]))) ≤
      Nat.card ((𝓞 K) ⧸
        ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))).radical) := by
  calc
    Nat.card
        (((ZMod p)[X] ⧸ Ideal.span
            ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])) ⧸
          nilradical ((ZMod p)[X] ⧸ Ideal.span
            ({(minpoly ℤ θ).map (Int.castRingHom (ZMod p))} : Set (ZMod p)[X])))
        = Nat.card ((adjoinOrder θ) ⧸
            ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (adjoinOrder θ))).radical) := by
            exact natCard_zmod_poly_nilrad_eq_adjoin_rad θ p
    _ ≤ Nat.card ((𝓞 K) ⧸
            ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))).radical) := by
            exact natCard_adjoin_rad_le_ringOfIntegers_rad θ p




end

end Commons.NumberTheory.NumberField