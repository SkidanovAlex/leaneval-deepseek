import Mathlib
import Submission.Work.DSG4b.sepQuot.isReduced
import Submission.Work.DSG4b.finiteDimReduced.isField_localizationAtPrime_of_finiteDimensional_reduced

@[expose] public section

set_option linter.unusedVariables false

namespace Work.DSG4b.minpolyQuotient

open Polynomial MvPolynomial

/-! ### Auxiliary 1: quotient by monic polynomials is a finite module -/

theorem moduleFinite_quotient_monic {R : Type*} [CommRing R] {σ : Type*} [Fintype σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hne : ∀ s, f s ≠ 1) :
    Module.Finite R (MvPolynomial σ R ⧸
      Ideal.span (Set.range fun s => (f s).aeval (MvPolynomial.X s : MvPolynomial σ R))) := by
  set I : Ideal (MvPolynomial σ R) :=
    Ideal.span (Set.range fun s => (f s).aeval (MvPolynomial.X s : MvPolynomial σ R)) with hI
  have hmem : ∀ s, (f s).aeval (MvPolynomial.X s : MvPolynomial σ R) ∈ I := by
    intro s; rw [hI]; exact Ideal.subset_span ⟨s, rfl⟩
  have hgen : ∀ s : σ, IsIntegral R (Ideal.Quotient.mk I (MvPolynomial.X s)) := by
    intro s
    refine ⟨f s, hf s, ?_⟩
    have h2 : Polynomial.aeval ((Ideal.Quotient.mkₐ R I) (MvPolynomial.X s)) (f s) = 0 := by
      rw [Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R I)]
      show Ideal.Quotient.mk I (Polynomial.aeval (MvPolynomial.X s) (f s)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hmem s
    exact h2
  have hall : ∀ x : MvPolynomial σ R ⧸ I, IsIntegral R x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hC : Ideal.Quotient.mk I (MvPolynomial.C a)
            = algebraMap R (MvPolynomial σ R ⧸ I) a := by
          rw [MvPolynomial.C_eq_algebraMap]
          exact AlgHom.commutes (Ideal.Quotient.mkₐ R I) a
        rw [hC]
        exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p n hp => rw [map_mul]; exact hp.mul (hgen n)
  haveI : Algebra.FiniteType R (MvPolynomial σ R ⧸ I) := inferInstance
  haveI : Algebra.IsIntegral R (MvPolynomial σ R ⧸ I) := Algebra.IsIntegral.mk hall
  exact Algebra.IsIntegral.finite

/-! ### Auxiliary 2: finite-dimensional reduced algebras mapping onto a field -/

theorem exists_mul_eq_zero_of_finiteDimensional_reduced {L A K : Type*} [Field L] [CommRing A]
    [Algebra L A] [Module.Finite L A] [IsReduced A] [Field K] [Algebra L K] (φ : A →ₐ[L] K) :
    ∀ a, φ a = 0 → ∃ s, φ s ≠ 0 ∧ s * a = 0 := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite L A
  haveI hprime : (RingHom.ker (φ : A →+* K)).IsPrime := RingHom.ker_isPrime φ
  intro a ha
  have hmax : (RingHom.ker (φ : A →+* K)).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime (RingHom.ker (φ : A →+* K))
  let m₀ : MaximalSpectrum A := ⟨RingHom.ker (φ : A →+* K), hmax⟩
  let e : A := (IsArtinianRing.equivPi A).symm (Pi.single m₀ 1)
  have he : (IsArtinianRing.equivPi A) e = Pi.single m₀ (1 : A ⧸ m₀.asIdeal) := by
    change (IsArtinianRing.equivPi A)
      ((IsArtinianRing.equivPi A).symm (Pi.single m₀ (1 : A ⧸ m₀.asIdeal))) = _
    rw [AlgEquiv.apply_symm_apply]
  have ha0 : (Ideal.Quotient.mk m₀.asIdeal) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  refine ⟨e, ?_, ?_⟩
  · have h2 : (Ideal.Quotient.mk m₀.asIdeal) e = 1 := by
      rw [← IsArtinianRing.equivPi_apply, he, Pi.single_eq_same]
    have h4 : e - 1 ∈ m₀.asIdeal := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, h2, map_one]
    have h3 : e - 1 ∈ RingHom.ker (φ : A →+* K) := h4
    have h5 : φ e = 1 := by
      have h6 : (φ : A →+* K) (e - 1) = 0 := RingHom.mem_ker.mp h3
      rw [map_sub, map_one, sub_eq_zero] at h6
      exact h6
    rw [h5]
    exact one_ne_zero
  · apply (IsArtinianRing.equivPi A).injective
    rw [map_mul, he, map_zero]
    funext M
    rw [Pi.mul_apply]
    by_cases hM : M = m₀
    · subst hM
      rw [Pi.single_eq_same, IsArtinianRing.equivPi_apply, ha0, mul_zero]
      rfl
    · rw [Pi.single_eq_of_ne hM, zero_mul]
      rfl

/-! ### Auxiliary 3: the transport to finitely many variables -/

/-- The "big" ideal, cutting out `MvPolynomial K L ⧸ _`. -/
noncomputable abbrev bigI (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K] :
    Ideal (MvPolynomial K L) :=
  Ideal.span (Set.range fun α : K => (minpoly L α).aeval (MvPolynomial.X α : MvPolynomial K L))

/-- The "small" ideal attached to a finite set `S` of variables. -/
noncomputable abbrev smallI (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K]
    (S : Finset K) : Ideal (MvPolynomial ↥S L) :=
  Ideal.span (Set.range fun a : ↥S =>
    (minpoly L (a : K)).aeval (MvPolynomial.X a : MvPolynomial ↥S L))

/-- The relation of a variable, transported along `MvPolynomial.rename`. -/
lemma rename_aeval_mem_bigI (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K]
    (S : Finset K) (a : ↥S) :
    (MvPolynomial.rename (Subtype.val : ↥S → K))
      ((minpoly L (a : K)).aeval (MvPolynomial.X a)) ∈ bigI L K := by
  rw [← Polynomial.aeval_algHom_apply (MvPolynomial.rename (Subtype.val : ↥S → K)),
    MvPolynomial.rename_X]
  rw [bigI]
  exact Ideal.subset_span ⟨(a : K), rfl⟩

/-- The composite `MvPolynomial ↥S L →ₐ[L] MvPolynomial K L ⧸ bigI L K` vanishes on
`smallI L K S`. -/
lemma psi_aux (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K] (S : Finset K) :
    ∀ y ∈ smallI L K S,
      ((Ideal.Quotient.mkₐ L (bigI L K)).comp
        (MvPolynomial.rename (Subtype.val : ↥S → K))) y = 0 := by
  intro y hy
  have hle : smallI L K S ≤ RingHom.ker ((Ideal.Quotient.mkₐ L (bigI L K)).comp
      (MvPolynomial.rename (Subtype.val : ↥S → K))) := by
    rw [smallI]
    refine Ideal.span_le.mpr ?_
    rintro z ⟨a, rfl⟩
    show Ideal.Quotient.mk (bigI L K)
      ((MvPolynomial.rename (Subtype.val : ↥S → K))
        ((minpoly L (a : K)).aeval (MvPolynomial.X a))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact rename_aeval_mem_bigI L K S a
  exact RingHom.mem_ker.mp (hle hy)

/-- The canonical map `MvPolynomial ↥S L ⧸ smallI L K S →ₐ[L] MvPolynomial K L ⧸ bigI L K`. -/
noncomputable def psi (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K]
    (S : Finset K) :
    (MvPolynomial ↥S L ⧸ smallI L K S) →ₐ[L] (MvPolynomial K L ⧸ bigI L K) :=
  Ideal.Quotient.liftₐ (smallI L K S)
    ((Ideal.Quotient.mkₐ L (bigI L K)).comp
      (MvPolynomial.rename (Subtype.val : ↥S → K)))
    (psi_aux L K S)

lemma psi_apply_mk (L : Type*) [Field L] (K : Type*) [Field K] [Algebra L K]
    (S : Finset K) (y : MvPolynomial ↥S L) :
    psi L K S ((Ideal.Quotient.mkₐ L (smallI L K S)) y) =
      (Ideal.Quotient.mkₐ L (bigI L K)) (MvPolynomial.rename (Subtype.val : ↥S → K) y) := by
  rw [show psi L K S = Ideal.Quotient.liftₐ (smallI L K S)
      ((Ideal.Quotient.mkₐ L (bigI L K)).comp (MvPolynomial.rename (Subtype.val : ↥S → K)))
      (psi_aux L K S) from rfl]
  exact AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (smallI L K S)
    ((Ideal.Quotient.mkₐ L (bigI L K)).comp (MvPolynomial.rename (Subtype.val : ↥S → K)))
    (psi_aux L K S)) y

/-! ### The main theorem -/

/-- Let `L` be a perfect field, `K/L` an algebraic field extension, and let
`M = L[X_a : a ∈ K] ⧸ (minpoly_L(a)(X_a))` be the "tensor product of all minimal polynomial
quotients", evaluated at the identity by `φ : M →ₐ[L] K`, `X_a ↦ a`.  Then the localisation of `M`
at `ker φ` is a field (namely `K`): every element of `ker φ` is annihilated by an element outside
`ker φ`.  Reduction to finitely many variables, using reducedness of finite tensors over the perfect
field `L` and the fact that the localisation of a finite-dimensional reduced `L`-algebra at a
maximal ideal is a field. -/
theorem exists_mul_eq_zero_of_eval_eq_zero (L K : Type*) [Field L] [PerfectField L] [Field K]
    [Algebra L K] [Algebra.IsAlgebraic L K]
    (φ : (MvPolynomial K L ⧸ Ideal.span (Set.range fun α : K =>
        (minpoly L α).aeval (MvPolynomial.X α : MvPolynomial K L))) →ₐ[L] K)
    (hφ : ∀ α : K, φ (Ideal.Quotient.mk _ (MvPolynomial.X α : MvPolynomial K L)) = α) :
    ∀ m, φ m = 0 → ∃ s, φ s ≠ 0 ∧ s * m = 0 := by
  intro m hm
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective m
  have hx' : (Ideal.Quotient.mkₐ L (bigI L K)) x = m := hx
  obtain ⟨S, x₀, hx₀ring⟩ := MvPolynomial.exists_finset_rename x
  have hx₀ : MvPolynomial.rename (Subtype.val : ↥S → K) x₀ = x := hx₀ring.symm
  haveI : Algebra.IsIntegral L K := Algebra.IsAlgebraic.isIntegral
  haveI : Fintype ↥S := Finset.fintypeCoeSort S
  have hmono : ∀ a : ↥S, (minpoly L (a : K)).Monic :=
    fun a => minpoly.monic (Algebra.IsIntegral.isIntegral (a : K))
  have hne : ∀ a : ↥S, minpoly L (a : K) ≠ 1 := by
    intro a h
    have h2 := minpoly.aeval L (a : K)
    rw [h] at h2
    simp at h2
  have hsep : ∀ a : ↥S, (minpoly L (a : K)).Separable :=
    fun a => Algebra.IsSeparable.isSeparable L (a : K)
  haveI hfin : Module.Finite L (MvPolynomial ↥S L ⧸ smallI L K S) :=
    moduleFinite_quotient_monic (fun a : ↥S => minpoly L (a : K)) hmono hne
  haveI hred : IsReduced (MvPolynomial ↥S L ⧸ smallI L K S) :=
    sepQuot.finiteCase L ↥S (fun a : ↥S => minpoly L (a : K)) hsep
  have hφS : (φ.comp (psi L K S)) ((Ideal.Quotient.mkₐ L (smallI L K S)) x₀) = 0 := by
    rw [AlgHom.comp_apply, psi_apply_mk L K S x₀, hx₀, hx']
    exact hm
  obtain ⟨s', hs'ne, hs'mul⟩ :=
    exists_mul_eq_zero_of_finiteDimensional_reduced (φ.comp (psi L K S))
      ((Ideal.Quotient.mkₐ L (smallI L K S)) x₀) hφS
  refine ⟨psi L K S s', ?_, ?_⟩
  · simpa only [AlgHom.comp_apply] using hs'ne
  · have h1 : psi L K S s' * (Ideal.Quotient.mkₐ L (bigI L K)) x = 0 := by
      have h2 : psi L K S (s' * (Ideal.Quotient.mkₐ L (smallI L K S)) x₀) = 0 := by
        rw [hs'mul, map_zero]
      rw [map_mul, psi_apply_mk L K S x₀, hx₀] at h2
      exact h2
    rw [← hx']
    exact h1

end Work.DSG4b.minpolyQuotient

