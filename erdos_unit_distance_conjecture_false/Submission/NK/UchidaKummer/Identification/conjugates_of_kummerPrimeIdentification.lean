import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.Identification.conjugates_of_comap_placeMap_eq
import Submission.NK.UchidaKummer.Identification.eq_one_of_stabilizes_places_of_hasFullDensity
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff

/-!
# The identification step of §5: prime identification ⟹ conjugacy (D-A)

Reference: the LaTeX sources of arXiv:2601.01251, §5 (*Full Neukirch–Uchida*).

The Kummer method of §5 produces, from a homeomorphic isomorphism
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of absolute Galois groups of number fields and the place
correspondence `a` of CoNF (12.1.9), a *base-field mapping* isomorphism `σ : K₂' ≃+* K₁'` which,
outside a set of primes of Dirichlet density zero, realizes the place correspondence
(`NK.UchidaKummer.KummerPrimeIdentification`).

This file performs the upgrade from that *density-one* prime-level statement to the group-level
statement `Submission.NeukirchUchida.Conjugates σ ϕ` (the step D-A of the paper):

* if `σ` realizes the place correspondence at a place `A` of `K₁'`, then `ϕ g` and the conjugation
  `σ⁻¹ g σ` move the `σ`-transport of `A` to the *same* place (`hstep` below, from the
  Galois-equivariance `a.map_smul` of the place map);
* hence their quotient `g⁻¹ · σ⁻¹ (ϕ g) σ` stabilizes every place over a prime in the
  full-density set `R`;
* an automorphism of `Gal(K₁'/K₁)` stabilizing all places over a full-density set of primes is
  trivial (`eq_one_of_stabilizes_places_of_hasFullDensity`): one picks a prime of `R` splitting
  completely in a finite Galois level and uses the freeness of the Galois action on the primes
  above it.

Consequently `σ` realizes the whole place correspondence and induces `ϕ`.
-/

namespace NK.UchidaKummer.Identification

open scoped Pointwise

theorem conjugates_of_kummerPrimeIdentification
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h : NK.UchidaKummer.KummerPrimeIdentification hϕ a) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _hlvl, R, hR, hplace⟩ := h
  refine ⟨σ, hσ, ?_⟩
  -- (1) the place correspondence is realized by `σ`, in `comap` form, over the primes of `R`
  have hplace' : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
      (a.placeMap A).1 = A.1.comap (σ : K₂' →+* K₁') := by
    intro A hA
    have h1 := congrArg (fun B : ValuationSubring K₁' => B.comap (σ : K₂' →+* K₁'))
      (hplace A hA)
    rw [ValuationSubring.comap_comap, RingEquiv.symm_comp] at h1
    rw [show (a.placeMap A).1.comap (RingHom.id K₂') = (a.placeMap A).1 from by
      ext x
      rw [ValuationSubring.mem_comap]
      simp] at h1
    exact h1
  -- the prime below a translated place is unchanged
  have hprime_smul : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Submission.NeukirchUchida.primeOf (NK.Reconstruct.placeSmul g A).1
        (NK.Reconstruct.placeSmul g A).2 =
      Submission.NeukirchUchida.primeOf A.1 A.2 := by
    intro g A
    refine Submission.NeukirchUchida.primeOf_eq_of_comap_eq _ _ ?_
    rw [NK.Reconstruct.placeSmul_val,
      Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap]
  -- (2) `ϕ g` transports the `σ`-transported places
  have hstep : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
      (ϕ g) • (A.1.comap (σ : K₂' →+* K₁')) = (g • A.1).comap (σ : K₂' →+* K₁') := by
    intro g A hA
    have h2 : (a.placeMap (NK.Reconstruct.placeSmul g A)).1 =
        (NK.Reconstruct.placeSmul g A).1.comap (σ : K₂' →+* K₁') :=
      hplace' (NK.Reconstruct.placeSmul g A) (by rw [hprime_smul g A]; exact hA)
    have h3 := congrArg Subtype.val (a.map_smul g A)
    rw [NK.Reconstruct.placeSmul₂_val, hplace' A hA, h2,
      NK.Reconstruct.placeSmul_val] at h3
    exact h3.symm
  -- the `σ`-transport is injective
  have hcomap_inj : Function.Injective
      (fun V : ValuationSubring K₁' => V.comap (σ : K₂' →+* K₁')) := by
    have hsq : ∀ V : ValuationSubring K₁',
        (V.comap (σ : K₂' →+* K₁')).comap (σ.symm : K₁' →+* K₂') = V := by
      intro V
      rw [ValuationSubring.comap_comap, RingEquiv.comp_symm]
      ext x
      rw [ValuationSubring.mem_comap]
      simp
    intro V W hVW
    have := congrArg (fun U : ValuationSubring K₂' => U.comap (σ.symm : K₁' →+* K₂')) hVW
    rwa [hsq V, hsq W] at this
  -- (3) the difference `g⁻¹ · σ⁻¹ (ϕ g) σ` stabilizes every place over a prime of `R`
  have hstab : ∀ g : Gal(K₁'/K₁),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
      (g⁻¹ * (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g)) • A.1 = A.1 := by
    intro g A hA
    have h1 : (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) • A.1 = g • A.1 := by
      apply hcomap_inj
      calc ((Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) • A.1).comap
              (σ : K₂' →+* K₁')
          = (Submission.NeukirchUchida.conjHomEquiv hσ
              ((Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g))) •
            (A.1.comap (σ : K₂' →+* K₁')) :=
            NK.UchidaKummer.Identification.smul_comap_sigma_eq_conj_smul hσ _ A.1
        _ = (ϕ g) • (A.1.comap (σ : K₂' →+* K₁')) := by
            rw [MulEquiv.apply_symm_apply]
        _ = (g • A.1).comap (σ : K₂' →+* K₁') := hstep g A hA
    rw [mul_smul, h1, ← mul_smul, inv_mul_cancel, one_smul]
  -- (4) `σ` induces `ϕ`
  have hkey : ∀ g : Gal(K₁'/K₁),
      (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) = g := by
    intro g
    have h1 : g⁻¹ * (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) = 1 := by
      refine eq_one_of_stabilizes_places_of_hasFullDensity hR _ (fun A hA => ?_)
      have h2 : g⁻¹ * (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) ∈
          MulAction.stabilizer Gal(K₁'/K₁) A.1 := by
        rw [MulAction.mem_stabilizer_iff]
        exact hstab g A hA
      exact (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A.1 _).mp h2
    have h3 : (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g) =
        g * (g⁻¹ * (Submission.NeukirchUchida.conjHomEquiv hσ).symm (ϕ g)) := by group
    rw [h3, h1, mul_one]
  intro g
  have h4 : ϕ g = Submission.NeukirchUchida.conjHomEquiv hσ g := by
    have h5 := congrArg (Submission.NeukirchUchida.conjHomEquiv hσ) (hkey g)
    rwa [MulEquiv.apply_symm_apply] at h5
  exact (congrArg (fun e : Gal(K₂'/K₂) => (e : K₂' ≃+* K₂')) h4).trans
    (Submission.NeukirchUchida.conj_toRingEquiv hσ g)

end NK.UchidaKummer.Identification
