import ChallengeDeps
import Submission.Commons.RingTheory.Jacobian.localization_quotient_jacobian_isField
import Submission.Commons.AlgebraicGeometry.Affine.irreducibleComponent_iso_spec_of_localization

open AlgebraicGeometry Module NumberField Real Scheme
open _root_.EnumeratingNumberFields

set_option autoImplicit false

namespace Submission.Models

/-- The algebraic model statement (to be supplied by the Commons lemma `small_algebraic_model`). -/
def ModelStatement : Prop :=
  ∃ Q > 0, ∀ n ≥ Q, ∀ (K : Type) [Field K] [NumberField K],
      Module.finrank ℚ K = n →
      ∃ r d : ℕ, (r : ℝ) ≤ Q * Real.log n ∧ (d : ℝ) ≤ Q * Real.log n ∧
        ((d + r).choose r : ℝ) ≤ Q * (n : ℝ) * Real.log n ∧
        ∃ E : Fin r → MvPolynomial (Fin r) ℤ,
          (∀ i, (E i).totalDegree ≤ d) ∧
          (∀ i j, |(E i).coeff j| ≤ ((n : ℝ) * NumberField.rootDiscr K) ^ (Q * Real.log n)) ∧
          ∃ φ : MvPolynomial (Fin r) ℚ →ₐ[ℚ] K, Function.Surjective φ ∧
            (∀ i, φ ((E i).map (algebraMap ℤ ℚ)) = 0) ∧
            IsUnit (φ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ))))

theorem theorem_1_of_algebraic_model (hmodel : ModelStatement) :
    ∃ Q > 0, ∀ n ≥ Q, ∀ K : NumberFieldOfDegree n, ∃ (r d : ℕ),
    r ≤ Q * log n ∧ d ≤ Q * log n ∧ (d + r).choose r ≤ Q * n * log n ∧
      ∃ E : Fin r → MvPolynomial (Fin r) ℤ, (∀ i, (E i).totalDegree ≤ d) ∧
        (∀ i j, |(E i).coeff j| ≤ (n * rootDiscr K) ^ (Q * log n)) ∧
          letI X := nonsingularOpen fun i ↦ (E i).map (algebraMap ℤ ℚ)
          ∃ Z, ∃ hZ : Z ∈ irreducibleComponents X,
            Nonempty (X.irreducibleComponent Z hZ ≅ Spec (.of K)) := by
  obtain ⟨Q, hQpos, hQ⟩ := hmodel
  refine ⟨Q, hQpos, ?_⟩
  intro n hn K
  obtain ⟨r, d, hr, hd, hbinom, E, hdeg, hcoeff, φ, hsurj, hE0, hunit⟩ :=
    hQ n hn K.carrier K.degree
  refine ⟨r, d, hr, hd, hbinom, E, hdeg, hcoeff, ?_⟩
  -- Now the scheme statement.
  let Eℚ : Fin r → MvPolynomial (Fin r) ℚ := fun i ↦ (E i).map (algebraMap ℤ ℚ)
  let A := (MvPolynomial (Fin r) ℚ) ⧸ Ideal.span (Set.range Eℚ)
  let det : MvPolynomial (Fin r) ℚ := Matrix.det fun i j ↦ MvPolynomial.pderiv j (Eℚ i)
  have hker : Set.range Eℚ ⊆ RingHom.ker (φ : MvPolynomial (Fin r) ℚ →+* K) := by
    rintro _ ⟨i, rfl⟩
    exact hE0 i
  have hker' : Ideal.span (Set.range Eℚ) ≤ RingHom.ker (φ : MvPolynomial (Fin r) ℚ →+* K) := by
    rw [Ideal.span_le]; exact hker
  let ψ : A →+* K := Ideal.Quotient.lift (Ideal.span (Set.range Eℚ))
    (φ : MvPolynomial (Fin r) ℚ →+* K) (fun a ha => RingHom.mem_ker.mp (hker' ha))
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨p, hp⟩ := hsurj x
    refine ⟨Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) p, ?_⟩
    change Ideal.Quotient.lift (Ideal.span (Set.range Eℚ))
      (φ : MvPolynomial (Fin r) ℚ →+* K) _ (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) p) = x
    rw [Ideal.Quotient.lift_mk]
    exact hp
  have hψdet : ψ (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det) = φ det := by
    change Ideal.Quotient.lift (Ideal.span (Set.range Eℚ))
      (φ : MvPolynomial (Fin r) ℚ →+* K) _ (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det) = φ det
    rw [Ideal.Quotient.lift_mk]
    rfl
  have hunitψ : IsUnit (ψ (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det)) := by rw [hψdet]; exact hunit
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψsurj
  have hf : (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det) ∉ RingHom.ker ψ := by
    intro hmem
    have h0 : ψ (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det) = 0 := hmem
    rw [hψdet] at h0
    exact hunit.ne_zero h0
  obtain ⟨hiso⟩ := Commons.RingTheory.Jacobian.localization_quotient_jacobian_isField
    Eℚ K ψ hψsurj hunitψ
  haveI hNoeth : AlgebraicGeometry.IsNoetherian
      ((Spec (.of A)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
          (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det)) : Scheme) :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian (nonsingularOpen Eℚ))
  obtain ⟨Z, hZ, hisocomp⟩ :=
    Commons.AlgebraicGeometry.Affine.irreducibleComponent_iso_spec_of_localization
      (A := A) (K := K) (𝔭 := RingHom.ker ψ) hmax (Ideal.Quotient.mk (Ideal.span (Set.range Eℚ)) det) hf ⟨hiso⟩
  refine ⟨Z, hZ, ?_⟩
  exact hisocomp

end Submission.Models
