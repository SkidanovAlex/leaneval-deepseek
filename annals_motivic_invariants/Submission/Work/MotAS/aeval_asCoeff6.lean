import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.map_asRuleQW

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-!
# Evaluation of the coefficient forms of `R^AS(A + T·B)`

`asCoeff6 S a b g j` is the `T^j`-coefficient of `R^AS_0(A + T·B)` regarded as a polynomial in
`T` over the (coefficient) ring `MvPolynomial (Fin 5) S`; the `X i` are the coordinates of `c`.
The target lemma says that evaluating that coefficient at `c` (i.e. applying
`MvPolynomial.aeval c`) equals the `T^j`-coefficient of `R^AS_0` evaluated directly at
`a, b, g, c`: evaluation commutes with taking the `T`-coefficient.

The three ingredients are:
* `map_asCoeffPoly_gen` — naturality of `kleinRAS0` over a polynomial ring under `Polynomial.map`;
* `aeval_qAS_A`, `aeval_qAS_B` — `MvPolynomial.aeval c` sends the polynomial ruling vectors
  `qAS_A = asRuleQA (C a) (C b) (C g) X` to `asRuleQA a b g c` (and likewise for `B`);
* `Polynomial.coeff_map` — the coefficient of a mapped polynomial is the image of the coefficient.
-/

/-- `MvPolynomial.aeval c` commutes with the first ruling vector `qAS_A`/`asRuleQA`. -/
theorem aeval_qAS_A {S : Type*} [CommRing S] (a b g : S) (c : Fin 5 → S) (k : Fin 5) :
    MvPolynomial.aeval c (qAS_A S a b g k) = asRuleQA a b g c k := by
  rw [qAS_A]
  have h := map_asRuleQA (R := MvPolynomial (Fin 5) S) (S := S)
    (MvPolynomial.aeval c).toRingHom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => MvPolynomial.X i) k
  simpa using h

/-- `MvPolynomial.aeval c` commutes with the second ruling vector `qAS_B`/`asRuleQB`. -/
theorem aeval_qAS_B {S : Type*} [CommRing S] (a b g : S) (c : Fin 5 → S) (k : Fin 5) :
    MvPolynomial.aeval c (qAS_B S a b g k) = asRuleQB a b g c k := by
  rw [qAS_B]
  have h := map_asRuleQB (R := MvPolynomial (Fin 5) S) (S := S)
    (MvPolynomial.aeval c).toRingHom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => MvPolynomial.X i) k
  simpa using h

/-- Naturality of `kleinRAS0` over a polynomial ring: mapping the coefficients of
`kleinRAS0 (C a) (C b) (C g) z` along `Φ : A →+* B` gives `kleinRAS0` of the mapped data. -/
theorem map_asCoeffPoly_gen {A B : Type*} [CommRing A] [CommRing B] (Φ : A →+* B)
    (a b g : A) (z : Fin 5 → Polynomial A) :
    Polynomial.map Φ (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z)
      = kleinRAS0 (Polynomial.C (Φ a)) (Polynomial.C (Φ b)) (Polynomial.C (Φ g))
          (fun k => Polynomial.map Φ (z k)) := by
  have h := map_kleinRAS0 (R := Polynomial A) (S := Polynomial B) (Polynomial.mapRingHom Φ)
    (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using h.symm

/-- **Evaluation commutes with the `T`-coefficients of `asCoeffPoly`.**  `MvPolynomial.aeval c`
applied to the polynomial `asCoeffPoly S a b g` (whose coefficients are multivariable polynomials)
gives the polynomial `R^AS_0(A(c) + T·B(c))` over `S`. -/
theorem aeval_asCoeffPoly {S : Type*} [CommRing S] (a b g : S) (c : Fin 5 → S) :
    Polynomial.map (MvPolynomial.aeval c).toRingHom (asCoeffPoly S a b g)
      = kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun k => Polynomial.C (asRuleQA a b g c k)
            + Polynomial.X * Polynomial.C (asRuleQB a b g c k)) := by
  rw [asCoeffPoly]
  rw [map_asCoeffPoly_gen (MvPolynomial.aeval c).toRingHom (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g)
      (fun k => Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k))]
  have hcoe : ∀ x : MvPolynomial (Fin 5) S,
      (MvPolynomial.aeval c).toRingHom x = MvPolynomial.aeval c x := fun x => rfl
  have h1 : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C a : MvPolynomial (Fin 5) S) = a := by
    simp
  have h2 : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C b : MvPolynomial (Fin 5) S) = b := by
    simp
  have h3 : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C g : MvPolynomial (Fin 5) S) = g := by
    simp
  have hf : (fun k => Polynomial.map (MvPolynomial.aeval c).toRingHom
        (Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k)))
      = (fun k => Polynomial.C (asRuleQA a b g c k)
          + Polynomial.X * Polynomial.C (asRuleQB a b g c k)) := by
    funext k
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      hcoe, aeval_qAS_A, aeval_qAS_B]
  rw [h1, h2, h3, hf]

theorem aeval_asCoeff6 {S : Type*} [CommRing S] (a b g : S) (c : Fin 5 → S) (j : ℕ) :
    MvPolynomial.aeval c (Work.MotAS.asCoeff6 S a b g j)
      = (Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun k => Polynomial.C (Work.MotAS.asRuleQA a b g c k)
            + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB a b g c k))).coeff j := by
  have key : MvPolynomial.aeval c (asCoeff6 S a b g j)
      = (Polynomial.map (MvPolynomial.aeval c).toRingHom (asCoeffPoly S a b g)).coeff j := by
    rw [asCoeff6]
    exact (Polynomial.coeff_map (f := (MvPolynomial.aeval c).toRingHom)
      (p := asCoeffPoly S a b g) (n := j)).symm
  rw [key, aeval_asCoeffPoly]

end Work.MotAS
