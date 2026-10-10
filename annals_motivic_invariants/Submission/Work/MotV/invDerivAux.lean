import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial MvPolynomial
open scoped Polynomial.Bivariate

namespace Work.MotV

namespace FracDeriv

open IsLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsDomain A]

/-- The candidate for the value of the extension of `d` at `z`, computed from the canonical
representative `IsLocalization.sec` of `z`. -/
noncomputable def extVal (d : Derivation R A A) (z : FractionRing A) : FractionRing A :=
  ((algebraMap A (FractionRing A) (d (IsLocalization.sec (nonZeroDivisors A) z).1)) *
      (algebraMap A (FractionRing A) ((IsLocalization.sec (nonZeroDivisors A) z).2 : A)) -
    (algebraMap A (FractionRing A) (IsLocalization.sec (nonZeroDivisors A) z).1) *
      (algebraMap A (FractionRing A) (d ((IsLocalization.sec (nonZeroDivisors A) z).2 : A)))) /
  (algebraMap A (FractionRing A) ((IsLocalization.sec (nonZeroDivisors A) z).2 : A)) ^ 2

lemma nz_coe (s : nonZeroDivisors A) : (s : A) ≠ 0 :=
  fun hz => one_ne_zero ((mem_nonZeroDivisors_iff.mp s.2).1 1 (by rw [hz, zero_mul]))

lemma nz_map (s : nonZeroDivisors A) : algebraMap A (FractionRing A) (s : A) ≠ 0 := by
  intro hz
  exact nz_coe s (IsFractionRing.injective A (FractionRing A) (by simpa using hz))

/-- `extVal` depends only on `z`, not on the chosen representative `z = a / s`. -/
lemma extVal_eq (d : Derivation R A A) (z : FractionRing A) (a : A) (s : nonZeroDivisors A)
    (h : z * algebraMap A (FractionRing A) (s : A) = algebraMap A (FractionRing A) a) :
    extVal d z = ((algebraMap A (FractionRing A) (d a)) * (algebraMap A (FractionRing A) (s : A)) -
      (algebraMap A (FractionRing A) a) * (algebraMap A (FractionRing A) (d (s : A)))) /
      (algebraMap A (FractionRing A) (s : A)) ^ 2 := by
  set s0 := IsLocalization.sec (nonZeroDivisors A) z with hs0def
  have hs0 : z * algebraMap A (FractionRing A) ((s0.2 : nonZeroDivisors A) : A) =
      algebraMap A (FractionRing A) s0.1 := IsLocalization.sec_spec _ _
  have hval : extVal d z =
      ((algebraMap A (FractionRing A) (d s0.1)) *
          (algebraMap A (FractionRing A) ((s0.2 : nonZeroDivisors A) : A)) -
        (algebraMap A (FractionRing A) s0.1) *
          (algebraMap A (FractionRing A) (d ((s0.2 : nonZeroDivisors A) : A)))) /
      (algebraMap A (FractionRing A) ((s0.2 : nonZeroDivisors A) : A)) ^ 2 := by
    rw [extVal, ← hs0def]
  rw [hval]
  have hab : a * (s0.2 : A) = s0.1 * (s : A) := by
    rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff]
    rw [map_mul, map_mul, ← h, ← hs0]
    first | refl_ring1 | ring
  have h2 : d a * (s0.2 : A) + a * d (s0.2 : A) = d s0.1 * (s : A) + s0.1 * d (s : A) := by
    have hh := congrArg (fun x => d x) hab
    rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hh
    linear_combination (norm := first | refl_ring1 | ring1) hh
  have h4 : a * (s0.2 : A) - s0.1 * (s : A) = 0 := sub_eq_zero.mpr hab
  have h3 : (d a * (s0.2 : A) + a * d (s0.2 : A)) * ((s : A) * (s0.2 : A))
      = (d s0.1 * (s : A) + s0.1 * d (s : A)) * ((s : A) * (s0.2 : A)) := by rw [h2]
  have hkey : (d a * (s : A) - a * d (s : A)) * (s0.2 : A)^2
      = (d s0.1 * (s0.2 : A) - s0.1 * d (s0.2 : A)) * (s : A)^2 := by
    linear_combination (norm := first | refl_ring1 | ring1) h3 - ((s : A) * d (s0.2 : A) + (s0.2 : A) * d (s : A)) * h4
  have hkeyK : (algebraMap A (FractionRing A) (d a) * algebraMap A (FractionRing A) (s : A) -
        algebraMap A (FractionRing A) a * algebraMap A (FractionRing A) (d (s : A))) *
        (algebraMap A (FractionRing A) ((s0.2 : nonZeroDivisors A) : A)) ^ 2
      = (algebraMap A (FractionRing A) (d s0.1) *
            algebraMap A (FractionRing A) ((s0.2 : nonZeroDivisors A) : A) -
          algebraMap A (FractionRing A) s0.1 *
            algebraMap A (FractionRing A) (d ((s0.2 : nonZeroDivisors A) : A))) *
        (algebraMap A (FractionRing A) (s : A)) ^ 2 := by
    have hh := congrArg (algebraMap A (FractionRing A)) hkey
    simpa only [map_mul, map_sub, map_pow] using hh
  rw [div_eq_div_iff (pow_ne_zero 2 (nz_map s0.2)) (pow_ne_zero 2 (nz_map s))]
  exact hkeyK.symm

lemma extVal_algebraMap (d : Derivation R A A) (a : A) :
    extVal d (algebraMap A (FractionRing A) a) = algebraMap A (FractionRing A) (d a) := by
  rw [extVal_eq d _ a 1 (by rw [Submonoid.coe_one, map_one, mul_one])]
  simp

lemma extVal_add (d : Derivation R A A) (z w : FractionRing A) :
    extVal d (z + w) = extVal d z + extVal d w := by
  obtain ⟨a, s, hz⟩ : ∃ (a : A) (s : nonZeroDivisors A),
      z * algebraMap A (FractionRing A) (s : A) = algebraMap A (FractionRing A) a :=
    ⟨(IsLocalization.sec (nonZeroDivisors A) z).1, (IsLocalization.sec (nonZeroDivisors A) z).2,
      IsLocalization.sec_spec _ _⟩
  obtain ⟨b, t, hw⟩ : ∃ (b : A) (t : nonZeroDivisors A),
      w * algebraMap A (FractionRing A) (t : A) = algebraMap A (FractionRing A) b :=
    ⟨(IsLocalization.sec (nonZeroDivisors A) w).1, (IsLocalization.sec (nonZeroDivisors A) w).2,
      IsLocalization.sec_spec _ _⟩
  have hzw : (z + w) * algebraMap A (FractionRing A)
        ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A)
      = algebraMap A (FractionRing A) (a * (t : A) + b * (s : A)) := by
    rw [show ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A) = (s : A) * (t : A)
      from rfl]
    simp only [map_mul, map_add]
    linear_combination (norm := first | refl_ring1 | ring1) (algebraMap A (FractionRing A) (t : A)) * hz +
      (algebraMap A (FractionRing A) (s : A)) * hw
  have hA : d (a * (t : A) + b * (s : A)) * ((s : A) * (t : A)) -
        (a * (t : A) + b * (s : A)) * d ((s : A) * (t : A))
      = (d a * (s : A) - a * d (s : A)) * (t : A)^2 +
        (d b * (t : A) - b * d (t : A)) * (s : A)^2 := by
    rw [Derivation.map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
    first | refl_ring1 | ring
  have hAK : (algebraMap A (FractionRing A) (d (a * (t : A) + b * (s : A)))) *
          (algebraMap A (FractionRing A) ((s : A) * (t : A))) -
        (algebraMap A (FractionRing A) (a * (t : A) + b * (s : A))) *
          (algebraMap A (FractionRing A) (d ((s : A) * (t : A))))
      = ((algebraMap A (FractionRing A) (d a) * algebraMap A (FractionRing A) (s : A) -
            algebraMap A (FractionRing A) a * algebraMap A (FractionRing A) (d (s : A))) *
            (algebraMap A (FractionRing A) (t : A))^2 +
          (algebraMap A (FractionRing A) (d b) * algebraMap A (FractionRing A) (t : A) -
            algebraMap A (FractionRing A) b * algebraMap A (FractionRing A) (d (t : A))) *
            (algebraMap A (FractionRing A) (s : A))^2) := by
    have hh := congrArg (algebraMap A (FractionRing A)) hA
    simpa only [map_mul, map_sub, map_add, map_pow] using hh
  rw [extVal_eq d z a s hz, extVal_eq d w b t hw, extVal_eq d (z + w) _ _ hzw]
  rw [show ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A) = (s : A) * (t : A)
    from rfl]
  rw [hAK, map_mul, mul_pow]
  rw [div_add_div _ _ (pow_ne_zero 2 (nz_map s)) (pow_ne_zero 2 (nz_map t))]
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 (nz_map s)) (pow_ne_zero 2 (nz_map t)))
    (mul_ne_zero (pow_ne_zero 2 (nz_map s)) (pow_ne_zero 2 (nz_map t)))]
  first | refl_ring1 | ring

lemma extVal_mul (d : Derivation R A A) (z w : FractionRing A) :
    extVal d (z * w) = z * extVal d w + w * extVal d z := by
  obtain ⟨a, s, hz⟩ : ∃ (a : A) (s : nonZeroDivisors A),
      z * algebraMap A (FractionRing A) (s : A) = algebraMap A (FractionRing A) a :=
    ⟨(IsLocalization.sec (nonZeroDivisors A) z).1, (IsLocalization.sec (nonZeroDivisors A) z).2,
      IsLocalization.sec_spec _ _⟩
  obtain ⟨b, t, hw⟩ : ∃ (b : A) (t : nonZeroDivisors A),
      w * algebraMap A (FractionRing A) (t : A) = algebraMap A (FractionRing A) b :=
    ⟨(IsLocalization.sec (nonZeroDivisors A) w).1, (IsLocalization.sec (nonZeroDivisors A) w).2,
      IsLocalization.sec_spec _ _⟩
  have hzw : (z * w) * algebraMap A (FractionRing A)
        ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A)
      = algebraMap A (FractionRing A) (a * b) := by
    rw [show ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A) = (s : A) * (t : A)
      from rfl, map_mul, map_mul]
    linear_combination (norm := first | refl_ring1 | ring1) (w * algebraMap A (FractionRing A) (t : A)) * hz +
      (algebraMap A (FractionRing A) a) * hw
  have hA : d (a * b) * ((s : A) * (t : A)) - (a * b) * d ((s : A) * (t : A))
      = a * (d b * (t : A) - b * d (t : A)) * (s : A) +
        b * (d a * (s : A) - a * d (s : A)) * (t : A) := by
    rw [Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
    first | refl_ring1 | ring
  have hAK : (algebraMap A (FractionRing A) (d (a * b))) *
          (algebraMap A (FractionRing A) ((s : A) * (t : A))) -
        (algebraMap A (FractionRing A) (a * b)) *
          (algebraMap A (FractionRing A) (d ((s : A) * (t : A))))
      = (algebraMap A (FractionRing A) a) *
            ((algebraMap A (FractionRing A) (d b)) * (algebraMap A (FractionRing A) (t : A)) -
              (algebraMap A (FractionRing A) b) * (algebraMap A (FractionRing A) (d (t : A)))) *
            (algebraMap A (FractionRing A) (s : A)) +
          (algebraMap A (FractionRing A) b) *
            ((algebraMap A (FractionRing A) (d a)) * (algebraMap A (FractionRing A) (s : A)) -
              (algebraMap A (FractionRing A) a) * (algebraMap A (FractionRing A) (d (s : A)))) *
            (algebraMap A (FractionRing A) (t : A)) := by
    have hh := congrArg (algebraMap A (FractionRing A)) hA
    simpa only [map_mul, map_sub, map_add, map_pow] using hh
  have hz' : z = (algebraMap A (FractionRing A) a) / (algebraMap A (FractionRing A) (s : A)) :=
    (eq_div_iff (nz_map s)).mpr hz
  have hw' : w = (algebraMap A (FractionRing A) b) / (algebraMap A (FractionRing A) (t : A)) :=
    (eq_div_iff (nz_map t)).mpr hw
  rw [extVal_eq d (z * w) (a * b) ⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ hzw,
    extVal_eq d w b t hw, extVal_eq d z a s hz]
  rw [show ((⟨(s : A) * (t : A), mul_mem s.2 t.2⟩ : nonZeroDivisors A) : A) = (s : A) * (t : A)
    from rfl]
  rw [hAK, map_mul, mul_pow, hz', hw']
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [div_add_div _ _ (mul_ne_zero (nz_map s) (pow_ne_zero 2 (nz_map t)))
    (mul_ne_zero (nz_map t) (pow_ne_zero 2 (nz_map s)))]
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 (nz_map s)) (pow_ne_zero 2 (nz_map t)))
    (mul_ne_zero (mul_ne_zero (nz_map s) (pow_ne_zero 2 (nz_map t)))
      (mul_ne_zero (nz_map t) (pow_ne_zero 2 (nz_map s))))]
  first | refl_ring1 | ring

lemma extVal_smul (d : Derivation R A A) (r : R) (z : FractionRing A) :
    extVal d (r • z) = r • extVal d z := by
  rw [Algebra.smul_def]
  rw [extVal_mul, IsScalarTower.algebraMap_apply R A (FractionRing A),
    extVal_algebraMap, Derivation.map_algebraMap, map_zero, mul_zero, add_zero]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R A (FractionRing A)]

/-- **A derivation on a domain extends to its fraction field.** -/
theorem exists_deriv_fractionRing (d : Derivation R A A) :
    ∃ D : Derivation R (FractionRing A) (FractionRing A),
      ∀ a : A, D (algebraMap A (FractionRing A) a) = algebraMap A (FractionRing A) (d a) := by
  refine ⟨Derivation.mk'
    { toFun := extVal d, map_add' := extVal_add d, map_smul' := extVal_smul d } ?_,
    extVal_algebraMap d⟩
  intro a b
  change extVal d (a * b) = a • extVal d b + b • extVal d a
  rw [extVal_mul, smul_eq_mul, smul_eq_mul]

end FracDeriv

namespace BivDeriv

set_option maxHeartbeats 1000000

/-- Conjugation of a derivation by an algebra equivalence. -/
noncomputable def conjAlgEquiv {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (d : Derivation R A A) : Derivation R B B :=
  Derivation.mk'
    { toFun := fun b => e (d (e.symm b))
      map_add' := by intro x y; simp [map_add]
      map_smul' := by intro x y; simp [map_smul] }
    (by
      intro x y
      change e (d (e.symm (x * y))) = x • e (d (e.symm y)) + y • e (d (e.symm x))
      simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul, AlgEquiv.apply_symm_apply])

/-- **The invariant derivation on the bivariate Weierstrass polynomial ring.**  It sends the
coordinate `X` to `∂W/∂Y` and `Y` to `-∂W/∂X`, and kills `W`. -/
theorem exists_deriv_bivariate {N : Type*} [Field N] (E : WeierstrassCurve N) :
    ∃ d : Derivation N (Polynomial (Polynomial N)) (Polynomial (Polynomial N)),
      d (Polynomial.C Polynomial.X) = WeierstrassCurve.Affine.polynomialY E ∧
      d Polynomial.X = -(WeierstrassCurve.Affine.polynomialX E) ∧
      d (WeierstrassCurve.Affine.polynomial E) = 0 := by
  let e : Polynomial (Polynomial N) ≃ₐ[N] MvPolynomial (Fin 2) N :=
    Polynomial.Bivariate.equivMvPolynomial N
  have hpd0 : MvPolynomial.pderiv 0 (e (WeierstrassCurve.Affine.polynomial E)) =
      e (WeierstrassCurve.Affine.polynomialX E) := by
    dsimp only [e]
    rw [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialX]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.Bivariate.equivMvPolynomial_C_C,
      Polynomial.Bivariate.equivMvPolynomial_C_X, Polynomial.Bivariate.equivMvPolynomial_X,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
      MvPolynomial.pderiv_X]
    simp
    ring_nf
    simp [map_ofNat]
  have hpd1 : MvPolynomial.pderiv 1 (e (WeierstrassCurve.Affine.polynomial E)) =
      e (WeierstrassCurve.Affine.polynomialY E) := by
    dsimp only [e]
    rw [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialY]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.Bivariate.equivMvPolynomial_C_C,
      Polynomial.Bivariate.equivMvPolynomial_C_X, Polynomial.Bivariate.equivMvPolynomial_X,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
      MvPolynomial.pderiv_X]
    simp
    ring_nf
    simp [map_ofNat]
  let g : Derivation N (MvPolynomial (Fin 2) N) (MvPolynomial (Fin 2) N) :=
    (MvPolynomial.pderiv 1 (e (WeierstrassCurve.Affine.polynomial E))) • (MvPolynomial.pderiv 0) -
      (MvPolynomial.pderiv 0 (e (WeierstrassCurve.Affine.polynomial E))) • (MvPolynomial.pderiv 1)
  have hg0 : g (MvPolynomial.X 0) = e (WeierstrassCurve.Affine.polynomialY E) := by
    simp only [g, Derivation.sub_apply, Derivation.smul_apply, MvPolynomial.pderiv_X]
    rw [hpd1, hpd0]
    simp
  have hg1 : g (MvPolynomial.X 1) = -(e (WeierstrassCurve.Affine.polynomialX E)) := by
    simp only [g, Derivation.sub_apply, Derivation.smul_apply, MvPolynomial.pderiv_X]
    rw [hpd1, hpd0]
    simp
  have hgW : g (e (WeierstrassCurve.Affine.polynomial E)) = 0 := by
    simp only [g, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    rw [hpd1, hpd0]
    first | refl_ring1 | ring
  refine ⟨conjAlgEquiv e.symm g, ?_, ?_, ?_⟩
  · change e.symm (g (e (Polynomial.C Polynomial.X))) = WeierstrassCurve.Affine.polynomialY E
    rw [show e (Polynomial.C Polynomial.X) = MvPolynomial.X 0 from
      Polynomial.Bivariate.equivMvPolynomial_C_X, hg0]
    exact e.symm_apply_apply _
  · change e.symm (g (e Polynomial.X)) = -(WeierstrassCurve.Affine.polynomialX E)
    rw [show e Polynomial.X = MvPolynomial.X 1 from
      Polynomial.Bivariate.equivMvPolynomial_X, hg1, map_neg, AlgEquiv.symm_apply_apply]
  · change e.symm (g (e (WeierstrassCurve.Affine.polynomial E))) = 0
    rw [hgW, map_zero]

end BivDeriv

end Work.MotV
