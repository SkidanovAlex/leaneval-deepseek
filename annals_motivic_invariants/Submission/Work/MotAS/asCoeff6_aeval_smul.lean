import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.aeval_asCoeff6
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.asRuleMinP_isHomogeneous
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asCoeff6_aeval_smul`

`asCoeff6 S a b g j` is a form of degree `6` in the five AS Galois coordinates `X₀,…,X₄`
(`Submission/Work/MotAS/AsCoeff6Defs.lean`): it is the `T^j`-coefficient of
`kleinRAS0 (C a) (C b) (C g) (A + T·B)` where `A`, `B` are the two quadratic ruling vectors.
This file proves the corresponding **dilation law**: evaluating at `fun i => s * x i` multiplies
the evaluation at `x` by `s ^ 6`.

## Route

Writing `Φ s = (MvPolynomial.aeval fun j => C s * X j).toRingHom` for the dilation endomorphism of
the coordinate ring, the argument is

* `asCoeff6_qAS_A_dil`, `asCoeff6_qAS_B_dil`: `Φ s` sends the quadratic ruling vectors `qAS_A`,
  `qAS_B` to `C (s²) · qAS_A`, `C (s²) · qAS_B` — this is the naturality `map_asRuleQA` under the
  ring hom `Φ s` combined with the quadraticity `as_hom_asRuleQA_smul` of the ruling vectors
  (`Submission/Work/MotAS/asRuleMinP_isHomogeneous.lean`);
* `asCoeff6_map_kleinRAS0`: naturality of `kleinRAS0` over a polynomial ring under
  `Polynomial.map` (`Work.MotAS.map_kleinRAS0`);
* `asCoeff6_poly_dil`: consequently `Polynomial.map (Φ s) (asCoeffPoly S a b g)` is
  `C (C (s⁶)) * asCoeffPoly S a b g`, since `kleinRAS0` is a cubic form (`kleinRAS0_smul`);
* reading off the `T^j`-coefficient (`Polynomial.coeff_map`) gives
  `Φ s (asCoeff6 j) = C (s⁶) · asCoeff6 j`, and finally `Φ s` is right-composed with `aeval x`
  using `MvPolynomial.aeval_bind₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

section Dilate

variable {S : Type*} [CommRing S]

/-- The dilation `X i ↦ C s * X i`, read as a ring hom. -/
theorem asCoeff6_asEval_dil_apply (s : S) (p : MvPolynomial (Fin 5) S) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom p
      = MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j) p := rfl

/-- The dilation `X i ↦ C s * X i` fixes the constants. -/
theorem asCoeff6_asEval_dil_C (s r : S) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (MvPolynomial.C r)
      = MvPolynomial.C r := by
  rw [asCoeff6_asEval_dil_apply, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- The dilation `X i ↦ C s * X i` acts on the coordinate `X k` by multiplication by `C s`. -/
theorem asCoeff6_asEval_dil_X (s : S) (k : Fin 5) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (MvPolynomial.X k : MvPolynomial (Fin 5) S)
      = MvPolynomial.C s * MvPolynomial.X k := by
  rw [asCoeff6_asEval_dil_apply, MvPolynomial.aeval_X]

/-- **The first ruling vector is a quadratic form**: the dilation sends `qAS_A` to `C (s²) · qAS_A`. -/
theorem asCoeff6_qAS_A_dil (a b g s : S) (i : Fin 5) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (qAS_A S a b g i)
      = MvPolynomial.C (s ^ 2) * qAS_A S a b g i := by
  have h := Work.MotAS.map_asRuleQA
      (φ := (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j) :
        MvPolynomial (Fin 5) S →ₐ[S] MvPolynomial (Fin 5) S).toRingHom)
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun j => MvPolynomial.X j) i
  simp only [Work.MotAS.qAS_A] at h ⊢
  rw [h]
  simp only [asCoeff6_asEval_dil_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [← MvPolynomial.C_eq_algebraMap]
  simp only [map_pow]
  rw [Work.MotAS.as_hom_asRuleQA_smul]

/-- **The second ruling vector is a quadratic form.** -/
theorem asCoeff6_qAS_B_dil (a b g s : S) (i : Fin 5) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (qAS_B S a b g i)
      = MvPolynomial.C (s ^ 2) * qAS_B S a b g i := by
  have h := Work.MotAS.map_asRuleQB
      (φ := (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j) :
        MvPolynomial (Fin 5) S →ₐ[S] MvPolynomial (Fin 5) S).toRingHom)
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun j => MvPolynomial.X j) i
  simp only [Work.MotAS.qAS_B] at h ⊢
  rw [h]
  simp only [asCoeff6_asEval_dil_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [← MvPolynomial.C_eq_algebraMap]
  simp only [map_pow]
  rw [Work.MotAS.as_hom_asRuleQB_smul]

/-- **Naturality of `kleinRAS0` over a polynomial ring** under `Polynomial.map`. -/
theorem asCoeff6_map_kleinRAS0 {A B : Type*} [CommRing A] [CommRing B] (Φ : A →+* B)
    (a b g : A) (z : Fin 5 → Polynomial A) :
    Polynomial.map Φ (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z)
      = kleinRAS0 (Polynomial.C (Φ a)) (Polynomial.C (Φ b)) (Polynomial.C (Φ g))
          (fun k => Polynomial.map Φ (z k)) := by
  have h := Work.MotAS.map_kleinRAS0 (R := Polynomial A) (S := Polynomial B)
    (Polynomial.mapRingHom Φ) (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using h.symm

/-- **The dilation law for `asCoeffPoly`**: `kleinRAS0` is a cubic form in the ruling data, and
each of `A`, `B` is a quadratic form, so the dilation of the coefficients by `s` produces `s⁶`. -/
theorem asCoeff6_poly_dil (a b g s : S) :
    Polynomial.map (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (asCoeffPoly S a b g)
      = Polynomial.C (MvPolynomial.C (s ^ 6)) * asCoeffPoly S a b g := by
  have hF : (fun k => Polynomial.map
        (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k)))
      = fun k => Polynomial.C (MvPolynomial.C (s ^ 2)) *
          (Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k)) := by
    funext k
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      asCoeff6_qAS_A_dil, asCoeff6_qAS_B_dil, Polynomial.C_mul]
    first | refl_ring1 | ring
  have hkey := asCoeff6_map_kleinRAS0
    (Φ := (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom)
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun k => Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k))
  rw [show asCoeffPoly S a b g = kleinRAS0 (Polynomial.C (MvPolynomial.C a))
        (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C g))
        (fun k => Polynomial.C (qAS_A S a b g k) + Polynomial.X * Polynomial.C (qAS_B S a b g k))
      from rfl]
  rw [hkey, asCoeff6_asEval_dil_C s a, asCoeff6_asEval_dil_C s b, asCoeff6_asEval_dil_C s g, hF]
  rw [kleinRAS0_smul]
  rw [show (Polynomial.C (MvPolynomial.C (s ^ 2)) : Polynomial (MvPolynomial (Fin 5) S)) ^ 3
      = Polynomial.C (MvPolynomial.C (s ^ 6)) from by
        rw [← map_pow, ← map_pow, show (s ^ 2) ^ 3 = s ^ 6 from by ring]]

/-- Evaluating a constant multiple of a polynomial multiplies the evaluation. -/
theorem asCoeff6_aeval_C_mul (x : Fin 5 → S) (r : S) (f : MvPolynomial (Fin 5) S) :
    MvPolynomial.aeval x (MvPolynomial.C r * f) = r * MvPolynomial.aeval x f := by
  rw [map_mul, MvPolynomial.aeval_C]
  simp

/-- **The dilation law for `asCoeff6`**: `Φ s (asCoeff6 j) = C (s⁶) · asCoeff6 j`. -/
theorem asCoeff6_dil (a b g s : S) (j : ℕ) :
    (MvPolynomial.aeval (fun j : Fin 5 => MvPolynomial.C s * MvPolynomial.X j)).toRingHom
        (asCoeff6 S a b g j)
      = MvPolynomial.C (s ^ 6) * asCoeff6 S a b g j := by
  have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 5) S) => p.coeff j)
    (asCoeff6_poly_dil (S := S) a b g s)
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, ← asCoeff6_eq] at h
  exact h

/-- The dilation composed with an evaluation is the evaluation at the dilated point. -/
theorem asCoeff6_aeval_dil_comp (a b g s : S) (x : Fin 5 → S) (j : ℕ) :
    MvPolynomial.aeval x
        ((MvPolynomial.aeval (fun i : Fin 5 => MvPolynomial.C s * MvPolynomial.X i)).toRingHom
          (asCoeff6 S a b g j))
      = MvPolynomial.aeval (fun i => s * x i) (asCoeff6 S a b g j) := by
  rw [asCoeff6_asEval_dil_apply]
  rw [MvPolynomial.aeval_eq_bind₁ (fun i : Fin 5 => MvPolynomial.C s * MvPolynomial.X i),
    MvPolynomial.aeval_bind₁]
  rw [show (fun i : Fin 5 => MvPolynomial.aeval x (MvPolynomial.C s * MvPolynomial.X i))
      = fun i => s * x i from by
        funext i
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        simp]

end Dilate

theorem asCoeff6_aeval_smul {S : Type*} [CommRing S] (a b g s : S) (x : Fin 5 → S) (j : ℕ) :
    MvPolynomial.aeval (fun i => s * x i) (Work.MotAS.asCoeff6 S a b g j)
      = s ^ 6 * MvPolynomial.aeval x (Work.MotAS.asCoeff6 S a b g j) := by
  have h2 : MvPolynomial.aeval (fun i => s * x i) (asCoeff6 S a b g j)
      = MvPolynomial.aeval x (MvPolynomial.C (s ^ 6) * asCoeff6 S a b g j) := by
    rw [← asCoeff6_aeval_dil_comp (S := S) a b g s x j]
    exact congrArg (MvPolynomial.aeval x) (asCoeff6_dil (S := S) a b g s j)
  rw [asCoeff6_aeval_C_mul] at h2
  exact h2

end Work.MotAS
