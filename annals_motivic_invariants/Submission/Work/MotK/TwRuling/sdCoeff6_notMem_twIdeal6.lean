import Mathlib
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.MotK.KleinTwPMapApply
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MotK.TwRuling

open MvPolynomial

/-! ## 0. Polynomial coefficient bookkeeping

The `T³`-coefficient of a product of polynomials of degree `≤ 1` is the product of their
`T¹`-coefficients, and `kleinTwR0` is a cubic form in its last argument, so substituting
`y k = C (u k) + T * C (v k)` and taking the coefficient of `T³` recovers `kleinTwR0 a b h v`. -/

theorem coeff_mul_of_natDegree_le {A : Type*} [CommRing A] {f g : Polynomial A} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (f * g).coeff (m + n) = f.coeff m * g.coeff n := by
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f.coeff i * g.coeff j)]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i hi hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : g.coeff (m + n - i) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [this]
    · have : f.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [this]
  · intro hm
    simp at hm

theorem lin_natDegree {A : Type*} [CommRing A] (u v : A) :
    (Polynomial.C u + Polynomial.X * Polynomial.C v).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_C, Polynomial.coeff_X]
  simp only [show ¬(N = 0) by omega, ite_false, show ¬(1 = N) by omega]
  first | refl_ring1 | ring

theorem lin_coeff_one {A : Type*} [CommRing A] (u v : A) :
    (Polynomial.C u + Polynomial.X * Polynomial.C v).coeff 1 = v := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_C, Polynomial.coeff_X]
  simp

/-- The `T³`-coefficient of `C c * (Y₁ * (Y₂ * Y₃))` where each `Yᵢ` is a linear polynomial. -/
theorem coeff3_C_prod3 {A : Type*} [CommRing A] (c u1 v1 u2 v2 u3 v3 : A) :
    (Polynomial.C c *
      ((Polynomial.C u1 + Polynomial.X * Polynomial.C v1)
        * ((Polynomial.C u2 + Polynomial.X * Polynomial.C v2)
          * (Polynomial.C u3 + Polynomial.X * Polynomial.C v3)))).coeff 3
      = c * (v1 * v2 * v3) := by
  rw [Polynomial.coeff_C_mul]
  rw [coeff_mul_of_natDegree_le (m := 1) (n := 2) (lin_natDegree u1 v1)
      (Polynomial.natDegree_mul_le.trans (by
        have h1 := lin_natDegree u2 v2
        have h2 := lin_natDegree u3 v3
        omega))]
  rw [coeff_mul_of_natDegree_le (m := 1) (n := 1) (lin_natDegree u2 v2) (lin_natDegree u3 v3)]
  simp only [lin_coeff_one]
  first | refl_ring1 | ring

/-- `kleinTwR0` is homogeneous of degree `3` in its last argument: substituting the linear
polynomials `C (u k) + T * C (v k)` and taking the coefficient of `T³` gives
`kleinTwR0 a b h v` in the coefficient ring. -/
theorem coeff3_kleinTwR0 {A : Type*} [CommRing A] (a b h : A) (u v : Fin 5 → A) :
    (Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
      (fun k => Polynomial.C (u k) + Polynomial.X * Polynomial.C (v k))).coeff 3
      = Work.MotK.kleinTwR0 a b h v := by
  simp only [Work.MotK.kleinTwR0, Polynomial.coeff_sub, Polynomial.coeff_add, pow_two, pow_three]
  simp only [← mul_assoc]
  simp only [← Polynomial.C_pow, ← Polynomial.C_mul, ← Polynomial.C_neg]
  simp only [mul_assoc]
  rw [coeff3_C_prod3, coeff3_C_prod3, coeff3_C_prod3, coeff3_C_prod3, coeff3_C_prod3,
    coeff3_C_prod3, coeff3_C_prod3]
  first | refl_ring1 | ring

/-! ## 1. `sdCoeff6 L a b h 3` is the cubic `kleinTwR0` applied to `qB`

`coeffPoly` is the cubic form `kleinTwR0 (C a) (C b) (C h)` evaluated at the linear polynomials
`y k = C (qA k) + T * C (qB k)`, so its `T³`-coefficient is `kleinTwR0 (C a) (C b) (C h) qB`. -/

theorem sdCoeff6_three_eq (R : Type*) [CommRing R] (a b h : R) :
    sdCoeff6 R a b h 3
      = Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (qB R a b h) := by
  rw [sdCoeff6_eq, coeffPoly]
  exact coeff3_kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (qA R a b h) (qB R a b h)

/-! ## 2. Naturality of `kleinTwR0` and evaluation of `MvPolynomial.aeval` on constants -/

theorem aeval_C_alg {A : Type*} [CommSemiring A] (z : Fin 5 → A) (r : A) :
    MvPolynomial.aeval z (MvPolynomial.C r : MvPolynomial (Fin 5) A) = r := by
  rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]

theorem aeval_X_alg {A : Type*} [CommSemiring A] (z : Fin 5 → A) (i : Fin 5) :
    MvPolynomial.aeval z (MvPolynomial.X i : MvPolynomial (Fin 5) A) = z i :=
  MvPolynomial.aeval_X z i

theorem aeval_C_toRingHom {A : Type*} [CommSemiring A] (z : Fin 5 → A) (r : A) :
    (MvPolynomial.aeval z).toRingHom (MvPolynomial.C r : MvPolynomial (Fin 5) A) = r := by
  show MvPolynomial.aeval z (MvPolynomial.C r) = r
  rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]

theorem aeval_X_toRingHom {A : Type*} [CommSemiring A] (z : Fin 5 → A) (i : Fin 5) :
    (MvPolynomial.aeval z).toRingHom (MvPolynomial.X i : MvPolynomial (Fin 5) A) = z i := by
  show MvPolynomial.aeval z (MvPolynomial.X i) = z i
  rw [MvPolynomial.aeval_X]

/-- `MvPolynomial.aeval` commutes with the standard basis vectors of `R⁵`
(they are `0`-`1` constants, fixed by the algebra map). -/
theorem aeval_kleinE {A : Type*} [CommRing A] (z : Fin 5 → A) (k i : Fin 5) :
    MvPolynomial.aeval z (Work.MotK.kleinE (R := MvPolynomial (Fin 5) A) k i) =
      Work.MotK.kleinE (R := A) k i := by
  simp only [Work.MotK.kleinE, Pi.single_apply]
  split <;> simp

theorem kleinTwR0_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (y : Fin 5 → R) :
    φ (Work.MotK.kleinTwR0 a b h y)
      = Work.MotK.kleinTwR0 (φ a) (φ b) (φ h) (fun k => φ (y k)) := by
  simp only [Work.MotK.kleinTwR0, map_add, map_sub, map_mul, map_pow, map_neg]

theorem aeval_kleinTwR0_C {A : Type*} [CommRing A] (a b h : A) (z : Fin 5 → A)
    (y : Fin 5 → MvPolynomial (Fin 5) A) :
    MvPolynomial.aeval z (Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C h) y)
      = Work.MotK.kleinTwR0 a b h (fun k => MvPolynomial.aeval z (y k)) := by
  have h := kleinTwR0_map (R := MvPolynomial (Fin 5) A) (S := A)
    ((MvPolynomial.aeval z).toRingHom) (MvPolynomial.C a) (MvPolynomial.C b)
    (MvPolynomial.C h) y
  simp only [aeval_C_toRingHom] at h
  simpa using h

/-! ## 3. The evaluated point `z` and the five values of `qB` at `z` -/

/-- The explicit evaluation point `z = (a·h·α, 0, a·h·α², b, b·h·α³)`. -/
def zpt (L : Type*) [CommRing L] (a b h α : L) : Fin 5 → L :=
  ![a * h * α, 0, a * h * α ^ 2, b, b * h * α ^ 3]

/-- The five values of the second ruling vector `qB` at `z`. -/
theorem aeval_qB (L : Type*) [Field L] (a b h α : L) :
    ∀ k : Fin 5,
      MvPolynomial.aeval (zpt L a b h α) (qB L a b h k)
      = ![0, -(3 * a ^ 4 * α ^ 3 * b ^ 2 * h ^ 2), -(a ^ 2 * b ^ 4 * h),
          -(3 * a ^ 3 * α ^ 2 * b ^ 3 * h ^ 2),
          -(2 * a ^ 2 * α ^ 4 * b ^ 4 * h ^ 3)] k := by
  intro k
  rw [qB_apply]
  unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP Work.MotK.kleinTwP0
    Work.MotK.kleinTwP1 Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 zpt
  fin_cases k <;>
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, aeval_C_alg,
      aeval_X_alg, aeval_kleinE, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_succ, Fin.isValue] <;>
    simp only [Work.MotK.kleinE, Pi.single_apply, Fin.isValue] <;>
    norm_num <;> ring

/-! ## 4. The value of `aeval z (sdCoeff6 L a b h 3)` -/

theorem aeval_sdCoeff6_three (L : Type*) [Field L] (a b h α : L) (hh : h ≠ 0)
    (hα : α ^ 5 = -(1 / h ^ 2)) :
    MvPolynomial.aeval (zpt L a b h α) (sdCoeff6 L a b h 3)
      = a ^ 9 * α ^ 3 * b ^ 8 * h ^ 6 * (27 * a ^ 5 - 11 * b ^ 5) := by
  have hrel : h ^ 2 * α ^ 5 = -1 := by
    rw [hα, mul_neg, mul_one_div, div_self (pow_ne_zero 2 hh)]
  rw [sdCoeff6_three_eq]
  rw [aeval_kleinTwR0_C (A := L) a b h (zpt L a b h α) (qB L a b h)]
  rw [show (fun k => MvPolynomial.aeval (zpt L a b h α) (qB L a b h k))
      = ![0, -(3 * a ^ 4 * α ^ 3 * b ^ 2 * h ^ 2), -(a ^ 2 * b ^ 4 * h),
          -(3 * a ^ 3 * α ^ 2 * b ^ 3 * h ^ 2),
          -(2 * a ^ 2 * α ^ 4 * b ^ 4 * h ^ 3)] from
    funext (aeval_qB L a b h α)]
  simp only [Work.MotK.kleinTwR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  linear_combination (norm := ring_nf)
    (a ^ 9 * α ^ 3 * b ^ 8 * h ^ 6 * (14 * b ^ 5 - 27 * a ^ 5)) * hrel

/-! ## 5. The five twisted Pfaffians vanish at `z` -/

theorem kleinTwP_zpt (L : Type*) [Field L] (a b h α : L) (hh : h ≠ 0)
    (hα : α ^ 5 = -(1 / h ^ 2)) :
    ∀ k : Fin 5, Work.MotK.kleinTwP a b h (zpt L a b h α) k = 0 := by
  have hrel : h ^ 2 * α ^ 5 = -1 := by
    rw [hα, mul_neg, mul_one_div, div_self (pow_ne_zero 2 hh)]
  intro k
  fin_cases k <;>
    simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
      Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, zpt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Fin.isValue,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    first
      | linear_combination (-(a * b ^ 3 * h)) * hrel
      | linear_combination (-(a * b ^ 3 * h * α)) * hrel
      | ring

/-! ## 6. The evaluation of `MvPolynomial.aeval z` on `kleinTwP` -/

theorem aeval_kleinTwP_zpt (L : Type*) [Field L] (a b h α : L) (k : Fin 5) :
    MvPolynomial.aeval (zpt L a b h α) (Work.MotK.kleinTwP (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinTwP a b h (zpt L a b h α) k := by
  change (MvPolynomial.aeval (zpt L a b h α)).toRingHom
      (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun i => MvPolynomial.X i) k) = _
  rw [Work.MotK.KleinTwPMapApply (R := MvPolynomial (Fin 5) L) (S := L)
    (φ := (MvPolynomial.aeval (zpt L a b h α)).toRingHom)]
  simp only [aeval_C_toRingHom, aeval_X_toRingHom]

/-! ## 7. The theorem -/

/-- `sdCoeff6 L a b h 3 ∉ twIdeal6 L a b h` when `27a⁵ ≠ 11b⁵`.

Route: pick `α` with `α⁵ = -1/h²` (`IsAlgClosed.exists_pow_nat_eq`, `h ≠ 0`), let
`z = (a·h·α, 0, a·h·α², b, b·h·α³)`.  By `sdCoeff6_eval_family` all five `kleinTwP`'s vanish at `z`,
so `MvPolynomial.aeval z` kills every generator `kleinTwP (C a) (C b) (C h) X q.1 * monomial q.2.1 1`
of the span, hence kills the whole span; but
`MvPolynomial.aeval z (sdCoeff6 L a b h 3) = a⁹α³b⁸h⁶(27a⁵-11b⁵) ≠ 0`
(`a,b,h,α ≠ 0`; `α ≠ 0` since `α⁵ = -1/h² ≠ 0`).  Contradiction. -/
theorem sdCoeff6_notMem_twIdeal6 (L : Type*) [Field L] [IsAlgClosed L] (a b h : L)
    (hab : a * b ≠ 0) (hh : h ≠ 0) (h3 : 27 * a ^ 5 - 11 * b ^ 5 ≠ 0) :
    Work.MotK.TwRuling.sdCoeff6 L a b h 3 ∉
      Submodule.span L (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)) := by
  intro hmem
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hab
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-(1 / h ^ 2)) (by norm_num : 0 < 5)
  have hpaff := kleinTwP_zpt L a b h α hh hα
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0] at hα
    have h1 : -(1 / h ^ 2) = 0 := by
      rw [← hα]
      first | refl_ring1 | ring
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hh) (neg_eq_zero.mp h1)
  have hval : MvPolynomial.aeval (zpt L a b h α) (sdCoeff6 L a b h 3) ≠ 0 := by
    rw [aeval_sdCoeff6_three L a b h α hh hα]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) h3
    · exact pow_ne_zero 9 ha
    · exact pow_ne_zero 3 hα0
    · exact pow_ne_zero 8 hb
    · exact pow_ne_zero 6 hh
  have hker : ∀ F ∈ Submodule.span L (Set.range (fun q : Fin 5 ×
        {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)),
      MvPolynomial.aeval (zpt L a b h α) F = 0 := by
    intro F hF
    have hle : Submodule.span L (Set.range (fun q : Fin 5 ×
          {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
          Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1))
        ≤ LinearMap.ker (MvPolynomial.aeval (zpt L a b h α)).toLinearMap := by
      rw [Submodule.span_le]
      rintro G ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      show MvPolynomial.aeval (zpt L a b h α)
        (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1) = 0
      rw [map_mul, aeval_kleinTwP_zpt L a b h α q.1, hpaff q.1, zero_mul]
    exact LinearMap.mem_ker.mp (hle hF)
  exact hval (hker _ hmem)

end Work.MotK.TwRuling
