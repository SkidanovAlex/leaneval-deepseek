import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The invariant derivation of a Weierstrass curve

`Work.MotV5.exists_invariantDeriv` constructs the *invariant derivation* `∂` of the function field
`N(E)` of an (affine) Weierstrass curve `E` over a field `N`, characterised by

  `∂ x = 2y + a₁x + a₃`,   `∂ y = 3x² + 2a₂x + a₄ - a₁y`.

Note that no smoothness (`E.IsElliptic`) is needed: the construction is purely formal, the
"logarithmic derivative" attached to the invariant differential `dx / (2y + a₁x + a₃)`.

## Route

1. `N[X][Y]` is presented as `MvPolynomial (Fin 2) N` via the algebra equivalence `e2`, which
   sends the outer variable `Y` to `X 0` and `C X` to `X 1`.  On the multivariable side the
   derivation `Dmv` with the prescribed values is `MvPolynomial.mkDerivation`.
2. `Dmv` kills the Weierstrass polynomial `mvW` (`Dmv_mvW`), hence descends to
   `N[X][Y]/(W) = L(E)` (`deriv_adjoinRoot_lift`).
3. The derivation extends from the domain `L(E)` to its fraction field (`deriv_extend_fractionRing`,
   the quotient rule `D(a/s) = (s·Da − a·Ds)/s²`).

## Tags

elliptic curve, function field, derivation
-/

noncomputable section

open Polynomial WeierstrassCurve.Affine

namespace Work.MotV5

/-! ## 1. The two-variable presentation of `N[X][Y]` -/

section TwoVar

variable {N : Type*} [Field N]

/-- The algebra equivalence `N[X][Y] ≃ₐ[N] N[X₀,X₁]` which sends the outer variable `Y` to `X 0`
and the inner variable `C X` to `X 1`. -/
private def e2 : Polynomial (Polynomial N) ≃ₐ[N] MvPolynomial (Fin 2) N :=
  (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv N (Fin 1)).symm).trans
    (MvPolynomial.finSuccEquiv N 1).symm

private lemma e2_X : e2 (Polynomial.X : Polynomial (Polynomial N)) = MvPolynomial.X 0 := by
  rw [show e2 (Polynomial.X : Polynomial (Polynomial N))
      = (MvPolynomial.finSuccEquiv N 1).symm (Polynomial.X) from by simp [e2]]
  exact (MvPolynomial.finSuccEquiv N 1).symm_apply_eq.mpr
    (MvPolynomial.finSuccEquiv_X_zero (R := N) (n := 1)).symm

private lemma e2_CX : e2 (Polynomial.C (Polynomial.X : Polynomial N)) = MvPolynomial.X 1 := by
  rw [show e2 (Polynomial.C (Polynomial.X : Polynomial N))
      = (MvPolynomial.finSuccEquiv N 1).symm (Polynomial.C (MvPolynomial.X (0 : Fin 1))) from by
    simp [e2]]
  exact (MvPolynomial.finSuccEquiv N 1).symm_apply_eq.mpr
    (MvPolynomial.finSuccEquiv_X_succ (R := N) (n := 1) (j := (0 : Fin 1))).symm

private lemma e2_symm_X0 :
    e2.symm (MvPolynomial.X 0) = (Polynomial.X : Polynomial (Polynomial N)) :=
  e2.symm_apply_eq.mpr e2_X.symm

private lemma e2_symm_X1 :
    e2.symm (MvPolynomial.X 1) = Polynomial.C (Polynomial.X : Polynomial N) :=
  e2.symm_apply_eq.mpr e2_CX.symm

private lemma e2_CC (a : N) : e2 (Polynomial.C (Polynomial.C a)) = MvPolynomial.C a := by
  have h1 : (Polynomial.C (Polynomial.C a) : Polynomial (Polynomial N)) = algebraMap N _ a := by
    rw [IsScalarTower.algebraMap_apply N (Polynomial N) (Polynomial (Polynomial N)),
      Polynomial.algebraMap_eq, Polynomial.algebraMap_eq]
  rw [h1, e2.commutes, MvPolynomial.algebraMap_eq]

private lemma e2_symm_C (a : N) : e2.symm (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  rw [← MvPolynomial.algebraMap_eq, e2.symm.commutes,
    IsScalarTower.algebraMap_apply N (Polynomial N) (Polynomial (Polynomial N)),
    Polynomial.algebraMap_eq, Polynomial.algebraMap_eq]

/-! ## 2. The derivation on the two-variable side -/

private noncomputable def mvF (E : WeierstrassCurve N) : MvPolynomial (Fin 2) N :=
  2 * MvPolynomial.X 0 + MvPolynomial.C E.a₁ * MvPolynomial.X 1 + MvPolynomial.C E.a₃

private noncomputable def mvG (E : WeierstrassCurve N) : MvPolynomial (Fin 2) N :=
  3 * (MvPolynomial.X 1) ^ 2 + 2 * MvPolynomial.C E.a₂ * MvPolynomial.X 1
    + MvPolynomial.C E.a₄ - MvPolynomial.C E.a₁ * MvPolynomial.X 0

private noncomputable def mvW (E : WeierstrassCurve N) : MvPolynomial (Fin 2) N :=
  (MvPolynomial.X 0) ^ 2 + (MvPolynomial.C E.a₁ * MvPolynomial.X 1 + MvPolynomial.C E.a₃)
    * MvPolynomial.X 0
    - ((MvPolynomial.X 1) ^ 3 + MvPolynomial.C E.a₂ * (MvPolynomial.X 1) ^ 2
      + MvPolynomial.C E.a₄ * MvPolynomial.X 1 + MvPolynomial.C E.a₆)

private noncomputable def Dmv (E : WeierstrassCurve N) :
    Derivation N (MvPolynomial (Fin 2) N) (MvPolynomial (Fin 2) N) :=
  MvPolynomial.mkDerivation N ![mvG E, mvF E]

private lemma Dmv_X0 (E : WeierstrassCurve N) : Dmv E (MvPolynomial.X 0) = mvG E := by
  simp [Dmv]

private lemma Dmv_X1 (E : WeierstrassCurve N) : Dmv E (MvPolynomial.X 1) = mvF E := by
  simp [Dmv]

private lemma Dmv_eq (E : WeierstrassCurve N) :
    Dmv E = mvG E • MvPolynomial.pderiv 0 + mvF E • MvPolynomial.pderiv 1 := by
  apply MvPolynomial.derivation_ext
  intro i
  fin_cases i
  · simp [Dmv_X0]
  · simp [Dmv_X1]

private lemma pderiv0_mvW (E : WeierstrassCurve N) :
    MvPolynomial.pderiv 0 (mvW E) = mvF E := by
  simp only [mvW, mvF, map_add, map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    MvPolynomial.pderiv_C, mul_zero, mul_one, add_zero, zero_mul, Nat.reduceSub, pow_one]
  first | refl_ring1 | ring

private lemma pderiv1_mvW (E : WeierstrassCurve N) :
    MvPolynomial.pderiv 1 (mvW E) = -mvG E := by
  simp only [mvW, mvG, map_add, map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
    MvPolynomial.pderiv_C, mul_zero, mul_one, add_zero, zero_mul, Nat.reduceSub, pow_one]
  first | refl_ring1 | ring

private lemma Dmv_mvW (E : WeierstrassCurve N) : Dmv E (mvW E) = 0 := by
  rw [Dmv_eq]
  simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, pderiv0_mvW, pderiv1_mvW]
  first | refl_ring1 | ring

/-! ## 3. The comparison of the Weierstrass polynomial with `mvW` -/

private lemma e2_polynomial (E : WeierstrassCurve N) : e2 (polynomial E) = mvW E := by
  rw [WeierstrassCurve.Affine.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, e2_X, e2_CX, e2_CC, Polynomial.C_add,
    Polynomial.C_mul, mvW]

private lemma e2_symm_mvF (E : WeierstrassCurve N) :
    e2.symm (mvF E) = 2 * (Polynomial.X : Polynomial (Polynomial N))
      + Polynomial.C (Polynomial.C E.a₁) * Polynomial.C (Polynomial.X : Polynomial N)
      + Polynomial.C (Polynomial.C E.a₃) := by
  rw [mvF]
  simp only [map_add, map_mul, map_ofNat, e2_symm_X0, e2_symm_X1, e2_symm_C]

private lemma e2_symm_mvG (E : WeierstrassCurve N) :
    e2.symm (mvG E) = 3 * (Polynomial.C (Polynomial.X : Polynomial N)) ^ 2
      + 2 * Polynomial.C (Polynomial.C E.a₂) * Polynomial.C (Polynomial.X : Polynomial N)
      + Polynomial.C (Polynomial.C E.a₄) - Polynomial.C (Polynomial.C E.a₁)
        * (Polynomial.X : Polynomial (Polynomial N)) := by
  rw [mvG]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, e2_symm_X0, e2_symm_X1, e2_symm_C]

/-! ## 4. Transporting the derivation to `N[X][Y]` -/

private lemma D0_kernel (E : WeierstrassCurve N) :
    ∀ x : MvPolynomial (Fin 2) N, e2.symm x = 0 → e2.symm (Dmv E x) = 0 := by
  intro x hx
  have hx0 : x = 0 := e2.symm.injective (by rw [hx, map_zero])
  subst hx0
  simp

private noncomputable def D0 (E : WeierstrassCurve N) :
    Derivation N (Polynomial (Polynomial N)) (Polynomial (Polynomial N)) :=
  Derivation.liftOfSurjective (d := Dmv E) (f := e2.symm.toAlgHom) e2.symm.surjective
    (D0_kernel E)

private lemma D0_apply_e (E : WeierstrassCurve N) (x : MvPolynomial (Fin 2) N) :
    D0 E (e2.symm x) = e2.symm (Dmv E x) :=
  Derivation.liftOfSurjective_apply (f := e2.symm.toAlgHom) e2.symm.surjective (D0_kernel E) x

private lemma D0_apply (E : WeierstrassCurve N) (z : Polynomial (Polynomial N)) :
    D0 E z = e2.symm (Dmv E (e2 z)) := by
  conv_lhs => rw [← e2.symm_apply_apply z]
  rw [D0_apply_e]

private lemma D0_polynomial (E : WeierstrassCurve N) : D0 E (polynomial E) = 0 := by
  rw [D0_apply, e2_polynomial, Dmv_mvW, map_zero]

private lemma D0_CX (E : WeierstrassCurve N) :
    D0 E (Polynomial.C (Polynomial.X : Polynomial N)) = e2.symm (mvF E) := by
  rw [← e2_symm_X1, D0_apply_e, Dmv_X1]

private lemma D0_Y (E : WeierstrassCurve N) :
    D0 E (Polynomial.X : Polynomial (Polynomial N)) = e2.symm (mvG E) := by
  rw [← e2_symm_X0, D0_apply_e, Dmv_X0]

end TwoVar

/-! ## 5. Descending a derivation to `AdjoinRoot` -/

section Adjoin

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- A derivation `d` of `A[X]` with `d p = 0` descends to the quotient `A[X]/(p) = AdjoinRoot p`. -/
private theorem deriv_adjoinRoot_lift (p : Polynomial A)
    (d : Derivation R (Polynomial A) (Polynomial A)) (hd : d p = 0) :
    ∃ D : Derivation R (AdjoinRoot p) (AdjoinRoot p),
      ∀ q : Polynomial A, D (AdjoinRoot.mk p q) = AdjoinRoot.mk p (d q) := by
  let f : Polynomial A →ₐ[R] AdjoinRoot p :=
    { toRingHom := AdjoinRoot.mk p
      commutes' := fun r => by
        change AdjoinRoot.mk p (Polynomial.C (algebraMap R A r)) = algebraMap R (AdjoinRoot p) r
        rw [AdjoinRoot.mk_C]
        exact IsScalarTower.algebraMap_apply R A (AdjoinRoot p) r }
  have hfp : f p = 0 := AdjoinRoot.mk_self
  have hf : Function.Surjective ⇑f := AdjoinRoot.mk_surjective
  have hker : ∀ x : Polynomial A, f x = 0 → f (d x) = 0 := by
    intro x hx
    have hxmem : x ∈ Ideal.span {p} := by
      have : AdjoinRoot.mk p x = 0 := hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hxmem
    rw [hq, Derivation.leibniz]
    simp only [smul_eq_mul, hd, mul_zero, add_zero, map_mul, hfp, zero_mul]
  refine ⟨Derivation.liftOfSurjective (d := d) (f := f) hf hker, fun q => ?_⟩
  change (Derivation.liftOfSurjective hf hker) (f q) = f (d q)
  rw [Derivation.liftOfSurjective_apply]

end Adjoin

/-! ## 6. Extending a derivation to the fraction field -/

section Fraction

variable {R A K : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
variable {M : Submonoid A} [Field K] [Algebra A K]

/-- The quotient-rule expression `(s·Da − a·Ds)/s²` attached to a derivation `d` of `A` and a pair
`(a, s)` of elements of `A`, viewed in the fraction field `K`. -/
private noncomputable def DQ (d : Derivation R A A) (a s : A) : K :=
  (algebraMap A K (d a) * algebraMap A K s - algebraMap A K a * algebraMap A K (d s))
    / (algebraMap A K s) ^ 2

variable [IsDomain A] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]

private lemma isDomain_map_ne_zero {s : A} (hs : s ∈ nonZeroDivisors A) :
    algebraMap A K s ≠ 0 := fun h0 =>
  (mem_nonZeroDivisors_iff_ne_zero.mp hs) (IsFractionRing.injective A K (by rw [h0, map_zero]))

/-- **Well-definedness of the quotient rule.**  `DQ d a s` depends only on the element
`a / s ∈ K`. -/
private lemma DQ_wellDefined (d : Derivation R A A) {a s a' s' : A}
    (hs : s ∈ nonZeroDivisors A) (hs' : s' ∈ nonZeroDivisors A)
    (h : algebraMap A K a / algebraMap A K s = algebraMap A K a' / algebraMap A K s') :
    (DQ d a s : K) = DQ d a' s' := by
  have hs0 : algebraMap A K s ≠ 0 := isDomain_map_ne_zero hs
  have hs0' : algebraMap A K s' ≠ 0 := isDomain_map_ne_zero hs'
  have has' : algebraMap A K a * algebraMap A K s' = algebraMap A K a' * algebraMap A K s :=
    (div_eq_div_iff hs0 hs0').mp h
  have hass' : a * s' = a' * s :=
    IsFractionRing.injective A K (by rw [map_mul, map_mul, has'])
  have hd : d a * s' + a * d s' = d a' * s + a' * d s := by
    have hc := congrArg d hass'
    rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hc
    linear_combination (norm := first | refl_ring1 | ring1) hc
  have key : (d a * s - a * d s) * s' ^ 2 = (d a' * s' - a' * d s') * s ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) (s * s') * hd - (s * d s' + s' * d s) * hass'
  have keyK : algebraMap A K (d a * s - a * d s) * (algebraMap A K s') ^ 2 =
      algebraMap A K (d a' * s' - a' * d s') * (algebraMap A K s) ^ 2 := by
    have := congrArg (algebraMap A K) key
    simpa only [map_mul, map_sub, map_pow] using this
  rw [DQ, DQ, div_eq_div_iff (pow_ne_zero 2 hs0) (pow_ne_zero 2 hs0')]
  simpa only [map_sub, map_mul] using keyK

/-- The quotient rule is additive in the numerator. -/
private lemma DQ_add (d : Derivation R A A) (a s a' s' : A)
    (hs : algebraMap A K s ≠ 0) (hs' : algebraMap A K s' ≠ 0) :
    (DQ d (a * s' + a' * s) (s * s') : K) = DQ d a s + DQ d a' s' := by
  have hd1 : d (a * s' + a' * s) = a * d s' + s' * d a + (a' * d s + s * d a') := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
  have hd2 : d (s * s') = s * d s' + s' * d s := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
  rw [DQ, DQ, DQ, hd1, hd2]
  simp only [map_add, map_mul, map_pow]
  field_simp
  try ring_nf

/-- The quotient rule on a product of two fractions (the product rule of derivatives). -/
private lemma DQ_mul (d : Derivation R A A) (a s a' s' : A)
    (hs : algebraMap A K s ≠ 0) (hs' : algebraMap A K s' ≠ 0) :
    (DQ d (a * a') (s * s') : K)
      = algebraMap A K a / algebraMap A K s * DQ d a' s'
        + algebraMap A K a' / algebraMap A K s' * DQ d a s := by
  have hd1 : d (a * a') = a * d a' + a' * d a := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
  have hd2 : d (s * s') = s * d s' + s' * d s := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
  rw [DQ, DQ, DQ, hd1, hd2]
  simp only [map_add, map_mul, map_pow]
  field_simp
  try ring_nf

/-- The quotient rule is `R`-linear (over the constants). -/
private lemma DQ_smul (d : Derivation R A A) (r : R) (a s : A)
    (hs : algebraMap A K s ≠ 0) :
    (DQ d (algebraMap R A r * a) s : K) = algebraMap R K r * DQ d a s := by
  have hd : d (algebraMap R A r * a) = algebraMap R A r * d a := by
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  rw [DQ, DQ, hd]
  simp only [map_mul, map_pow]
  rw [IsScalarTower.algebraMap_apply R A K]
  field_simp
  try ring_nf

/-- **Extension of a derivation to the fraction field.**  Every derivation of a domain `A`
extends, via the quotient rule, to its fraction field `K`. -/
private theorem deriv_extend_fractionRing (d : Derivation R A A) :
    ∃ D : Derivation R K K, ∀ a : A, D (algebraMap A K a) = algebraMap A K (d a) := by
  classical
  have hsurj : ∀ z : K, ∃ a, ∃ s ∈ nonZeroDivisors A, algebraMap A K a / algebraMap A K s = z :=
    IsFractionRing.div_surjective A
  let rep : K → A × A := fun z =>
    (Classical.choose (hsurj z), Classical.choose (Classical.choose_spec (hsurj z)))
  have rep_spec : ∀ z : K, (rep z).2 ∈ nonZeroDivisors A ∧
      algebraMap A K (rep z).1 / algebraMap A K (rep z).2 = z := fun z =>
    Classical.choose_spec (Classical.choose_spec (hsurj z))
  have rep_ne : ∀ z : K, algebraMap A K (rep z).2 ≠ 0 := fun z =>
    isDomain_map_ne_zero (rep_spec z).1
  let Dfun : K → K := fun z => DQ d (rep z).1 (rep z).2
  have Dfun_eq : ∀ (z : K) (a s : A), s ∈ nonZeroDivisors A →
      algebraMap A K a / algebraMap A K s = z → Dfun z = DQ d a s :=
    fun z a s hs h => DQ_wellDefined d (rep_spec z).1 hs (by rw [(rep_spec z).2, ← h])
  have Dfun_rep : ∀ z : K, Dfun z = DQ d (rep z).1 (rep z).2 := fun _ => rfl
  have Dfun_algebraMap : ∀ a : A, Dfun (algebraMap A K a) = algebraMap A K (d a) := by
    intro a
    rw [Dfun_eq (algebraMap A K a) a 1 (one_mem _) (by simp)]
    rw [DQ]
    simp
  have Dfun_add : ∀ z w : K, Dfun (z + w) = Dfun z + Dfun w := by
    intro z w
    have hzw : algebraMap A K ((rep z).1 * (rep w).2 + (rep w).1 * (rep z).2)
        / algebraMap A K ((rep z).2 * (rep w).2) = z + w := by
      have h1 : algebraMap A K ((rep z).1 * (rep w).2 + (rep w).1 * (rep z).2)
          = algebraMap A K (rep z).1 * algebraMap A K (rep w).2
            + algebraMap A K (rep w).1 * algebraMap A K (rep z).2 := by
        rw [map_add, map_mul, map_mul]
      have h2 : algebraMap A K ((rep z).2 * (rep w).2)
          = algebraMap A K (rep z).2 * algebraMap A K (rep w).2 := by rw [map_mul]
      calc algebraMap A K ((rep z).1 * (rep w).2 + (rep w).1 * (rep z).2)
            / algebraMap A K ((rep z).2 * (rep w).2)
          = algebraMap A K (rep z).1 / algebraMap A K (rep z).2
            + algebraMap A K (rep w).1 / algebraMap A K (rep w).2 := by
            rw [h1, h2, div_add_div (algebraMap A K (rep z).1) (algebraMap A K (rep w).1)
              (rep_ne z) (rep_ne w)]
            first | refl_ring1 | ring
        _ = z + w := by simp only [(rep_spec z).2, (rep_spec w).2]
    rw [Dfun_eq (z + w) _ _ (mul_mem (rep_spec z).1 (rep_spec w).1) hzw,
      Dfun_rep z, Dfun_rep w, DQ_add d _ _ _ _ (rep_ne z) (rep_ne w)]
  have Dfun_mul : ∀ z w : K, Dfun (z * w) = z * Dfun w + w * Dfun z := by
    intro z w
    have hzw : algebraMap A K ((rep z).1 * (rep w).1) / algebraMap A K ((rep z).2 * (rep w).2)
        = z * w := by
      have h1 : algebraMap A K ((rep z).1 * (rep w).1)
          = algebraMap A K (rep z).1 * algebraMap A K (rep w).1 := by rw [map_mul]
      have h2 : algebraMap A K ((rep z).2 * (rep w).2)
          = algebraMap A K (rep z).2 * algebraMap A K (rep w).2 := by rw [map_mul]
      calc algebraMap A K ((rep z).1 * (rep w).1) / algebraMap A K ((rep z).2 * (rep w).2)
          = algebraMap A K (rep z).1 / algebraMap A K (rep z).2
            * (algebraMap A K (rep w).1 / algebraMap A K (rep w).2) := by
            simp only [h1, h2, ← mul_div_mul_comm]
        _ = z * w := by simp only [(rep_spec z).2, (rep_spec w).2]
    rw [Dfun_eq (z * w) _ _ (mul_mem (rep_spec z).1 (rep_spec w).1) hzw, Dfun_rep z,
      Dfun_rep w, DQ_mul d _ _ _ _ (rep_ne z) (rep_ne w), (rep_spec z).2, (rep_spec w).2]
  have Dfun_smul : ∀ (r : R) (z : K), Dfun (r • z) = r • Dfun z := by
    intro r z
    have hz : algebraMap A K (algebraMap R A r * (rep z).1) / algebraMap A K (rep z).2
        = r • z := by
      have h1 : algebraMap A K (algebraMap R A r * (rep z).1)
          = algebraMap R K r * algebraMap A K (rep z).1 := by
        rw [map_mul, IsScalarTower.algebraMap_apply R A K]
      rw [h1, mul_div_assoc, (rep_spec z).2, ← Algebra.smul_def]
    rw [Dfun_eq (r • z) _ _ (rep_spec z).1 hz, Dfun_rep z, DQ_smul d r _ _ (rep_ne z),
      Algebra.smul_def]
  refine ⟨Derivation.mk' { toFun := Dfun, map_add' := Dfun_add, map_smul' := Dfun_smul }
    Dfun_mul, Dfun_algebraMap⟩

end Fraction

/-! ## 7. The invariant derivation -/

section Main

variable {N : Type*} [Field N]

private lemma mk_CC (E : WeierstrassCurve N) (a : N) :
    AdjoinRoot.mk (polynomial E) (Polynomial.C (Polynomial.C a)) =
      algebraMap N (Work.MotC2.Coord E) a := by
  rw [AdjoinRoot.mk_C, Work.MotC2.of_poly_C]

end Main

theorem exists_invariantDeriv {N : Type*} [Field N] (E : WeierstrassCurve N) :
    ∃ D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E),
      D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃ ∧
      D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E := by
  -- descend to the coordinate ring
  obtain ⟨D1, hD1⟩ := deriv_adjoinRoot_lift (p := polynomial E) (D0 E) (D0_polynomial E)
  -- extend to the function field
  obtain ⟨D, hD⟩ := deriv_extend_fractionRing (R := N) (A := Work.MotC2.Coord E)
    (K := Work.MotC2.Func E) (d := D1)
  refine ⟨D, ?_, ?_⟩
  · -- value on `x`
    have hcoord : Work.MotC2.genX E = algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
        (Work.MotC2.coordX E) := rfl
    rw [hcoord, hD]
    have hx : D1 (Work.MotC2.coordX E) = 2 * Work.MotC2.coordY E
        + algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordX E
        + algebraMap N (Work.MotC2.Coord E) E.a₃ := by
      rw [Work.MotC2.coordX_eq_mk E, hD1, D0_CX, e2_symm_mvF]
      simp only [map_add, map_mul, map_ofNat, mk_CC E, ← Work.MotC2.coordY_eq_mk E,
        ← Work.MotC2.coordX_eq_mk E]
    rw [hx]
    simp only [map_add, map_mul, map_ofNat]
    rw [show algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordY E)
          = Work.MotC2.genY E from rfl,
      show algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordX E)
          = Work.MotC2.genX E from rfl,
      ← IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E) E.a₁,
      ← IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E) E.a₃]
  · -- value on `y`
    have hcoord : Work.MotC2.genY E = algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
        (Work.MotC2.coordY E) := rfl
    rw [hcoord, hD]
    have hy : D1 (Work.MotC2.coordY E) = 3 * (Work.MotC2.coordX E) ^ 2
        + 2 * algebraMap N (Work.MotC2.Coord E) E.a₂ * Work.MotC2.coordX E
        + algebraMap N (Work.MotC2.Coord E) E.a₄
        - algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordY E := by
      rw [Work.MotC2.coordY_eq_mk E, hD1, D0_Y, e2_symm_mvG]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, mk_CC E,
        ← Work.MotC2.coordY_eq_mk E, ← Work.MotC2.coordX_eq_mk E]
    rw [hy]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [show algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordX E)
          = Work.MotC2.genX E from rfl,
      show algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordY E)
          = Work.MotC2.genY E from rfl,
      ← IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E) E.a₂,
      ← IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E) E.a₄,
      ← IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E) E.a₁]

end Work.MotV5
