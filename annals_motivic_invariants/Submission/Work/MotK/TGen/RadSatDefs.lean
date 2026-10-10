import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.MotK.TGen.zG3Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The coefficient of `X 0 ^ 2` in the quadratic relation `zF1`. -/
noncomputable def zAl (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K := C (a^2*b^4*h)

/-- The coefficient of `X 0` in the quadratic relation `zF1`. -/
noncomputable def zBet (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  C (-(a^6*h)) * (X 2)^3

/-- The constant coefficient of the quadratic relation `zF1`. -/
noncomputable def zGam (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a^4*b^2*h) * (X 1)^2 * (X 2)^2 + C (a*b^5*h) * (X 1)^3 - C (a^5*b + b^6) * X 2

/-- The quadratic relation `f1 = α·X0² + β·X0 + γ` cutting `Z` out of the `X0`-direction. -/
noncomputable def zF1 (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  zAl K a b h * (X 0)^2 + zBet K a b h * X 0 + zGam K a b h

theorem zF1_eq (a b h : K) :
    zF1 K a b h = zAl K a b h * (X 0)^2 + zBet K a b h * X 0 + zGam K a b h := rfl

/-- `zF1 ∈ ZI`, with the three-term certificate `a^2*b*zF1 = (a*b^4*X0)*Zcub1 +
(b^5*X1)*Zcub2 - (a^5+b^5)*X2*Zcub3`. -/
theorem zF1_cert (a b h : K) :
    C (a^2*b) * zF1 K a b h
      = (C a * C (b^4) * X 0) * Work.MotK.TwCensus.Zcub a b h 1
        + (C (b^5) * X 1) * Work.MotK.TwCensus.Zcub a b h 2
        - (C (a^5 + b^5) * X 2) * Work.MotK.TwCensus.Zcub a b h 3 := by
  rw [zF1, zAl, zBet, zGam,
    show Work.MotK.TwCensus.Zcub a b h 1
      = Work.MotK.kleinTwR1 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    show Work.MotK.TwCensus.Zcub a b h 2
      = Work.MotK.kleinTwR2 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    show Work.MotK.TwCensus.Zcub a b h 3
      = Work.MotK.kleinTwR3 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3]
  simp only [Work.MotK.TwCensus.chart3_zero, Work.MotK.TwCensus.chart3_one,
    Work.MotK.TwCensus.chart3_two, Work.MotK.TwCensus.chart3_three,
    Work.MotK.TwCensus.chart3_four, C_mul, C_pow, C_add, map_neg, map_ofNat]
  first | refl_ring1 | ring

/-- `zF1 ∈ ZI`. -/
theorem zF1_mem_ZI (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    zF1 K a b h ∈ Work.MotK.TwCensus.ZI a b h := by
  have h1 : Work.MotK.TwCensus.Zcub a b h 1 ∈ Work.MotK.TwCensus.ZI a b h :=
    Ideal.subset_span (s := Set.range (Work.MotK.TwCensus.Zcub a b h)) ⟨1, rfl⟩
  have h2 : Work.MotK.TwCensus.Zcub a b h 2 ∈ Work.MotK.TwCensus.ZI a b h :=
    Ideal.subset_span (s := Set.range (Work.MotK.TwCensus.Zcub a b h)) ⟨2, rfl⟩
  have h3 : Work.MotK.TwCensus.Zcub a b h 3 ∈ Work.MotK.TwCensus.ZI a b h :=
    Ideal.subset_span (s := Set.range (Work.MotK.TwCensus.Zcub a b h)) ⟨3, rfl⟩
  have hmem : (C a * C (b^4) * X 0) * Work.MotK.TwCensus.Zcub a b h 1
      + (C (b^5) * X 1) * Work.MotK.TwCensus.Zcub a b h 2
      - (C (a^5 + b^5) * X 2) * Work.MotK.TwCensus.Zcub a b h 3
      ∈ Work.MotK.TwCensus.ZI a b h := by
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ h1
    · exact Ideal.mul_mem_left _ _ h2
    · exact Ideal.mul_mem_left _ _ h3
  have h3' : (C ((a^2*b)⁻¹) : MvPolynomial (Fin 3) K) * (C (a^2*b) * zF1 K a b h)
      = zF1 K a b h := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 2 ha) hb), C_1, one_mul]
  rw [← h3', zF1_cert]
  exact Ideal.mul_mem_left _ _ hmem

/-- **The quadratic identity**: `α·zC² + β·zC·zA + γ·zA² = b⁴h·zg`, whence
`α·zC² + β·zC·zA + γ·zA² ∈ ZI`. -/
theorem zElim_quad_id (a b h : K) :
    zAl K a b h * (zC K a b h)^2 + zBet K a b h * zC K a b h * zA K a b h
      + zGam K a b h * (zA K a b h)^2 = C (b^4*h) * zg K a b h := by
  rw [zAl, zBet, zGam, zC, zA, zg_eq_ZElim, Work.MotK.TwCensus.ZElim]
  simp only [C_mul, C_pow, C_add, map_neg, map_ofNat]
  first | refl_ring1 | ring

/-- The element `zG3` lies in `(zF1, zB, zg)`. -/
theorem zG3_cert (a b h : K) :
    zG3 a b h = (C (a^3) * (X 2)^2 - C (b^3) * X 1) * zF1 K a b h
      + (C (a^2*b^4) * X 0 - C (2*a^6) * (X 2)^3 - C (a^3*b^3) * X 1 * X 2) * zB K a b h := by
  rw [zG3, zE, zR3, zF1, zAl, zBet, zGam, zB, zA, zC]
  simp only [C_mul, C_pow, C_add, map_neg, map_sub, map_ofNat]
  first | refl_ring1 | ring

/-- The element `zG3` lies in the ideal `(zF1, zB, zg)`. -/
theorem zG3_mem_span (a b h : K) :
    zG3 a b h ∈ Ideal.span {zF1 K a b h, zB K a b h, zg K a b h} := by
  have h1 : zF1 K a b h ∈ Ideal.span {zF1 K a b h, zB K a b h, zg K a b h} :=
    Ideal.subset_span (by simp)
  have h2 : zB K a b h ∈ Ideal.span {zF1 K a b h, zB K a b h, zg K a b h} :=
    Ideal.subset_span (by simp)
  rw [zG3_cert]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

/-- **The `β`-identity used in the syzygy step.** -/
theorem zF2_identity (a b h : K) :
    zAl K a b h * zC K a b h * X 0 + zA K a b h * zGam K a b h + zBet K a b h * zC K a b h
      = -(C (a^6*h) * (X 2)^3 + C (a^3*b^3*h) * X 1 * X 2) * zB K a b h
        - C h * zG3 a b h := by
  rw [zAl, zBet, zGam, zG3, zE, zR3, zB, zA, zC]
  simp only [C_mul, C_pow, C_add, map_neg, map_sub, map_ofNat]
  first | refl_ring1 | ring

/-- `α·zC·X0 + zA·γ + β·zC ∈ (zF1, zB, zg)`. -/
theorem zF2_mem (a b h : K) :
    zAl K a b h * zC K a b h * X 0 + zA K a b h * zGam K a b h + zBet K a b h * zC K a b h
      ∈ Ideal.span {zF1 K a b h, zB K a b h, zg K a b h} := by
  have h2 : zB K a b h ∈ Ideal.span {zF1 K a b h, zB K a b h, zg K a b h} :=
    Ideal.subset_span (by simp)
  rw [zF2_identity]
  refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ (zG3_mem_span a b h))
  exact Ideal.mul_mem_left _ _ h2


/-- The projection `R = K[X0,X1,X2] → A[T]` (`A = K[X0,X1]/(ZElim2)`) sending `X0 ↦ T` and the
other two variables to the classes of the two variables of `K[X0,X1]`. -/
noncomputable def rho (K : Type) [Field K] (a b h : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Polynomial (ZD K a b h) :=
  MvPolynomial.aeval ![Polynomial.X,
    Polynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)),
    Polynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 2) K))]

end Work.MotK.TGen
