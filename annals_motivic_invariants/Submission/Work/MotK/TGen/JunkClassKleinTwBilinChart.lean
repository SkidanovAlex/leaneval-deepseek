import Mathlib
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotK.JunkClassLinearThree
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.JunkClassKleinTwBilinChart`

The polar form `b(p, ·) = kleinTwBilin a b h p (chart3 K)` of the T-twisted Klein quadric,
evaluated at the rational point `p = pRa a b h = kleinPointT a b h` and the affine chart
`chart3 K = ![0, x₀, x₁, x₂, 1]`, is the **linear form**

  `b(p, chart3) = a·b·x₁ + a²·h·x₂`   (`kleinTwBilin_pRa_chart3`).

Consequently it has total degree `1`, is a prime element of `K[x₀,x₁,x₂]`
(`kleinTwBilin_pRa_chart3_prime`), and the height-one primes containing it are exactly its
principal prime: `JunkClassLinearThree` then identifies the residue field of the corresponding
codimension-one point of `𝔸³_K` as the rational surface `K(x₀,x₂)`, so that point is a
*JunkClass* divisor (`JunkClassKleinTwBilinChart`).

The evaluation is done through the polar expansion

  `kleinTwBilin a b h u v = -2ab·u₀v₀ + a²h·(u₂v₃ + u₃v₂) - b²h·(u₁v₄ + u₄v₁)`

of `kleinTwQ = kleinTwP0`, the only non-vanishing contributions coming from the entries
`u₂ = 1`, `u₃ = b/(a·h)`, `v₂ = x₁`, `v₃ = x₂`; the field identity `a²h · b/(a·h) = a·b`
(needing `a ≠ 0`, `h ≠ 0`) produces the coefficient `a·b` of `x₁`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The polar expansion of the T-twisted Klein quadric**: the polar form of
`kleinTwQ = kleinTwP0` is `-2ab·u₀v₀ + a²h·(u₂v₃ + u₃v₂) - b²h·(u₁v₄ + u₄v₁)`. -/
lemma kleinTwBilin_polar {R : Type*} [CommRing R] (a b h : R) (u v : Fin 5 → R) :
    Work.MotK.kleinTwBilin a b h u v
      = -2*a*b*(u 0 * v 0) + a^2*h*(u 2 * v 3 + u 3 * v 2)
          - b^2*h*(u 1 * v 4 + u 4 * v 1) := by
  simp only [Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

/-- **The polar form at the link point and the affine chart**: `b(p, chart3) = a·b·x₁ + a²h·x₂`
where `p = pRa a b h = kleinPointT a b h = (1,0,1,b/(ah),0)` and
`chart3 K = (0, x₀, x₁, x₂, 1)`. -/
theorem kleinTwBilin_pRa_chart3 (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRa a b h) (Work.MotK.chart3 K)
      = MvPolynomial.C (a * b) * MvPolynomial.X 1 + MvPolynomial.C (a^2 * h) * MvPolynomial.X 2 := by
  have hc : a^2 * h * (b / (a*h)) = a * b := by
    have h1 : a * h ≠ 0 := mul_ne_zero ha hh
    field_simp
  have k0 : Work.MotK.kleinPointT a b h 0 = 1 := rfl
  have k1 : Work.MotK.kleinPointT a b h 1 = 0 := rfl
  have k2 : Work.MotK.kleinPointT a b h 2 = 1 := rfl
  have k3 : Work.MotK.kleinPointT a b h 3 = b / (a*h) := rfl
  have k4 : Work.MotK.kleinPointT a b h 4 = 0 := rfl
  have c0 : Work.MotK.chart3 K 0 = (0 : MvPolynomial (Fin 3) K) := rfl
  have c1 : Work.MotK.chart3 K 1 = MvPolynomial.X 0 := rfl
  have c2 : Work.MotK.chart3 K 2 = MvPolynomial.X 1 := rfl
  have c3 : Work.MotK.chart3 K 3 = MvPolynomial.X 2 := rfl
  have c4 : Work.MotK.chart3 K 4 = (1 : MvPolynomial (Fin 3) K) := rfl
  rw [kleinTwBilin_polar]
  simp only [Work.MotK.pRa_apply, k0, k1, k2, k3, k4, c0, c1, c2, c3, c4,
    map_zero, map_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, sub_zero]
  have hca : (MvPolynomial.C a)^2 * MvPolynomial.C h
      = (MvPolynomial.C (a^2*h) : MvPolynomial (Fin 3) K) := by
    rw [← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
  have hab : (MvPolynomial.C (a^2*h)) * MvPolynomial.C (b/(a*h))
      = (MvPolynomial.C (a*b) : MvPolynomial (Fin 3) K) := by
    rw [← MvPolynomial.C_mul, hc]
  rw [mul_add, hca, ← mul_assoc, hab]
  first | refl_ring1 | ring

/-- **The polar form at the chart has total degree one.** -/
theorem kleinTwBilin_pRa_chart3_totalDegree (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) :
    (Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRa a b h) (Work.MotK.chart3 K)).totalDegree = 1 := by
  rw [kleinTwBilin_pRa_chart3 a b h ha hh]
  rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.C_mul_X_eq_monomial]
  have h1 : (MvPolynomial.monomial (Finsupp.single 1 1) (a*b)
      : MvPolynomial (Fin 3) K).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_monomial _ (mul_ne_zero ha hb)]
    simp
  have h2 : (MvPolynomial.monomial (Finsupp.single 2 1) (a^2*h)
      : MvPolynomial (Fin 3) K).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_monomial _ (mul_ne_zero (pow_ne_zero 2 ha) hh)]
    simp
  refine le_antisymm ?_ ?_
  · calc (MvPolynomial.monomial (Finsupp.single 1 1) (a*b)
          + MvPolynomial.monomial (Finsupp.single 2 1) (a^2*h)
          : MvPolynomial (Fin 3) K).totalDegree
        ≤ max (MvPolynomial.monomial (Finsupp.single 1 1) (a*b)
              : MvPolynomial (Fin 3) K).totalDegree
            (MvPolynomial.monomial (Finsupp.single 2 1) (a^2*h)
              : MvPolynomial (Fin 3) K).totalDegree := MvPolynomial.totalDegree_add _ _
      _ = 1 := by rw [h1, h2, max_self]
  · have hcoeff : (MvPolynomial.monomial (Finsupp.single 1 1) (a*b)
        + MvPolynomial.monomial (Finsupp.single 2 1) (a^2*h)
        : MvPolynomial (Fin 3) K).coeff (Finsupp.single 1 1) ≠ 0 := by
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      have hne : (Finsupp.single 2 1 : Fin 3 →₀ ℕ) ≠ Finsupp.single 1 1 := by
        intro hc
        rw [Finsupp.single_eq_single_iff] at hc
        rcases hc with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact one_ne_zero h
      rw [if_pos rfl, if_neg hne, add_zero]
      exact mul_ne_zero ha hb
    have hmem := MvPolynomial.mem_support_iff.mpr hcoeff
    have hle := MvPolynomial.le_totalDegree hmem
    simpa using hle

/-- **The polar form at the chart is a prime element** of `K[x₀,x₁,x₂]`: it is a nonzero linear
form, hence irreducible (its total degree is additive over products, and a degree-zero factor of a
nonzero product is a nonzero constant, i.e. a unit) and therefore prime in the UFD
`K[x₀,x₁,x₂]`. -/
theorem kleinTwBilin_pRa_chart3_prime (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Prime (Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRa a b h) (Work.MotK.chart3 K)) := by
  set l := Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.pRa a b h) (Work.MotK.chart3 K) with hl
  have hdeg : l.totalDegree = 1 := by
    rw [hl]; exact kleinTwBilin_pRa_chart3_totalDegree a b h ha hb hh
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0] at hdeg; simp at hdeg
  have hirr : Irreducible l := by
    refine ⟨?_, ?_⟩
    · intro hunit
      have hdvd : l ∣ (1 : MvPolynomial (Fin 3) K) := IsUnit.dvd hunit
      have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd one_ne_zero
      rw [MvPolynomial.totalDegree_one, hdeg] at hle
      exact absurd hle (by norm_num)
    · intro f g hfg
      have hf0 : f ≠ 0 := by intro h; exact hl0 (by rw [hfg, h, zero_mul])
      have hg0 : g ≠ 0 := by intro h; exact hl0 (by rw [hfg, h, mul_zero])
      have hsum : f.totalDegree + g.totalDegree = 1 := by
        rw [← MvPolynomial.totalDegree_mul_of_isDomain hf0 hg0, ← hfg]; exact hdeg
      have hone : f.totalDegree = 0 ∨ g.totalDegree = 0 := by omega
      rcases hone with hf | hg
      · left
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hf
        rw [hf]
        exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr
          (by intro hc; exact hf0 (by rw [hf, hc, MvPolynomial.C_0])))
      · right
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hg
        rw [hg]
        exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr
          (by intro hc; exact hg0 (by rw [hg, hc, MvPolynomial.C_0])))
  exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hirr

/-- **The height-one primes of `𝔸³_K` cut out by the polar form `b(p, chart3) = a·b·x₁ + a²h·x₂`
are junk divisors.**  Since the polar form is a prime element of total degree one, a height-one
prime containing it is its principal prime (`Work.MotK.CensusPrime.eq_span_of_height_one`), and at
that point `Work.MotK.JunkClassLinearThree` identifies the residue field with the rational surface
`K(x₀,x₂) = RatFunc (RatFunc K)`. -/
theorem JunkClassKleinTwBilinChart {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.pRa a b h) (Work.MotK.chart3 K) ∈ x.asIdeal →
      Work.MotV.JunkClass K x := by
  intro x hcoh hmem
  set l := Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.pRa a b h) (Work.MotK.chart3 K) with hl
  have hdeg : l.totalDegree = 1 := by
    rw [hl]; exact kleinTwBilin_pRa_chart3_totalDegree a b h ha hb hh
  have hprime : Prime l := by
    rw [hl]; exact kleinTwBilin_pRa_chart3_prime a b h ha hb hh
  have hspan : (Ideal.span {l}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hheight : Ideal.height (Ideal.span {l}) = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero) hprime.not_isUnit
  have hmem' : l ∈ x.asIdeal := by rw [hl]; exact hmem
  have hx : x.asIdeal = Ideal.span {l} := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Work.MotK.CensusPrime.eq_span_of_height_one l hspan hheight x.asIdeal
      (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hcoh) hmem'
  have hxe : x = ⟨Ideal.span {l}, hspan⟩ := PrimeSpectrum.ext hx
  rw [hxe]
  exact Work.MotK.JunkClassLinearThree l hdeg hspan

end Work.MotK.TGen
