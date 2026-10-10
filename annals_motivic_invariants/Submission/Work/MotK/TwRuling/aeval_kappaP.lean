import Mathlib
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- Splitting `(c * f i) ^ k = c ^ k * (f i) ^ k` inside a `Finsupp.prod` and collecting the
`c`-powers: the product of the `(c * f i) ^ (v i)` over the support of `v` is
`c ^ (degree v)` times the product of the `f i ^ (v i)`. -/
private lemma finsupp_prod_smul {σ S : Type*} [CommMonoid S]
    (v : σ →₀ ℕ) (c : S) (f : σ → S) :
    (v.prod fun i k => (c * f i) ^ k) = c ^ v.degree * (v.prod fun i k => f i ^ k) := by
  simp only [Finsupp.prod]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-- **Homogeneity under a scalar substitution**: replacing the evaluation point `f` by
`fun i => c * f i` multiplies `aeval f F` by `c ^ n` when `F` is homogeneous of degree `n`. -/
private lemma aeval_smul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (f : σ → S) (c : S) (F : MvPolynomial σ R) {n : ℕ}
    (hF : F.IsHomogeneous n) :
    MvPolynomial.aeval (fun i => c * f i) F = c ^ n * MvPolynomial.aeval f F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hdeg : v.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (MvPolynomial.mem_support_iff.mp hv)
  simp only [MvPolynomial.aeval_monomial]
  rw [finsupp_prod_smul, hdeg]
  first | refl_ring1 | ring

/-- The transfer back from the `L(5·O)`-adapted basis `kappaP` to the twisted coordinates
`twCoordG` (used by `rpEval` and hence by the target), via homogeneity of degree `6`.

Route: `kappaP K D h i = kleinCoord D (KbG K) 0 * twCoordG K D h i` (cancel `κ₀`, using
`hD.coord0_ne (KbG K)`), then the standard homogeneity fact
`F ∈ homogeneousSubmodule n → aeval (fun i => c * x i) F = c ^ n * aeval x F`. -/
theorem aeval_kappaP (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (F : MvPolynomial (Fin 5) (Work.MotK.KbG K))
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotK.KbG K) 6) :
    MvPolynomial.aeval (Work.MotK.TwRuling.kappaP K D h) F
      = (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 6
        * MvPolynomial.aeval (Work.MotK.twCoordG K D h) F := by
  -- `kappaP` differs from `κ₀ • twCoordG` only by cancelling the unit `κ₀`.
  have hκ0 : Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 ≠ 0 := hD.coord0_ne (Work.MotK.KbG K)
  have hcp : Work.MotK.TwRuling.kappaP K D h
      = fun i => Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 * Work.MotK.twCoordG K D h i := by
    funext i
    simp only [Work.MotK.TwRuling.kappaP, Work.MotK.twCoordG]
    field_simp
  rw [hcp]
  -- Homogeneity of `F` of degree `6` transfers the factor `κ₀` to the sixth power.
  exact aeval_smul_of_isHomogeneous (Work.MotK.twCoordG K D h)
    (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) F hF

end Work.MotK.TwRuling
