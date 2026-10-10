import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- `d.prod (fun _ k => t ^ k) = t ^ (weight 1 d)` for `d : σ →₀ ℕ`: the product of the
`t ^ (d i)` over the support is `t` to the total degree. -/
lemma finsupp_prod_pow_eq_pow_weight {σ : Type*} {A : Type*} [CommSemiring A]
    (d : σ →₀ ℕ) (t : A) :
    d.prod (fun _ k => t ^ k) = t ^ (Finsupp.weight (1 : σ → ℕ) d) := by
  rw [Finsupp.prod_of_support_subset d (Finset.Subset.refl _) _ (by intro i _; simp),
    Finsupp.weight_apply, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  simp

/-- The general form of the statement: if `P` is homogeneous of degree `n` over a commutative
semiring `A`, then evaluating its variables at `t * c i` multiplies the evaluation at `c` by
`t ^ n`. -/
lemma aeval_smul_of_homogeneous_general {σ : Type*} {A : Type*} [CommSemiring A]
    (P : MvPolynomial σ A) {n : ℕ} (hP : P.IsHomogeneous n) (t : A) (c : σ → A) :
    (MvPolynomial.aeval (fun i => t * c i)) P = t ^ n * (MvPolynomial.aeval c) P := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d r hr =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    have h1 : d.prod (fun i k => (t * c i) ^ k) = t ^ n * d.prod (fun i k => (c i) ^ k) := by
      rw [Finsupp.prod_congr (g1 := fun i k => (t * c i) ^ k)
            (g2 := fun i k => t ^ k * (c i) ^ k) (f := d) (fun i _ => by rw [mul_pow]),
        Finsupp.prod_mul, finsupp_prod_pow_eq_pow_weight, hr]
    rw [h1]
    first | refl_ring1 | ring

theorem aeval_smul_of_homogeneous {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {F : MvPolynomial (Fin 5) K} {n : ℕ} (hF : F.IsHomogeneous n) (l : R) (c : Fin 5 → R) :
    MvPolynomial.aeval (fun i => l * c i) F = l ^ n * MvPolynomial.aeval c F := by
  have hgen := aeval_smul_of_homogeneous_general (MvPolynomial.map (algebraMap K R) F)
    (n := n) (hF.map (algebraMap K R)) l c
  have h1 := MvPolynomial.aeval_map_algebraMap (A := R) c F
  have h2 := MvPolynomial.aeval_map_algebraMap (A := R) (fun i : Fin 5 => l * c i) F
  rw [← h2, hgen, h1]

end Work.MotAS
