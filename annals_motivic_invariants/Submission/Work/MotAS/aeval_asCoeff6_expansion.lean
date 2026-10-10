import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.map_asRuleQW

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.aeval_asCoeff6_expansion`

The `T`-expansion of the `0`-th component of the AS inverse quadro-cubic map on the ruling line of
the corrected AS chart:

`kleinRAS0 a b g (asRuleQW a b g c t) = Σ_{j<4} aeval c (asCoeff6 R a b g j) · t ^ j`.

## Route

* `asRuleQW a b g c t = A(c) + t·B(c)` (`SdualAS2Defs.lean`), so the left hand side is the value at
  `t` of the explicit polynomial in `T` over `A`
  `P := kleinRAS0 (C a) (C b) (C g) (fun k => C (A(c) k) + T * C (B(c) k))`
  (`eval_asCoeffPoly_base`, from the ring-hom naturality `kleinRAS0_map_gen` of `kleinRAS0`).
* `P` has `T`-degree `≤ 3` because `kleinRAS0` is a cubic form and each entry of the vector is
  linear in `T` (`natDegree_kleinRAS0_C_le`), so `P.eval t = ∑_{j<4} P.coeff j * t ^ j`
  (`Polynomial.eval_eq_sum_range'`).
* `P.coeff j = aeval c (asCoeff6 R a b g j)`: this is the `T^j`-coefficient of the *universal*
  polynomial `asCoeffPoly R a b g`, transported along `MvPolynomial.aeval c`
  (`aeval_asCoeff6_base`, via `map_asCoeffPoly_aeval` and `Polynomial.coeff_map`).
-/

namespace Work.MotAS

open Polynomial

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## §0  Naturality of `kleinRAS0` under ring homomorphisms -/

/-- `kleinRAS0` is a polynomial expression with integer coefficients in its arguments, hence
commutes with every ring homomorphism. -/
theorem kleinRAS0_map_gen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (z : Fin 5 → R) :
    kleinRAS0 (φ a) (φ b) (φ g) (fun k => φ (z k)) = φ (kleinRAS0 a b g z) := by
  simp only [kleinRAS0, map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- Naturality of `kleinRAS0` under `Polynomial.map` (the coefficient-ring form). -/
theorem kleinRAS0_map_poly {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)
    (a b g : Polynomial R) (z : Fin 5 → Polynomial R) :
    Polynomial.map ψ (kleinRAS0 a b g z)
      = kleinRAS0 (Polynomial.map ψ a) (Polynomial.map ψ b) (Polynomial.map ψ g)
          (fun k => Polynomial.map ψ (z k)) := by
  have h := kleinRAS0_map_gen (φ := Polynomial.mapRingHom ψ) a b g z
  exact h.symm

/-! ## §1  `MvPolynomial.aeval c` of the universal coefficient polynomial -/

/-- **The transport of `asCoeffPoly` along `MvPolynomial.aeval c`**: substituting the coordinates
`c` for the variables `X i` turns the universal polynomial `asCoeffPoly R a b g` into the explicit
polynomial `kleinRAS0 (C a') (C b') (C g') (A(c) + T·B(c))` over `A`. -/
theorem map_asCoeffPoly_aeval {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a b g : R) (c : Fin 5 → A) :
    (asCoeffPoly R a b g).map (MvPolynomial.aeval c).toRingHom
      = kleinRAS0 (Polynomial.C (algebraMap R A a)) (Polynomial.C (algebraMap R A b))
          (Polynomial.C (algebraMap R A g))
          (fun k => Polynomial.C
              (asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
            + Polynomial.X * Polynomial.C
              (asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)) := by
  have ha : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C a : MvPolynomial (Fin 5) R)
      = algebraMap R A a := by
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
  have hb : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C b : MvPolynomial (Fin 5) R)
      = algebraMap R A b := by
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
  have hg : (MvPolynomial.aeval c).toRingHom (MvPolynomial.C g : MvPolynomial (Fin 5) R)
      = algebraMap R A g := by
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
  have hf : (fun i => (MvPolynomial.aeval c).toRingHom
      (MvPolynomial.X i : MvPolynomial (Fin 5) R)) = c := by
    funext i
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
  have hA : ∀ k, (MvPolynomial.aeval c).toRingHom
      (asRuleQA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) k)
      = asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k := by
    intro k
    rw [map_asRuleQA, ha, hb, hg, hf]
  have hB : ∀ k, (MvPolynomial.aeval c).toRingHom
      (asRuleQB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) k)
      = asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k := by
    intro k
    rw [map_asRuleQB, ha, hb, hg, hf]
  simp only [asCoeffPoly, qAS_A_apply, qAS_B_apply]
  rw [kleinRAS0_map_poly]
  simp only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X]
  congr 1
  · rw [ha]
  · rw [hb]
  · rw [hg]
  · funext k
    rw [hA k, hB k]

/-- **The coefficient identity.**  The `j`-th coefficient of the explicit polynomial
`kleinRAS0 (C a') (C b') (C g') (A(c) + T·B(c))` is the evaluation at `c` of the universal
`j`-th coefficient form `asCoeff6 R a b g j`. -/
theorem aeval_asCoeff6_base {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a b g : R) (c : Fin 5 → A) (j : ℕ) :
    MvPolynomial.aeval c (asCoeff6 R a b g j)
      = (kleinRAS0 (Polynomial.C (algebraMap R A a)) (Polynomial.C (algebraMap R A b))
          (Polynomial.C (algebraMap R A g))
          (fun k => Polynomial.C
              (asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
            + Polynomial.X * Polynomial.C
              (asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k))).coeff j := by
  rw [show asCoeff6 R a b g j = (asCoeffPoly R a b g).coeff j from rfl]
  rw [← map_asCoeffPoly_aeval (R := R) (A := A) a b g c]
  exact (Polynomial.coeff_map (MvPolynomial.aeval c).toRingHom j).symm

/-! ## §2  Evaluation of the coefficient polynomial at `t` -/

/-- Evaluation at `T = t` of the explicit coefficient polynomial is `kleinRAS0` on the ruling
point `A(c) + t·B(c)`. -/
theorem eval_asCoeffPoly_base {S : Type*} [CommRing S] (a b g : S) (c : Fin 5 → S) (t : S) :
    (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (fun k => Polynomial.C (asRuleQA a b g c k)
          + Polynomial.X * Polynomial.C (asRuleQB a b g c k))).eval t
      = kleinRAS0 a b g (fun k => asRuleQA a b g c k + t * asRuleQB a b g c k) := by
  have h := kleinRAS0_map_gen (φ := Polynomial.evalRingHom t)
    (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
    (fun k => Polynomial.C (asRuleQA a b g c k) + Polynomial.X * Polynomial.C (asRuleQB a b g c k))
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X] using h.symm

/-! ## §3  The `T`-degree bound -/

/-- `kleinRAS0` is a cubic form, so on a vector whose entries are linear in `X` it has degree
at most `3` in `X`. -/
theorem natDegree_kleinRAS0_C_le {S : Type*} [CommRing S] (a b g : S) (z : Fin 5 → Polynomial S)
    (hz : ∀ k, (z k).natDegree ≤ 1) :
    (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z).natDegree ≤ 3 := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  have h4 := hz 4
  rw [kleinRAS0]
  compute_degree!
  simp only [max_le_iff]
  all_goals omega

/-! ## §4  The expansion -/

theorem aeval_asCoeff6_expansion {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a b g : R) (c : Fin 5 → A) (t : A) :
    Work.MotAS.kleinRAS0 (algebraMap R A a) (algebraMap R A b) (algebraMap R A g)
        (Work.MotAS.asRuleQW (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c t)
      = ∑ j ∈ Finset.range 4, MvPolynomial.aeval c (Work.MotAS.asCoeff6 R a b g j) * t ^ j := by
  have hz : ∀ k, (Polynomial.C
        (Work.MotAS.asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
      + Polynomial.X * Polynomial.C
        (Work.MotAS.asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
      : Polynomial A).natDegree ≤ 1 := by
    intro k
    compute_degree!
  have hP : (Work.MotAS.kleinRAS0 (Polynomial.C (algebraMap R A a))
      (Polynomial.C (algebraMap R A b)) (Polynomial.C (algebraMap R A g))
      ((fun k => Polynomial.C
          (Work.MotAS.asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
        + Polynomial.X * Polynomial.C
          (Work.MotAS.asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k))
        : Fin 5 → Polynomial A)).natDegree ≤ 3 :=
    natDegree_kleinRAS0_C_le _ _ _ _ hz
  have hdeg : (Work.MotAS.kleinRAS0 (Polynomial.C (algebraMap R A a))
      (Polynomial.C (algebraMap R A b)) (Polynomial.C (algebraMap R A g))
      ((fun k => Polynomial.C
          (Work.MotAS.asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k)
        + Polynomial.X * Polynomial.C
          (Work.MotAS.asRuleQB (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k))
        : Fin 5 → Polynomial A)).natDegree < 4 := by omega
  rw [show Work.MotAS.asRuleQW (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c t
      = (fun k => Work.MotAS.asRuleQA (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c k
          + t * Work.MotAS.asRuleQB (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A g) c k) from rfl]
  rw [← eval_asCoeffPoly_base (algebraMap R A a) (algebraMap R A b) (algebraMap R A g) c t]
  rw [Polynomial.eval_eq_sum_range' hdeg t]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← aeval_asCoeff6_base (R := R) (A := A) a b g c j]

end Work.MotAS
