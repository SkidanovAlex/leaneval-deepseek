import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.asRuleMinP_isHomogeneous
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotAS.isHomogeneous_of_aeval_smul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asCoeff6_isHomogeneous`

`asCoeff6 K a b g j` is the `T ^ j`-coefficient of

  `kleinRAS0 (C a) (C b) (C g) (A + T · B)`,

where `A = qAS_A`, `B = qAS_B` are the two AS ruling vectors, quadratic forms in the five AS Galois
coordinates `X 0, …, X 4`.  Since `kleinRAS0` is a cubic form and each of `A`, `B` is quadratic in
the `X`s, the `T ^ j`-coefficient is a form of degree `2 · 3 = 6`: that is the statement proved
here.

## Route

The proof is the general dilation (scaling) law for `asCoeff6`: for **any** commutative ring `S`
which is an algebra over `K` (the coefficient ring of `asCoeff6`), any `s : S` and any
`x : Fin 5 → S`,

  `aeval (fun i => s * x i) (asCoeff6 K a b g j) = s ^ 6 * aeval x (asCoeff6 K a b g j)`

(`asCoeff6_dilation_gen`).  Its proof is a coefficientwise computation:

* `aeval_asCoeff6_gen`: evaluating `asCoeff6` at a substitution `Φ` is the `j`-th coefficient of
  the `T`-polynomial `kleinRAS0 (C a) (C b) (C g) (asZW a b g Φ)`, where `asZW a b g Φ` is the
  vector `C (asRuleQA a b g Φ k) + T · C (asRuleQB a b g Φ k)`.  This is the naturality of
  `kleinRAS0` (`map_kleinRAS0`) combined with the naturality of the ruling vectors
  (`map_asRuleQA`, `map_asRuleQB`) — see `map_asCoeffPoly_aeval`.
* the ruling vectors are quadratic in `c`, so `asRuleQA a b g (s · x) = s ^ 2 · asRuleQA a b g x`
  and similarly for `asRuleQB` (`as_hom_asRuleQA_smul`, `as_hom_asRuleQB_smul`); hence
  `asZW a b g (s · x) = C (s ^ 2) · asZW a b g x` (`asZW_smul`).
* `kleinRAS0` is cubic (`kleinRAS0_smul`), so the whole `T`-polynomial is multiplied by
  `(C (s ^ 2)) ^ 3 = C (s ^ 6)`, and taking the `j`-th coefficient gives the law.

The target is then the case `S = Polynomial (MvPolynomial (Fin 5) K)`, `s = Polynomial.X`,
`x i = C (X i)` of that law, together with `isHomogeneous_of_aeval_smul` (the converse of
`IsHomogeneous.aeval` for the fresh-variable dilation).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

/-! ## The substituted ruling data -/

/-- The substituted ruling data: `C (asRuleQA a b g Φ k) + T · C (asRuleQB a b g Φ k)`, an element
of `Polynomial S` for every `k`.  This is the vector at which `kleinRAS0` is evaluated after the
substitution `Φ`. -/
private noncomputable def asZW {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (Φ : Fin 5 → S) : Fin 5 → Polynomial S :=
  fun k => Polynomial.C (asRuleQA (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) Φ k)
    + Polynomial.X * Polynomial.C (asRuleQB (algebraMap K S a) (algebraMap K S b)
        (algebraMap K S g) Φ k)

/-! ## Naturality: `aeval` of `asCoeffPoly` -/

/-- Evaluation of the polynomial version of the first ruling vector at a substitution. -/
private theorem aeval_qAS_A {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (Φ : Fin 5 → S) (k : Fin 5) :
    MvPolynomial.aeval (R := K) Φ (qAS_A K a b g k)
      = asRuleQA (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) Φ k := by
  have h := map_asRuleQA (R := MvPolynomial (Fin 5) K) (S := S)
    (MvPolynomial.aeval (R := K) Φ).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin 5) K)) k
  simpa only [qAS_A, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using h

/-- Evaluation of the polynomial version of the second ruling vector at a substitution. -/
private theorem aeval_qAS_B {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (Φ : Fin 5 → S) (k : Fin 5) :
    MvPolynomial.aeval (R := K) Φ (qAS_B K a b g k)
      = asRuleQB (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) Φ k := by
  have h := map_asRuleQB (R := MvPolynomial (Fin 5) K) (S := S)
    (MvPolynomial.aeval (R := K) Φ).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin 5) K)) k
  simpa only [qAS_B, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using h

/-- The coefficientwise evaluation of `asCoeffPoly` at a substitution `Φ`. -/
private theorem map_asCoeffPoly_aeval {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (Φ : Fin 5 → S) :
    Polynomial.mapRingHom ((MvPolynomial.aeval (R := K) Φ).toRingHom) (asCoeffPoly K a b g)
      = kleinRAS0 (Polynomial.C (algebraMap K S a)) (Polynomial.C (algebraMap K S b))
          (Polynomial.C (algebraMap K S g)) (asZW a b g Φ) := by
  have hmain : Polynomial.mapRingHom ((MvPolynomial.aeval (R := K) Φ).toRingHom)
        (asCoeffPoly K a b g)
      = kleinRAS0 (Polynomial.C (algebraMap K S a)) (Polynomial.C (algebraMap K S b))
          (Polynomial.C (algebraMap K S g))
          (fun k => Polynomial.C (asRuleQA (algebraMap K S a) (algebraMap K S b)
                (algebraMap K S g) Φ k)
            + Polynomial.X * Polynomial.C (asRuleQB (algebraMap K S a) (algebraMap K S b)
                (algebraMap K S g) Φ k)) := by
    let ψ : MvPolynomial (Fin 5) K →+* S := (MvPolynomial.aeval (R := K) Φ).toRingHom
    have hψ : ∀ m, ψ m = MvPolynomial.aeval (R := K) Φ m := fun m => rfl
    change Polynomial.mapRingHom ψ (asCoeffPoly K a b g) = _
    rw [asCoeffPoly]
    rw [← map_kleinRAS0 (R := Polynomial (MvPolynomial (Fin 5) K)) (S := Polynomial S)
      (Polynomial.mapRingHom ψ)
      (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C g))
      (fun k => Polynomial.C (qAS_A K a b g k)
        + Polynomial.X * Polynomial.C (qAS_B K a b g k))]
    have h1 : (Polynomial.mapRingHom ψ) (Polynomial.C (MvPolynomial.C a))
        = Polynomial.C (algebraMap K S a) := by
      simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, hψ, MvPolynomial.aeval_C]
    have h2 : (Polynomial.mapRingHom ψ) (Polynomial.C (MvPolynomial.C b))
        = Polynomial.C (algebraMap K S b) := by
      simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, hψ, MvPolynomial.aeval_C]
    have h3 : (Polynomial.mapRingHom ψ) (Polynomial.C (MvPolynomial.C g))
        = Polynomial.C (algebraMap K S g) := by
      simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, hψ, MvPolynomial.aeval_C]
    have h4 : (fun k => (Polynomial.mapRingHom ψ)
          (Polynomial.C (qAS_A K a b g k) + Polynomial.X * Polynomial.C (qAS_B K a b g k)))
        = (fun k => Polynomial.C (asRuleQA (algebraMap K S a) (algebraMap K S b)
                (algebraMap K S g) Φ k)
            + Polynomial.X * Polynomial.C (asRuleQB (algebraMap K S a) (algebraMap K S b)
                (algebraMap K S g) Φ k)) := by
      funext k
      simp only [Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, hψ]
      rw [aeval_qAS_A (K := K) (S := S) a b g Φ k, aeval_qAS_B (K := K) (S := S) a b g Φ k]
    rw [h1, h2, h3, h4]
  rw [hmain]
  rfl

/-- **Evaluation of `asCoeff6` at a substitution**: the `j`-th `T`-coefficient of the substituted
`kleinRAS0`-expression. -/
private theorem aeval_asCoeff6_gen {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (Φ : Fin 5 → S) (j : ℕ) :
    MvPolynomial.aeval (R := K) Φ (asCoeff6 K a b g j)
      = (kleinRAS0 (Polynomial.C (algebraMap K S a)) (Polynomial.C (algebraMap K S b))
          (Polynomial.C (algebraMap K S g)) (asZW a b g Φ)).coeff j := by
  rw [asCoeff6_eq]
  have hc : MvPolynomial.aeval (R := K) Φ ((asCoeffPoly K a b g).coeff j)
      = (Polynomial.mapRingHom ((MvPolynomial.aeval (R := K) Φ).toRingHom)
          (asCoeffPoly K a b g)).coeff j := by
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    rfl
  rw [hc, map_asCoeffPoly_aeval]

/-! ## The dilation law -/

/-- The substituted ruling data dilates: `A` and `B` are quadratic in the curve point. -/
private theorem asZW_smul {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (s : S) (x : Fin 5 → S) :
    asZW a b g (fun i => s * x i) = fun k => Polynomial.C (s ^ 2) * asZW a b g x k := by
  funext k
  simp only [asZW]
  rw [as_hom_asRuleQA_smul (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) s x k,
    as_hom_asRuleQB_smul (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) s x k]
  rw [Polynomial.C_mul, Polynomial.C_mul]
  first | refl_ring1 | ring

/-- **The dilation law of `asCoeff6`**: substituting `X i ↦ s * x i` multiplies the evaluation by
`s ^ 6`. -/
private theorem asCoeff6_dilation_gen {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (a b g : K) (s : S) (x : Fin 5 → S) (j : ℕ) :
    MvPolynomial.aeval (R := K) (fun i => s * x i) (asCoeff6 K a b g j)
      = s ^ 6 * MvPolynomial.aeval (R := K) x (asCoeff6 K a b g j) := by
  rw [aeval_asCoeff6_gen (Φ := (fun i => s * x i)), aeval_asCoeff6_gen (Φ := x)]
  rw [asZW_smul]
  rw [kleinRAS0_smul (Polynomial.C (algebraMap K S a)) (Polynomial.C (algebraMap K S b))
      (Polynomial.C (algebraMap K S g)) (Polynomial.C (s ^ 2)) (asZW a b g x)]
  rw [← Polynomial.C_pow, show (s ^ 2) ^ 3 = s ^ 6 by ring, Polynomial.coeff_C_mul]

/-! ## The target -/

/-- Evaluating at the variables of a polynomial ring is the coefficient extension
`K[X 0,…,X 4] → K[X 0,…,X 4][T]`. -/
private theorem aeval_CX {K : Type} [CommRing K] (f : MvPolynomial (Fin 5) K) :
    MvPolynomial.aeval (R := K) (fun i => Polynomial.C (MvPolynomial.X i)) f = Polynomial.C f := by
  have h : MvPolynomial.aeval (R := K) (fun i => Polynomial.C (MvPolynomial.X i))
      = (IsScalarTower.toAlgHom K (MvPolynomial (Fin 5) K)
          (Polynomial (MvPolynomial (Fin 5) K))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  rw [h]
  rfl

theorem asCoeff6_isHomogeneous {K : Type} [CommRing K] (a b g : K) (j : ℕ) :
    (Work.MotAS.asCoeff6 K a b g j).IsHomogeneous 6 := by
  refine isHomogeneous_of_aeval_smul (Work.MotAS.asCoeff6 K a b g j) 6 ?_
  have key := asCoeff6_dilation_gen (K := K) (S := Polynomial (MvPolynomial (Fin 5) K))
      a b g Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i)) j
  rw [show (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i) * Polynomial.X)
      = (fun i : Fin 5 => Polynomial.X * Polynomial.C (MvPolynomial.X i)) from by
        funext i; rw [mul_comm]]
  rw [key, aeval_CX]

end Work.MotAS
