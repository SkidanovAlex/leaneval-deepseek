import Mathlib
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asRuleMinP_isHomogeneous`

`Work.MotAS.asRuleMinP a b g` (`Submission/Work/MotAS/AsRuleRankDefs.lean`) is the `(0,1)`-minor

  `asRuleQA a b g X 1 · asRuleQB a b g X 0 − asRuleQA a b g X 0 · asRuleQB a b g X 1`

of the two AS ruling vectors, a quartic form in the five AS Galois coordinates `X₀,…,X₄`.  This
file proves that it is homogeneous of degree `4` (`MvPolynomial.IsHomogeneous 4`).

## Route

* `asRuleQA a b g · i` and `asRuleQB a b g · i` are *quadratic forms* in the coordinate vector `c`:
  they satisfy the dilation law `asRuleQA a b g (s • c) i = s ^ 2 · asRuleQA a b g c i` for every
  commutative ring `S` (`as_hom_asRuleQA_smul`, `as_hom_asRuleQB_smul`; the pieces being the
  bilinearity of `kleinBilinAS` and the quadraticity of the Pfaffians `kleinPAS`, which is
  `Work.MotAS.kleinPAS_smul`).  Consequently `asRuleMinP` satisfies the quartic dilation law
  `asRuleMinP_aeval_smul`.
* Naturality of the ruling data under a ring homomorphism is `Work.MotAS.map_asRuleQA` /
  `map_asRuleQB` (`Submission/Work/MotAS/map_asRuleQW.lean`); it converts the dilation law for the
  *function* `asRuleQA a b g · i` into the dilation law for the *polynomial*
  `asRuleQA (C a) (C b) (C g) X i` under `MvPolynomial.aeval`.
* Finally `isHomogeneous_of_aeval_fresh` is the converse of
  `MvPolynomial.IsHomogeneous.aeval` for the *fresh-variable* dilation
  `aeval (fun i => C (X i) * Polynomial.X)`: a polynomial satisfying `P(t·x) = tⁿ P(x)` for a
  formal `t` is homogeneous of degree `n`.  Applying it to `asRuleMinP` (at `t = Polynomial.X`,
  `x i = Polynomial.C (X i)`, over the coefficient ring `K[X₀,…,X₄]`) gives the result.

(The companion statement `Work.MotAS.isHomogeneous_of_aeval_smul`, with the same statement, is
proved independently in `Submission/Work/MotAS/isHomogeneous_of_aeval_smul.lean`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

/-! ## Free homogeneity of the AS ruling data -/

section Free

variable {S : Type*} [CommRing S]

/-- `kleinBilinAS` is linear in its **first** argument. -/
theorem as_hom_kleinBilinAS_smul_left (a b s : S) (u v : Fin 5 → S) :
    kleinBilinAS a b (fun i => s * u i) v = s * kleinBilinAS a b u v := by
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply, Pi.mul_apply]
  first | refl_ring1 | ring

/-- The tangent vectors `asTanQ · k` are linear in the base point. -/
theorem as_hom_asTanQ_smul (a b s : S) (c : Fin 5 → S) (k : Fin 5) :
    asTanQ a b (fun i => s * c i) k = fun i => s * asTanQ a b c k i := by
  funext i
  simp only [asTanQ, Pi.mul_apply, as_hom_kleinBilinAS_smul_left]
  first | refl_ring1 | ring

/-- The polarisation `asPolarP` is homogeneous of degree `2` in `(c, u)`. -/
theorem as_hom_asPolarP_smul (a b g s : S) (c u : Fin 5 → S) (k : Fin 5) :
    asPolarP a b g (fun i => s * c i) (fun i => s * u i) k = s ^ 2 * asPolarP a b g c u k := by
  have h : (fun i => s * c i) + (fun i => s * u i) = fun i => s * (c + u) i := by
    funext i; simp only [Pi.add_apply]; ring
  simp only [asPolarP, h, kleinPAS_smul]
  first | refl_ring1 | ring

/-- **The first ruling vector is homogeneous of degree `2`** in the curve point. -/
theorem as_hom_asRuleQA_smul (a b g s : S) (c : Fin 5 → S) (i : Fin 5) :
    asRuleQA a b g (fun j => s * c j) i = s ^ 2 * asRuleQA a b g c i := by
  simp only [asRuleQA, as_hom_asTanQ_smul, as_hom_asPolarP_smul]

/-- **The second ruling vector is homogeneous of degree `2`** in the curve point. -/
theorem as_hom_asRuleQB_smul (a b g s : S) (c : Fin 5 → S) (i : Fin 5) :
    asRuleQB a b g (fun j => s * c j) i = s ^ 2 * asRuleQB a b g c i := by
  simp only [asRuleQB, as_hom_asTanQ_smul, as_hom_asPolarP_smul]

end Free

/-! ## The two ruling-vector components as polynomials in the Galois coordinates -/

section Klein

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The `k`-th component of the first AS ruling vector, as a polynomial in the five AS Galois
coordinates `X₀,…,X₄` (over the coefficient field `𝕜`). -/
noncomputable def asRuleQX (a b g : 𝕜) (k : Fin 5) : MvPolynomial (Fin 5) 𝕜 :=
  asRuleQA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => MvPolynomial.X i) k

/-- The `k`-th component of the second AS ruling vector, as a polynomial in the five AS Galois
coordinates `X₀,…,X₄`. -/
noncomputable def asRuleQBX (a b g : 𝕜) (k : Fin 5) : MvPolynomial (Fin 5) 𝕜 :=
  asRuleQB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (fun i => MvPolynomial.X i) k

/-- `asRuleMinP` is the `(0,1)`-minor of the two ruling-vector polynomials. -/
theorem asRuleMinP_eq (a b g : 𝕜) :
    asRuleMinP a b g
      = asRuleQX a b g 1 * asRuleQBX a b g 0 - asRuleQX a b g 0 * asRuleQBX a b g 1 := rfl

/-- Evaluation of the first ruling-vector polynomial under a substitution. -/
theorem aeval_asRuleQX {S : Type*} [CommRing S] [Algebra 𝕜 S] (a b g : 𝕜) (k : Fin 5)
    (h : Fin 5 → S) :
    MvPolynomial.aeval h (asRuleQX a b g k)
      = asRuleQA (algebraMap 𝕜 S a) (algebraMap 𝕜 S b) (algebraMap 𝕜 S g) h k := by
  have hh := map_asRuleQA (MvPolynomial.aeval h).toRingHom (MvPolynomial.C a)
    (MvPolynomial.C b) (MvPolynomial.C g) (fun i => MvPolynomial.X i) k
  simpa only [asRuleQX, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using hh

/-- Evaluation of the second ruling-vector polynomial under a substitution. -/
theorem aeval_asRuleQBX {S : Type*} [CommRing S] [Algebra 𝕜 S] (a b g : 𝕜) (k : Fin 5)
    (h : Fin 5 → S) :
    MvPolynomial.aeval h (asRuleQBX a b g k)
      = asRuleQB (algebraMap 𝕜 S a) (algebraMap 𝕜 S b) (algebraMap 𝕜 S g) h k := by
  have hh := map_asRuleQB (MvPolynomial.aeval h).toRingHom (MvPolynomial.C a)
    (MvPolynomial.C b) (MvPolynomial.C g) (fun i => MvPolynomial.X i) k
  simpa only [asRuleQBX, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using hh

/-- **Dilation law of the first ruling-vector polynomial**: it is a quadratic form in the
Galois coordinates. -/
theorem asRuleQX_aeval_smul {S : Type*} [CommRing S] [Algebra 𝕜 S] (a b g : 𝕜) (k : Fin 5)
    (s : S) (x : Fin 5 → S) :
    MvPolynomial.aeval (fun i => s * x i) (asRuleQX a b g k)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQX a b g k) := by
  rw [aeval_asRuleQX (h := fun i => s * x i), aeval_asRuleQX (h := x)]
  exact as_hom_asRuleQA_smul _ _ _ _ _ _

/-- **Dilation law of the second ruling-vector polynomial**. -/
theorem asRuleQBX_aeval_smul {S : Type*} [CommRing S] [Algebra 𝕜 S] (a b g : 𝕜) (k : Fin 5)
    (s : S) (x : Fin 5 → S) :
    MvPolynomial.aeval (fun i => s * x i) (asRuleQBX a b g k)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQBX a b g k) := by
  rw [aeval_asRuleQBX (h := fun i => s * x i), aeval_asRuleQBX (h := x)]
  exact as_hom_asRuleQB_smul _ _ _ _ _ _

/-- **Dilation law of `asRuleMinP`**: it is a quartic form in the Galois coordinates. -/
theorem asRuleMinP_aeval_smul (a b g : 𝕜) {S : Type*} [CommRing S] [Algebra 𝕜 S]
    (s : S) (x : Fin 5 → S) :
    MvPolynomial.aeval (fun i => s * x i) (asRuleMinP a b g)
      = s ^ 4 * MvPolynomial.aeval x (asRuleMinP a b g) := by
  have h1 : MvPolynomial.aeval (fun i => s * x i) (asRuleQX a b g 1)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQX a b g 1) :=
    asRuleQX_aeval_smul a b g 1 s x
  have h2 : MvPolynomial.aeval (fun i => s * x i) (asRuleQBX a b g 0)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQBX a b g 0) :=
    asRuleQBX_aeval_smul a b g 0 s x
  have h3 : MvPolynomial.aeval (fun i => s * x i) (asRuleQX a b g 0)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQX a b g 0) :=
    asRuleQX_aeval_smul a b g 0 s x
  have h4 : MvPolynomial.aeval (fun i => s * x i) (asRuleQBX a b g 1)
      = s ^ 2 * MvPolynomial.aeval x (asRuleQBX a b g 1) :=
    asRuleQBX_aeval_smul a b g 1 s x
  rw [asRuleMinP_eq]
  simp only [map_mul, map_sub]
  rw [h1, h2, h3, h4]
  first | refl_ring1 | ring

end Klein

/-! ## The fresh-variable dilation criterion for homogeneity -/

section Dilate

variable {σ : Type*} {R : Type*} [CommRing R]

/-- **The dilation of a monomial** by the fresh variable `Polynomial.X`:
`aeval (fun i => C (X i) · T) (monomial d c) = C (monomial d c) · T ^ d.degree`. -/
theorem aeval_monomial_dilate (d : σ →₀ ℕ) (c : R) :
    MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)
        (MvPolynomial.monomial d c)
      = Polynomial.C (MvPolynomial.monomial d c) * Polynomial.X ^ d.degree := by
  rw [MvPolynomial.aeval_monomial]
  rw [show algebraMap R (Polynomial (MvPolynomial σ R)) c
      = Polynomial.C (MvPolynomial.C c) from by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
      (Polynomial (MvPolynomial σ R)), Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]]
  rw [Finsupp.prod]
  have h1 : ∀ i ∈ d.support,
      (Polynomial.C (MvPolynomial.X i) * Polynomial.X : Polynomial (MvPolynomial σ R)) ^ (d i)
        = Polynomial.C (MvPolynomial.X i ^ d i) * Polynomial.X ^ (d i) := by
    intro i _
    rw [mul_pow, ← Polynomial.C_pow]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib,
    ← map_prod, MvPolynomial.prod_X_pow_eq_monomial, Finset.prod_pow_eq_pow_sum]
  rw [← MvPolynomial.prod_X_pow_eq_monomial, MvPolynomial.monomial_eq, map_mul, Finsupp.prod,
    Finsupp.degree_apply]
  first | refl_ring1 | ring

/-- **The `T`-coefficient of the dilation** is the homogeneous component:
`(aeval (fun i => C (X i) · T) f).coeff k = homogeneousComponent k f`. -/
theorem coeff_dilate (f : MvPolynomial σ R) (k : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f).coeff k
      = MvPolynomial.homogeneousComponent k f := by
  classical
  have hL : (MvPolynomial.aeval
      (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f).coeff k
      = ∑ d ∈ f.support, (if k = d.degree then MvPolynomial.monomial d (f.coeff d) else 0) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum, ← Polynomial.lcoeff_apply (R := MvPolynomial σ R) k, map_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Polynomial.lcoeff_apply, aeval_monomial_dilate, Polynomial.coeff_C_mul_X_pow]
  have hR : MvPolynomial.homogeneousComponent k f
      = ∑ d ∈ f.support, (if k = d.degree then MvPolynomial.monomial d (f.coeff d) else 0) := by
    rw [MvPolynomial.homogeneousComponent_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hkd : d.degree = k
    · rw [if_pos hkd, if_pos hkd.symm]
    · rw [if_neg hkd, if_neg (fun hc => hkd hc.symm)]
  rw [hL, hR]

/-- **A polynomial whose variables are dilated by a formal variable is homogeneous of the
corresponding degree.**  Converse of `MvPolynomial.IsHomogeneous.aeval` for the substitution
`X i ↦ C (X i) · Polynomial.X`: since `Polynomial.X` is a *fresh* variable, the equality
`P(T·x) = Tⁿ·P(x)` forces every monomial of `P` to have total degree `n`. -/
theorem isHomogeneous_of_aeval_fresh (f : MvPolynomial σ R) (n : ℕ)
    (h : MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f
        = Polynomial.X ^ n * Polynomial.C f) :
    f.IsHomogeneous n := by
  classical
  rw [MvPolynomial.as_sum f]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun d hd => ?_)
  refine MvPolynomial.isHomogeneous_monomial (f.coeff d) ?_
  by_contra hne
  have h2 : (MvPolynomial.aeval
      (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X) f).coeff d.degree
      = (Polynomial.X ^ n * Polynomial.C f).coeff d.degree := by rw [h]
  rw [coeff_dilate f d.degree, mul_comm, Polynomial.coeff_C_mul_X_pow, if_neg hne] at h2
  have hc : (MvPolynomial.homogeneousComponent d.degree f).coeff d = f.coeff d := by
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl]
  rw [h2, MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hd) hc.symm

end Dilate

/-- **The `(0,1)`-minor `asRuleMinP a b g` of the AS ruling vectors is a quartic form.** -/
theorem asRuleMinP_isHomogeneous (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.asRuleMinP a b g).IsHomogeneous 4 := by
  refine isHomogeneous_of_aeval_fresh (Work.MotAS.asRuleMinP a b g) 4 ?_
  have hscal := asRuleMinP_aeval_smul (𝕜 := K) a b g
    (s := (Polynomial.X : Polynomial (MvPolynomial (Fin 5) K)))
    (x := (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i) :
      Fin 5 → Polynomial (MvPolynomial (Fin 5) K)))
  have hsub : (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i) * Polynomial.X :
        Fin 5 → Polynomial (MvPolynomial (Fin 5) K))
      = fun i => Polynomial.X * Polynomial.C (MvPolynomial.X i) := by
    funext i; rw [mul_comm]
  have hC : MvPolynomial.aeval (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i))
      (Work.MotAS.asRuleMinP a b g) = Polynomial.C (Work.MotAS.asRuleMinP a b g) := by
    have h : MvPolynomial.aeval (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i))
        = IsScalarTower.toAlgHom K (MvPolynomial (Fin 5) K)
            (Polynomial (MvPolynomial (Fin 5) K)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    rw [h]
    change (algebraMap (MvPolynomial (Fin 5) K) (Polynomial (MvPolynomial (Fin 5) K)))
        (Work.MotAS.asRuleMinP a b g) = Polynomial.C (Work.MotAS.asRuleMinP a b g)
    rw [Polynomial.algebraMap_eq]
  rw [hsub, hscal, hC]

end Work.MotAS
