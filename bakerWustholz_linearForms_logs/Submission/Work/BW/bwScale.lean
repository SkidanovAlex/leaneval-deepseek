import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The torus action on the coordinate ring of `(P¹)^{N+1}`.

`scaleEnd N lam` is the ℂ-algebra endomorphism of `MR N = ℂ[X_{i,0},X_{i,1}]` sending
`X_{i,j} ↦ lam i * X_{i,j}`.  `wtPow N lam d = ∏ᵢ lamᵢ^{dᵢ}` and `degSup N φ` is the finite set
of multidegrees of the monomials of `φ`.
-/

namespace Work.BW

open MvPolynomial

/-- The scaling endomorphism `X_{i,j} ↦ lam i * X_{i,j}` of `MR N`. -/
noncomputable def scaleEnd (N : ℕ) (lam : Fin (N + 1) → ℂ) : MR N →ₐ[ℂ] MR N :=
  MvPolynomial.aeval (fun v : Fin (N + 1) × Fin 2 => MvPolynomial.C (lam v.1) * MvPolynomial.X v)

/-- The weight `∏ᵢ lamᵢ^{dᵢ}` attached to a multidegree `d`. -/
noncomputable def wtPow (N : ℕ) (lam : Fin (N + 1) → ℂ) (d : Fin (N + 1) →₀ ℕ) : ℂ :=
  ∏ i, lam i ^ (d i)

/-- The finite set of multidegrees of the monomials occurring in `φ`. -/
noncomputable def degSup (N : ℕ) (φ : MR N) : Finset (Fin (N + 1) →₀ ℕ) :=
  φ.support.image (Finsupp.weight (mdeg N))

/-- The inverse of a torus point, as a plain complex point. -/
noncomputable def invPt {N : ℕ} (lam : Fin (N + 1) → ℂˣ) : Fin (N + 1) → ℂ :=
  fun i => ((lam i)⁻¹ : ℂˣ)

variable {N : ℕ}

lemma scaleEnd_X (lam : Fin (N + 1) → ℂ) (v : Fin (N + 1) × Fin 2) :
    scaleEnd N lam (MvPolynomial.X v) = MvPolynomial.C (lam v.1) * MvPolynomial.X v := by
  simp [scaleEnd]

lemma scaleEnd_monomial_aux (lam mu : Fin (N + 1) → ℂ) (v : Fin (N + 1) × Fin 2) :
    scaleEnd N lam (MvPolynomial.C (mu v.1) * MvPolynomial.X v) =
      MvPolynomial.C (lam v.1 * mu v.1) * MvPolynomial.X v := by
  rw [map_mul, scaleEnd_X]
  have h : (scaleEnd N lam) (MvPolynomial.C (mu v.1)) = MvPolynomial.C (mu v.1) := by
    simp [scaleEnd]
  rw [h, ← mul_assoc, ← MvPolynomial.C_mul, mul_comm (mu v.1) (lam v.1)]

lemma scaleEnd_comp (lam mu : Fin (N + 1) → ℂ) :
    (scaleEnd N lam).comp (scaleEnd N mu) = scaleEnd N (fun i => lam i * mu i) := by
  rw [scaleEnd, scaleEnd, scaleEnd, MvPolynomial.comp_aeval]
  congr 1
  funext v
  exact scaleEnd_monomial_aux lam mu v

lemma scaleEnd_one : scaleEnd N (fun _ : Fin (N + 1) => (1 : ℂ)) = AlgHom.id ℂ (MR N) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [scaleEnd_X]

lemma scaleEnd_mul_invPt (lam : Fin (N + 1) → ℂˣ) :
    (fun i => (lam i : ℂ) * invPt lam i) = fun _ : Fin (N + 1) => (1 : ℂ) := by
  funext i
  simp [invPt]

lemma scaleEnd_invPt_mul (lam : Fin (N + 1) → ℂˣ) :
    (fun i => invPt lam i * (lam i : ℂ)) = fun _ : Fin (N + 1) => (1 : ℂ) := by
  funext i
  simp [invPt]

lemma scaleEnd_comp_invPt (lam : Fin (N + 1) → ℂˣ) :
    (scaleEnd N (fun i => (lam i : ℂ))).comp (scaleEnd N (invPt lam)) = AlgHom.id ℂ (MR N) := by
  rw [scaleEnd_comp, scaleEnd_mul_invPt, scaleEnd_one]


lemma scaleEnd_invPt_comp (lam : Fin (N + 1) → ℂˣ) :
    (scaleEnd N (invPt lam)).comp (scaleEnd N (fun i => (lam i : ℂ))) = AlgHom.id ℂ (MR N) := by
  rw [scaleEnd_comp, scaleEnd_invPt_mul, scaleEnd_one]

lemma wtPow_pt (t : ℂ) (c : Fin (N + 1) → ℕ) (e : Fin (N + 1) →₀ ℕ) :
    wtPow N (fun i => t ^ (c i)) e = t ^ (∑ i, c i * e i) := by
  rw [wtPow]
  have h : ∀ i : Fin (N + 1), (t ^ (c i)) ^ (e i) = t ^ (c i * e i) := fun i => by rw [pow_mul]
  simp only [h]
  rw [Finset.prod_pow_eq_pow_sum]

/-- The quotient class of a scaled sum of multihomogeneous components, expanded. -/
lemma mk_scale_sum (p : Ideal (MR N)) (D : Finset (Fin (N + 1) →₀ ℕ)) (t : ℂ)
    (c : Fin (N + 1) → ℕ) (r : MR N) :
    (Ideal.Quotient.mkₐ ℂ p)
        (∑ e ∈ D, wtPow N (fun i => t ^ (c i)) e •
          MvPolynomial.weightedHomogeneousComponent (mdeg N) e r)
      = ∑ e ∈ D, (algebraMap ℂ (MR N ⧸ p) t) ^ (∑ i, c i * e i) *
          (Ideal.Quotient.mkₐ ℂ p) (MvPolynomial.weightedHomogeneousComponent (mdeg N) e r) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Algebra.smul_def, map_mul, AlgHomClass.commutes, wtPow_pt, map_pow]

end Work.BW
