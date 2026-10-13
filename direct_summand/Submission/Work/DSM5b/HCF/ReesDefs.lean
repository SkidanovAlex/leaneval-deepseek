/-
# The Rees module `⨁_d J^d` of `J = (t_i)`, as a graded module over `R[X_0,…,X_{n-1}]`

For `t : Fin n → R` and `J = Ideal.span (Set.range t)`, the Rees module `M = ⨁_{d} J^d` is
realised here as an `R`-submodule of the polynomial ring `R[u]`: it is the range of the
`R`-algebra homomorphism

  `reesPhi t : R[X_0,…,X_{n-1}] → R[u],  X_i ↦ t_i · u`,

whose image is the span of the monomials `t^a u^{|a|}`.  The `R[X_0,…,X_{n-1}]`-module structure
`f • x = reesPhi t f * x` is defined by hand on the subtype `reesM t = ↥(range (reesPhi t))`, and
the grading is `reesGr t d = {c u^d : c ∈ J^d}` (the image of the `d`-th homogeneous piece).
-/
import Mathlib
import Submission.Work.DSCOH.Basic

open MvPolynomial Polynomial

namespace Work.DSM5b.HCF

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- **The Rees algebra map** `R[X_0,…,X_{n-1}] → R[u]`, `X_i ↦ t_i · u`.  Its image is the Rees
algebra `R[t_1 u, …, t_n u] = ⨁_d J^d`, `J = (t_i)`. -/
noncomputable def reesPhi (t : Fin n → R) : Work.DSCOH.Poly R n →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun i => Polynomial.C (t i) * Polynomial.X

@[simp] lemma reesPhi_X (t : Fin n → R) (i : Fin n) :
    reesPhi t (MvPolynomial.X i) = Polynomial.C (t i) * Polynomial.X :=
  MvPolynomial.aeval_X _ _

@[simp] lemma reesPhi_C (t : Fin n → R) (r : R) : reesPhi t (MvPolynomial.C r) = Polynomial.C r :=
  MvPolynomial.aeval_C _ _

/-- The image of a monomial under the Rees map: `r X^a ↦ r t^a u^{|a|}`. -/
lemma reesPhi_monomial (t : Fin n → R) (a : Fin n →₀ ℕ) (r : R) :
    reesPhi t (MvPolynomial.monomial a r) =
      Polynomial.C (r * a.prod fun i k => t i ^ k) * Polynomial.X ^ (a.sum fun _ k => k) := by
  rw [reesPhi, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod, Finsupp.prod]
  have h1 : ∀ i ∈ a.support, (Polynomial.C (t i) * Polynomial.X) ^ a i
      = Polynomial.C (t i ^ a i) * Polynomial.X ^ a i := by
    intro i _; rw [mul_pow, map_pow]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib,
    ← map_prod (Polynomial.C : R →+* Polynomial R), ← mul_assoc, ← Polynomial.C_mul]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-! ## The Rees module -/

/-- **The Rees module** `M = ⨁_d J^d`, as the range of the Rees algebra map inside `R[u]`. -/
noncomputable def reesM (t : Fin n → R) : Submodule R (Polynomial R) :=
  (reesPhi t).toLinearMap.range

/-- The ideal `J = (t_i) ⊆ R` of which the Rees module is `⨁_d J^d`. -/
noncomputable def reesJ (t : Fin n → R) : Ideal R := Ideal.span (Set.range t)

lemma reesJ_eq (t : Fin n → R) : reesJ t = Ideal.span (Set.range t) := rfl

lemma mem_reesM {t : Fin n → R} {x : Polynomial R} :
    x ∈ reesM t ↔ ∃ f : Work.DSCOH.Poly R n, reesPhi t f = x :=
  LinearMap.mem_range

noncomputable instance reesM_smul (t : Fin n → R) : SMul (Work.DSCOH.Poly R n) (↥(reesM t)) where
  smul f x := ⟨reesPhi t f * x.1, by
    obtain ⟨g, hg⟩ := mem_reesM.mp x.2
    exact ⟨f * g, by rw [AlgHom.toLinearMap_apply, map_mul, hg]⟩⟩

@[simp] lemma reesM_smul_coe (t : Fin n → R) (f : Work.DSCOH.Poly R n) (x : ↥(reesM t)) :
    (f • x).1 = reesPhi t f * x.1 := rfl

lemma reesM_one_mem (t : Fin n → R) : (1 : Polynomial R) ∈ reesM t :=
  ⟨1, by rw [AlgHom.toLinearMap_apply, map_one]⟩

/-- The element `1` of the Rees module (the generator `1 ∈ J^0 = R`). -/
noncomputable def reesGen (t : Fin n → R) : ↥(reesM t) := ⟨1, reesM_one_mem t⟩

@[simp] lemma reesGen_coe (t : Fin n → R) : (reesGen t).1 = 1 := rfl

noncomputable instance reesM_module (t : Fin n → R) : Module (Work.DSCOH.Poly R n) (↥(reesM t))
    where
  one_smul x := Subtype.ext (by
    show reesPhi t 1 * x.1 = x.1
    rw [map_one, one_mul])
  mul_smul f g x := Subtype.ext (by
    show reesPhi t (f * g) * x.1 = reesPhi t f * (reesPhi t g * x.1)
    rw [map_mul, mul_assoc])
  smul_zero x := Subtype.ext (by simp)
  smul_add f x y := Subtype.ext (by simp [mul_add])
  add_smul f g x := Subtype.ext (by
    show reesPhi t (f + g) * x.1 = reesPhi t f * x.1 + reesPhi t g * x.1
    rw [map_add, add_mul])
  zero_smul x := Subtype.ext (by
    show reesPhi t 0 * x.1 = 0
    rw [map_zero, zero_mul])

noncomputable instance reesM_isScalarTower (t : Fin n → R) :
    IsScalarTower R (Work.DSCOH.Poly R n) (↥(reesM t)) where
  smul_assoc r f x := Subtype.ext (by
    show reesPhi t (r • f) * x.1 = r • (reesPhi t f * x.1)
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, Polynomial.algebraMap_eq,
      ← Polynomial.C_mul', mul_assoc])

/-- **The `d`-th graded piece of the Rees module**: the image of the degree-`d` forms, i.e. the
set of `c u^d` with `c ∈ J^d`. -/
noncomputable def reesGr (t : Fin n → R) (d : ℕ) : Submodule R (↥(reesM t)) :=
  Submodule.comap (Submodule.subtype (reesM t))
    (Submodule.map ((reesPhi t).toLinearMap) (Work.DSCOH.homSub R n d))

lemma mem_reesGr {t : Fin n → R} {d : ℕ} {x : ↥(reesM t)} :
    x ∈ reesGr t d ↔ ∃ f ∈ Work.DSCOH.homSub R n d, reesPhi t f = x.1 := by
  simp only [reesGr, Submodule.mem_comap, Submodule.subtype_apply]
  exact Submodule.mem_map

end Work.DSM5b.HCF
