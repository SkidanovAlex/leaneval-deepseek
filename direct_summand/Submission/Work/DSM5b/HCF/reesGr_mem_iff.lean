/-
# The graded pieces of the Rees module `⨁_d J^d` of `J = (t_i)`

For `t : Fin n → R` and `J = reesJ t = Ideal.span (Set.range t)`, the `d`-th graded piece
`reesGr t d` of the Rees module `reesM t = range (reesPhi t) ⊆ R[u]` (see
`Submission/Work/DSM5b/HCF/ReesDefs.lean` for the definitions) is the set of elements `c u^d` with
`c ∈ J^d`.  The interesting half is `⊆`: the image of a form `f` of degree `d` is
`C (aeval t f) * X^d` (`reesPhi_aeval_homogeneous`), and `aeval t f = ∑_a (coeff a) t^a` is a sum
of products of `a.degree = d` elements of `J` (`aeval_mem_pow`).  For `⊇` one uses that
`J^d = span ((range t)^d)` (`Submodule.span_pow`); each product `∏_i t (σ i)` of `d` elements of
`J` is the image of the degree-`d` form `∏_i X (σ i)` under `reesPhi t`
(`reesPhi_prod_X`).

The main structural statement is `reesGr_map_eq`: the two ways of describing the `d`-th piece,
namely as `reesPhi t '' {forms of degree d}` and as `{c u^d : c ∈ J^d}`, coincide; the stated
equivalence is its immediate consequence.
-/
import Mathlib
import Submission.Work.DSM5b.HCF.ReesDefs
import Submission.Work.DSM5b.HCF.reesPhi_aeval_homogeneous
import Submission.Work.DSM5b.HCF.prod_pow_mem_pow

open MvPolynomial Polynomial

namespace Work.DSM5b.HCF

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The `R`-linear map `c ↦ C c * X^d`; its image on `J^d` is the `d`-th graded piece of the
Rees module. -/
noncomputable def reesPsi (d : ℕ) : R →ₗ[R] Polynomial R where
  toFun c := Polynomial.C c * Polynomial.X ^ d
  map_add' a b := by simp [Polynomial.C_add, add_mul]
  map_smul' r c := by simp [Algebra.smul_def, Polynomial.C_mul, mul_assoc]

lemma reesPsi_apply (d : ℕ) (c : R) :
    reesPsi (R := R) d c = Polynomial.C c * Polynomial.X ^ d := rfl

/-- The product of the variables indexed by `σ : Fin d → Fin n` is a form of degree `d`. -/
lemma isHomogeneous_prod_X {d : ℕ} (σ : Fin d → Fin n) :
    (∏ i : Fin d, (MvPolynomial.X (σ i) : Work.DSCOH.Poly R n)).IsHomogeneous d := by
  have h := IsHomogeneous.prod (s := (Finset.univ : Finset (Fin d)))
    (φ := fun i => (MvPolynomial.X (σ i) : Work.DSCOH.Poly R n)) (n := fun _ => 1)
    (fun i _ => isHomogeneous_X (R := R) (σ := Fin n) (σ i))
  simpa using h

/-- `reesPhi` of the product of the variables indexed by `σ : Fin d → Fin n`. -/
lemma reesPhi_prod_X (t : Fin n → R) {d : ℕ} (σ : Fin d → Fin n) :
    reesPhi t (∏ i : Fin d, (MvPolynomial.X (σ i) : Work.DSCOH.Poly R n)) =
      Polynomial.C (∏ i, t (σ i)) * Polynomial.X ^ d := by
  rw [map_prod]
  simp only [reesPhi_X]
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]
  congr 1
  rw [Finset.prod_const]
  simp

/-- **The evaluation of a form of degree `d` lies in `J^d`**: writing `aeval t f` as a sum of
monomials `(coeff a) t^a` over `a ∈ f.support`, each `a` has total degree `d`, and
`t^a = ∏_i t_i^{a_i} ∈ J^{a.degree}` is a product of `d` elements of `J` (`prod_pow_mem_pow`). -/
lemma aeval_mem_pow (t : Fin n → R) {f : Work.DSCOH.Poly R n} {d : ℕ}
    (hf : f.IsHomogeneous d) : MvPolynomial.aeval t f ∈ (reesJ t) ^ d := by
  have haeval : MvPolynomial.aeval t f =
      ∑ a ∈ f.support, f.coeff a * a.prod (fun i k => t i ^ k) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.aeval_monomial]
    simp
  rw [haeval]
  apply Submodule.sum_mem
  intro a ha
  have hdeg : a.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (Finsupp.mem_support_iff.mp ha)
  rw [← hdeg]
  exact (reesJ t ^ a.degree).mul_mem_left (f.coeff a)
    (prod_pow_mem_pow (reesJ t) t (fun i => Ideal.subset_span ⟨i, rfl⟩) a)

/-- **The `d`-th graded piece of the Rees module, as a submodule of `R[u]`**: the image of the
degree-`d` forms under `reesPhi t` is exactly the set `{c u^d : c ∈ J^d}`.

`⊆` is `reesPhi_aeval_homogeneous` together with `aeval_mem_pow`; for `⊇` one uses
`J^d = span ((range t)^d)` and `reesPhi_prod_X`, which exhibits `∏_i t (σ i)` as the image of the
form `∏_i X (σ i)`. -/
theorem reesGr_map_eq (t : Fin n → R) (d : ℕ) :
    Submodule.map (reesPhi t).toLinearMap (Work.DSCOH.homSub R n d)
      = Submodule.map (reesPsi (R := R) d) ((reesJ t) ^ d) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    rw [Submodule.mem_comap]
    refine Submodule.mem_map.mpr ⟨MvPolynomial.aeval t f, aeval_mem_pow t ?_, ?_⟩
    · exact hf
    · show reesPsi (R := R) d (MvPolynomial.aeval t f) = reesPhi t f
      rw [reesPhi_aeval_homogeneous t hf, reesPsi_apply]
  · rw [reesJ, Submodule.span_pow, Submodule.map_span, Submodule.span_le]
    rintro p ⟨c, hc, rfl⟩
    obtain ⟨g, hg, hprod⟩ := Set.mem_pow_iff_prod.mp hc
    choose σ hσ using hg
    refine Submodule.mem_map.mpr
      ⟨∏ i : Fin d, (MvPolynomial.X (σ i) : Work.DSCOH.Poly R n), ?_, ?_⟩
    · exact isHomogeneous_prod_X σ
    · show reesPhi t (∏ i, (MvPolynomial.X (σ i) : Work.DSCOH.Poly R n)) =
        reesPsi (R := R) d c
      have hprod' : (∏ i, t (σ i)) = c := by
        rw [← hprod]
        exact Finset.prod_congr rfl fun i _ => hσ i
      rw [reesPhi_prod_X t σ, reesPsi_apply, hprod']

/-- **The graded pieces of the Rees module are the sets `c u^d` with `c ∈ J^d`.**  For
`J = reesJ t = Ideal.span (Set.range t)` and the Rees module `reesM t = range (reesPhi t)` inside
`R[u]` (`reesPhi t : R[X_0,…,X_{n-1}] → R[u]`, `X_i ↦ t_i u`), the `d`-th graded piece
`reesGr t d` (the image of the degree-`d` forms) consists exactly of the elements `C c * X^d`
with `c ∈ J^d`.

Route: `reesPhi` of a monomial `r X^a` is `C (r * ∏ t_i^{a_i}) * X^{|a|}` (proved:
`reesPhi_monomial` in `Submission/Work/DSM5b/HCF/ReesDefs.lean`), so for `f` homogeneous of degree
`d` (use `MvPolynomial.as_sum` and `MvPolynomial.IsHomogeneous`/`mem_homogeneousSubmodule`) the
image is `C (reesEval t f) * X^d`; the product `∏ t_i^{a_i}` with `∑ a_i = d` lies in `J^d`
(multiplication of `d` elements of `J`).  Conversely, a product `∏_{i ∈ s} t i` with `s.card = d`
is `reesEval t (∏_{i ∈ s} X i)`, and membership in `J^d` reduces to its spanning set, giving the
reverse inclusion. -/
theorem reesGr_mem_iff {n : ℕ} {R : Type u} [CommRing R] (t : Fin n → R) (d : ℕ)
    (x : ↥(Work.DSM5b.HCF.reesM t)) :
    x ∈ Work.DSM5b.HCF.reesGr t d ↔
      ∃ c ∈ (Work.DSM5b.HCF.reesJ t) ^ d, x.1 = Polynomial.C c * Polynomial.X ^ d := by
  have hgr : ∀ y : ↥(reesM t), y ∈ reesGr t d ↔
      y.1 ∈ Submodule.map (reesPhi t).toLinearMap (Work.DSCOH.homSub R n d) := by
    intro y
    rw [reesGr, Submodule.mem_comap]
    exact Iff.rfl
  rw [hgr x, reesGr_map_eq t d, Submodule.mem_map]
  exact ⟨fun ⟨c, hc, hcx⟩ => ⟨c, hc, hcx.symm⟩, fun ⟨c, hc, hxc⟩ => ⟨c, hc, hxc.symm⟩⟩

end Work.DSM5b.HCF
