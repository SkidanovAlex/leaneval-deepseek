import Mathlib
import Submission.Work.DSM5b.HCF.ReesDefs

namespace Work.DSM5b.HCF

universe u

open MvPolynomial

/-- **A form of degree `d` maps under `reesPhi` to `C c · u^d`.**  If `f` is a form of degree `d`
(i.e. `f ∈ homSub R n d = homogeneousSubmodule R d`), then its image under the Rees map
`reesPhi t : R[X_0,…,X_{n-1}] → R[u]`, `X_i ↦ t_i u`, is `C c * X^d` where `c` is the `d`-th
coefficient of the image.  (Concretely the image of a monomial `r X^a` of total degree `d` is
`C (r ∏ t_i^{a_i}) * X^d`, so the image is a sum of such terms.) -/
lemma reesPhi_eq_C_mul_X_pow_of_mem_homSub {n : ℕ} {R : Type u} [CommRing R] {t : Fin n → R}
    {d : ℕ} {f : Work.DSCOH.Poly R n} (hf : f ∈ Work.DSCOH.homSub R n d) :
    reesPhi t f = Polynomial.C ((reesPhi t f).coeff d) * Polynomial.X ^ d := by
  have hdeg : ∀ v ∈ f.support, (v.sum fun _ k => k) = d := by
    intro v hv
    have hvne : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
    have hd : v.degree = d := by
      by_contra hne
      exact hvne (hf.coeff_eq_zero hne)
    show (v.sum fun _ k => k) = d
    rw [show (v.sum fun _ k => k) = v.degree from rfl, hd]
  have heq : reesPhi t f =
      Polynomial.C (∑ v ∈ f.support, f.coeff v * v.prod fun i k => t i ^ k) *
        Polynomial.X ^ d := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    trans ∑ v ∈ f.support,
        Polynomial.C (f.coeff v * v.prod fun i k => t i ^ k) * Polynomial.X ^ d
    · exact Finset.sum_congr rfl fun v hv => by
        rw [reesPhi_monomial t v (f.coeff v), hdeg v hv]
    · rw [← Finset.sum_mul]
      congr 1
      exact (map_sum Polynomial.C
        (fun v => f.coeff v * v.prod fun i k => t i ^ k) f.support).symm
  rw [heq, Polynomial.coeff_C_mul_X_pow]
  simp

/-- **The graded pieces of the Rees module are of the form `C c · u^d`.**  Any element `x` of the
`d`-th graded piece `reesGr t d` is `C c * X^d` in `R[u]`, with `c` the `d`-th coefficient of `x`. -/
lemma reesGr_eq_C_mul_X_pow {n : ℕ} {R : Type u} [CommRing R] {t : Fin n → R} {j : ℕ}
    {x : ↥(reesM t)} (hx : x ∈ reesGr t j) :
    x.1 = Polynomial.C (x.1.coeff j) * Polynomial.X ^ j := by
  obtain ⟨f, hf, hfe⟩ := mem_reesGr.mp hx
  rw [← hfe]
  exact reesPhi_eq_C_mul_X_pow_of_mem_homSub hf

/-- **The Rees module is the internal direct sum of its graded pieces.**  For
`J = reesJ t = Ideal.span (Set.range t)`, `reesM t = range (reesPhi t) ⊆ R[u]` (with
`reesPhi t : R[X_0,…,X_{n-1}] → R[u]`, `X_i ↦ t_i u`) and `reesGr t d = {c u^d : c ∈ J^d}`
(the image of the degree-`d` forms), the family `reesGr t` is an internal direct sum: every element
of `reesM t` is a sum of its `u`-homogeneous components, and these are independent.

Route: use `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`;
* independence: `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`; a relation `∑_{d∈s} x_d = 0` with
  `x_d ∈ reesGr t d` lifts to `∑_{d ∈ s} C c_d * X^d = 0` in `R[u]`, and taking `Polynomial.coeff d`
  gives `c_d = 0` (use the description of the pieces, or `reesPhi_monomial` + homogeneity);
* spanning: every element of `reesM t` is `reesPhi t f = ∑_d reesPhi t (f_d)` where `f_d` is the
  `d`-th homogeneous component of `f` (`MvPolynomial.sum_homogeneousComponent`,
  `MvPolynomial.homogeneousComponent_mem`), and each `reesPhi t (f_d)` lies in `reesGr t d`. -/
theorem reesGr_isInternal {n : ℕ} {R : Type u} [CommRing R] (t : Fin n → R) :
    DirectSum.IsInternal (Work.DSM5b.HCF.reesGr t) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- **Independence.**  A relation `∑_{j ∈ s} x_j = 0` with `x_j ∈ reesGr t j` forces `x_i = 0`:
    -- each `x_j` is `C c_j * X^j`, and taking the `i`-th coefficient gives `c_i = 0`.
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0 i hi
    have hcoeff : (v i).1.coeff i = 0 := by
      have hcoe := Submodule.coe_sum (reesM t) v s
      rw [hv0] at hcoe
      have hcoe' : ∑ j ∈ s, (v j).1 = 0 := by simpa using hcoe.symm
      have hsum : ∑ j ∈ s, ((v j).1).coeff i = 0 := by
        have h := congrArg (Polynomial.lcoeff R i) hcoe'
        rw [map_sum, map_zero] at h
        simpa [Polynomial.lcoeff_apply] using h
      have hsingle := Finset.sum_eq_single_of_mem (f := fun j => ((v j).1).coeff i) i hi
        (fun j hj hji => by
          rw [reesGr_eq_C_mul_X_pow (hv j hj), Polynomial.coeff_C_mul_X_pow]
          split_ifs with hij
          · exact absurd hij.symm hji
          · rfl)
      rw [hsingle] at hsum
      exact hsum
    apply Subtype.ext
    rw [reesGr_eq_C_mul_X_pow (hv i hi), hcoeff]
    simp
  · -- **Spanning.**  Writing `f = ∑_a monomial a (f.coeff a)` (finitely many `a`), the element
    -- `reesPhi t f ∈ reesM t` is the sum of the `reesPhi t (monomial a (f.coeff a))`, each of
    -- which lies in the graded piece `reesGr t a.degree`.
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨f, hf⟩ := mem_reesM.mp x.2
    have hxsum : (∑ a ∈ f.support, (⟨reesPhi t (MvPolynomial.monomial a (f.coeff a)),
        ⟨MvPolynomial.monomial a (f.coeff a), rfl⟩⟩ : ↥(reesM t))) = x := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← hf]
      conv_rhs => rw [MvPolynomial.as_sum f]
      rw [map_sum]
    rw [← hxsum]
    apply Submodule.sum_mem
    intro a ha
    refine Submodule.mem_iSup_of_mem a.degree ?_
    exact mem_reesGr.mpr ⟨MvPolynomial.monomial a (f.coeff a), by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.isHomogeneous_monomial _ rfl, rfl⟩

end Work.DSM5b.HCF
