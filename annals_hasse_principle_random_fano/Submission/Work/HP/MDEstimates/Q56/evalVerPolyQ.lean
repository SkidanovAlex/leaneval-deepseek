import Mathlib
import Submission.Work.HP.MDEstimates.WClassDefs

namespace Work.HP.MDEstimates.Q56

/-- Evaluating the `ℚ`-model `verPolyQ v m` of the `m`-th coordinate of `ν(∑_j t_j v_j)`
at a rational point `s` is the sum, over the degree-`4` exponent vectors `e`, of the
witness-class coefficient `wCoeff v e m` against the monomial `∏_j s_j^{e_j}`. -/
lemma evalVerPolyQ (v : Fin 3 → (Fin 5 → ℤ)) (s : Fin 3 → ℚ) (m : Work.HP.Mon 4 4) :
    MvPolynomial.eval s (Work.HP.MDEstimates.verPolyQ v m)
      = ∑ e : Work.HP.Tri4,
          ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
  -- Expand the evaluation of a multivariate polynomial as the sum of its coefficients
  -- against the corresponding monomials, indexed by the support.
  rw [MvPolynomial.eval_eq']
  -- `verPolyQ v m` is homogeneous of degree `4`, so its support lies in the image of `Tri4`.
  set F : Finset (Fin 3 →₀ ℕ) := Finset.univ.image (fun e : Work.HP.Tri4 => e.1) with hF
  have hsub : (Work.HP.MDEstimates.verPolyQ v m).support ⊆ F := by
    intro d hd
    rw [hF, Finset.mem_image]
    refine ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩
    have hc : (Work.HP.MDEstimates.verPolyQ v m).coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have h4 : Finsupp.degree d = 4 := by
      by_contra h
      exact hc ((Work.HP.MDEstimates.verPolyQ_isHomogeneous v m).coeff_eq_zero h)
    exact h4
  -- Enlarge the support to that image (the extra terms are zero).
  rw [Finset.sum_subset hsub (fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.mp hx, zero_mul])]
  -- Reindex the image by the subtype `Tri4` of degree-`4` exponent vectors.
  rw [hF]
  rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
  -- Identify the `ℚ`-coefficients with the integral witness coefficients.
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Work.HP.MDEstimates.verPolyQ_coeff]
  rfl

end Work.HP.MDEstimates.Q56
