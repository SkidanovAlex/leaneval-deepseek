import Mathlib
import Submission.Work.HP.MDEstimates.WClassDefs

namespace Work.HP.MDEstimates

open MvPolynomial Finset

/-- Evaluating the `ℚ`-model `verPolyQ v m` of the `m`-th coordinate of `ν(∑_j t_j v_j)` at
rational `s` expands as the sum of the witness-class coefficients against the monomials. -/
lemma q44_eval_verPolyQ (v : Fin 3 → (Fin 5 → ℤ)) (s : Fin 3 → ℚ) (m : Work.HP.Mon 4 4) :
    MvPolynomial.eval s (Work.HP.MDEstimates.verPolyQ v m)
      = ∑ e : Work.HP.Tri4,
          ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
  -- Expand the evaluation as a sum of coefficients against monomials, over the support.
  rw [MvPolynomial.eval_eq']
  -- The support of a degree-`4` homogeneous polynomial consists of degree-`4` exponents.
  set F : Finset (Fin 3 →₀ ℕ) := Finset.univ.image (fun e : Work.HP.Tri4 => e.1) with hF
  have hsub : (verPolyQ v m).support ⊆ F := by
    intro d hd
    rw [hF, Finset.mem_image]
    have hc : (verPolyQ v m).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hdeg : d.sum (fun _ n => n) = 4 := by
      have h4 : Finsupp.degree d = 4 := by
        by_contra h
        exact hc ((verPolyQ_isHomogeneous v m).coeff_eq_zero h)
      exact h4
    exact ⟨⟨d, hdeg⟩, Finset.mem_univ _, rfl⟩
  -- Replace the support by `F` (the coefficients vanish off the support).
  have h1 : ∑ d ∈ (verPolyQ v m).support, (verPolyQ v m).coeff d * ∏ i : Fin 3, s i ^ d i
      = ∑ d ∈ F, (verPolyQ v m).coeff d * ∏ i : Fin 3, s i ^ d i :=
    Finset.sum_subset hsub (fun x _ hx => by rw [MvPolynomial.notMem_support_iff.mp hx]; simp)
  -- Reindex `F` as the subtype of degree-`4` exponents.
  have h2 : ∑ d ∈ F, (verPolyQ v m).coeff d * ∏ i : Fin 3, s i ^ d i
      = ∑ e : Work.HP.Tri4, (verPolyQ v m).coeff e.1 * ∏ i : Fin 3, s i ^ (e.1 i) := by
    rw [hF]
    exact Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)
  rw [h1, h2]
  -- Match the `ℚ`-model coefficients with the integral witness coefficients.
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [verPolyQ_coeff]
  rfl

end Work.HP.MDEstimates
