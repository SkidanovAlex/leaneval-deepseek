import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.Q44Geom.formOf_eval
import Submission.Work.HP.MDEstimates.linFormEvalEq
import Submission.Work.HP.MDEstimates.ratDenClearVec

namespace Work.HP.MDEstimates

/-- A nonzero rational linear form has an integral "denominator-cleared" version: there is a
nonzero integer vector `a` such that every integral point of the hyperplane `g = 0` is orthogonal
to `a`. Proof route: write `g = ∑ i, C (g.coeff (Finsupp.single i 1)) * X i` (degree-1 expansion),
let `N` clear the denominators of the coefficients, and take `a i := N * c i`. -/
theorem linFormIntVec (g : MvPolynomial (Fin 5) ℚ) (hg : g.IsHomogeneous 1) (hgne : g ≠ 0) :
    ∃ a : Fin 5 → ℤ, a ≠ 0 ∧ ∀ x : Fin 5 → ℤ,
      MvPolynomial.eval (Work.Q44Geom.toRatLM x) g = 0 → Work.HP.dotZ x a = 0 := by
  classical
  -- some coefficient of `g` is nonzero
  have hcnz : ∃ i : Fin 5, g.coeff (Finsupp.single i 1) ≠ 0 := by
    obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hgne
    have hdeg : d.degree = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hg hd
    have hmem : d ∈ Set.range (fun a : Fin 5 => Finsupp.single a 1) := by
      rw [Finsupp.range_single_one]
      exact hdeg
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, ?_⟩
    have hi' : Finsupp.single i 1 = d := hi
    rw [hi']
    exact hd
  -- clear denominators
  obtain ⟨N, hNnz, a, hanz, haid⟩ :=
    ratDenClearVec (fun i => g.coeff (Finsupp.single i 1)) hcnz
  refine ⟨a, hanz, ?_⟩
  intro x hx
  have hev := linFormEvalEq hg (Work.Q44Geom.toRatLM x)
  rw [hx] at hev
  have hsum0 : ∑ i, g.coeff (Finsupp.single i 1) * (x i : ℚ) = 0 := hev.symm
  have key : ((Work.HP.dotZ x a : ℤ) : ℚ) = 0 := by
    calc ((Work.HP.dotZ x a : ℤ) : ℚ)
        = ∑ i, (x i : ℚ) * (a i : ℚ) := by
            rw [Work.HP.dotZ_apply]; push_cast; rfl
      _ = ∑ i, (x i : ℚ) * ((N : ℚ) * g.coeff (Finsupp.single i 1)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [haid i]
      _ = (N : ℚ) * ∑ i, g.coeff (Finsupp.single i 1) * (x i : ℚ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
      _ = 0 := by rw [hsum0, mul_zero]
  exact_mod_cast key

end Work.HP.MDEstimates
