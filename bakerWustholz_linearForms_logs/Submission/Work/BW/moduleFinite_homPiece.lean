import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The multihomogeneous piece `homPiece N d` is finite-dimensional: it is contained in the
(total-)homogeneous piece of degree `∑ i, d i`, which is spanned by finitely many monomials. -/
theorem moduleFinite_homPiece (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    Module.Finite ℂ ↥(Work.BW.homPiece N d) := by
  rw [Module.Finite.iff_fg]
  refine Submodule.FG.of_le
    (MvPolynomial.homogeneousSubmodule_fg (Fin (N + 1) × Fin 2) ℂ (∑ i, d i)) ?_
  intro p hp
  rw [MvPolynomial.mem_homogeneousSubmodule, MvPolynomial.IsHomogeneous]
  intro a ha
  have hkey : (Finsupp.degree a : ℕ) = ∑ i, Finsupp.weight (mdeg N) a i := by
    have h : (Finsupp.degree (Finsupp.weight (mdeg N) a) : ℕ) = ∑ v, a v := by
      rw [Finsupp.weight_eq_sum, map_sum]
      simp [mdeg, Finsupp.degree_single]
    rw [Finsupp.degree_eq_sum (f := a),
      (Finsupp.degree_eq_sum (f := Finsupp.weight (mdeg N) a)).symm, h]
  have hwa : Finsupp.weight (mdeg N) a = d := hp ha
  have h1 : Finsupp.weight (1 : Fin (N + 1) × Fin 2 → ℕ) a = Finsupp.degree a := by
    simp only [Finsupp.weight, Finsupp.degree_eq_weight_one]; rfl
  rw [h1, hkey, hwa]

end Work.BW
