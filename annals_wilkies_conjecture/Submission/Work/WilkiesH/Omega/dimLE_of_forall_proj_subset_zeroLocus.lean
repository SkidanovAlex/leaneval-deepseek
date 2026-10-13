import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Omega.interior_zeroLocus_eq_empty

namespace Work.WilkiesH.Omega

/-- If for every `(μ+1)`-tuple of coordinates `e` the projection of `V` onto those
coordinates lies in the zero locus of a nonzero polynomial, then `dim V ≤ μ`:
the projection is contained in the zero set of that polynomial, which has empty
interior, so its interior is empty. -/
theorem dimLE_of_forall_proj_subset_zeroLocus {n μ : ℕ} {V : Set (Fin n → ℝ)} (h : ∀ e : Fin (μ + 1) ↪ Fin n, ∃ Q : MvPolynomial (Fin (μ + 1)) ℝ, Q ≠ 0 ∧ ∀ x ∈ V, MvPolynomial.eval (fun i : Fin (μ + 1) => x (e i)) Q = 0) : WilkiesDesign.DimLE V μ := by
  intro e
  obtain ⟨Q, hQ, hVQ⟩ := h e
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  have hsub : (fun x : Fin n → ℝ => x ∘ e) '' V ⊆ {z : Fin (μ + 1) → ℝ | Q.eval z = 0} := by
    rintro z ⟨x, hx, rfl⟩
    exact hVQ x hx
  have hmono : interior ((fun x : Fin n → ℝ => x ∘ e) '' V)
      ⊆ interior {z : Fin (μ + 1) → ℝ | Q.eval z = 0} := interior_mono hsub
  have hmem : y ∈ interior {z : Fin (μ + 1) → ℝ | Q.eval z = 0} := hmono hy
  rw [interior_zeroLocus_eq_empty Q hQ] at hmem
  exact hmem

end Work.WilkiesH.Omega
