import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.MDEstimates.WClassDefs
import Submission.Work.HP.MDEstimates.q44_eval_verPolyQ
import Submission.Work.HP.MDEstimates.q44_exists_ratRepr

namespace Work.HP.MDEstimates

open MvPolynomial Finset

/-- `formEval 4 4 a` at the point `∑_j s_j v_j` (`s` rational) is the degree-`4` polynomial in
`s` whose coefficients are the witness class `wClass v a`.  This is the exact identity behind
the "witness class determines the restriction to `L`". -/
lemma formEval_eq_wClass_sum (v : Fin 3 → (Fin 5 → ℤ)) (a : Work.HP.Mon 4 4 → ℤ)
    (s : Fin 3 → ℚ) :
    Work.HP.formEval 4 4 a (fun i => ∑ j : Fin 3, s j * (v j i : ℚ))
      = ∑ e : Work.HP.Tri4,
          ((Work.HP.wClass v a e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
  have hinner : ∀ m : Work.HP.Mon 4 4,
      ∏ i : Fin 5, (∑ j : Fin 3, s j * (v j i : ℚ)) ^ (m.1 i : ℕ)
        = ∑ e : Work.HP.Tri4,
            ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
    intro m
    rw [← eval_verPolyQ_lin v s m]
    exact q44_eval_verPolyQ v s m
  simp only [Work.HP.formEval, Work.HP.veronese]
  calc ∑ m : Work.HP.Mon 4 4,
        ((a m : ℤ) : ℚ) * ∏ i : Fin 5, (∑ j : Fin 3, s j * (v j i : ℚ)) ^ (m.1 i : ℕ)
      = ∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) *
          (∑ e : Work.HP.Tri4, ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) *
            ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hinner m]
    _ = ∑ m : Work.HP.Mon 4 4, ∑ e : Work.HP.Tri4, ((a m : ℤ) : ℚ) *
          (((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ e : Work.HP.Tri4, ∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) *
          (((Work.HP.wCoeff v e.1 m : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j)) :=
        Finset.sum_comm
    _ = ∑ e : Work.HP.Tri4,
          (∑ m : Work.HP.Mon 4 4, ((a m : ℤ) : ℚ) * ((Work.HP.wCoeff v e.1 m : ℤ) : ℚ)) *
            ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = ∑ e : Work.HP.Tri4,
          ((Work.HP.wClass v a e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        congr 1
        rw [Work.HP.wClass]
        push_cast
        rfl

/-- If two coefficient vectors of quartic forms have the same witness class `wClass v a`
relative to a triple `v` of `ℤ`-linearly independent vectors that all lie in a rank-`3`
sublattice `L ⊆ ℤ^5` (so that the `ℚ`-span of `v` is the whole `ℚ`-span of `L`), then the
two forms agree at every point of `L`.  This is the key fact behind the "witness class"
fibre count: a class determines the restriction of the form to `L`. -/
theorem q44_wclass_determines {L : Submodule ℤ (Fin 5 → ℤ)} (hL : Work.HP.rk L = 3)
    {v : Fin 3 → (Fin 5 → ℤ)} (hv : LinearIndependent ℤ v) (hvL : ∀ j, v j ∈ L)
    {a a' : Work.HP.Mon 4 4 → ℤ} (h : Work.HP.wClass v a = Work.HP.wClass v a') :
    ∀ u : Fin 5 → ℤ, u ∈ L → Work.HP.formEval 4 4 a u = Work.HP.formEval 4 4 a' u := by
  intro u hu
  obtain ⟨s, hs⟩ := q44_exists_ratRepr hL hv hvL hu
  have key : ∀ b : Work.HP.Mon 4 4 → ℤ,
      ((Work.HP.formEval 4 4 b u : ℤ) : ℚ)
        = ∑ e : Work.HP.Tri4,
            ((Work.HP.wClass v b e : ℤ) : ℚ) * ∏ j : Fin 3, s j ^ ((e.1 : Fin 3 →₀ ℕ) j) := by
    intro b
    have h1 : ((Work.HP.formEval 4 4 b u : ℤ) : ℚ)
        = Work.HP.formEval 4 4 b (fun i => (u i : ℚ)) := by
      simp only [Work.HP.formEval, Work.HP.veronese]
      push_cast
      rfl
    have h2 : Work.HP.formEval 4 4 b (fun i => (u i : ℚ))
        = Work.HP.formEval 4 4 b (fun i => ∑ j : Fin 3, s j * (v j i : ℚ)) := by
      congr 1
      funext i
      exact hs i
    rw [h1, h2, formEval_eq_wClass_sum]
  have hcast : ((Work.HP.formEval 4 4 a u : ℤ) : ℚ)
      = ((Work.HP.formEval 4 4 a' u : ℤ) : ℚ) := by
    rw [key a, key a']
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [h]
  exact Int.cast_injective hcast

end Work.HP.MDEstimates
