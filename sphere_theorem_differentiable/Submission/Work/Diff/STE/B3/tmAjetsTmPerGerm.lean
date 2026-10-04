import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **The germ of the periodisation of a cube-supported real function.**

Let `f : (Fin n → ℝ) → ℝ` have its support in the open unit cube `(-1/2, 1/2)^n`.  Then at every
point `x` of the closed unit cube `(0,1]^n` the complexification of the real periodisation
`tmPer f` agrees, on a whole neighbourhood of `x`, with the finite sum of the translates
`f (· + k)` over the `2^n` lattice vectors `k ∈ csqp_boxIdx (Fin n) = {-1,0}^n`.

This is the pointwise germ form of
`Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx`, transported through the definition
`tmPer f = re ∘ (periodisation of the complexification of f)` (the real part commutes with the
finite sum, and `((r : ℝ) : ℂ) = ofReal r` commutes with `Finset.sum`). -/
theorem tmAjetsTmPerGerm {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (x : Fin n → ℝ) (hx : x ∈ Work.Diff.STE.unitCube (ι := Fin n)) :
    Filter.EventuallyEq (nhds x)
      (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ))
      (fun y : Fin n → ℝ => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) := by
  -- Prove the statement with the lattice vector `iVec k` unfolded (`iVec k = fun i => (k i : ℝ)`):
  -- the periodisation lemma is stated in that form, and the two forms are definitionally equal.
  have key : Filter.EventuallyEq (nhds x)
      (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ))
      (fun y : Fin n → ℝ => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        ((f (y + fun i => (k i : ℝ)) : ℝ) : ℂ)) := by
    set F : (Fin n → ℝ) → ℂ := fun y => ((f y : ℝ) : ℂ) with hF
    have hFsupp : Function.support F ⊆
        Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
      intro z hz
      refine hsupp ?_
      rw [Function.mem_support] at hz ⊢
      intro h
      exact hz (by rw [hF]; simp [h])
    have hP := Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx (ι := Fin n) hFsupp hx
    filter_upwards [hP] with y hy
    -- `tmPer f y` is the real part of the periodisation of `F = ofReal ∘ f`
    have h1 : ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)
        = (((∑' m : Fin n → ℤ, F (y + Work.Diff.STE.iVec m)).re : ℝ) : ℂ) := by
      simp only [Work.Diff.STE.B3.tmPer, hF]
    rw [h1]
    have hy' : (∑' m : Fin n → ℤ, F (y + Work.Diff.STE.iVec m))
        = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), F (y + Work.Diff.STE.iVec k) := hy
    rw [hy', Complex.re_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => rfl)
  exact key

end Work.Diff.STE.B3
