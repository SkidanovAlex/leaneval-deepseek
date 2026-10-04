import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat.galerkin

theorem coeff_box_sum_bound {n N : ℕ} {T tstar : ℝ} (htstarT : tstar < T)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hdiff : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ k ∈ Work.Diff.STE.Flat.box n N, ∀ i j : Fin n,
      DifferentiableAt ℝ (fun s : ℝ => c s k i j) t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0:ℝ) tstar,
      (∑ k : Work.Diff.STE.Flat.box n N, ∑ i : Fin n, ∑ j : Fin n, ‖c t k.1 i j‖) ≤ B := by
  -- `Icc 0 tstar` sits inside the interval on which the coefficients are differentiable
  have hsub : Set.Icc (0:ℝ) tstar ⊆ Set.Ico (0:ℝ) T := fun t ht =>
    ⟨ht.1, lt_of_le_of_lt ht.2 htstarT⟩
  -- the box sum of entry norms is continuous there
  have hcont : ContinuousOn (fun t : ℝ => ∑ k : Work.Diff.STE.Flat.box n N, ∑ i : Fin n,
      ∑ j : Fin n, ‖c t k.1 i j‖) (Set.Icc (0:ℝ) tstar) := by
    refine continuousOn_finsetSum _ ?_
    intro k hk
    refine continuousOn_finsetSum _ ?_
    intro i hi
    refine continuousOn_finsetSum _ ?_
    intro j hj
    have hd : DifferentiableOn ℝ (fun s : ℝ => c s k.1 i j) (Set.Ico (0:ℝ) T) :=
      fun t ht => (hdiff t ht k.1 k.2 i j).differentiableWithinAt
    exact (hd.continuousOn.norm).mono hsub
  -- and a continuous function on a compact interval is bounded
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := tstar)).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have hnn : 0 ≤ ∑ k : Work.Diff.STE.Flat.box n N, ∑ i : Fin n, ∑ j : Fin n, ‖c t k.1 i j‖ :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => norm_nonneg _
  have h1 := hC t ht
  rw [Real.norm_of_nonneg hnn] at h1
  exact le_trans h1 (le_max_left _ _)

end Work.Diff.STE.flat.galerkin
