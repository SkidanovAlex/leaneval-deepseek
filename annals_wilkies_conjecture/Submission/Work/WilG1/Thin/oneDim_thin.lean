/-
  WilG1 / Thin / oneDim_thin

  `interior {x | ¬ DifferentiableAt ℝ g x} = ∅` for `g : ℝ → ℝ` whose graph is `Ω`-definable.

  The non-differentiability set is covered (`bad_covered`) by the oscillation sets `oscR g q`,
  `oscL g q` (`q ∈ ℚ`), the corner sets `cornerMax g q`, `cornerMin g q` (`q ∈ ℚ`) and the
  two infinite-derivative sets `infDeriv g 1`, `infDeriv g (-1)`.  Each of these families is
  countable -- the oscillation and the infinite-derivative sets are even finite, being
  `Ω`-definable with empty interior -- so the bad set is countable, hence has empty interior.

  The supporting lemmas live in the sibling modules `oneDim_shape` (the `OShape` formula and
  its realisation), `oneDim_pred` (`Ω`-membership of `oscR`, `oscL`) and `oneDim_fin`
  (finiteness of the oscillation and infinite-derivative sets).
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.bad_covered
import Submission.Work.WilG1.OneDim.thin_corner
import Submission.Work.WilG1.Thin.oneDim_fin

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture Work.WilG1

theorem oneDim_thin {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    interior {x : ℝ | ¬ DifferentiableAt ℝ g x} = ∅ := by
  have hcount : ({x : ℝ | ¬ DifferentiableAt ℝ g x} : Set ℝ).Countable := by
    have hcover : ({x : ℝ | ¬ DifferentiableAt ℝ g x} : Set ℝ) ⊆
        (⋃ q : ℚ, (oscR g (q:ℝ) ∪ oscL g (q:ℝ) ∪ cornerMax g (q:ℝ) ∪
          cornerMin g (q:ℝ))) ∪ infDeriv g 1 ∪ infDeriv g (-1) := by
      intro y hy
      have hy' : y ∈ badSet g := hy
      rcases Work.WilG1.OneDim.bad_covered hy' with ⟨q, hq⟩ | h1 | h2 | ⟨q, hq⟩
      · rcases hq with hq | hq
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inl hq))⟩))
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inr hq))⟩))
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2
      · rcases hq with hq | hq
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inr hq)⟩))
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inr hq⟩))
    refine Set.Countable.mono hcover ?_
    refine Set.Countable.union (Set.Countable.union ?_ ?_) ?_
    · refine Set.countable_iUnion (fun q : ℚ => ?_)
      exact ((((finite_oscR (S := S) (F := F) (D := D) g hg (q:ℝ)).countable.union
        (finite_oscL (S := S) (F := F) (D := D) g hg (q:ℝ)).countable).union
        (Work.WilG1.OneDim.cornerMax_countable g (q:ℝ))).union
        (Work.WilG1.OneDim.cornerMin_countable g (q:ℝ)))
    · exact (finite_infDeriv_one (S := S) (F := F) (D := D) g hg).countable
    · exact (finite_infDeriv_neg_one (S := S) (F := F) (D := D) g hg).countable
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hnb : ({y : ℝ | ¬ DifferentiableAt ℝ g y} : Set ℝ) ∈ 𝓝 x := by
    rwa [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hsubI : Set.Ioo (x - ε) (x + ε) ⊆ {y : ℝ | ¬ DifferentiableAt ℝ g y} := by
    intro y hy
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  exact not_countable_Ioo (by linarith) (hcount.mono hsubI)

end Work.WilG1.Thin
