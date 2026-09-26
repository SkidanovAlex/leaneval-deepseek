import Mathlib
import Submission.Work.Core.Torus

namespace Work.Geometry

/-- Reduction of an arbitrary real number into the fundamental interval `[0, c]`
for a function that is periodic with period `c > 0`: some point of `[0, c]` has
the same value. -/
private lemma periodic_reduce {β : Type*} (c : ℝ) (hc : 0 < c) (g : ℝ → β)
    (hg : Function.Periodic g c) (x : ℝ) :
    ∃ x' ∈ Set.Icc (0:ℝ) c, g x' = g x := by
  refine ⟨Int.fract (x / c) * c, ⟨?_, ?_⟩, ?_⟩
  · exact mul_nonneg (Int.fract_nonneg _) hc.le
  · have h1 : Int.fract (x / c) < 1 := Int.fract_lt_one _
    have := mul_lt_mul_of_pos_right h1 hc
    simpa using this.le
  · have h2 : Int.fract (x / c) * c + (⌊x / c⌋ : ℝ) * c = x := by
      rw [← add_mul, Int.fract_add_floor, div_mul_cancel₀ x (ne_of_gt hc)]
    have hstep :
        g (Int.fract (x / c) * c + (⌊x / c⌋ : ℝ) * c) = g (Int.fract (x / c) * c) :=
      hg.int_mul ⌊x / c⌋ _
    have hxx : g x = g (Int.fract (x / c) * c) := by
      conv_lhs => rw [← h2]
      exact hstep
    exact hxx.symm

theorem periodic_bounded (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hcont : Continuous (fun p : ℝ × ℝ => psi p.1 p.2))
    (hper1 : ∀ x y, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y, psi x (y + 2 * Real.pi) = psi x y) :
    Bornology.IsBounded (Set.range fun p : ℝ × ℝ => psi p.1 p.2) := by
  have hc : (0:ℝ) < 2 * Real.pi := by positivity
  -- every value of `psi` is attained somewhere in the fundamental square
  have hsub : Set.range (fun p : ℝ × ℝ => psi p.1 p.2) ⊆
      (fun p : ℝ × ℝ => psi p.1 p.2) ''
        (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    obtain ⟨x', hx', hx'eq⟩ := periodic_reduce (2 * Real.pi) hc (fun t => psi t y)
      (fun t => hper1 t y) x
    obtain ⟨y', hy', hy'eq⟩ := periodic_reduce (2 * Real.pi) hc (fun s => psi x' s)
      (fun s => hper2 x' s) y
    exact ⟨(x', y'), ⟨hx', hy'⟩, hy'eq.trans hx'eq⟩
  -- the fundamental square is compact, so its image under the continuous map is bounded
  exact Bornology.IsBounded.subset
    ((isCompact_Icc.prod isCompact_Icc).image hcont).isBounded hsub

end Work.Geometry
