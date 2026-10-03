import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs

namespace Work.HornSC.CellBoundaryJordan

open Complex

/-- For any `a : ℂ` there is a direction `1 + ε i` (`ε > 0`) such that the open ray
`{a + t (1 + ε i) | t > 0}` contains no Gaussian integer `m + n i`.

The point is that the "bad" set of `ε` is countable: if `a + t(1+εi) = m + n i` with
`t > 0`, then comparing real parts forces `t = m - a.re` and comparing imaginary parts
gives `ε = (n - a.im)/(m - a.re)`. Hence it suffices to choose a positive real outside
this countable image of `ℤ × ℤ`. -/
theorem exists_generic_ray_direction (a : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I := by
  -- the countable set of "bad" directions
  have hSc : ((fun p : ℤ × ℤ => ((p.2 : ℝ) - a.im) / ((p.1 : ℝ) - a.re)) '' Set.univ).Countable :=
    Set.Countable.image (Set.countable_univ (α := ℤ × ℤ)) _
  -- `(0, ∞)` is uncountable, so some positive real is not bad
  have hunc : ¬ (Set.Ioi (0 : ℝ)).Countable := by
    intro hc
    have hle : Cardinal.mk ↑(Set.Ioi (0 : ℝ)) ≤ Cardinal.aleph0 :=
      Cardinal.mk_le_aleph0_iff.mpr hc
    rw [Cardinal.mk_Ioi_real] at hle
    exact (not_le.mpr Cardinal.aleph0_lt_continuum) hle
  obtain ⟨ε, hεpos, hεS⟩ : ∃ ε : ℝ, 0 < ε ∧
      ε ∉ ((fun p : ℤ × ℤ => ((p.2 : ℝ) - a.im) / ((p.1 : ℝ) - a.re)) '' Set.univ) := by
    by_contra hcon
    have hsub : Set.Ioi (0 : ℝ) ⊆
        ((fun p : ℤ × ℤ => ((p.2 : ℝ) - a.im) / ((p.1 : ℝ) - a.re)) '' Set.univ) := by
      intro x hx
      by_contra hxS
      exact hcon ⟨x, hx, hxS⟩
    exact hunc (Set.Countable.mono hsub hSc)
  refine ⟨ε, hεpos, ?_⟩
  intro t ht m n heq
  -- compare real parts: `a.re + t = m`
  have hre : a.re + t = (m : ℝ) := by
    have h' := congrArg Complex.re heq
    simp [Complex.add_re, Complex.mul_re] at h'
    simpa using h'
  -- compare imaginary parts: `a.im + t * ε = n`
  have him : a.im + t * ε = (n : ℝ) := by
    have h' := congrArg Complex.im heq
    simp [Complex.add_im, Complex.mul_im] at h'
    simpa using h'
  have hmd : (m : ℝ) - a.re = t := by linarith
  have hthis : ε = ((n : ℝ) - a.im) / ((m : ℝ) - a.re) := by
    rw [hmd, eq_div_iff (ne_of_gt ht)]
    linarith
  exact hεS ⟨(m, n), Set.mem_univ _, hthis.symm⟩

end Work.HornSC.CellBoundaryJordan
