import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **The one-sided mean value bound on a subinterval.**  If `ω y` is continuous on
`[0,T]` and has right derivative `timeDeriv ω y x` at every `x ∈ [0,T)`, with
`‖timeDeriv ω y x‖ ≤ C` there, then on any subinterval `[a,b] ⊆ [0,T]` (`a ≤ b`) one has
`‖ω y b - ω y a‖ ≤ C (b - a)`.  This is the mean value inequality
`norm_image_sub_le_of_norm_deriv_right_le_segment` applied to the slice `ω y`, the point
being that the derivative hypothesis (available on `Ici x` at each `x ∈ [0,T)`) restricts
to the right-derivative form the MVT needs. -/
theorem norm_time_sub_le_of_mem_Icc {ω : R3 → ℝ → R3} {T C : ℝ}
    (hcont : ∀ y, ContinuousOn (ω y) (Set.Icc 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s)
    (hbd : ∀ y, ∀ s ∈ Set.Ico 0 T, ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ C) :
    ∀ y, ∀ a ∈ Set.Icc 0 T, ∀ b ∈ Set.Icc 0 T,
      a ≤ b → ‖ω y b - ω y a‖ ≤ C * (b - a) := by
  intro y a ha b hb hab
  obtain ⟨ha0, haT⟩ := ha
  obtain ⟨hb0, hbT⟩ := hb
  have hkey : ∀ x ∈ Set.Icc a b, ‖ω y x - ω y a‖ ≤ C * (x - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment (f := ω y)
      (f' := FiniteTimeSingularity.timeDeriv ω y) (C := C) (a := a) (b := b)
      ((hcont y).mono (fun x hx => ⟨le_trans ha0 hx.1, le_trans hx.2 hbT⟩))
      (fun x hx => hderiv y x ⟨le_trans ha0 hx.1, lt_of_lt_of_le hx.2 hbT⟩)
      (fun x hx => hbd y x ⟨le_trans ha0 hx.1, lt_of_lt_of_le hx.2 hbT⟩)
  exact hkey b ⟨hab, le_rfl⟩

theorem lipschitz_time_of_hasDerivWithinAt {ω : R3 → ℝ → R3} {T C : ℝ}
    (hcont : ∀ y, ContinuousOn (ω y) (Set.Icc 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s)
    (hbd : ∀ y, ∀ s ∈ Set.Ico 0 T, ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ C) :
    ∀ y, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T, ‖ω y s - ω y s'‖ ≤ C * |s - s'| := by
  intro y s hs s' hs'
  rcases le_total s s' with h | h
  · have hkey : ‖ω y s' - ω y s‖ ≤ C * (s' - s) :=
      norm_time_sub_le_of_mem_Icc hcont hderiv hbd y s hs s' hs' h
    rw [show ‖ω y s - ω y s'‖ = ‖ω y s' - ω y s‖ from norm_sub_rev (ω y s) (ω y s'),
      show |s - s'| = s' - s from by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]]
    exact hkey
  · have hkey : ‖ω y s - ω y s'‖ ≤ C * (s - s') :=
      norm_time_sub_le_of_mem_Icc hcont hderiv hbd y s' hs' s hs h
    rw [show |s - s'| = s - s' from abs_of_nonneg (sub_nonneg.mpr h)]
    exact hkey

end Work.FTS.PressureOn
