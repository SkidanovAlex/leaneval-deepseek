import Mathlib

namespace Work.WilCrux

theorem monotone_or_antitone_of_deriv_sign (f : ℝ → ℝ) {s t : ℝ}
    (hdiff : ∀ u ∈ Set.Ioo s t, DifferentiableAt ℝ f u)
    (hsign : (∀ u ∈ Set.Ioo s t, 0 ≤ deriv f u) ∨ (∀ u ∈ Set.Ioo s t, deriv f u ≤ 0)) :
    MonotoneOn f (Set.Ioo s t) ∨ AntitoneOn f (Set.Ioo s t) := by
  have hcont : ContinuousOn f (Set.Ioo s t) := fun u hu =>
    (hdiff u hu).continuousAt.continuousWithinAt
  have hD : Convex ℝ (Set.Ioo s t) := convex_Ioo s t
  have hsub : interior (Set.Ioo s t) ⊆ Set.Ioo s t := interior_subset
  rcases hsign with h | h
  · left
    exact monotoneOn_of_deriv_nonneg hD hcont
      (fun u hu => (hdiff u (hsub hu)).differentiableWithinAt)
      (fun u hu => h u (hsub hu))
  · right
    exact antitoneOn_of_deriv_nonpos hD hcont
      (fun u hu => (hdiff u (hsub hu)).differentiableWithinAt)
      (fun u hu => h u (hsub hu))

end Work.WilCrux
