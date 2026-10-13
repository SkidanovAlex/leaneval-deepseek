/-
  annals_wilkies_conjecture, AREA E3, frame step: the parametrised curve function
  `u ↦ f (Ψ (u|_ιᶜ, 0))` is constant along the `ι`-coordinates.
-/
import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.FoldZero

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

variable {k : ℕ}

/-- The parametrised curve function `u ↦ f (Ψ (u|_ιᶜ, 0))` is constant along every coordinate in
`Set.range ι`: changing the `ι`-coordinate of `u` does not change `u|_ιᶜ`, hence not the image
under `Ψ`.  This is the "wrong coordinates" half of the hypothesis of
`iteratedDeriv_line_eq_zero` (the other half is `partial_curve_eq_Vword`). -/
theorem constAlong_comp_subtype {k r j : ℕ} (c : EAChain k r) (f : EAPoly k r)
    (ι : Fin j → Fin k) (Ψ : ((U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ)) (s : Fin k)
    (hs : s ∈ Set.range ι) :
    ConstAlong (fun u : Fin k → ℂ => eaEvalC c f (Ψ (fun i : U k ι => u i.1, 0))) s := by
  intro u c'
  have harg : (fun i : U k ι => (u + c' • Pi.single s (1 : ℂ) : Fin k → ℂ) i.1)
      = fun i : U k ι => u i.1 := by
    funext i
    have hne : (i : Fin k) ≠ s := fun h => i.2 (by rw [h]; exact hs)
    simp [Pi.single_eq_of_ne (i := s) hne]
  exact congrArg (fun v : U k ι → ℂ => eaEvalC c f (Ψ (v, 0))) harg

end

end Work.WilE3.Frame
