import Mathlib
import Submission.Work.WilG0.API

namespace Work.WilG0

/-- Binary intersection with *independent* formats.  Both sets are first pushed up to the
common format `max F₁ F₂` (`Omega_mono_F`), after which the `k = 2` intersection axiom
(`SOMin.inter`, packaged as `Omega_inter2`) gives the stated format `max F₁ F₂ + 1`; the
degrees are simply added. -/
theorem Omega_inter2_le {S : WilkiesDesign.SOMin} {n F₁ F₂ D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∩ B ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have hA' : A ∈ S.Ω (max F₁ F₂) D₁ n := Omega_mono_F (le_max_left F₁ F₂) hA
  have hB' : B ∈ S.Ω (max F₁ F₂) D₂ n := Omega_mono_F (le_max_right F₁ F₂) hB
  exact Omega_inter2 hA' hB'

end Work.WilG0
