import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.RegularityCompacts

open MeasureTheory

namespace Commons.MeasureTheory

/-- The map `y ↦ z - y` preserves Lebesgue measure on `Fin d → ℂ`. -/
lemma map_sub_right_eq_self {d : ℕ} (z : Fin d → ℂ) :
    Measure.map (fun y : Fin d → ℂ => z - y)
      (volume : Measure (Fin d → ℂ)) = volume := by
  have hm : (fun y : Fin d → ℂ => z - y) =
      (fun x : Fin d → ℂ => z + x) ∘ (fun y : Fin d → ℂ => -y) := by
    funext y; simp [sub_eq_add_neg]
  rw [hm, ← Measure.map_map (g := fun x : Fin d → ℂ => z + x)
        (f := fun y : Fin d → ℂ => -y) (by fun_prop) (by fun_prop)]
  rw [Measure.map_neg_eq_self]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self z

/-- Precomposition with `y ↦ z - y` preserves local integrability. -/
lemma locallyIntegrable_sub_self {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {V : (Fin d → ℂ) → E}
    (hV : MeasureTheory.LocallyIntegrable V (volume : Measure (Fin d → ℂ)))
    (z : Fin d → ℂ) :
    MeasureTheory.LocallyIntegrable (fun y => V (z - y)) (volume : Measure (Fin d → ℂ)) := by
  let e : (Fin d → ℂ) ≃ₜ (Fin d → ℂ) :=
    { toFun := fun y => z - y
      invFun := fun y => z - y
      left_inv := by intro y; simp
      right_inv := by intro y; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hmap : Measure.map (⇑e) (volume : Measure (Fin d → ℂ)) = volume := by
    change Measure.map (fun y : Fin d → ℂ => z - y) volume = volume
    exact map_sub_right_eq_self z
  have h := (locallyIntegrable_map_homeomorph e).mp (by rw [hmap]; exact hV)
  convert h using 2
  all_goals rfl

/-- **Local integrability of a mollifying integrand.**  For a continuous compactly supported real
kernel `ρ` and a locally integrable `V`, the function `y ↦ ρ y • V (z - y)` is integrable. -/
theorem integrable_smul_sub_of_locallyIntegrable {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : (Fin d → ℂ) → ℝ} {V : (Fin d → ℂ) → E} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ)
    (hV : MeasureTheory.LocallyIntegrable V (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (z : Fin d → ℂ) :
    MeasureTheory.Integrable (fun y => ρ y • V (z - y))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  exact (locallyIntegrable_sub_self hV z).integrable_smul_left_of_hasCompactSupport hρc hρs

end Commons.MeasureTheory