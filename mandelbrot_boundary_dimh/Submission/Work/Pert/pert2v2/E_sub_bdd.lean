import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.end_bound_piExp
import Submission.Work.Repel.periodic_strip_bound

/-!
# `Work.Pert.pert2v2.E_sub_bdd` — `d.E - id` is bounded on every band `{|Im| ≥ y}`, `y > η₀`

The per-step defect bound of the return map needed by `pert2v2.shift_pos_of_step` is
`‖R x - x + 1/α‖ ≤ δ + ‖d.E x - x‖` on the walk (`R_close` on the band), so the assembly needs the
boundedness of the *datum's* defect `d.E - id` on the band `{y ≤ |Im|}`.

`d.E - id` is continuous on `{η₀ < |Im|}` (`Work.Repel.continuousOn_E_sub`), `1`-periodic
(`Work.Repel.E_add_one`) and has finite limits at both ends (`ParabData.E_upper`/`E_lower`, made
quantitative in `Work.Repel.E_sub_upper_bound`/`E_sub_lower_bound`); so it is bounded on the band
by the generic `Work.Repel.periodic_strip_bound`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

/-- `d.E - id` is `1`-periodic on the end region. -/
theorem E_sub_id_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    (hw : d.η₀ < |w.im|) :
    d.E (w + 1) - (w + 1) = d.E w - w := by
  rw [Work.Repel.E_add_one d hw]
  ring

/-- **Boundedness of the datum's defect on a band.** -/
theorem exists_bound_E_sub_id {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y : ℝ} (hy : d.η₀ < y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, y ≤ |w.im| → ‖d.E w - w‖ ≤ M := by
  obtain ⟨cl, hcl⟩ := d.E_lower
  obtain ⟨Tup, hup⟩ := Work.Repel.E_sub_upper_bound d
  obtain ⟨Tdn, hdn⟩ := Work.Repel.E_sub_lower_bound d hcl
  exact Work.Repel.periodic_strip_bound (F := fun w : ℂ => d.E w - w)
    (η := d.η₀) (y := y) (Cup := 1) (Cdn := ‖cl‖ + 1) hy zero_le_one (by positivity)
    (fun w hw => E_sub_id_add_one d hw) (Work.Repel.continuousOn_E_sub d)
    ⟨Tup, hup⟩ ⟨Tdn, hdn⟩

end Work.Pert.pert2v2
