import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Repel.pushdown_holo
import Submission.Work.Repel.pushdown_deriv

/-!
# The `HornData.g_holo` field

`pushdown Ẽ` is holomorphic on `{0} ∪ π(Bu ∪ Bl)`, where `Bu, Bl` are `T`-invariant open sets
inside `DE = φ₀⁻¹(basin)` containing the two half planes.  Uses the colleague-proved
`pushdown_holo` (differentiability away from `0`) and `pushdown_deriv` (the germ at `0`,
from the normalization `E w - w → 0` at the upper end).
-/

noncomputable section

open MandelDim Set Filter Topology Metric
open scoped Topology

namespace Work.Horn

open Work.Horn.MandelDim

/-- `E = Φ ∘ φ` is holomorphic on `DE`. -/
theorem differentiableOn_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    DifferentiableOn ℂ d.E d.DE := by
  intro w hw
  rw [ParabData.mem_DE] at hw
  have hmap : MapsTo d.φ d.DE (ParabolicBasin f₀ D₀) :=
    fun x hx => (ParabData.mem_DE d).mp hx |>.2
  have hφ : DifferentiableWithinAt ℂ d.φ d.DE w :=
    (d.φ_holo w hw.1).mono (fun x hx => (ParabData.mem_DE d).mp hx |>.1)
  have hΦ : DifferentiableWithinAt ℂ d.Φ (ParabolicBasin f₀ D₀) (d.φ w) :=
    d.Φ_holo (d.φ w) hw.2
  exact hΦ.comp w hφ hmap

/-- `HornData.g_holo`: `pushdown Ẽ` is holomorphic on `{0} ∪ π(Bu ∪ Bl)`. -/
theorem pushdown_E_differentiableOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    (η : ℝ) (Bu Bl : Set ℂ) (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (htBu : IsTInvariant Bu) (htBl : IsTInvariant Bl) (hsub : Bu ∪ Bl ⊆ d.DE)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    DifferentiableOn ℂ (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))) := by
  have hT : IsTInvariant (Bu ∪ Bl) := fun w => by
    constructor
    · rintro (hw | hw)
      · exact Or.inl ((htBu w).mp hw)
      · exact Or.inr ((htBl w).mp hw)
    · rintro (hw | hw)
      · exact Or.inl ((htBu w).mpr hw)
      · exact Or.inr ((htBl w).mpr hw)
  have heq : IsTEquivariantOn d.E (Bu ∪ Bl) :=
    ⟨hT, fun w hw => ParabData.E_add_one d (hsub hw) (hsub ((hT w).mp hw))⟩
  have hdiff : DifferentiableOn ℂ d.E (Bu ∪ Bl) :=
    (differentiableOn_E d).mono hsub
  have hpi : DifferentiableOn ℂ (pushdown d.E) (piExp '' (Bu ∪ Bl)) :=
    Work.Repel.pushdown_holo heq hdiff
  have hy : ∀ w : ℂ, η + 1 ≤ |w.im| → w ∈ Bu ∪ Bl := by
    intro w hw
    by_cases h : 0 ≤ w.im
    · have h1 : |w.im| = w.im := abs_of_nonneg h
      have h2 : η < w.im := by linarith
      exact Or.inl (hup h2)
    · have h1 : |w.im| = -w.im := abs_of_neg (not_le.mp h)
      have h2 : w.im < -η := by linarith
      exact Or.inr (hlo h2)
  have hder : HasDerivAt (pushdown d.E) 1 0 := by
    have h : HasDerivAt (pushdown d.E) (piExp (-(0 : ℂ))) 0 :=
      Work.Repel.pushdown_deriv (E := d.E) (c := (0 : ℂ)) (y := η + 1)
        (hBuO.union hBlO) heq hdiff hy (by simpa [ParabData.E] using d.E_upper)
    simpa [piExp] using h
  intro ζ hζ
  rcases hζ with rfl | hζ
  · exact hder.differentiableAt.differentiableWithinAt
  · have hζne : ζ ≠ 0 := by
      obtain ⟨w, -, rfl⟩ := hζ
      exact piExp_ne_zero w
    exact (hpi ζ hζ).congr_nhds (nhdsWithin_insert_of_ne (x := ζ) (y := (0 : ℂ)) hζne).symm

end Work.Horn
