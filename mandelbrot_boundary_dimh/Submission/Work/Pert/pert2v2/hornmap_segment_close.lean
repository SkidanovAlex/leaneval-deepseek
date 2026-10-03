import Mathlib
import Submission.Work.Pert.RBlock3
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Gates
import Submission.Work.Pert.MaxDom

namespace Work.Pert.pert2v2

theorem hornmap_segment_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ : ℝ} {α : ℂ} {F f τ Φm Φp : ℂ → ℂ} {Df Qp' : Set ℂ} {m : ℕ} {y₀ δ : ℝ}
    (hΦp : MandelDim.IsFatouCoordOn F Φp (Work.Pert.Qp Ξ α))
    (hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ α) (hinjτ : Set.InjOn τ Qp')
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ α, τ (F z) = f (τ z))
    (hAbel : ∀ z ∈ Work.Pert.Qp Ξ α, F z ∈ Work.Pert.Qp Ξ α → Φp (F z) = Φp z + 1)
    {ς : ℝ → ℂ}
    (hς : ∀ x ∈ Set.Icc (0 : ℝ) 1, ς x ∈ Work.Pert.Qm Ξ α ∧
      Φm (ς x) = (x : ℂ) + (y₀ : ℂ) * Complex.I)
    (hwalk : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ m →
      F^[i] (ς x) ∈ Work.Pert.Qp Ξ α)
    (hland : ∀ x ∈ Set.Icc (0 : ℝ) 1, F^[m] (ς x) ∈ Qp')
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Work.Pert.coordP f Df τ Φm (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I) = τ (ς x))
    (hres : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖Φp (Work.Pert.invOn τ Qp' (f^[m]
            (Work.Pert.coordP f Df τ Φm (Work.Pert.Qm Ξ α)
              ((x : ℂ) + (y₀ : ℂ) * Complex.I))))
          - (m : ℂ) - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖Φp (ς x) - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2 := by
  intro x hx
  -- `hφ` identifies the argument of the residual with `τ (ς x)`, so the chosen `τ`-preimage
  -- in `Qp'` of `f^[m] (τ (ς x))` is `F^[m] (ς x)` and `Φp` of it is `Φp (ς x) + m`.
  have hres' := hres x hx
  rw [hφ x hx] at hres'
  have hkey := ParabData.PhiP_invOn_level (Φp := Φp) (ς := ς x) (m := m) hinjτ
    (fun j hj => hwalk x hx j hj) hτF hAbel (hland x hx)
  rw [hkey] at hres'
  simpa only [add_sub_cancel_right] using hres'

end Work.Pert.pert2v2
