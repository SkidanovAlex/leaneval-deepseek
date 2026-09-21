import Mathlib
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_AA
import Submission.Work.OddVolterra.Window.contDiffOn_fixed_window

namespace Work.OddVolterra.Smooth

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

/-!
# Smoothness of the fixed-interval part `AA`

`AA n h u = ∫_t in (-X₁)..X₁, Ψ(u,t)^n √(Ψ(u,t))` with `Ψ(u,t) = 1 - t² - (ut + h u)²`.

For `s ∈ [a,c]` the radicand `Ψ` is strictly positive on a window `{|u-s| < ε} × [-X₁,X₁]`
(`Work.OddVolterra.RowIdentity.Setup.Psi_window_pos`), so the windowed parametric integral is
`C^∞` there (`Work.OddVolterra.Window.contDiffOn_window_integral`); it agrees with `AA` near
`s`, whence `AA` is `C^∞` at `s`.

This is the `C^∞` statement underlying `Work.OddVolterra.RowIdentity.contDiffAt_AA`, which
records the weaker consequence `ContDiffAt ℝ (↑(H.n + 1))` needed for the single
`(n+1)`-st derivative of the row identity; the smooth version is what the higher-order
differentiations of the odd-case Volterra argument consume.
-/

theorem contDiffAt_AA_top (H : Work.OddVolterra.RowIdentity.Setup) {s : ℝ}
    (hs : s ∈ Set.Icc H.a H.c) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.OddVolterra.RowIdentity.AA H.n H.h) s := by
  have hcd : -(profileX 1) ≤ profileX 1 := by
    linarith [Work.OddVolterra.RowIdentity.profileX_one_pos]
  -- The parametric smoothness of the windowed integral `∫ Ψ^n √Ψ`.
  obtain ⟨δ, hδ, hcont⟩ :=
    Work.OddVolterra.Window.contDiffOn_window_integral (n := H.n) (c := -(profileX 1))
      (d := profileX 1) (s := s) hcd (Work.OddVolterra.RowIdentity.contDiff_Psi H)
      contDiff_const (Work.OddVolterra.RowIdentity.Setup.Psi_window_pos H hs)
  -- It agrees with `AA` (the constant factor `1` is spurious).
  have hE : (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        (fun q : ℝ × ℝ => Work.OddVolterra.RowIdentity.Psi H.h q.1 q.2) (u, t) ^ H.n
          * Real.sqrt ((fun q : ℝ × ℝ => Work.OddVolterra.RowIdentity.Psi H.h q.1 q.2) (u, t))
          * (fun _ : ℝ × ℝ => (1 : ℝ)) (u, t))
      = Work.OddVolterra.RowIdentity.AA H.n H.h := by
    funext u
    simp only [Work.OddVolterra.RowIdentity.AA, mul_one]
  rw [hE] at hcont
  exact hcont.contDiffAt (Ioo_mem_nhds (by linarith) (by linarith))

end Work.OddVolterra.Smooth
