import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.Analysis.Calculus.contDiff_dslope
import Submission.Work.OddVolterra.Window.contDiffOn_fixed_window

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-- The frozen radicand `Psi` is jointly `C^∞` in `(u,t)`, since `H.h` is. -/
lemma contDiff_Psi (H : Setup) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => Psi H.h q.1 q.2) := by
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => H.h q.1) := H.hh.comp contDiff_fst
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => (1 : ℝ) - q.2 ^ 2) :=
    contDiff_const.sub (contDiff_snd.pow 2)
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => (q.1 * q.2 + H.h q.1) ^ 2) :=
    ((contDiff_fst.mul contDiff_snd).add hcomp).pow 2
  simpa [Psi] using h1.sub h2

/-- **Smoothness of the fixed-interval part `AA`.**

`AA n h u = ∫_t in (-X₁)..X₁, Ψ(u,t)^n √(Ψ(u,t))` with `Ψ(u,t) = 1 - t² - (ut + h u)²`.
Since `Ψ` is `C^∞` on `ℝ × ℝ` and strictly positive on a window `{|u-s| < ε} × [-X₁,X₁]`
(see `Work.OddVolterra.RowIdentity.Setup.Psi_window_pos` in
`Submission.Work.OddVolterra.RowIdentity.Basic`), the integrand is `C^∞` there; glue it to a
globally `C^∞` function with a product of smooth bumps in `u` and in `t` (the `t`-bump being `1`
on `[-X₁,X₁]`), then apply the smoothness of parametric interval integrals
(`Work.Analysis.Calculus.contDiff_intervalIntegral_parametric` in the module
`Submission.Work.Analysis.Calculus.contDiff_dslope`) and conclude with `ContDiffAt.congr` since
the two integrals agree for `u` near `s`. -/
theorem contDiffAt_AA (H : Setup) {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) :
    ContDiffAt ℝ (H.n + 1) (AA H.n H.h) s := by
  have hcd : -(profileX 1) ≤ profileX 1 := by linarith [profileX_one_pos]
  -- The parametric smoothness of the windowed integral `∫ Ψ^n √Ψ`.
  obtain ⟨δ, hδ, hcont⟩ :=
    Work.OddVolterra.Window.contDiffOn_window_integral (n := H.n) (c := -(profileX 1))
      (d := profileX 1) (s := s) hcd (contDiff_Psi H) contDiff_const
      (Setup.Psi_window_pos H hs)
  -- It agrees with `AA` (the constant factor `1` is spurious).
  have hE : (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        (fun q : ℝ × ℝ => Psi H.h q.1 q.2) (u, t) ^ H.n
          * Real.sqrt ((fun q : ℝ × ℝ => Psi H.h q.1 q.2) (u, t))
          * (fun _ : ℝ × ℝ => (1 : ℝ)) (u, t)) = AA H.n H.h := by
    funext u
    simp only [AA, mul_one]
  rw [hE] at hcont
  have hca : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (AA H.n H.h) s :=
    hcont.contDiffAt (Ioo_mem_nhds (by linarith) (by linarith))
  exact hca.of_le
    (show ((H.n + 1 : ℕ) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)

end

end Work.OddVolterra.RowIdentity
