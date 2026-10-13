import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.PhiStar.Psi0Ode
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.const_le_of_moment

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Wdiv_bound`

The function `v = ψ / sin 2θ` of the angular model is *determined up to an additive constant*:
its derivative is `P/sin²θ = (wZer α)'` (hypothesis `hp`), so `v − wZer α` is constant on the
connected interval `(0, π/2)` (`IsOpen.exists_eq_add_of_deriv_eq`).  The constant is pinned by
the moment condition `∫_{Iθ} ψ · sinθcos²θ = 0`: since `sin 2θ · sinθcos²θ ≥ 0` on `Iθ` with
`∫_{Iθ} sin 2θ · sinθcos²θ = 4/15 > 0`, the moment of `ψ = sin 2θ · v` is
`c·(4/15) + ∫_{Iθ} sin 2θ · wZer · sinθcos²θ`, so

`|c|·(4/15) = |∫ sin 2θ · wZer · sinθcos²θ| ≤ (500·(π/2))·(4/15)`,

i.e. `|c| ≤ 500·(π/2)`.  Since `|wZer α θ| ≤ 500·(π/2)` as well
(`abs_wZer_le`), the triangle inequality gives `|v θ| ≤ 500·π`.

The measure-theoretic half (the moment inequality `const_le_of_moment`) is proved in
`Submission/Work/FTS/PhiStar/const_le_of_moment.lean`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem Wdiv_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hmom : ∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ = 0)
    (h0 : ψ 0 = 0) (h1 : ψ (Real.pi / 2) = 0)
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), DifferentiableAt ℝ (fun θ' => ψ θ' / Real.sin (2 * θ')) θ)
    (hp : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ / Real.sin (2 * θ)| ≤ 500 * Real.pi := by
  -- `v − wZer` is constant on the connected open interval `(0, π/2)`
  obtain ⟨c, hc⟩ := IsOpen.exists_eq_add_of_deriv_eq (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
    (f := fun θ => ψ θ / Real.sin (2 * θ)) (g := wZer α) isOpen_Ioo isPreconnected_Ioo
    (fun θ hθ => (hdiff θ hθ).differentiableWithinAt)
    (fun θ hθ => (hasDerivAt_wZer α hα hα4 hθ).differentiableAt.differentiableWithinAt)
    (fun θ hθ => by rw [hp θ hθ, (hasDerivAt_wZer α hα hα4 hθ).deriv])
  -- `sin 2θ` does not vanish on the open interval
  have hsin_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  -- hence `ψ = sin 2θ · (wZer + c)` on the open interval
  have hpsi : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ψ θ = Real.sin (2 * θ) * (wZer α θ + c) := by
    intro θ hθ
    have hcθ : ψ θ / Real.sin (2 * θ) = wZer α θ + c := hc hθ
    rw [← hcθ, mul_div_cancel₀ _ (hsin_ne θ hθ)]
  -- the identification `sin 2θ · v = ψ` on `Iθ`, including the endpoints where `sin 2θ = 0`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Real.sin (2 * θ) * (ψ θ / Real.sin (2 * θ)) * Work.Elliptic.sinCos2 θ
        = ψ θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hpos | hzero
    · rcases lt_or_eq_of_le hθ.2 with hlt | hpi
      · rw [mul_div_cancel₀ _ (hsin_ne θ ⟨hpos, hlt⟩)]
      · rw [hpi, h1, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
        ring
    · rw [← hzero, h0, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero]
      ring
  -- so the moment condition transfers to `v`
  have hzero : ∫ θ in Work.Spaces.Iθ,
      Real.sin (2 * θ) * (ψ θ / Real.sin (2 * θ)) * Work.Elliptic.sinCos2 θ = 0 := by
    rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc hpt, hmom]
  -- the moment inequality pins the constant
  have hcle : |c| ≤ 500 * (Real.pi / 2) :=
    Work.FTS.PhiStar.const_le_of_moment
      (v := fun θ => ψ θ / Real.sin (2 * θ)) (w := wZer α) (c := c)
      (M := 500 * (Real.pi / 2))
      (fun θ hθ => by rw [hpsi θ hθ, mul_div_cancel_left₀ _ (hsin_ne θ hθ)])
      (fun θ hθ => abs_wZer_le α hα hα4 hθ)
      ((continuousOn_wZer α hα hα4).aestronglyMeasurable measurableSet_Icc)
      hzero
  intro θ hθ
  have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcθ : ψ θ / Real.sin (2 * θ) = wZer α θ + c := hc hθ
  calc |ψ θ / Real.sin (2 * θ)| = |wZer α θ + c| := by rw [hcθ]
    _ ≤ |wZer α θ| + |c| := abs_add_le _ _
    _ ≤ 500 * (Real.pi / 2) + 500 * (Real.pi / 2) := by
        linarith [abs_wZer_le α hα hα4 hθI, hcle]
    _ = 500 * Real.pi := by ring

end Work.FTS.PhiStar
