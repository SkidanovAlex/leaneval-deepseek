import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Horn.piExp_hasDerivAt

namespace Work.Horn

open Filter Topology Metric
open scoped Topology

noncomputable section

/-- **The pushed-down map agrees with the lift near a lift point.**

If `D` is `ℤ`-invariant, `D ∈ 𝓝 w` and `E (u + 1) = E u + 1` on `D`, then
`(pushdown E) ∘ π` and `π ∘ E` agree on a neighbourhood of `w` (each `u` close to `w` lies in `D`,
so `MandelDim.pushdown_piExp` applies).  This is the local equality that lets the chain rule
transfer critical points of `pushdown E` at `π w` to critical points of `E` at `w`. -/
theorem pushdown_piExp_eventually {E : ℂ → ℂ} {D : Set ℂ} (hT : MandelDim.IsTInvariant D) {w : ℂ}
    (hD : D ∈ 𝓝 w) (heq : ∀ u ∈ D, E (u + 1) = E u + 1) :
    (MandelDim.pushdown E ∘ MandelDim.piExp) =ᶠ[𝓝 w] (MandelDim.piExp ∘ E) := by
  filter_upwards [hD] with u hu
  exact MandelDim.pushdown_piExp hT (fun v hv _ => heq v hv) hu

set_option linter.unusedVariables false

/-- **`pushdown` preserves criticality inside the lift.**

For a `ℤ`-invariant set `D` (`MandelDim.IsTInvariant D`, the deck group of the universal covering
`MandelDim.piExp = exp(2πi ·)` acting by `w ↦ w + 1`) and a `T`-equivariant `E` on `D`, the
pushed-down map `MandelDim.pushdown E` satisfies
`MandelDim.pushdown E (piExp u) = piExp (E u)` for `u ∈ D`
(`Work.Horn.MandelDim.pushdown_piExp`).  Since `D` is a neighbourhood of `w`, the two functions
`(pushdown E) ∘ piExp` and `piExp ∘ E` agree on a neighbourhood of `w`, hence have the same
`deriv` there; the chain rule gives
`deriv (pushdown E) (π w) * deriv π w = deriv π (E w) * deriv E w`, and
`deriv π z = 2πi · π z ≠ 0`, so the critical points of `pushdown E` at `π w` are exactly those
of `E` at `w`. -/
theorem deriv_pushdown_zero {E : ℂ → ℂ} {D : Set ℂ} (hT : MandelDim.IsTInvariant D) {w : ℂ}
    (hw : w ∈ D) (hD : D ∈ 𝓝 w) (heq : ∀ u ∈ D, E (u + 1) = E u + 1)
    (hE : DifferentiableAt ℂ E w)
    (hd : DifferentiableAt ℂ (MandelDim.pushdown E) (MandelDim.piExp w)) :
    (deriv (MandelDim.pushdown E) (MandelDim.piExp w) = 0 ↔ deriv E w = 0) := by
  -- `π` is differentiable with derivative `2πi·π ≠ 0`
  have hπw : HasDerivAt MandelDim.piExp (2 * ↑Real.pi * Complex.I * MandelDim.piExp w) w :=
    piExp_hasDerivAt w
  have hπE : HasDerivAt MandelDim.piExp (2 * ↑Real.pi * Complex.I * MandelDim.piExp (E w))
      (E w) := piExp_hasDerivAt (E w)
  -- chain rule on the left: `deriv ((pushdown E) ∘ π) w = (pushdown E)'(π w) · π'(w)`
  have hA : HasDerivAt (MandelDim.pushdown E ∘ MandelDim.piExp)
      (deriv (MandelDim.pushdown E) (MandelDim.piExp w) *
        (2 * ↑Real.pi * Complex.I * MandelDim.piExp w)) w :=
    hd.hasDerivAt.comp w hπw
  -- chain rule on the right: `deriv (π ∘ E) w = π'(E w) · E'(w)`
  have hB : HasDerivAt (MandelDim.piExp ∘ E)
      ((2 * ↑Real.pi * Complex.I * MandelDim.piExp (E w)) * deriv E w) w :=
    hπE.comp w hE.hasDerivAt
  -- the two functions agree near `w`, so their derivatives at `w` agree
  have heqd : deriv (MandelDim.pushdown E) (MandelDim.piExp w) *
        (2 * ↑Real.pi * Complex.I * MandelDim.piExp w) =
      (2 * ↑Real.pi * Complex.I * MandelDim.piExp (E w)) * deriv E w := by
    have h1 := Filter.EventuallyEq.deriv_eq (pushdown_piExp_eventually hT hD heq)
    rw [hA.deriv, hB.deriv] at h1
    exact h1
  have hcw : (2 * ↑Real.pi * Complex.I * MandelDim.piExp w) ≠ 0 :=
    mul_ne_zero Complex.two_pi_I_ne_zero (MandelDim.piExp_ne_zero w)
  have hcEw : (2 * ↑Real.pi * Complex.I * MandelDim.piExp (E w)) ≠ 0 :=
    mul_ne_zero Complex.two_pi_I_ne_zero (MandelDim.piExp_ne_zero (E w))
  constructor
  · intro h
    have h2 : (2 * ↑Real.pi * Complex.I * MandelDim.piExp (E w)) * deriv E w = 0 := by
      rw [← heqd, h, zero_mul]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hcEw
    · exact h3
  · intro h
    have h2 : deriv (MandelDim.pushdown E) (MandelDim.piExp w) *
        (2 * ↑Real.pi * Complex.I * MandelDim.piExp w) = 0 := by
      rw [heqd, h, mul_zero]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hcw

end

end Work.Horn
