/-
# The continuation of the CKMRV layer `layerLow` across `Re τ = 1`

CKMRV Proposition 4.6: the generating function `F₂` of §5 is defined on the `Γ(2)`-fundamental
domain `𝒟` by the `low + trunc + high` decomposition (5.3)/(5.4) and extends holomorphically to a
neighbourhood of `closure 𝒟`.  The obstruction is the moving pole `z = τ - 1` of the kernel, which
crosses the contour `z = it` as `Re τ` passes through `1`.

This file isolates the *low* half of the continuation.  For `τ` in a ball around `1 + i t₀` with
pole height `t₀ ∈ (0,1)`, only the piece `∫_{t ∈ (0,1]}` crosses the pole, and the corrected object
is the integral over `(0,1]` with the interval `I = (t₀-A, t₀+A)` removed plus the *left* detour
`Work.Asymptotics.detourLeftC` at height `t₀` (three edge integrals in `Re ≤ 0`), together with the
residue correction `Work.Asymptotics.resCorr r τ = e^{πir²(τ-1)}` of Theorem 4.9(3)
(`Res_{z=τ-1} K(τ,z) = 1/(2π)`).

The identity `detourLeftC ℓ d r t₀ A ξ τ = ∫_{I} edgeV - resCorr r τ` of
`Work.Asymptotics.detourLeftC_eq_interval_sub_residue` (Cauchy–Goursat across the pole) gives
exactly the agreement of `layerLowCont` with `layerLow` on `{Re τ < 1}`, while the deformed
expression is holomorphic across `Re τ = 1` (the pole is *inside* the swept rectangle, so it is
compensated by `resCorr`; the other orbit point in the rectangle, the removable coincidence
`ST⁻¹τ`, has vanishing residue since `φ(TS) = 0`).
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.F2LayerDefs

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory
open Work.Asymptotics

/-- The low part of the contour, `(0,1]`, with the interval `(t₀-A, t₀+A)` (the one swept by the
moving pole `τ - 1` when `Im τ` is near `t₀`) removed. -/
def layerLowPiece (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∫ t in (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀ - A) (t₀ + A),
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t

/-- **The continuation of `layerLow` across `Re τ = 1`.**  The integral of the low piece over the
deformed contour (the removed interval replaced by the left detour at height `t₀`), plus the
residue correction `e^{πir²(τ-1)}`. -/
def layerLowCont (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A ξ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r
      * (layerLowPiece ℓ d t₀ A r τ + Work.Asymptotics.detourLeftC ℓ d r t₀ A ξ τ)
    + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ

/-- `sinSqC` and `sinSq` are the same function (two spellings of `4 sin²(πr²/2)`). -/
lemma sinSqC_eq_sinSq (r : ℝ) : Work.Asymptotics.sinSqC r = Work.Asymptotics.sinSq r := rfl

/-- `edgeV` at `u = 0` is the axis integrand `K(τ,it)·e^{-πr²t}`. -/
lemma edgeV_zero_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    {v : ℝ} (hv : 0 < v) :
    Work.Asymptotics.edgeV ℓ d r τ 0 v
      = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
  have hof : Work.Asymptotics.ofReImT 0 v = Work.Kernels.imagAxis v hv := by
    apply UpperHalfPlane.ext
    rw [Work.Asymptotics.ofReImT_coe 0 v hv, Work.Kernels.imagAxis]
    simp
  have hph : Work.Asymptotics.phaseWeight r 0 = 1 := by simp [Work.Asymptotics.phaseWeight]
  simp only [Work.Asymptotics.edgeV, hof, hph, one_mul]
  rw [Work.Kernels.Kaxis, dif_pos hv]

end Work.LayerCont
