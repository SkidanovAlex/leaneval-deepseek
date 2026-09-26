/-
# The bottom arcs: the `S`-dictionary between the two layers

`Work.Asymptotics.DomainD` is bounded below by the two arcs `|z ∓ 1/2| = 1/2`, and `S` maps the
lines `Re z = ∓1` onto them (`S(±1 + i y) = ±1/(1+y²) + i y/(1+y²)`).  Since `S ∈ SL(2,ℤ)`, an
arc point `S • σ` has **the same `SL(2,ℤ)`-orbit as the line point `σ`**: all the *geometry* of
the chart construction (the heights at which the imaginary axis carries poles, the orbit
exclusion, the edge avoidance) is literally the same for `S • σ` as for `σ`.  What changes is the
*kernel*, by the second functional equation

  `K̂ = -K |^τ_{d/2} S`,  i.e.  `Khat τ z = - τ^{-d/2} Kfun (S • τ) z`,

equivalently `Kfun τ z = - τ^{d/2} Khat (S • τ) z` (because `K|S|S = K` up to the central factor
`(-1)^{d/2} = 1` for `d = 8, 24`).

This file records that dictionary at the level of the axis integrand `Kaxis` and of the layer
pieces, which is what the arc charts of the layer continuation are built from: the `K`-layer at an
arc point is (up to the explicit automorphy factor and the constant `-1`) the `K̂`-layer at the
corresponding line point, and vice versa.  See `README.md` in this directory for what remains.
-/
import Mathlib
import Submission.Work.LayerCont.SplitPoint
import Submission.Work.Residues.Section5Shift
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KMinus_Sopm

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Arc

open Work.Asymptotics Work.Kernels

/-- The hatted (`K̂`-based) low integral: the analogue of `Work.Asymptotics.layerLowAt` with
`Khat` in place of `Kfun`. -/
def layerLowAtHat (ℓ : LogLambdaData) (d : ℕ) (p r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..p,
    Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) τ t * Work.Asymptotics.gaussWeight r t

/-! ## The kernel dictionary -/

/-- **The second functional equation at the level of the axis integrand**:
`K^{(d)}(S•σ, it) = -σ^{d/2} K̂^{(d)}(σ, it)`. -/
theorem Kaxis_Kfun_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (σ : ℍ) (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t := by
  rw [Work.Kernels.Kaxis, Work.Kernels.Kaxis]
  by_cases h : 0 < t
  · simp only [dif_pos h]
    have hp := KernelFacts.KPlus_S_smul d hd (Work.Kernels.imagAxis t h) σ
    have hm := KernelFacts.KMinus_S_smul ℓ d hd (Work.Kernels.imagAxis t h) σ
    rw [Work.Kernels.Kfun, Work.Kernels.Khat, hp, hm]
    ring
  · simp only [dif_neg h, mul_zero]

/-! ## The layer dictionary -/

/-- **The low piece of the `K`-layer at an arc point is the low piece of the `K̂`-layer at the
corresponding line point**, up to the automorphy factor `-σ^{d/2}`. -/
theorem layerLowAt_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (p r : ℝ) (σ : ℍ) :
    Work.LayerCont.layerLowAt ℓ d p r (ModularGroup.S • σ)
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * layerLowAtHat ℓ d p r σ := by
  have hfun : (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
        * Work.Asymptotics.gaussWeight r t)
      = fun t : ℝ => (-((σ : ℂ) ^ ((d : ℤ) / 2)))
        * (Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t) := by
    funext t
    rw [Kaxis_Kfun_S_smul ℓ d hd σ t]
    ring
  rw [Work.LayerCont.layerLowAt, layerLowAtHat, hfun, intervalIntegral.integral_const_mul]
  ring

/-- The same dictionary for the *trunc* piece: the `K`-layer's cusp-subtracted tail at an arc
point is the `K̂`-layer's tail at the line point.  (The hatted cusp data is
`Ghatcusp := - Gcusp |^z_{2-d/2} S`, so that `Aexp Ghatcusp σ t` is the `S`-transform of
`Aexp Gcusp (S•σ) t`; the identity is then the same computation as `layerLowAt_S_smul`.) -/
theorem layerTruncAt_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (p r : ℝ) (σ : ℍ)
    (Ghat : Fin 2 → Fin 2 → ℍ → ℂ)
    (hGhat : ∀ t : ℝ, Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • σ) t
      = -((σ : ℂ) ^ ((d : ℤ) / 2)) * Work.Asymptotics.Aexp Ghat σ t) :
    Work.LayerCont.layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r (ModularGroup.S • σ)
      = -((σ : ℂ) ^ ((d : ℤ) / 2))
        * (Work.Asymptotics.sinSqC r * ∫ t in Set.Ici p,
            (Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t - Work.Asymptotics.Aexp Ghat σ t)
              * Work.Asymptotics.gaussWeight r t) := by
  have hfun : (fun t : ℝ =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • σ) t)
          * Work.Asymptotics.gaussWeight r t)
      = fun t : ℝ => (-((σ : ℂ) ^ ((d : ℤ) / 2)))
        * ((Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) σ t - Work.Asymptotics.Aexp Ghat σ t)
          * Work.Asymptotics.gaussWeight r t) := by
    funext t
    rw [Kaxis_Kfun_S_smul ℓ d hd σ t, hGhat t]
    ring
  rw [Work.LayerCont.layerTruncAt, hfun, MeasureTheory.integral_const_mul,
    Work.Asymptotics.sinSqC, mul_assoc]
  ring

end Work.LayerCont.Arc
