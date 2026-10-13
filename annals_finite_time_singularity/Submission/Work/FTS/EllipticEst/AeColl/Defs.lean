import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl/Defs` — the vocabulary of the cut-off chain for `AeColl.i1PaperWeakMixed`

The route (see `NOTES_i1PaperWeakMixed_ROUTE.md`) uses the two proved 2-D cut-off identities
`I1Wk.truncZIbp2` (radial) and `I1Wk.truncThetaIbpSep` (angular), whose combination gives, for the
radial cut-off `χ_n = Work.FTS.EllipticEst.cut n` and the angular bump `ψ_δ`,

`κ·P ≤ D + Tr − 2η·A + (1/2)|W|`,

with `P, D, Tr, A` as below and `W = ∫∫ χ_n w² σ ψ_δ'' U²` controlled by the collar `Col` through
the Hardy-type rate of the slices of `U = z∂_zu` (`AeColl.sliceWBound`,
`AeColl.aeGradTraceRateUnw`).

These definitions live in their own module so that the two limit lemmas
(`AeColl.pairChain`, `AeColl.limitBound`) and the final assembly in `AeColl.i1PaperWeakMixed`
can all import them without a cycle.
-/

namespace Work.FTS.EllipticEst.AeColl

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
def sigθ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The squared radial weight `w z²`. -/
def wt (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- `U = z ∂_z u`. -/
def Uz (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- `V = z ∂_z ∂_θ u`. -/
def Vz (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ

/-- `A = z² ∂_z² u`. -/
def Az (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- `cw z = 2(z-1)/(1+z) = (w²z²)'/(z·w²)`. -/
def cwf (z : ℝ) : ℝ := 2 * (z - 1) / (1 + z)

/-- The angular bump `ψ_δ` of the cut-off chain (equal to `1` on `[δ/2, π/2−δ/2]`). -/
def psiD (δ θ : ℝ) : ℝ :=
  Real.smoothTransition ((θ - δ / 4) / (δ / 4))
    * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))

/-- The `(χ_n, ψ_δ)`-truncated angular energy of the mixed slot `V`. -/
def Ptr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * psiD δ θ * (Vz u z θ) ^ 2

/-- The `(χ_n, ψ_δ)`-truncated angular energy of `U`. -/
def Atr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * psiD δ θ * (Uz u z θ) ^ 2

/-- The `(χ_n, ψ_δ)`-truncated pairing of `A = z²∂_z²u` with `B = ∂_θ²u`. -/
def Dtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
    * sigθ θ * psiD δ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The `(χ_n, ψ_δ)`-truncated angular transfer term. -/
def Trtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
      * sigθ θ * psiD δ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The angular collar energy of `V`, cut off radially by `χ_n`. -/
def Col (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
      * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
    + ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
      * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2)

/-- The radial-cutoff truncated mixed energy (the `δ ↓ 0` limit of `Ptr`). -/
def Pcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2

/-- The radial-cutoff truncated energy of `U` (the `δ ↓ 0` limit of `Atr`). -/
def Acut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ) ^ 2

/-- The radial-cutoff truncated `⟨A,B⟩` (the `δ ↓ 0` limit of `Dtr`). -/
def Dcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
    * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The radial-cutoff truncated transfer term (the `δ ↓ 0` limit of `Trtr`). -/
def Trcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
      * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The full (untruncated) weighted angular energy of the mixed slot `V`. -/
def Vfull (u : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2

/-- The full (untruncated) weighted angular energy of `U`. -/
def Ufull (u : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ) ^ 2

end

end Work.FTS.EllipticEst.AeColl
