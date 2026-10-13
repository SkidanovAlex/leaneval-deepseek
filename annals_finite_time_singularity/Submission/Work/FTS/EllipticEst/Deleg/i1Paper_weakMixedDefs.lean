/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/i1Paper_weakMixedDefs` — the interfaces of the cut-off chain for `i1Paper_weakMixed`

The target

```
∃ C > 0, ∀ α u G, AeData α u G → HkMem α 0 (grad u) →
  (H1) ∀ᵐ z, ∫_θ (z∂_z∂_θu)² σ < ∞      (a.e.-slicewise mixed honesty)
  (H2) ∫_z ∫_θ (z∂_z∂_θu)² σ < ∞        (unweighted outer finiteness)
  κ·α²·HkSq α 0 (∂_θ(grad u)) − C α² (⟨U,U⟩ + √⟨U,U⟩√⟨B,B⟩) ≤ α² ⟨z²∂_zz u, B⟩
```

(`U = grad u = z∂_zu`, `B = ∂_θθu`, `V = ∂_θU = z∂_z∂_θu`, `σ = AngSecond.sig = sin(2θ)^{-η}`,
`w = Spaces.w = (1+z)²/z²`, `κ = (1-η)/(1+η)`, `η = 99/100`, `⟨f,g⟩ = AngSecond.IP f g`)

is proved here by the *cut-off chain* of `Submission/Work/FTS/EllipticEst/AeColl/`: the two
proved 2-D integration-by-parts identities

* `I1Wk.truncZIbp2` (radial, with cut-offs `χ(z)`, `ψ(θ)`),
* `I1Wk.truncThetaIbpSep_split` (angular, the slice identity `S2`),

combined, give `D_χψ = −Tr_χψ + 2ηA_χψ + κP_χψ + c·Def_χψ − ½W_χψ`, hence
`κP_χψ ≤ D_χψ + Tr_χψ − 2ηA_χψ + ½|W_χψ|`; the `W`-term is controlled by the endpoint *rate* of
the slices of `U` (from `I1Wk.aeGradTrace0`, whose hypotheses are exactly `(H1)+(H2)`), and the
two cut-off limits (`ψ_δ ↑ 1`, then `χ_n ↑ 1`, the latter using `I1Wk.chiDerivLimit`) give the
target.

This module only fixes the vocabulary shared by the pieces of that chain: the standing
`AeData + HkMem α 0 (grad u)` hypotheses, the a.e. mixed honesty `(H1)+(H2)` as one `Prop`, the
a.e. endpoint rate as one `Prop`, the 1-D collar bound as a schema, and the per-`(χ_n, ψ_δ)`
inequality.  No proof is carried out here.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-- `κ = (1-η)/(1+η)`, the constant of the target. -/
def kap : ℝ := (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)

/-- **The a.e. mixed honesty** `(H1)+(H2)` of the target, as a single `Prop`: for a.e. `z` the
angular slice of `V = z∂_z∂_θu` is `σ`-honest, and the (unweighted) `z`-integral of the slice
energy is finite. -/
def MixedHon (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz

/-- **The a.e. endpoint rate of the slices of `U = z∂_zu`** (the analytic input of the collar
bound): for a.e. `z`, `(z∂_zu(z,·))²` is controlled by `θ^{1+η}` (resp. `(π/2-θ)^{1+η}`) times
the partial `σ`-energy of `V`. -/
def SliceRate (K : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))
    ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))

/-- The a.e. rate at a *fixed* constant, restricted to the open angular interval. -/
def SliceRateAt (K : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : Prop :=
  (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))
    ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t))

/-- **The 1-D collar bound for the angular cut-off `psiD δ`** (schema in the rate constant `K`):
for `0 < δ ≤ π/8` and every `f : ℝ → ℝ` of class `C¹` on `(0,π/2)` with `σ(f')²` integrable and
the two endpoint rates, the `ψ_δ''`-moment of `f²` is bounded by `Cw·K` times the two *collar*
`σ`-energies of `f'`. -/
def CollarBound (Cw : ℝ) : Prop :=
  ∀ (K : ℝ), 0 < K → ∀ (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 → ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig t)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig t)) →
    |∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AngSecond.sig θ
        * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ,
            Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2))

/-- **The per-`(χ_n, ψ_δ)` inequality** (the `δ > 0` form of the chain, before the two limits):
with the radial cut-off `χ_n = cut n` and the angular bump `ψ_δ = psiD δ`,

`κ·P_χψ ≤ D_χψ + Tr_χψ − 2η·A_χψ + Cw·K·Col_χδ`,

where `P, D, Tr, A, Col` are the truncated quantities of `AeColl.Defs`
(`Ptr`, `Dtr`, `Trtr`, `Atr`, `Col`) and `Cw·K` is the bound on the collar term `½|W_χψ|`. -/
def TruncPairLe (Cw : ℝ) : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    MixedHon u →
    ∀ (K : ℝ), 0 < K → SliceRate K u →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 →
      kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
        ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
          + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ

/-- **The `ψ_δ ↓ 0` limit** for fixed `n`: the per-`δ` inequality (`TruncPairLe`) passes to the
limit `δ → 0⁺`, giving the inequality with the `δ`-free truncated quantities
`Pcut, Dcut, Trcut, Acut` of `AeColl.Defs`. -/
def PairLimit (Cw : ℝ) : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    MixedHon u →
    ∀ (K : ℝ), 0 < K → SliceRate K u →
    (hpair : ∀ (n : ℕ) (δ : ℝ), 0 < δ → 4 * δ ≤ Real.pi / 2 →
      kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
        ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
          + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ) →
    ∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n

end Work.FTS.EllipticEst.Deleg
