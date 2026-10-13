/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak/step1Ae` — Step 1 of Elgindi's `prop:H2` in the almost-everywhere class

Target (the `Prop Step1` of `Submission/Work/FTS/EllipticEst/H2W/Ae/Assembly.lean`):

```
∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
  HkMem α 0 u ∧ HkMem α 0 (grad u) ∧
  nrm α u ≤ C * nrm α G ∧ α * nrm α (grad u) ≤ C * nrm α G
```

`AeData` is the almost-everywhere class of `H2W/Ae/Defs.lean`: the equation `bslOp α u = G`
holds on the *open* quadrant only, the Dirichlet data are *values*, `u` is `C^∞` on the open
quadrant only, `HkMem α 0` is assumed only of `G`, `z²∂_zzu` and `∂_θθu`, and the two moment
conditions `F_* u = 0`, `F_* G = 0` hold only *almost everywhere*.

## The assembly

Write `ρ = w² sin(2θ)^{-η}` and `nrm α f = √(HkSq α 0 f) = ‖f‖_ρ`.

* `AngAWeak.aeUHk` (delegated module) is the paper's **Step 1 in the `ρ`-norm**: the
  `w²`-energy identity together with the constrained slice gap (`Honest.Gap9Open`) and the
  `σ`-upgrade (`Honest.SigmaPoincare`) give `HkMem α 0 u` and `‖u‖_ρ ≤ C₁‖G‖_ρ`:
  ```
  HkMem α 0 u ∧ nrm α u ≤ C₁ * nrm α G
  ```
* `AngAWeak.aeDzNormLeaf` (proved, sorry-free cone) is the **radial first-order half**, stated
  *conditionally on any given bound of `‖u‖_ρ`* (`nrm α u ≤ M * nrm α G`), which decouples it
  from the proof of `aeUHk`; it is the same statement as `AngAWeak.aeDzNorm` (which is the
  delegated path of the same claim, proved as `aeDzNormLeaf`):
  ```
  α * nrm α (grad u) ≤ C₂(M) * nrm α G
  ```
* `HkMem α 0 (grad u)` needs **no norm bound at all**: it is the honesty clause of the *proved*
  radial Agmon–Nirenberg interpolation, available on the clash-free cone of
  `Work.FTS.EllipticEst.Dispatch.hkMem_gradUD`, whose hypotheses are exactly `HkMem α 0 u`
  (from `aeUHk`) and `HkMem α 0 (z²∂_zzu)` (a field of `AeData`).  This is `hkMem_grad_of`.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.AngAWeak.aeUHk
import Submission.Work.FTS.EllipticEst.AngAWeak.aeDzNormLeaf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology

set_option autoImplicit false

/-- `nrm` is a square root, hence nonnegative. -/
theorem nrm_nonneg (α : ℝ) (G : ℝ → ℝ → ℝ) :
    0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
  Real.sqrt_nonneg _

/-- `grad u = z ∂_zu` is `D_z u`, so the radial Agmon–Nirenberg interpolation applies to it. -/
theorem grad_eq_Dz (u : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.Ae.grad u = Work.Spaces.Dz u := rfl

/-- **`HkMem α 0 (grad u)` for an `AeData` datum**, taken from the proved module
`Work.FTS.EllipticEst.Dispatch.hkMem_gradUD` (the same statement as
`Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`, on a self-contained import cone; it is the honesty
clause of the radial Agmon–Nirenberg interpolation, which needs only `HkMem α 0 u` and
`HkMem α 0 (z²∂_zz u)` — no norm bound, and no `z`-integration by parts). -/
theorem hkMem_grad_of {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
  Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h

theorem step1Ae : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := aeUHk
  obtain ⟨C₂, hC₂pos, hC₂⟩ := aeDzNormLeaf C₁
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro α u G hA
  obtain ⟨hmu, hmuBd⟩ := hC₁ α u G hA
  have hα : 0 < α := hA.hα
  have hα1 : α ≤ 1 := by linarith [hA.hα4]
  have hG0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := nrm_nonneg α G
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    hkMem_grad_of hA
  have hdBd : α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hC₂ α u G hA hmuBd
  refine ⟨hmu, hgrad, ?_, ?_⟩
  · calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        ≤ C₁ * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hmuBd
      _ ≤ max C₁ C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hG0
  · calc α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hdBd
      _ ≤ max C₁ C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hG0

end Work.FTS.EllipticEst.AngAWeak
