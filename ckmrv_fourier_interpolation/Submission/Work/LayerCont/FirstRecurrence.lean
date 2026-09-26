/-
# The first recurrence of the layer, assembled from the far-side `(5.7)` identity

The socket `Work.Asymptotics.exists_pair_of_propagated_F2` asks for, for every `r`, a holomorphic
`F₂` on an open neighbourhood `O` of `closure 𝒟` whose `(T-I)²`-defect is
`-T2op (gaussTerm · r)`.  This file records the *algebraic* step of that: once the corrected
layer is known to agree

* with the paper's layer `paperLayer` at `τ` and `τ+1` (which are on the `𝒟`-side), and
* with `paperLayer + sinSqC r · resCorr r ·` at `τ+2` (the far side, CKMRV's `(matchF2sharp)`),

then the defect follows from `Work.LayerCont.T2op_paperLayer` (`(T-I)²` annihilates the paper
layer for every real `r`) and `Work.Residues.resCorr_vadd_two` (the residue correction at the
shifted point *is* `-T2op (gaussTerm · r)`).

This is the exact interface through which the far-side `(5.7)` identity of the layer
continuation is consumed; nothing else about the chart is needed here.
-/
import Mathlib
import Submission.Work.LayerCont.LayerT2
import Submission.Work.Residues.Section5Shift

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold
open Filter
open scoped Topology

namespace Work.LayerCont

open Work.Kernels

/-- **The `(T-I)²`-defect of a function that satisfies the far-side `(5.7)` identity.**

`H` agrees with the paper's layer at `τ`, `τ+1` and with the layer plus the residue correction
`sinSqC r * resCorr r` at `τ+2`; the paper's layer is annihilated by `(T-I)²`.  Then `H` has
exactly the defect required by CKMRV Proposition 5.1,

  `T2op H τ = - T2op (fun σ => gaussTerm σ r) τ`. -/
theorem T2op_of_far_identity (ℓ : LogLambdaData) (d : ℕ) (r : ℝ) (τ : ℍ) (H : ℍ → ℂ)
    (h2 : H ((2 : ℝ) +ᵥ τ)
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((2 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ))
    (h1 : H ((1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r)
    (h0 : H τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
    (hk : Work.Kernels.T2op
      (fun σ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0) :
    Work.Kernels.T2op H τ = - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) τ := by
  rw [Work.Kernels.T2op, h2, h1, h0]
  rw [show Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((2 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ)
        - 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ)
        + (Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((2 : ℝ) +ᵥ τ) r
          - 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r
          + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) by ring]
  rw [show Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((2 : ℝ) +ᵥ τ) r
        - 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.Kernels.T2op
        (fun σ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ
      from rfl,
    hk, add_zero, Work.Residues.resCorr_vadd_two]

end Work.LayerCont
