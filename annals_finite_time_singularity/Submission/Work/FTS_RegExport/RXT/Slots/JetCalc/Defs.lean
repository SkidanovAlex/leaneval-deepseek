import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JetCalc/Defs` — the jet functional of a differential combination

This module fixes the *explicit* expansion of the mixed jets `D_z^j D_θ^i` of a
combination `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` of a stream function `X` and its first
derivatives, in terms of the mixed jets `D_z^j D_θ^i X` of `X` itself.

The expansion is the iterated Leibniz rule in the angular variable
`D_θ = sin(2θ)·∂_θ` (which sees the `θ`-dependent coefficients) combined with the
radial Leibniz rule `D_z^j (d(θ)·Y) = d(θ)·D_z^j Y` (the coefficients do not depend on
`z`) and Clairaut's theorem for the two curvilinear derivatives.  Concretely, for
`j + i ≤ 2`,

* `a(θ)·X`      contributes `∑_k C(i,k)·(D_θ^k a)·(D_z^jD_θ^{i-k} X)` (`coefJetS a j i 0`),
* `b(θ)·D_zX`   contributes `∑_k C(i,k)·(D_θ^k b)·(D_z^{j+1}D_θ^{i-k} X)` (`coefJetS b (j+1) i 0`),
* `c(θ)·∂_θX`   contributes `∑_k C(i,k)·(D_θ^k (c/sin 2·))·(D_z^jD_θ^{i-k+1} X)`
  (`coefJetS (c / sin 2·) j i 1`),

the last because `D_θ = sin(2θ)·∂_θ`.  All the jets of `X` occurring have total order at
most `j + i + 1 ≤ 3`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- The angular Leibniz sum: the contribution of a `θ`-dependent coefficient `d` times a
function whose `θ`-jets are `D_θ`-iterates of order `i - k` shifted by `s`. -/
def coefJetS (d : ℝ → ℝ) (j i s : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
    (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ
      * Work.Spaces.mixed j (i - k + s) X z θ)

/-- The jet functional of the combination `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` at the point
`(z,θ)`: the explicit finite linear combination of the mixed jets of `X` into which its
mixed jets of order `(j,i)` expand. -/
def EJet (a b c : ℝ → ℝ) (j i : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  coefJetS a j i 0 X z θ
    + coefJetS b (j + 1) i 0 X z θ
    + coefJetS (fun θ' : ℝ => c θ' / Real.sin (2 * θ')) j i 1 X z θ

/-- The combination whose jets `EJet` computes. -/
def combo (a b c : ℝ → ℝ) (X : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ

@[simp] theorem combo_apply (a b c : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    combo a b c X z θ
      = a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ := rfl

end Work.FTS_RegExport.RXT.Slots.JetCalc
