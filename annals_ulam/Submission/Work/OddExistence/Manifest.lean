import Submission.Work.OddBridge.KernelDefs
import Submission.Work.OddVolterra.Defs

/-!
# The manifest kernel `𝚯M` of the odd-case Volterra system

The paper's kernel `𝚯 n h s σ ·` (the `s`-derivative of the Abel average `G₂` of the paper's
kernel `Kvec`) is **discontinuous across the diagonal `σ = s`**: for its first slope argument
strictly larger than the second the kernel `Kvec` collapses to `0` (Lean's `√` of a negative real
is `0`), while on the diagonal it is the nonzero limit value.  Consequently `𝚯` is not continuous
on the square `[a,b]²`, and the abstract long-interval existence theorem
`Work.VolterraLong.volterra_long_exists_bump` — whose hypotheses include the *continuity and
Lipschitzness of the kernel on the square* — cannot be applied to it.

The remedy is the same as the one used by `Work.OddBridge` for the Abel inversion: replace the
paper's (piecewise-defined, discontinuous) kernel on the triangle `s ≤ σ`, where it is actually
sampled, by a manifestly smooth representative.  `Work.OddBridge.KvecM` is that representative
(smooth on a box, `KvecM_eq_Kvec` on the triangle), and here we take the Abel average of it:

`ThetaM n h s σ Z := (-Z 2, -Z 3, -∂_s(G2M n h · σ Z)₀, -∂_s(G2M n h · σ Z)₁)`.

The data `ThetaM` are continuous on the square, Lipschitz in the state, and agree with the paper's
`Theta` on the triangle `s < σ`; hence a solution of the *manifest* Volterra system is a solution
of the paper's system (the two integrands agree almost everywhere in `σ`, the diagonal being a
single point).
-/

namespace Work.OddExistence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **The manifest kernel `𝚯M`.**  The paper's `Work.OddVolterra.Theta`, with the discontinuous
kernel `Kvec` replaced by its manifest representative `Work.OddBridge.KvecM`. -/
def ThetaM (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (Z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  ![- Z 2, - Z 3,
    - deriv (fun u : ℝ => (Work.OddBridge.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 0) s,
    - deriv (fun u : ℝ => (Work.OddBridge.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 1) s]

/-- The manifest kernel at `h = 0`. -/
abbrev ThetaM0 (n : ℕ) (s σ : ℝ) (Z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  ThetaM n (fun _ => 0) s σ Z

/-- The positivity hypothesis on the box of slopes which the manifest lemmas use: the Abel
denominator `Kden` is positive at every `t` with `|t| ≥ 1/5`, i.e. off the axis on the state
region.  It is supplied by `Work.OddVolterra.Existence.krad_pos_state_region` together with the
support and `C¹`-smallness of `h`. -/
def KdenPosOn (h : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ u ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, (1 / 5 : ℝ) ≤ |t| →
    0 < Work.OddVolterra.Kden h u σ t

end

end Work.OddExistence
