/-
# `Work.FTS.GalBasis.cc.CutSpec` — the packaged clauses of the cutoff family

`CutSpec ψ K` collects the properties of the cutoff family `ψ` proved in
`Work.FTS.GalBasis.cc.psiCut_spec` (which the companion modules `CutDefs`/`psiCut_spec` prove
for the explicit family `psiCut`), in the form consumed by the assembly of the density lemma:
smoothness, the range `[0,1]`, the *plateau* value `1`, the vanishing off the *outer box*, the
uniform bound on the mixed derivatives of order `≤ 4`, and the vanishing of the `θ`-derivatives
outside the two angular layers.

The elementary facts about the `D_z`/`D_θ`-iterates of a function which is *locally constant* at
a point (the mechanism by which the plateau value `ψ = 1` and the layer-constancy of `cutB`
propagate to the derivatives) now live in the separate module
`Work.FTS.GalBasis.cc.CutZero`, which is imported (and hence re-exported) here.  The split is
what makes the module acyclic: the proof `cc.psiCut_spec` needs `cc.psiCut_layer_zero`, which in
turn needs those two lemmas — but it must *not* need `cc.CutSpec`, which in turn needs
`cc.psiCut_spec` in order to construct the packaged specification without any `axiom`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.CutZero
import Submission.Work.FTS.GalBasis.cc.psiCut_spec
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The clauses of `psiCut_spec` that the assembly uses -/

/-- The properties of the cutoff family proved in `psiCut_spec`, in packaged form. -/
structure CutSpec (ψ : ℕ → Fn) (K : ℝ) : Prop where
  Kpos : 0 < K
  smooth : ∀ N : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (ψ N))
  nonneg : ∀ N : ℕ, ∀ z θ : ℝ, 0 ≤ ψ N z θ
  leone : ∀ N : ℕ, ∀ z θ : ℝ, ψ N z θ ≤ 1
  one : ∀ N : ℕ, ∀ z θ : ℝ, InPlateau N z θ → ψ N z θ = 1
  zero : ∀ N : ℕ, ∀ z θ : ℝ, OffBox N z θ → ψ N z θ = 0
  bound : ∀ N : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.mixed j i (ψ N) z θ| ≤ K
  lay : ∀ N : ℕ, ∀ j i : ℕ, 1 ≤ i → ∀ z θ : ℝ,
    NotInThetaLayer N θ → Work.Spaces.mixed j i (ψ N) z θ = 0

/-- `psiCut_spec` packaged.  (The specification is *proved* — no `axiom` is involved.) -/
theorem exists_cutSpec : ∃ (ψ : ℕ → Fn) (K : ℝ), CutSpec ψ K := by
  obtain ⟨K, hK, hspec⟩ := psiCut_spec
  exact ⟨psiCut, K, ⟨hK, fun N => (hspec N).1,
    fun N z θ => ((hspec N).2.1 z θ).1,
    fun N z θ => ((hspec N).2.1 z θ).2,
    fun N z θ => (hspec N).2.2.1 z θ,
    fun N z θ => (hspec N).2.2.2.1 z θ,
    fun N j i hij z θ => (hspec N).2.2.2.2.1 j i hij z θ,
    fun N j i hi z θ hnot => (hspec N).2.2.2.2.2 j i hi z θ hnot⟩⟩

end Work.FTS.GalBasis.cc
