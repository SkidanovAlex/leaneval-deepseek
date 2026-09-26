import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Homotopy.Lifting

open scoped Topology

namespace Commons.Topology.Covering

/-
# Record of the received request (quoted verbatim)

This commons file was requested with the declaration quoted below, but the
request text wrapped it in the module skeleton and glued the proof placeholder
after the closing `end Commons.Topology.Covering` (and used a binder written
with a combining tilde that Lean's lexer does not accept).  The received text
is kept here exactly as sent, truncated just before the placeholder, for the
record; the declaration is then stated afresh with the identical header
(binder renamed to a lexically valid name) and proved.
theorem exists_liftOnIoo {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {t₀ : Set.Ioo (0 : ℝ) 1}
    (x₀ : E) (γ : C(Set.Ioo (0 : ℝ) 1, X)) (h₀ : p x₀ = γ t₀) :
    ∃ γ̃ : C(Set.Ioo (0 : ℝ) 1, E), (∀ t : Set.Ioo (0 : ℝ) 1, p (γ̃ t) = γ t) ∧ γ̃ t₀ = x₀

end Commons.Topology.Covering := by
-/

/-- **Path lifting for covering maps over an open interval.**  If
`p : E → X` is a covering map (`IsCoveringMap p`), every continuous map
`γ` from the open unit interval `(0,1) ⊆ ℝ` into `X` lifts through `p`
through any prescribed point `x₀` of the fibre over `γ t₀`: there is a
continuous `γ̃ : (0,1) → E` with `p ∘ γ̃ = γ` and `γ̃ t₀ = x₀`.  (No
hypotheses on `X` beyond the covering-map definition; the domain is an
open interval, and `Set.Ioo (0 : ℝ) 1` is a contractible, locally path
connected topological space, so the unique-lifting theorem applies.) -/
theorem exists_liftOnIoo {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {t₀ : Set.Ioo (0 : ℝ) 1}
    (x₀ : E) (γ : C(Set.Ioo (0 : ℝ) 1, X)) (h₀ : p x₀ = γ t₀) :
    ∃ G : C(Set.Ioo (0 : ℝ) 1, E),
      (∀ t : Set.Ioo (0 : ℝ) 1, p (G t) = γ t) ∧ G t₀ = x₀ := by
  classical
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace (Set.nonempty_Ioo.mpr zero_lt_one)
  letI : LocallyPathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).locallyPathConnectedSpace
  rcases hp.existsUnique_continuousMap_lifts γ t₀ x₀ h₀ with ⟨G, hG⟩
  exact ⟨G, fun t => congr_fun hG.left.2 t, hG.left.1⟩

end Commons.Topology.Covering