import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared contract: smooth flows of time-dependent vector fields on a compact manifold
(lead-written; used by STE (DeTurck pull-back) and by the d = 2 branch (gradient-like flow)).
A field defined only on an open set is first multiplied by a bump function; its flow agrees with the
original one as long as the trajectory stays where the bump is `1`.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

namespace Submission.Diff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

variable (I M) in
/-- CONTRACT ODE: every jointly smooth time-dependent vector field `X` has a jointly smooth global
two-parameter flow `Φ s t x` (position at time `t` of the integral curve through `x` at time `s`). -/
def SmoothFlow : Prop :=
  ∀ X : ℝ → Π x : M, TangentSpace I x,
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) →
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞ (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      ∀ s t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ ↦ Φ s τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ s t x)))

variable (I M) in
/-- CONTRACT ODE-Icc: the same for a field that is only smooth on `[a,b] × M` (within), with the flow
on `[a,b]²`. (Needed by STE: the DeTurck field is smooth up to `t = 0` from the right only.) -/
def SmoothFlowIcc : Prop :=
  ∀ (a b : ℝ) (X : ℝ → Π x : M, TangentSpace I x), a < b →
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) (Icc a b ×ˢ univ) →
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞ (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2)
        ((Icc a b ×ˢ Icc a b) ×ˢ univ) ∧
      (∀ s ∈ Icc a b, ∀ x, Φ s s x = x) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, ∀ x, Φ t u (Φ s t x) = Φ s u x) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun τ ↦ Φ s τ x) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ s t x)))

end Submission.Diff
