import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.T.FrameExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A family of tangent fields whose pairings against every jointly smooth family are jointly
smooth is itself jointly smooth.

This is the family (time-dependent) version of `Work.EXT.lc_section_of_inner` (see
`Submission/Work/EXT/lcSmooth_noBoundary.lean`), whose proof should be adapted.  Fix `p₀ = (t₀,y₀)`
in the open set `V`, let `triv := trivializationAt E (TangentSpace I) y₀`, and let `Z i` be
globally smooth fields agreeing near `y₀` with `triv.symmL ℝ · (finBasis i)`
(`Work.Diff.T.exists_global_eventuallyEq_symmL` in `Submission/Work/Diff/T/FrameExt.lean`).  By
`Trivialization.contMDiffAt_iff` (`Bundle.Trivialization.contMDiffAt_iff`, with the base `M`, the
domain `ℝ × M`, `IM := (𝓘(ℝ,ℝ)).prod I`, `IB := I`, `f p := ⟨p.2, σ p.1 p.2⟩`) it suffices to
show that `p ↦ (triv ⟨p.2, σ p.1 p.2⟩).2 = triv.continuousLinearMapAt ℝ p.2 (σ p.1 p.2)` is
jointly `C^∞` near `p₀` (use `Trivialization.continuousLinearMapAt_apply_of_mem` to switch).

The Gram matrix `Γ p i j = (G p.1).inner p.2 (Z i p.2) (Z j p.2)` has jointly smooth entries
(apply `Work.Diff.EXT.covK_metric_pairing_family` to the constant-in-`t` families `fun _ => Z i`,
`fun _ => Z j`, which are `JointField` as `CMDiff ∞ (T% (Z i))` composed with `Prod.snd`), and
`Γ p₀` is invertible because it is the Gram matrix of a basis for the positive definite form
`(G t₀).inner y₀` (use `Matrix.posDef_gram_of_linearIndependent` under a local
`letI : RiemannianBundle _ := ⟨(G t₀).toRiemannianMetric⟩`, or
`Work.Diff.EXT.eq_sum_basis_of_pairing_gram`).  The vector
`x p = (Γ p)⁻¹ *ᵥ (fun k ↦ (G p.1).inner p.2 (σ p.1 p.2) (Z k p.2))` has jointly smooth entries:
`Work.Diff.EXT.contMDiffAt_matrix_inv` gives the inverse, the entries of the vector are smooth by
the hypothesis `h` applied to `W := fun _ => Z k` (a `JointField`), and we close under
`Matrix.mulVec` (finite sum).  Finally, near `p₀`, `σ p.1 p.2 = Σ k, (x p) k • Z k p.2` — the
linear algebra is `Work.Diff.EXT.eq_sum_basis_of_pairing_gram` (in
`Submission/Work/Diff/EXT/eq_sum_frameVector_of_pairing.lean`) applied at each `p` with the basis
`(finBasis ℝ E).map (trivializationAt E (TangentSpace I) y₀).linearEquivAt` — so the trivialised
form becomes `Σ k, (x p) k • finBasis k`, which is smooth because each `p ↦ x p k` is. -/
theorem covK_section_of_pairing_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {σ : ℝ → TField (I := I) (M := M)}
    (h : ∀ W : ℝ → TField (I := I) (M := M), JointField W V →
        ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
          (fun p : ℝ × M ↦ (G p.1).inner p.2 (σ p.1 p.2) (W p.1 p.2)) V) :
    JointField σ V := by sorry

end Work.Diff.EXT
