import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.Core
import Submission.Work.Projection.compact_embedding
import Submission.Work.Drive.N2.exists_smooth_retraction_manifold
import Submission.Work.Drive.N2.eq_of_deriv_eq_one
import Submission.Work.Drive.N2.retraction_fixed_of_isIntegralCurve
import Submission.Work.Drive.N2.exists_contDiff_bump_isCompact
import Submission.Work.Drive.N2.contDiff_levelField
import Submission.Work.Drive.N2.levelField_spec
import Submission.Work.Drive.N2.isIntegralCurve_mem_tsupport_or_eq
import Submission.Work.Drive.N2.auxField_retraction_ne_zero
import Submission.Work.Drive.N2.exists_flow_jointSmooth_levelField

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — hasLevelFlow_of_noCritical
WHY: compact n = 2 (every compact surface embeds in ℝ⁴) is the last of the three inputs of Whitney's strong
embedding theorem. The lead chose MORSE THEORY. The vocabulary is `Submission/Work/Drive/Morse.lean`: `IsCritical`,
`NondegCrit`, `IsMorseDistinct`, `HasLevelFlow`, `MorseLemma2`. Other agents prove the other pieces in parallel:
existence of Morse functions, the level flow, the planar Morse lemma, and the embedding from these. Every piece
consumes the others ONLY through those definitions, so do not change them. If one is unusable or false for your
purpose, stop and say so precisely with `declare_false`.

Route:
1. The critical set is closed, and none of it lies over [a, b]. So there is an open V ⊇ f⁻¹[a, b] with df ≠ 0 on V.
   Build a smooth vector field X on M, compactly supported, with X f = 1 on a neighbourhood of f⁻¹[a, b]. Do
   it locally in charts, where v = ∇(f∘φ⁻¹)/|∇|² pushed forward, and glue with a smooth partition of unity:
   Σ ρ_i X_i f = Σ ρ_i = 1. Mathlib has `SmoothPartitionOfUnity`.
2. Its flow Φ. Mathlib has global integral curves on compact boundaryless manifolds
   (`Mathlib/Geometry/Manifold/IntegralCurve/UniformTime.lean`: `exists_isMIntegralCurve_of_isMIntegralCurveOn`,
   and uniqueness in `ExistUnique.lean`). That gives Φ(·, x) and the flow law.
3. THE REAL WORK: joint SMOOTHNESS of (t, x) ↦ Φ(t, x). Mathlib does not have smooth dependence on initial
   conditions. Options:
   (a) Prove it for ODEs in ℝ^k with a smooth, compactly supported, globally Lipschitz field. Use the standard
       argument: the flow is C¹ with derivative solving the variational equation, then bootstrap C^k by
       induction on k (the pair (flow, derivative) solves an ODE of the same kind). Then transfer to M.
   (b) Avoid charts: embed M in ℝ^N (weak Whitney, proved), extend X to a compactly supported smooth field on
       ℝ^N tangent to M along M, and flow in ℝ^N. The flow preserves M by uniqueness.
   Do (a) in ℝ^k as a self-contained sub-lemma; delegate it if it is big.
4. f(Φ(t, x)) = f x + t holds while the curve stays where X f = 1, i.e. while the values stay in [a, b]:
   d/dt f(Φ) = (X f)(Φ) = 1.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- Over an interval of values free of critical points, a smooth function on a compact surface has a smooth
level flow. -/
theorem hasLevelFlow_of_noCritical {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (a b : ℝ)
    (hcrit : ∀ x, f x ∈ Set.Icc a b → ¬ IsCritical f x) : HasLevelFlow f a b := by
  refine hasLevelFlow_of_hypotheses (f := f) (hf := hf) (a := a) (b := b) (hcrit := hcrit)
    (hretr := fun {n N} {M'} _ _ _ _ _ _ e he hinj himm =>
      exists_smooth_retraction_manifold e he hinj himm)
    (hflowSmooth := fun E G χ hE hG hχ hcχ hsupp =>
      exists_flow_jointSmooth_levelField E G χ hE hG hχ hcχ hsupp)
    (hcmp := fun hu a0 b0 h0 hd => eq_of_deriv_eq_one hu a0 b0 h0 hd)
    (hfix := fun E Y γ hE hY hc hYrange horth hγ h0 =>
      retraction_fixed_of_isIntegralCurve E Y γ hE hY hc hYrange horth hγ h0)
    (hbump := fun hK hO hKO => exists_contDiff_bump_isCompact hK hO hKO)
    (hfield := fun E G χ hE hG hχ hcχ hsupp => contDiff_levelField E G χ hE hG hχ hcχ hsupp)
    (hspec := fun E G χ hE hG => levelField_spec E G χ hE hG)
    (hts := fun Y hY hc γ hγ => isIntegralCurve_mem_tsupport_or_eq Y hY hc γ hγ)
    (haux := fun {n N} {M'} _ _ _ e he himm U hUopen π hπsm hπe x₀ hU g hg hmf =>
      auxField_retraction_ne_zero e he himm U hUopen π hπsm hπe x₀ hU g hg hmf)

end Work.Drive.N2
