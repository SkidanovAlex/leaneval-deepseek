import Submission.Work.OddBound.IndexBound

/-!
# The index bound in *Dirichlet* form (the interface consumed by the based-loop minimax)

`Work.OddBound.IndexAtMostOne` (`Submission/Work/OddBound/IndexBound.lean`) bounds the index by
considering *periodic* fields `V L = V 0` along the closed geodesic.  Its conclusion is exactly what
the **free** loop space minimax produces (Abresch--Meyer's proof of their Theorem 1.6 works on the
free loop space).

Klingenberg's original argument, and Abresch--Meyer's Remark 4.4, work instead in the **based** loop
space `Ω_p M`: the critical points are geodesic loops at the base point `p`, and the relevant
variations are the **Dirichlet** fields, vanishing at *both* ends.  There the minimax yields "at most
one negative Dirichlet direction", which is *weaker* than `IndexAtMostOne` (periodic fields with
`V L = V 0` need not vanish), and therefore a **better** interface for the isolated minimax input.

This module provides

* `DirichletIndexAtMostOne cov γ L` — "at most one negative Dirichlet direction";
* `dirichletIndexAtMostOne_of_indexAtMostOne` — the periodic form implies the Dirichlet form;
* `not_indexAtMostOne_of_not_dirichletIndexAtMostOne` — the contrapositive, for consumers of the
  periodic form;
* `not_dirichletIndexAtMostOne_of_parallelNormalPair` — **the index bound in Dirichlet form**:
  a unit-speed closed geodesic of length `L ≥ π/√δ` whose curvature is `≥ δ + ε` (`ε > 0`) on the
  planes of a parallel normal pair has **two independent negative Dirichlet fields**, so it cannot
  satisfy the Dirichlet form either.  The two fields are the same
  `sin (π s / L) • X_j` as in the periodic proof — they vanish at `s = 0` and `s = L`
  (`sin 0 = 0`, `sin π = 0`) *and* are periodic.

This is the conclusion of the minimax input used by `Submission/Work/OddBound/Minimax.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. The Dirichlet form of "index ≤ 1" -/

/-- **`Morse index ≤ 1` on the based loop space**, in negation-friendly form: there are no two
linearly independent smooth fields along the closed geodesic `γ` that **vanish at both ends**
(`V 0 = 0 = V L`) and whose index integral `∫₀^L idxAlong` is negative.

A field vanishing at both ends is in particular periodic (`V L = V 0`), so this statement is
*weaker* than `IndexAtMostOne`; it is exactly the conclusion of the minimax in the based loop space
`Ω_p M` (Abresch--Meyer Remark 4.4). -/
def DirichletIndexAtMostOne (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (L : ℝ) : Prop :=
  ∀ (V W : (t : ℝ) → TangentSpace I (γ t)),
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ V s) → V 0 = 0 → V L = 0 →
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ W s) → W 0 = 0 → W L = 0 →
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t) < 0 →
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ W (covAlong cov W) t) < 0 →
    ∃ c : ℝ, ∀ t : ℝ, W t = c • V t

/-- The periodic form implies the Dirichlet form. -/
theorem dirichletIndexAtMostOne_of_indexAtMostOne {γ : ℝ → M} {L : ℝ}
    (h : IndexAtMostOne (I := I) (cov := cov) γ L) :
    DirichletIndexAtMostOne (I := I) (cov := cov) γ L :=
  fun V W hVsm hV0 hVL hWsm hW0 hWL =>
    h V W hVsm (by rw [hVL, hV0]) hWsm (by rw [hWL, hW0])

/-- Contrapositive of the previous implication: failing the Dirichlet form implies failing the
periodic form. -/
theorem not_indexAtMostOne_of_not_dirichletIndexAtMostOne {γ : ℝ → M} {L : ℝ}
    (h : ¬ DirichletIndexAtMostOne (I := I) (cov := cov) γ L) :
    ¬ IndexAtMostOne (I := I) (cov := cov) γ L :=
  fun h' => h (dirichletIndexAtMostOne_of_indexAtMostOne (I := I) (cov := cov) h')

/-! ## 2. The Dirichlet field vanishes at both ends -/

/-- The Dirichlet field `s ↦ sin (π s / L) • X s` vanishes at `s = 0`. -/
lemma dirichletField_zero {γ : ℝ → M} {L : ℝ}
    (X : (t : ℝ) → TangentSpace I (γ t)) :
    (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) 0 = 0 := by
  have h2 : Real.pi * 0 / L = 0 := by ring
  show Real.sin (Real.pi * 0 / L) • X 0 = 0
  rw [h2, Real.sin_zero, zero_smul]

/-- The Dirichlet field `s ↦ sin (π s / L) • X s` vanishes at `s = L` for `L ≠ 0`. -/
lemma dirichletField_at_right {γ : ℝ → M} {L : ℝ} (hL : L ≠ 0)
    (X : (t : ℝ) → TangentSpace I (γ t)) :
    (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) L = 0 := by
  have h1 : Real.pi * L / L = Real.pi := by field_simp
  show Real.sin (Real.pi * L / L) • X L = 0
  rw [h1, Real.sin_pi, zero_smul]

/-! ## 3. The index bound in Dirichlet form -/

/-- **The index bound of the odd-dimensional Klingenberg estimate, Dirichlet form.**  A closed
unit-speed geodesic `γ` of length `L ≥ π/√δ` whose curvature is `≥ δ + ε` (`ε > 0`) on the planes of
a parallel normal pair has two independent **Dirichlet fields with negative index integral**, so it
fails `DirichletIndexAtMostOne`.

The proof is the same computation as in `Work.OddBound.not_indexAtMostOne_of_parallelNormalPair`, with
the periodicity `V L = V 0` of the two test fields replaced by their vanishing at `0` and `L`
(`dirichletField_zero`, `dirichletField_at_right`); the two fields
`sin (π s / L) • X₁`, `sin (π s / L) • X₂` satisfy both. -/
theorem not_dirichletIndexAtMostOne_of_parallelNormalPair (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L δ ε : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hε : 0 < ε) (hπ : Real.pi / Real.sqrt δ ≤ L)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    (hp : ParallelNormalPair (I := I) cov γ L) :
    ¬ DirichletIndexAtMostOne (I := I) (cov := cov) γ L := by
  intro hidx
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hsm₁ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ
      (fun u : ℝ => Real.sin (Real.pi * u / L) • hp.X₁ u) s := fun s hs =>
    dirichletField_smooth (L := L) (hp.smooth₁ s hs)
  have hsm₂ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ
      (fun u : ℝ => Real.sin (Real.pi * u / L) • hp.X₂ u) s := fun s hs =>
    dirichletField_smooth (L := L) (hp.smooth₂ s hs)
  have hneg₁ := integral_idxAlong_dirichletField_neg (cov := cov) htor hγsm hne hL hspeed hδ hε
    hπ hcurv hp.smooth₁ hp.parallel₁ hp.unitNormal₁
  have hneg₂ := integral_idxAlong_dirichletField_neg (cov := cov) htor hγsm hne hL hspeed hδ hε
    hπ hcurv hp.smooth₂ hp.parallel₂ hp.unitNormal₂
  obtain ⟨c, hc⟩ := hidx _ _ hsm₁ (dirichletField_zero (I := I) hp.X₁)
    (dirichletField_at_right (I := I) hL0 hp.X₁) hsm₂ (dirichletField_zero (I := I) hp.X₂)
    (dirichletField_at_right (I := I) hL0 hp.X₂) hneg₁ hneg₂
  -- evaluate at the midpoint, where the sine equals one
  refine hp.independent (L / 2) ⟨by linarith, by linarith⟩ ⟨c, ?_⟩
  have hmid : Real.pi * (L / 2) / L = Real.pi / 2 := by
    field_simp
    try ring
  have hval := hc (L / 2)
  rw [hmid, Real.sin_pi_div_two] at hval
  simpa using hval

end

end Work.OddBound
