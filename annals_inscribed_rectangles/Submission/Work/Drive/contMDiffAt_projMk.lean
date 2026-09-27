import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.contMDiffAt_projCharted_iff

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
set_option linter.style.haveILetI false in
/-- **Smoothness into `ℝPⁿ` of a projectivised smooth non-vanishing vector.**  For a map
`V : ℝᵏ → Eucl n` that is `C^∞` at `x₀` and non-zero everywhere, the map
`x ↦ Projectivization.mk ℝ (V x) (hV x)` into `ℝPⁿ` with the transparent smooth structure
`Work.Drive.projCharted n` (`Submission/Work/Drive/projCharted.lean`) is `C^∞` at `x₀`.

This is the general tool that turns an explicit sphere/vector lift of a map into `ℝPⁿ` into
smoothness: by `Work.Drive.contMDiffAt_projCharted_iff` one has to check continuity (from
`Work.Drive.continuous_projectivizationMk` composed with the continuous `x ↦ ⟨V x, hV x⟩`) and the
smoothness of `projChartMap i ∘ (⋯)` for one chart `i` with `(V x₀).ofLp i ≠ 0` — such an `i` exists
because `V x₀ ≠ 0` — where `projChartMap i (Projectivization.mk ℝ (V x) ⋯) = projCoordFun i (V x)`,
whose coordinates `(V x).ofLp j / (V x).ofLp i` are ratios of smooth functions with non-vanishing
denominator on a neighbourhood of `x₀`. -/
theorem contMDiffAt_projMk {n k : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl n)
    (hV : ∀ x, V x ≠ 0) (x₀ : EuclideanSpace ℝ (Fin k))
    (hVs : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ (Eucl n)) ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    letI := Work.Drive.projCharted n
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Projectivization.mk ℝ (V x) (hV x)) x₀ := by
  -- the transparent projective structure, so that the chart `projChart i` is available
  letI := Work.Drive.projCharted n
  -- a chart index at which the vector `V x₀` is non-zero; it exists because `V x₀ ≠ 0`
  have hex : ∃ i : Fin (n + 1), (V x₀).ofLp i ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    refine hV x₀ ?_
    ext i
    simpa using not_not.mp (hcon i)
  obtain ⟨i, hi⟩ := hex
  -- reduce to continuity plus smoothness of the composite with the chart `projChart i`
  rw [Work.Drive.contMDiffAt_projCharted_iff (n := n) (k := k)
    (f := fun x => Projectivization.mk ℝ (V x) (hV x)) x₀ i
    ((Work.Drive.mem_projChartSource_iff' (i := i) (hV x₀)).mpr hi)]
  refine ⟨?_, ?_⟩
  · -- continuity: `Projectivization.mk` is continuous and `x ↦ ⟨V x, hV x⟩` is continuous at `x₀`
    have hc : ContinuousAt (fun x => (⟨V x, hV x⟩ : {v : Eucl n // v ≠ 0})) x₀ :=
      hVs.continuousAt.codRestrict (t := {v : Eucl n | v ≠ 0}) (fun x => hV x)
    exact (Work.Drive.continuous_projectivizationMk ℝ (Eucl n)).continuousAt.comp hc
  · -- smoothness of the composite: it is `fun w ↦ projCoordFun i (V w)`, whose coordinates are
    -- quotients of smooth functions with non-vanishing denominator
    have key : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.projCoordFun i (V w)) x₀ := by
      refine (contDiffAt_piLp (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (p := 2)
        (E := fun _ : Fin n => ℝ) (f := fun w => Work.Drive.projCoordFun i (V w))).2 ?_
      intro j
      have hcoord (l : Fin (n + 1)) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w => (V w).ofLp l) x₀ :=
        (contDiffAt_piLp_apply (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (p := 2)
          (E := fun _ : Fin (n+1) => ℝ) (i := l)).comp x₀ hVs.contDiffAt
      have hj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w => (V w).ofLp (i.succAbove j) / (V w).ofLp i) x₀ := by fun_prop
      simpa only [Work.Drive.projCoordFun_ofLp] using hj
    have hfun : (fun w => Work.Drive.projChartMap i
        (Projectivization.mk ℝ (V w) (hV w))) = fun w => Work.Drive.projCoordFun i (V w) := by
      funext w
      exact Work.Drive.projChartMap_mk i (V w) (hV w)
    rw [hfun]
    exact key.contMDiffAt

end Work.Drive
