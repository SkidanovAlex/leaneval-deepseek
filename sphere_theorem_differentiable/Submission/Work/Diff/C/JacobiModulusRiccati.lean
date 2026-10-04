import Mathlib
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.modulus_le_sin_add_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic Submission.JacobiGlobal

/-!
# Riccati comparison for the modulus of a Jacobi field, `hHess` version

`Work.Diff.C.jld_log_deriv_eq_rhess` converts a Jacobi field `Z` with `Z 0 = 0` into
`(½ log ⟪Z,·,Z,·⟫)'(t) = rhess (rdist p)(γ t)(Z t, Z t)/⟪Z t, Z t⟫` (the shape operator applied to
`Z t`), and the two-sided shape-operator bound `Work.Diff.C.rhess_rdist_bound_of_hHess` bounds that
Hessian.  Here we record the resulting pointwise bound

  `(log ‖Z‖)'(t) ≤ cot t + ε`

for the two forms of the error in which the bound is used (`ε` uniform, and `ε / sin t` as delivered
by `hHess`).  The passage from this bound to `‖Z d‖ ≤ (sin d + C √ε)‖∇Z(0)‖` is a purely
one-dimensional Sturm/Grönwall comparison (`Work.Diff.C.modulus_le_sin_add_sqrt`).
-/

/-- **Log-derivative of the modulus of a Jacobi field is bounded by the shape operator.**  If the
bridge identity `⟪∇_{γ'}Z, Z⟫ = rhess (rdist p)(γ ·)(Z,Z)` holds for the Jacobi field `Z` (supplied by
`Work.Diff.C.jld_log_deriv_eq_rhess`), `Z` stays orthogonal to `rgrad (rdist p)` and the shape
operator is bounded by `cot + ε`, then `(log ‖Z‖)' ≤ cot + ε` on the interval. -/
theorem jld_log_deriv_le_cot_of_shapeOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u : TangentSpace I p} {γ : ℝ → M}
    (hγeq : γ = fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
    {d : ℝ} {e : ℝ → ℝ}
    {Z : (t : ℝ) → TangentSpace I (γ t)}
    (hbridge : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        = Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)
            (Z t) (Z t))
    (horth : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (Z t) (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)) = 0)
    (hshape : ∀ t ∈ Set.Ioo (0 : ℝ) d, ∀ V : TangentSpace I (γ t),
      Inner.inner ℝ V (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)) = 0 →
      Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t) V V
        ≤ (Real.cot t + e t) * Inner.inner ℝ V V)
    (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) d, 0 < Inner.inner ℝ (Z t) (Z t))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) d) :
    Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t) ≤ Real.cot t + e t := by
  have h1 : Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)
      (Z t) (Z t) ≤ (Real.cot t + e t) * Inner.inner ℝ (Z t) (Z t) :=
    hshape t ht (Z t) (horth t ht)
  have h2 : (0 : ℝ) < Inner.inner ℝ (Z t) (Z t) := hpos t ht
  rw [hbridge t ht]
  exact (div_le_iff₀ h2).mpr h1

open Bundle in
/-- **The modulus bound for a Jacobi field with `J(0) = 0`.**  Assembling
`Work.Diff.C.jld_log_deriv_le_cot_of_shapeOp` (the bridge + the shape-operator bound give
`(log ‖Z‖)' ≤ cot t + ε / sin t`) with the one-dimensional Sturm/Grönwall comparison
`Work.Diff.C.modulus_le_sin_add_sqrt` gives, under the model asymptotics `‖Z t‖ = a t + O(t³)` with a
constant `C ≤ a` on `(0, √ε)`,

  `‖Z d‖ ≤ (sin d + 16 √ε) a`   (`a = ‖∇_{γ'}Z (0)‖`, `0 < ε ≤ 1/16`, `d ≤ π`).

This is the sphere-size input (`far_sphere_size`): the Jacobi field is the differential of
`v ↦ GExp q (t • v)`, so it bounds how much a geodesic sphere of radius `ρ` can spread.  The
`√ε` (rather than `ε`) is what the `ε / sin` shape-operator error delivered by `hHess` supports; a
uniform `ε` shape-operator error would upgrade it (see the note in `HANDOFF.md`). -/
theorem jld_modulus_le_sin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u : TangentSpace I p} {γ : ℝ → M}
    (hγeq : γ = fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
    {d ε a C : ℝ} (hd : 0 < d) (hdπ : d ≤ Real.pi) (ha : 0 < a) (hC : 0 ≤ C) (hCa : C ≤ a)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    {Z : (t : ℝ) → TangentSpace I (γ t)}
    (hne : ∀ t ∈ Set.Ioo (0 : ℝ) d, Z t ≠ 0)
    (hcont : ContinuousOn (fun t : ℝ => ‖Z t‖) (Set.Icc (0 : ℝ) d))
    (hlog : ∀ t ∈ Set.Ioo (0 : ℝ) d, HasDerivAt (fun s : ℝ => Real.log ‖Z s‖)
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t)) t)
    (hbridge : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        = Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)
            (Z t) (Z t))
    (horth : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (Z t) (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)) = 0)
    (hshape : ∀ t ∈ Set.Ioo (0 : ℝ) d, ∀ V : TangentSpace I (γ t),
      Inner.inner ℝ V (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t)) = 0 →
      Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) (γ t) V V
        ≤ (Real.cot t + ε / Real.sin t) * Inner.inner ℝ V V)
    (hasym : ∀ t ∈ Set.Ioo (0 : ℝ) (min d (Real.sqrt ε)), |‖Z t‖ - a * t| ≤ C * t ^ 3) :
    ‖Z d‖ ≤ (Real.sin d + 16 * Real.sqrt ε) * a := by
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) d, 0 < ‖Z t‖ := by
    intro t ht
    exact norm_pos_iff.mpr (hne t ht)
  have hmain := modulus_le_sin_add_sqrt (u := fun t : ℝ => ‖Z t‖)
    (w := fun t : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t)
        / Inner.inner ℝ (Z t) (Z t))
    hd hdπ ha hC hε hε1 hpos hcont hlog ?_ hasym
  · calc ‖Z d‖ ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := hmain
      _ ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + a) := by
          have h1 : 0 ≤ 8 * Real.sqrt ε := by positivity
          have h2 : a + C ≤ a + a := by linarith
          linarith [mul_le_mul_of_nonneg_left h2 h1]
      _ = (Real.sin d + 16 * Real.sqrt ε) * a := by ring
  · intro t ht
    have h := jld_log_deriv_le_cot_of_shapeOp (I := I) (M := M) (cov := cov)
      (e := fun s : ℝ => ε / Real.sin s)
      hmet hγeq hbridge horth hshape (t := t) ?_ ht
    · exact h
    · intro s hs
      rw [real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr (hne s hs)) 2

end Work.Diff.C

