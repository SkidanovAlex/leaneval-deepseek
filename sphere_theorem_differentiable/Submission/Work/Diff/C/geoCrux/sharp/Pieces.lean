import Mathlib
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.geoCrux.sharp.VarMod
import Submission.Work.Diff.C.geoCrux.sharp.ray_package
import Submission.Work.Diff.C.geoCrux.sharp.varfield_ne_zero
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.JacobiLogDeriv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pieces of the sharp modulus bound, discharged from the delegated lemmas

This file collects the inputs of `Work.Diff.C.geoCrux.sharp.varMod_core`:

* `Zf_norm_eq`, `Zf_ne_zero_iff` — the transfer of norms and of non-vanishing between the asserted
  type of `Zf` (at `GExp q (t • v)`) and the natural type of the raw velocity field (at
  `GExp q (t • (v + 0 • ξ))`), which are propositionally equal points;
* `Zf_ne_zero` — non-vanishing of the radial variation field, from
  `Work.Diff.C.geoCrux.sharp.varfield_ne_zero`;
* `logderiv_le` — the bound `⟪∇Z_η(t), Z_η(t)⟫ / ⟪Z_η(t), Z_η(t)⟫ ≤ cot t + ε₁/sin t`, from the ray
  package `Work.Diff.C.geoCrux.sharp.ray_package`, the bridge
  `Work.Diff.C.dmRadialBridge` (inside the ray package) and the shape-operator bound
  `Work.Diff.C.rhess_rdist_bound_of_hHess`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic Submission.JacobiGlobal

namespace Work.Diff.C.geoCrux.sharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **Non-vanishing of `Zf`**, from `Work.Diff.C.geoCrux.sharp.varfield_ne_zero`. -/
theorem Zf_ne_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (η : TangentSpace I q) (hη : Inner.inner ℝ v η = 0) (hη0 : η ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)) :
    Zf (cov := cov) hmet q v η t ≠ 0 := by
  have h := Work.Diff.C.geoCrux.sharp.varfield_ne_zero (E := E) (H := H) (I := I) (M := M)
    hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv η hη hη0 t ht0 htρ
  intro hz
  exact h ((Zf_ne_zero_iff (cov := cov) hmet q v η t).mp hz)

/-- **The log-derivative bound for the radial variation field.** -/
theorem logderiv_le
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (η : TangentSpace I q) (hη : Inner.inner ℝ v η = 0) (hη0 : η ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (htρ : t < Real.pi - Real.arccos (1 - c)) :
    Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
        (Zf (cov := cov) hmet q v η t)
      / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
      ≤ Real.cot t + ε₁ / Real.sin t := by
  obtain ⟨hsm, hrd, hgradeq, horthT, hbridge⟩ :=
    Work.Diff.C.geoCrux.sharp.ray_package (E := E) (H := H) (I := I) (M := M)
      hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad q v hv t ht0 htρ
  have hρ₀π : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hdπ : t < Real.pi := lt_trans htρ hρ₀π
  -- the region hypothesis `-1 + c < fcos q (γ t)`
  have hfc : -1 + c < fcos (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := t)
      (y := Real.pi - Real.arccos (1 - c)) ht0.le (le_of_lt hρ₀π) htρ
    have hcr : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
      rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
      ring
    rw [hcr] at hcos
    have hcos_t : fcos (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) = Real.cos t := by
      show Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))) = Real.cos t
      rw [hrd]
    rw [hcos_t]
    exact hcos
  -- the orthogonality with `∇(fcos q)`
  have hV : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)))
      (Zf (cov := cov) hmet q v η t) = 0 := by
    apply horthT
    have hg0 : Inner.inner ℝ (Zf (cov := cov) hmet q v η t)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t) = 0 := by
      rw [ray_pt (cov := cov) hmet q v η t, Zf_eq_fv]
      have hη' : Inner.inner ℝ η v = 0 := by rw [real_inner_comm]; exact hη
      rw [Work.Diff.C.geoCrux.fv_gauss (cov := cov) hmet htor q v η t, hη', mul_zero]
    rw [hgradeq, real_inner_comm]
    exact hg0
  -- the shape-operator bound at `γ t`
  have hshape := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov)
    (c := c) (ε := ε₁) (q := q) (hHess q) hfc hsm (by rw [hrd]; exact ht0)
    (by rw [hrd]; exact hdπ) (Zf (cov := cov) hmet q v η t) hV
  -- the bridge and positivity
  have hbr := hbridge η hη
  have hbrZ : Inner.inner ℝ
        (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
        (Zf (cov := cov) hmet q v η t)
      = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
          (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t) := by
    have h1 : (Zf (cov := cov) hmet q v η)
        = (fun s : ℝ => (show TangentSpace I
            (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) from
              fv (cov := cov) hmet q v η s)) := by
      funext s
      rw [Zf_eq_fv]
    rw [h1]
    exact hbr
  have hpos : 0 < Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t) := by
    rw [real_inner_self_eq_norm_sq]
    refine pow_pos ?_ 2
    rw [norm_pos_iff]
    exact Zf_ne_zero hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv η hη hη0 t
      ht0 htρ.le
  -- the bound on the numerator
  have hnum : Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
      ≤ (Real.cot t + ε₁ / Real.sin t)
        * Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t) := by
    have h1 := (abs_le.mp hshape).2
    rw [hrd] at h1
    have h2 : (ε₁ / Real.sin t)
        * Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
        ≤ (ε₁ / Real.sin t)
          * Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t) :=
      le_refl _
    linarith [h1, h2]
  calc Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
        (Zf (cov := cov) hmet q v η t)
        / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
      = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
          (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
          / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t) := by
        rw [hbrZ]
    _ ≤ Real.cot t + ε₁ / Real.sin t := by
        rw [div_le_iff₀ hpos]
        exact hnum

end Work.Diff.C.geoCrux.sharp
