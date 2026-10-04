import Mathlib
import Submission.Work.Diff.C.geoCrux.FarBallDefs
import Submission.Work.Diff.C.geoCrux.rayCore
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.rgrad_fcos_eikonal
import Submission.Work.Diff.C.ray_minimising
import Submission.InjRadiusCut
import Submission.CutTime

set_option backward.isDefEq.respectTransparency.types false

/-!
# The injectivity-radius input of the hard case (`Work.Diff.C.geoCrux.InjectivityProp`)

This file proves `Work.Diff.C.geoCrux.InjectivityProp`: under the C-area hypotheses
(`hsmC`, `hHess`, `hcont`, `hgrad`, `hdiam`, `4 ε₁ π < c`, `c ≤ 1/4`), the exponential map at
every point `x` is injective on the ball of radius `ρ := π - arccos (1 - c)`.

## Route

The geometric input is the **ODE/Grönwall comparison** of the radial pairing

`C t := ⟪∇(rdist x)(γ t), γ'(t)⟫`   along the unit ray `γ t := GExp x (t • ξ)`,

whose analytic core is in `Submission/Work/Diff/C/geoCrux/rayCore.lean` (namespace
`Work.Diff.C.geoCrux.RayCore`):

* `hasDerivAt_rdist_ray` — `(rdist x ∘ γ)' = C`;
* `hasDerivAt_C` — `C' = Hess (rdist x)(γ', γ')`;
* `deriv_psi_le` — `(1 - C²)' ≤ (2(1+ε₁)/sin (rdist x ∘ γ)) (1 - C²)`;
* `C_eq_one_of_deriv_bound` — the scalar Grönwall conclusion `C ≡ 1`.

Since `C ≤ 1` (Cauchy–Schwarz, using the eikonal `|∇(rdist x)| = 1` and `|γ'| = 1`), the quantity
`Ψ := 1 - C²` is nonnegative and vanishes wherever the ray is minimising. The scalar Grönwall lemma
therefore propagates the identity `rdist x (γ t) = t` from a small interval (where it holds by
`Work.Diff.C.ray_minimising`) to the whole of `[0, ρ]`: the set of times at which `rdist x ∘ γ = id`
is both closed (continuity of `rdist x`) and open (Grönwall), so it is all of `[0, ρ]`.

The passage from "every ray of length `≤ ρ` is minimising" to `InjAtLeast` is
`Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le`, applied at the endpoint `ρ` via
`Submission.CutTime.mem_minimisingSet_iff`.

## Remark on the analytic core

The four analytic lemmas above are the ones proved in
`Submission/Work/Diff/C/geoCrux/cutTime_ge.lean` (their canonical home, which also proves the
`∀ q` statement `Work.Diff.C.GeoCrux.CutTimeGeProp`).  Since the present file had to be *proved*
while `cutTime_ge.lean` was being edited by another agent, the analytic core used here is a frozen,
namespace-isolated snapshot of it, in `Submission/Work/Diff/C/geoCrux/rayCore.lean`
(namespace `Work.Diff.C.geoCrux.RayCore`, so there are no name clashes with
`Work.Diff.C.geoCrux.*` and the two modules can be imported together); this file therefore does not
track further edits of that file.

Once `Work.Diff.C.GeoCrux.CutTimeGeProp` (proved in `cutTime_ge.lean`) is stable, `injectivity_radius`
also follows from it in two lines together with
`Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le`: the bridge between the cut-time statement
`CutTimeGeProp` and the injectivity statement proved here is the "injectivity radius = minimal cut
time" lemma `Submission.InjRadiusCut.injAtLeast_iff_forall_cutTime_le`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The distance to the base point `x` along the ray `t ↦ GExp x (t • ξ)`. -/
noncomputable def rayD (hmet : IsMetricCompatible cov) (x : M) (ξ : TangentSpace I x)
    (t : ℝ) : ℝ :=
  rdist (I := I) (M := M) x (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))

/-- The radial pairing `⟪∇(rdist x)(γ t), γ'(t)⟫` along the ray `γ t = GExp x (t • ξ)`. -/
noncomputable def rayC (hmet : IsMetricCompatible cov) (x : M) (ξ : TangentSpace I x)
    (t : ℝ) : ℝ :=
  Inner.inner ℝ
    (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))
    (Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ ↦
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t)

section Helpers

/-- The ray is at most as long as its parameter: `rdist x (GExp x (t • ξ)) ≤ t` for `‖ξ‖ = 1`,
`t ≥ 0`. -/
lemma rayD_le (hmet : IsMetricCompatible cov) {x : M} {ξ : TangentSpace I x}
    (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 ≤ t) : rayD hmet x ξ t ≤ t := by
  have h := eik_rdist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet x ξ ht
  rw [hξ, mul_one] at h
  exact h

/-- The Riemannian distance is symmetric in the `rdist` vocabulary. -/
lemma rdist_comm_aux {x y : M} :
    rdist (I := I) (M := M) x y = rdist (I := I) (M := M) y x := by
  rw [rdist, rdist, Manifold.riemannianEDist_comm]

/-- **The pointwise facts along the ray.**  At a time `t > 0` where the ray is at distance
`0 < rayD t < π - arccos (1-c)` from `x`:

* `|rayC t| ≤ 1` (Cauchy–Schwarz with the unit eikonal gradient and the unit-speed ray),
* `rayC` is differentiable at `t`,
* `rayD` is differentiable at `t` with derivative `rayC t`. -/
lemma ray_pointwise
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht : 0 < t)
    (hrd0 : 0 < rayD hmet x ξ t) (hrd : rayD hmet x ξ t < Real.pi - Real.arccos (1 - c)) :
    |rayC hmet x ξ t| ≤ 1 ∧ DifferentiableAt ℝ (rayC hmet x ξ) t ∧
      HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ t) t := by
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξn
    norm_num at hξn
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) :=
    Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam x _ hrd0 hrd
  have heik : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))) = 1 :=
    rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor (q := x) (x := _)
      (ne_of_gt hrd0) hsm
  have hvn : ‖Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ ↦
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t‖ = 1 := by
    rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet x hξ0
      (ne_of_gt ht), hξn]
  have hgn : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))‖ = 1 := by
    have h : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact heik
    nlinarith [norm_nonneg (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))]
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_real_inner_le_norm
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))
      (Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ ↦
        Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t)
    rwa [hgn, hvn, one_mul] at h
  · exact (RayCore.hasDerivAt_C (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
      hcont hgrad hdiam hξ ht hrd0 hrd).differentiableAt
  · exact RayCore.hasDerivAt_rdist_ray (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
      hHess hcont hgrad hdiam hξ ht hrd0 hrd

/-- `rayC` is continuous at every point of a window on which the ray is at distance in `(0, ρ)`. -/
lemma continuousOn_rayC
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {a b : ℝ} (ha : 0 < a)
    (hwin : ∀ t ∈ Set.Icc a b,
      0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < Real.pi - Real.arccos (1 - c)) :
    ContinuousOn (rayC hmet x ξ) (Set.Icc a b) := by
  intro t ht
  exact ((ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
    hcont hgrad hdiam hξ (lt_of_lt_of_le ha ht.1) (hwin t ht).1
    (hwin t ht).2).2.1.continuousAt).continuousWithinAt

/-- **The Grönwall endpoint step.**  If `rayC ≡ 1` on `[a,b]`, the ray is at distance in `(0,ρ)`
on that window and `rayD a = a`, then `rayD b = b`.

The mean value theorem applied to `f := rayD - id` (with `f' = 0` on `[a,b]`, from the
differentiability at every point of the window and `rayC ≡ 1`) gives `f b = f a = 0`. -/
lemma rayD_eq_of_rayC_eq_one
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b)
    (hwin : ∀ t ∈ Set.Icc a b,
      0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < Real.pi - Real.arccos (1 - c))
    (haD : rayD hmet x ξ a = a)
    (hC1 : ∀ t ∈ Set.Icc a b, rayC hmet x ξ t = 1) :
    rayD hmet x ξ b = b := by
  have hfderiv : ∀ t ∈ Set.Icc a b,
      HasFDerivWithinAt (fun s : ℝ ↦ rayD hmet x ξ s - s) (0 : ℝ →L[ℝ] ℝ) (Set.Icc a b) t := by
    intro t ht
    have h1 : HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ t) t :=
      (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont
        hgrad hdiam hξ (lt_of_lt_of_le ha ht.1) (hwin t ht).1 (hwin t ht).2).2.2
    have h2 : HasDerivAt (fun s : ℝ ↦ rayD hmet x ξ s - s) (rayC hmet x ξ t - 1) t :=
      h1.sub (hasDerivAt_id t)
    have h3 : rayC hmet x ξ t - 1 = 0 := by rw [hC1 t ht]; ring
    rw [h3] at h2
    simpa using h2.hasFDerivAt.hasFDerivWithinAt
  have hmvt : ‖(rayD hmet x ξ b - b) - (rayD hmet x ξ a - a)‖ ≤ (0 : ℝ) * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
      (s := Set.Icc a b) (f := fun s : ℝ ↦ rayD hmet x ξ s - s)
      (f' := fun _ : ℝ ↦ (0 : ℝ →L[ℝ] ℝ)) (C := 0) (x := a) (y := b)
      hfderiv (fun _ _ => by simp) (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rw [zero_mul] at hmvt
  have hzero : (rayD hmet x ξ b - b) - (rayD hmet x ξ a - a) = 0 :=
    norm_eq_zero.mp (le_antisymm hmvt (norm_nonneg _))
  have ha0 : rayD hmet x ξ a - a = 0 := by rw [haD]; ring
  rw [ha0, sub_zero] at hzero
  linarith

end Helpers

/-- **Every ray of length at most `π - arccos (1-c)` is minimising.**

This is the geometric core of `InjectivityProp`: under the C-area hypotheses, for a unit vector
`ξ` at `x` and every `t ∈ [0, π - arccos (1-c)]` one has `rdist x (GExp x (t • ξ)) = t`.

The proof is the closed-and-open argument on the set
`S := {T | T ≤ ρ ∧ ∀ t ∈ [0,T], rdist x (GExp x (t • ξ)) = t}`:

* `S` contains a small interval by `Work.Diff.C.ray_minimising`;
* if `T := sSup S < ρ`, then `T ∈ S` (closedness: `rdist x` is continuous, so `{t | rayD t = t}`
  is closed), and the Grönwall step at `T` produces `T + δ ∈ S` with
  `δ = min (T/2) ((ρ-T)/2) > 0`, contradicting the definition of `T`. -/
theorem ray_minimising_upto
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi - Real.arccos (1 - c)), rayD hmet x ξ t = t := by
  classical
  haveI : RegularSpace M := inferInstance
  haveI : ConnectedSpace M := inferInstance
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξn
    norm_num at hξn
  set ρ : ℝ := Real.pi - Real.arccos (1 - c) with hρdef
  have hρπ : ρ ≤ Real.pi := by
    rw [hρdef]; linarith [Real.arccos_nonneg (1 - c)]
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    have h : Real.arccos (1 - c) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    linarith
  -- continuity of the ray and of `rayD`
  have hγcont : Continuous (fun s : ℝ ↦
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hξ0).continuous
  have hDcont : Continuous (rayD hmet x ξ) :=
    (rdist_continuous (I := I) (M := M) x).comp hγcont
  -- small times are minimising
  obtain ⟨t₁, ht₁pos, ht₁ρ, ht₁⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ ρ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t₁, rayD hmet x ξ t = t := by
    obtain ⟨ε, hε0, hε⟩ := ray_minimising (I := I) (M := M) (cov := cov) hmet htor x ξ hξ0
    refine ⟨min (ε / 2) ρ, lt_min (by linarith) hρ0, min_le_right _ _, ?_⟩
    intro t ht
    have hlt : |t| < ε := by
      have h2 : t ≤ ε / 2 := le_trans ht.2 (min_le_left _ _)
      rw [abs_of_nonneg ht.1]; linarith
    have h := hε t hlt
    show rdist (I := I) (M := M) x (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) = t
    rw [rdist, h, hξn, mul_one, abs_of_nonneg ht.1, ENNReal.toReal_ofReal ht.1]
  -- the good set
  set S : Set ℝ := {T : ℝ | T ≤ ρ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, rayD hmet x ξ t = t} with hSdef
  have hSne : S.Nonempty := ⟨t₁, ht₁ρ, ht₁⟩
  have hbdd : BddAbove S := ⟨ρ, fun T hT => hT.1⟩
  set T : ℝ := sSup S with hTdef
  have hTρ : T ≤ ρ := csSup_le hSne fun t ht => ht.1
  have hTpos : 0 < T := lt_of_lt_of_le ht₁pos (le_csSup hbdd ⟨ht₁ρ, ht₁⟩)
  have hltS : ∀ t : ℝ, t < T → t ∈ S := by
    intro t ht
    obtain ⟨T', hT'S, htT'⟩ := exists_lt_of_lt_csSup hSne ht
    exact ⟨le_trans htT'.le hT'S.1, fun s hs => hT'S.2 s ⟨hs.1, le_trans hs.2 htT'.le⟩⟩
  have hTS : T ∈ S := by
    refine ⟨hTρ, fun t ht => ?_⟩
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact (hltS t h).2 t ⟨ht.1, le_rfl⟩
    · have hZcl : IsClosed {s : ℝ | rayD hmet x ξ s = s} :=
        isClosed_eq hDcont continuous_id
      have hsub : Set.Ioo (0 : ℝ) T ⊆ {s : ℝ | rayD hmet x ξ s = s} := by
        intro s hs
        exact (hltS s hs.2).2 s ⟨hs.1.le, le_rfl⟩
      have hmem : T ∈ closure (Set.Ioo (0 : ℝ) T) := by
        rw [closure_Ioo (a := (0 : ℝ)) (b := T) (ne_of_lt hTpos)]
        exact ⟨le_of_lt hTpos, le_rfl⟩
      have hTZ : rayD hmet x ξ T = T := (hZcl.closure_subset_iff).mpr hsub hmem
      rw [h]
      exact hTZ
  -- the main claim
  have hTeq : T = ρ := by
    rcases lt_or_eq_of_le hTρ with hlt | heq
    · exfalso
      set δ : ℝ := min (T / 2) ((ρ - T) / 2) with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
      have hδT : δ ≤ T / 2 := by rw [hδdef]; exact min_le_left _ _
      have hδρ : δ ≤ (ρ - T) / 2 := by rw [hδdef]; exact min_le_right _ _
      have hTδρ : T + δ < ρ := by linarith
      have hTa : rayD hmet x ξ T = T := hTS.2 T ⟨le_of_lt hTpos, le_rfl⟩
      -- the window `[T, T+δ]` stays in `(0,ρ)`
      have hwin : ∀ t ∈ Set.Icc T (T + δ),
          0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < ρ := by
        intro t ht
        have htT : T ≤ t := ht.1
        have htδ : t ≤ T + δ := ht.2
        have hle : rayD hmet x ξ t ≤ t :=
          rayD_le (I := I) (M := M) (cov := cov) hmet hξn (le_of_lt (lt_of_lt_of_le hTpos htT))
        constructor
        · have htri : rayD hmet x ξ T ≤ rayD hmet x ξ t
              + rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
                (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ)) :=
            eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor x
              (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
              (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ))
          have hsub : rdist (I := I) (M := M)
              (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
              (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ)) ≤ t - T := by
            rw [rdist_comm_aux]
            exact eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet x hξn
              (le_of_lt hTpos) htT
          have h3 : t ≤ T + T / 2 := by linarith
          linarith
        · linarith
      -- `rayC T = 1`, from `rayC ≡ 1` on `[T/2, T]`
      have hwin2 : ∀ t ∈ Set.Icc (T / 2) T,
          0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < ρ := by
        intro t ht
        have hd : rayD hmet x ξ t = t :=
          hTS.2 t ⟨le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1, ht.2⟩
        rw [hd]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hs0 : 0 < T / 2 := by linarith
      have h25 : T / 2 < T := by linarith
      have hCT : rayC hmet x ξ T = 1 := by
        have hev : (rayD hmet x ξ) =ᶠ[𝓝 (T / 2)] (fun t : ℝ ↦ t) := by
          filter_upwards [Ioo_mem_nhds hs0 h25] with t ht
          exact hTS.2 t ⟨ht.1.le, le_of_lt ht.2⟩
        have h1 : HasDerivAt (rayD hmet x ξ) 1 (T / 2) :=
          (hasDerivAt_id (T / 2)).congr_of_eventuallyEq hev
        have h2 : HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ (T / 2)) (T / 2) :=
          (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
            hcont hgrad hdiam hξ hs0 (hwin2 (T / 2) ⟨le_rfl, le_of_lt h25⟩).1
            (hwin2 (T / 2) ⟨le_rfl, le_of_lt h25⟩).2).2.2
        have hd1 : deriv (rayD hmet x ξ) (T / 2) = 1 := h1.deriv
        have hd2 : deriv (rayD hmet x ξ) (T / 2) = rayC hmet x ξ (T / 2) := h2.deriv
        rw [hd2] at hd1
        have hCs : rayC hmet x ξ (T / 2) = 1 := hd1
        have hkey := RayCore.C_eq_one_of_deriv_bound (A := rayD hmet x ξ) (C := rayC hmet x ξ)
          (ε := ε₁) (t₁ := T / 2) (T := T) hε₁ (by linarith)
          hDcont.continuousOn
          (continuousOn_rayC (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hdiam hξ hs0 hwin2)
          (fun t ht => (hwin2 t ht).1)
          (fun t ht => by
            have hd : rayD hmet x ξ t = t :=
              hTS.2 t ⟨le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1, ht.2⟩
            rw [hd]; linarith [ht.2, hlt, hρπ])
          (fun t ht => (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hdiam hξ (lt_of_lt_of_le hs0 ht.1) (hwin2 t ht).1
            (hwin2 t ht).2).1)
          hCs
          (fun t ht => (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hdiam hξ (lt_of_lt_of_le hs0 (le_of_lt ht.1))
            (hwin2 t ⟨ht.1.le, ht.2.le⟩).1 (hwin2 t ⟨ht.1.le, ht.2.le⟩).2).2.1)
          (fun t ht => RayCore.deriv_psi_le (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hdiam hξ (lt_of_lt_of_le hs0 (le_of_lt ht.1))
            (hwin2 t ⟨ht.1.le, ht.2.le⟩).1 (hwin2 t ⟨ht.1.le, ht.2.le⟩).2)
        exact hkey T ⟨by linarith, le_rfl⟩
      -- `rayC = 1` on the whole window `[T, T+δ]`
      have hC1 : ∀ t ∈ Set.Icc T (T + δ), rayC hmet x ξ t = 1 := by
        refine RayCore.C_eq_one_of_deriv_bound (A := rayD hmet x ξ) (C := rayC hmet x ξ) (ε := ε₁)
          (t₁ := T) (T := T + δ) hε₁ (by linarith) hDcont.continuousOn ?_ ?_ ?_ ?_ hCT ?_ ?_
        · exact continuousOn_rayC (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hdiam hξ hTpos hwin
        · intro t ht
          exact (hwin t ht).1
        · intro t ht
          have hle : rayD hmet x ξ t ≤ t :=
            rayD_le (I := I) (M := M) (cov := cov) hmet hξn (le_trans (le_of_lt hTpos) ht.1)
          linarith [ht.2, hTδρ, hρπ]
        · intro t ht
          exact (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hdiam hξ (lt_of_lt_of_le hTpos ht.1) (hwin t ht).1
            (hwin t ht).2).1
        · intro t ht
          exact (ray_pointwise (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hdiam hξ (lt_of_lt_of_le hTpos (le_of_lt ht.1))
            (hwin t ⟨ht.1.le, ht.2.le⟩).1 (hwin t ⟨ht.1.le, ht.2.le⟩).2).2.1
        · intro t ht
          exact RayCore.deriv_psi_le (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
            hcont hgrad hdiam hξ (lt_of_lt_of_le hTpos (le_of_lt ht.1))
            (hwin t ⟨ht.1.le, ht.2.le⟩).1 (hwin t ⟨ht.1.le, ht.2.le⟩).2
      -- the endpoint
      have hDb : rayD hmet x ξ (T + δ) = T + δ :=
        rayD_eq_of_rayC_eq_one (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
          hHess hcont hgrad hdiam hξ hTpos (by linarith) hwin hTa hC1
      -- hence `T + δ ∈ S`, contradicting the definition of `T`
      have hed : Manifold.riemannianEDist I x
          (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))
          = ENNReal.ofReal (T + δ) := by
        have hfin : Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ)) ≠ ⊤ :=
          (Submission.HopfRinow.riemannianEDist_lt_top hmet htor x _).ne
        have htr : (Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))).toReal = T + δ := hDb
        calc Manifold.riemannianEDist I x
              (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))
            = ENNReal.ofReal ((Manifold.riemannianEDist I x
                (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))).toReal) :=
              (ENNReal.ofReal_toReal hfin).symm
          _ = ENNReal.ofReal (T + δ) := by rw [htr]
      have hTδS : T + δ ∈ S := by
        refine ⟨le_of_lt hTδρ, fun t ht => ?_⟩
        by_cases h : t ≤ T
        · exact hTS.2 t ⟨ht.1, h⟩
        · have hgt : T < t := lt_of_not_ge h
          have hmem : (T + δ) ∈ Submission.CutTime.minimisingSet (I := I) hmet x ξ :=
            ⟨le_of_lt (by linarith), hed⟩
          have hmem' := Submission.CutTime.minimisingSet_of_le (I := I) (cov := cov) hmet htor
            hξn hmem (le_of_lt (lt_of_lt_of_le hTpos (le_of_lt hgt))) ht.2
          show rdist (I := I) (M := M) x
            (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) = t
          rw [rdist, hmem'.2, ENNReal.toReal_ofReal (le_of_lt (lt_of_lt_of_le hTpos (le_of_lt hgt)))]
      have hle : T + δ ≤ T := le_csSup hbdd hTδS
      linarith
    · exact heq
  -- conclusion
  intro t ht
  rcases lt_or_eq_of_le ht.2 with h | h
  · exact (hltS t (by rw [hTeq]; exact h)).2 t ⟨ht.1, le_rfl⟩
  · subst h
    rw [← hTeq]
    exact hTS.2 T ⟨hTpos.le, le_rfl⟩

/-- **`Work.Diff.C.geoCrux.InjectivityProp`**: under the C-area hypotheses the exponential map at
every point is injective on the ball of radius `π - arccos (1-c)`.

By `ray_minimising_upto` every ray of length `≤ ρ` is minimising, i.e. `ρ` lies in the minimising
set of every unit direction; `Submission.CutTime.mem_minimisingSet_iff` converts this into
`ρ ≤ cutTime x ξ`, and `Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le` into the
injectivity statement. -/
theorem injectivity_radius : Work.Diff.C.geoCrux.InjectivityProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam x
  haveI : RegularSpace M := inferInstance
  refine Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le (I := I) (cov := cov) hmet htor ?_
  intro ξ hξn
  have hξi : Inner.inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξn, one_pow]
  have hρpos : 0 < Real.pi - Real.arccos (1 - c) := by
    have h : Real.arccos (1 - c) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    linarith
  have hmin : rayD hmet x ξ (Real.pi - Real.arccos (1 - c)) = Real.pi - Real.arccos (1 - c) :=
    ray_minimising_upto (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
      hcont hgrad hdiam hξi _ ⟨le_of_lt hρpos, le_rfl⟩
  have hed : Manifold.riemannianEDist I x
      (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
      = ENNReal.ofReal (Real.pi - Real.arccos (1 - c)) := by
    have hfin : Manifold.riemannianEDist I x
        (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
        ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top hmet htor x _).ne
    have htr : (Manifold.riemannianEDist I x
        (Submission.GlobalExp.GExp (cov := cov) hmet x
          ((Real.pi - Real.arccos (1 - c)) • ξ))).toReal
        = Real.pi - Real.arccos (1 - c) := hmin
    calc Manifold.riemannianEDist I x
          (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
        = ENNReal.ofReal ((Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x
              ((Real.pi - Real.arccos (1 - c)) • ξ))).toReal) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal (Real.pi - Real.arccos (1 - c)) := by rw [htr]
  have hmem : (Real.pi - Real.arccos (1 - c))
      ∈ Submission.CutTime.minimisingSet (I := I) hmet x ξ := ⟨le_of_lt hρpos, hed⟩
  exact ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξn).mp hmem).2

end Work.Diff.C.geoCrux
