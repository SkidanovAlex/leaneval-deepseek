import Mathlib
import Submission.Work.Diff.C.geoCrux.BadGeoProps
import Submission.Work.Diff.C.dip_model_through
import Submission.Work.Diff.C.ode_compare_halfopen
import Submission.Work.Diff.C.gp_ode_compare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The restarted Sturm comparison along a `GExp`-ray

This module proves `Work.Diff.C.GeoCrux.RestartCompareProp`, the *anchored* (restarted) form of the
Sturm comparison for a function `f` along the ray `σ ↦ GExp p (σ • u)` of the global exponential
map.  Writing `γ σ := GExp p (σ • u)` (a unit-speed geodesic by `Submission.GExpRayZero`), the
function `Φ := f ∘ γ` satisfies `Φ'' + Φ = Hess f (γ',γ') + f∘γ`, so if

`|Hess f (γ σ) V V + f (γ σ) ⟪V,V⟫| ≤ ε ⟪V,V⟫`   for `σ ∈ (b,τ]` and all `V`,

then both the value and the radial derivative of `Φ` at time `τ` are within `ε(τ-b)` of the model
solution anchored at `b`:

`|Φ τ - (Φ b cos(τ-b) + Φ' b sin(τ-b))| ≤ ε(τ-b)`,
`|Φ' τ - (Φ' b cos(τ-b) - Φ b sin(τ-b))| ≤ ε(τ-b)`.

The forcing bound is required only on the *half-open* interval `(b,τ]`, which is exactly what is
needed to *restart* the comparison at a dip exit, where `f` is clamped and hence nothing is known
about its second derivative.

Contents:

* `ode_compare_anchor_ray` — the scalar (`ℝ → ℝ`) anchored comparison, obtained from the half-open
  comparison `Work.Diff.C.ode_compare_halfopen` of `Diff/C/ode_compare_halfopen.lean` by shifting the
  time variable to the anchor `b`.
* `restart_compare_ray` — the geometric statement, from
  `Work.Diff.C.gpOde_grad_smoothAt` (smoothness of the gradient of `f`),
  `Work.Diff.C.gpOde_hasDerivAt_secondDeriv_along_geodesic` (the Hessian along a geodesic is the
  second derivative of the restriction), `Work.Diff.C.gpOde_inner_rgrad_mvfderiv`
  (`⟪∇f, v⟫ = df(v)`) — all in `Diff/C/gp_ode_compare.lean` — and the ray facts
  `Submission.ConjEnergy.contMDiff_GExp_smul`, `Submission.GExpRayZero.isGeodesicAt_GExp_smul_all`,
  `Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero`,
  `Submission.GlobalExp.norm_curveVelocity_GExp_smul`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.Diff.C.geoCrux

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic

/-- **Anchored scalar Sturm comparison.**

If `Φ` is differentiable on `[b,τ]` with derivative `Φ'`, `Φ'` is differentiable on `[b,τ]` with
derivative `Φ''`, and the forcing `|Φ'' + Φ|` is bounded by `ε` on the half-open interval `(b,τ]`
(so that `Φ''` may behave arbitrarily at the left endpoint `b`), then `Φ` is within `ε(τ-b)` of the
solution of `y'' + y = 0` with initial data at the anchor `b` — both for the values and for the
derivatives.

This is `Work.Diff.C.ode_compare_halfopen` applied to the shifted function `r ↦ Φ (b + r)`. -/
theorem ode_compare_anchor_ray {Φ Φ' Φ'' : ℝ → ℝ} {ε b τ : ℝ} (hε : 0 ≤ ε) (hbτ : b ≤ τ)
    (h1 : ∀ t ∈ Set.Icc b τ, HasDerivAt Φ (Φ' t) t)
    (h2 : ∀ t ∈ Set.Icc b τ, HasDerivAt Φ' (Φ'' t) t)
    (h3 : ∀ t ∈ Set.Ioc b τ, |Φ'' t + Φ t| ≤ ε) :
    |Φ τ - (Φ b * Real.cos (τ - b) + Φ' b * Real.sin (τ - b))| ≤ ε * (τ - b) ∧
    |Φ' τ - (Φ' b * Real.cos (τ - b) - Φ b * Real.sin (τ - b))| ≤ ε * (τ - b) := by
  have hτb : (0 : ℝ) ≤ τ - b := by linarith
  have h1' : ∀ t ∈ Set.Icc (0 : ℝ) (τ - b),
      HasDerivAt (fun r : ℝ => Φ (b + r)) ((fun r : ℝ => Φ' (b + r)) t) t := by
    intro t ht
    exact (h1 (b + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_const_add b t
  have h2' : ∀ t ∈ Set.Icc (0 : ℝ) (τ - b),
      HasDerivAt (fun r : ℝ => Φ' (b + r)) ((fun r : ℝ => Φ'' (b + r)) t) t := by
    intro t ht
    exact (h2 (b + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_const_add b t
  have h3' : ∀ t ∈ Set.Ioc (0 : ℝ) (τ - b),
      |(fun r : ℝ => Φ'' (b + r)) t + (fun r : ℝ => Φ (b + r)) t| ≤ ε := by
    intro t ht
    exact h3 (b + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := ode_compare_halfopen (φ := fun r : ℝ => Φ (b + r)) (φ' := fun r : ℝ => Φ' (b + r))
    (φ'' := fun r : ℝ => Φ'' (b + r)) hε hτb h1' h2' h3'
  exact ⟨by simpa [add_sub_cancel, add_zero] using h.1,
         by simpa [add_sub_cancel, add_zero] using h.2⟩

/-- **The restarted (anchored) ODE comparison along a `GExp`-ray**
(`Work.Diff.C.GeoCrux.RestartCompareProp`). -/
theorem restart_compare_ray : Work.Diff.C.GeoCrux.RestartCompareProp := by
  intro E i1 i2 i3 i4 H i5 I M i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 cov i16 hmet htor p u hu f ε b τ
    hε hb hbτ hsm hHess
  -- the ray is a unit-speed geodesic, and `f` is smooth along it
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hunorm : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  set γ : ℝ → M := fun t => GExp (cov := cov) hmet p (t • u) with hγdef
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ γ := by
    rw [hγdef]; exact Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu_ne
  have hγgeo : ∀ t : ℝ, IsGeodesicAt cov γ t := by
    intro t; rw [hγdef]
    exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hu_ne t
  have hvel_ne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0 := by
    intro t; rw [hγdef]
    exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hu_ne t
  have hspeed : ∀ t : ℝ, 0 < t →
      Inner.inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 := by
    intro t ht
    have h1 : ‖curveVelocity (I := I) γ t‖ = ‖u‖ := by
      rw [hγdef]
      exact Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet p hu_ne ht
    rw [real_inner_self_eq_norm_sq, h1, hunorm]
    norm_num
  have hsmγ : ∀ t ∈ Set.Icc b τ, CMDiffAt ∞ f (γ t) := by
    intro t ht
    rw [hγdef]
    exact hsm t ht
  have hgrada : ∀ t ∈ Set.Icc b τ, MDiffAt (T% (rgrad (I := I) f)) (γ t) := by
    intro t ht
    exact (gpOde_grad_smoothAt (I := I) (F := f) (x := γ t) (hsmγ t ht)).mdifferentiableAt
      (by simp)
  -- the restriction of `f` to the ray and its first two derivatives
  set Φ : ℝ → ℝ := fun r => f (γ r) with hΦdef
  set Φ' : ℝ → ℝ := fun r => mvfderiv I f (γ r) (curveVelocity (I := I) γ r) with hΦ'def
  set Φ'' : ℝ → ℝ := fun r =>
    rhess cov f (γ r) (curveVelocity (I := I) γ r) (curveVelocity (I := I) γ r) with hΦ''def
  have hA1 : ∀ t ∈ Set.Icc b τ, HasDerivAt Φ (Φ' t) t := by
    intro t ht
    have hfmd : MDifferentiableAt I (𝓘(ℝ, ℝ)) f (γ t) := (hsmγ t ht).mdifferentiableAt (by simp)
    have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t := (hγsm t).mdifferentiableAt (by simp)
    have hcomp := hfmd.hasMFDerivAt.comp t hγmd.hasMFDerivAt
    have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := f)
      (γ := γ) (t := t) hfmd hγmd
    have hval : Φ' t = deriv (f ∘ γ) t := by
      change mvfderiv I f (γ t) (curveVelocity (I := I) γ t) = deriv (f ∘ γ) t
      exact hkey
    rw [hval]
    exact hcomp.hasFDerivAt.differentiableAt.hasDerivAt
  have hA2 : ∀ t ∈ Set.Icc b τ, HasDerivAt Φ' (Φ'' t) t := by
    intro t ht
    have hsec : HasDerivAt (fun σ : ℝ => mvfderiv I f (γ σ) (curveVelocity (I := I) γ σ))
        (rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) t :=
      gpOde_hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet isOpen_univ (Set.mem_univ t)
        hγsm.contMDiffOn (fun r _ => hγgeo r) (hvel_ne t) (hgrada t ht)
    exact hsec
  have hA3 : ∀ t ∈ Set.Ioc b τ, |Φ'' t + Φ t| ≤ ε := by
    intro t ht
    have hgt : 0 < t := by linarith [hb, ht.1]
    have hV : Inner.inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 :=
      hspeed t hgt
    have hpt : Submission.GlobalExp.GExp (cov := cov) hmet p (t • u) = γ t := by rw [hγdef]
    have hh := hHess t ht (curveVelocity (I := I) γ t)
    rw [hpt, hV, mul_one] at hh
    simpa [hΦdef, hΦ''def] using hh
  obtain ⟨hval, hder⟩ :=
    ode_compare_anchor_ray (Φ := Φ) (Φ' := Φ') (Φ'' := Φ'') hε hbτ hA1 hA2 hA3
  -- identify the anchor state and the endpoint state with the statement's quantities
  have hΦτ : Φ τ = f (GExp (cov := cov) hmet p (τ • u)) := by
    change f (γ τ) = f (GExp (cov := cov) hmet p (τ • u))
    rw [hγdef]
  have hΦb : Φ b = f (GExp (cov := cov) hmet p (b • u)) := by
    change f (γ b) = f (GExp (cov := cov) hmet p (b • u))
    rw [hγdef]
  have hΦ'b : Φ' b = Inner.inner ℝ (rgrad (I := I) f (GExp (cov := cov) hmet p (b • u)))
      (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) b) := by
    change mvfderiv I f (γ b) (curveVelocity (I := I) γ b)
      = Inner.inner ℝ (rgrad (I := I) f (GExp (cov := cov) hmet p (b • u)))
        (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) b)
    exact (gpOde_inner_rgrad_mvfderiv (I := I) f (GExp (cov := cov) hmet p (b • u))
      (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) b)).symm
  have hΦ'τ : Φ' τ = Inner.inner ℝ (rgrad (I := I) f (GExp (cov := cov) hmet p (τ • u)))
      (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) τ) := by
    change mvfderiv I f (γ τ) (curveVelocity (I := I) γ τ)
      = Inner.inner ℝ (rgrad (I := I) f (GExp (cov := cov) hmet p (τ • u)))
        (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) τ)
    exact (gpOde_inner_rgrad_mvfderiv (I := I) f (GExp (cov := cov) hmet p (τ • u))
      (curveVelocity (fun r : ℝ => GExp (cov := cov) hmet p (r • u)) τ)).symm
  constructor
  · rw [hΦτ, hΦb, hΦ'b] at hval
    exact hval
  · rw [hΦ'τ, hΦb, hΦ'b] at hder
    exact hder

end Work.Diff.C.geoCrux
