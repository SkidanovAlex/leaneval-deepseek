/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTDefs` — the vocabulary of the `∂_θ²`-domination

The target `Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ttDom` dominates the second angular
derivative of the log-mollified datum `Φ = zmoll G δ ε` by the doubly-odd-mollified second
angular derivative of `G`.  The route goes through the *fold* of the doubly odd extension

  `thMoll G ε w θ = ∫_{Iθ} km ε θ s · G w s ds`,

`km ε θ s = sKer ε (θ-s) - sKer ε (θ+s) - sKer ε (θ+s-π)` being the signed three-image kernel
(of. `thMoll_abs_le`), and then through two integrations by parts in `s` which move the
`s`-derivatives of `km` onto the datum (`∂_s² km ε θ · = kmθθ ε θ ·` below, and the boundary
terms at `s = 0, π/2` vanish because `G w 0 = G w (π/2) = 0` and `km ε θ 0 = km ε θ (π/2) = 0`).

This module fixes the notation and proves the elementary calculus facts about the kernels:

* `sKerd2 ε = (sKerd ε)' = (sKer ε)''`, continuous with compact support (hence bounded);
* `km`, `kmθ = ∂_θ km`, `kms = ∂_s km`, `kmθθ = ∂_θ kmθ = ∂_s kms` (and `∂_θ² km = ∂_s² km`);
* the pointwise bound `|km ε θ s| ≤ KJ ε θ s` (the positivity of `sKer`).

Everything here is elementary (`HasDerivAt` composition, compact support bounds).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false

open Work.FTS.EllSol.PkgK5.K5c (sKer Qext)

/-- `sKer ε` has compact support (inside `[-ε, ε]`). -/
theorem hasCompactSupport_sKer {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `sKerd ε = (sKer ε)'` is smooth. -/
theorem contDiff_sKerd (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ (n + 1) (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε
  simpa only [Work.FTS.EllSol.EllPkgAux.sKerd] using h.deriv'

/-- The second derivative of the mollifying kernel, `sKerd2 ε = (sKer ε)''`. -/
def sKerd2 (ε : ℝ) : ℝ → ℝ := deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε)

theorem sKerd2_def (ε : ℝ) : sKerd2 ε = deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) := rfl

theorem contDiff_sKerd2 (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (sKerd2 ε) := by
  have h : ContDiff ℝ (n + 1) (Work.FTS.EllSol.EllPkgAux.sKerd ε) := contDiff_sKerd ε
  simpa only [sKerd2] using h.deriv'

/-- `sKerd ε` has compact support. -/
theorem hasCompactSupport_sKerd {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
  (hasCompactSupport_sKer hε).deriv

/-- `sKerd2 ε` has compact support. -/
theorem hasCompactSupport_sKerd2 {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKerd2 ε) :=
  (hasCompactSupport_sKerd hε).deriv

theorem sKerd_bdd' {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M := by
  have hc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
    (contDiff_sKerd ε (n := 0)).continuous
  have hcs : HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) := hasCompactSupport_sKerd hε
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- A bound for `sKerd2 ε`. -/
theorem sKerd2_bdd {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |sKerd2 ε x| ≤ M := by
  have hc : Continuous (sKerd2 ε) := (contDiff_sKerd2 ε (n := 0)).continuous
  have hcs : HasCompactSupport (sKerd2 ε) := hasCompactSupport_sKerd2 hε
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-! ## The signed three-image kernel and its derivatives -/

/-- The signed three-image kernel of the fold of the doubly odd extension. -/
def km (ε θ s : ℝ) : ℝ :=
  sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)

/-- `∂_θ` of `km`. -/
def kmθ (ε θ s : ℝ) : ℝ :=
  Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
    - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)

/-- `∂_s` of `km`. -/
def kms (ε θ s : ℝ) : ℝ :=
  - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
    - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)

/-- `∂_θ² km = ∂_s² km` (and `∂_θ kmθ = ∂_s kms`). -/
def kmθθ (ε θ s : ℝ) : ℝ :=
  sKerd2 ε (θ - s) - sKerd2 ε (θ + s) - sKerd2 ε (θ + s - Real.pi)

/-! ## `HasDerivAt` in `θ` -/

theorem hasDerivAt_km_theta (ε θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => km ε θ' s) (kmθ ε θ s) θ := by
  have h1 : HasDerivAt (fun x : ℝ => sKer ε (x - s))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ - s)) (θ - s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).sub_const s)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => sKer ε (x + s))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s)) (θ + s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).add_const s)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => sKer ε (x + s - Real.pi))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp θ (((hasDerivAt_id θ).add_const s).sub_const Real.pi)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_kmθ_theta (ε θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => kmθ ε θ' s) (kmθθ ε θ s) θ := by
  have h1 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x - s))
      (sKerd2 ε (θ - s)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ - s)) (θ - s) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).sub_const s)
    simpa [Function.comp_def, sKerd2] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x + s))
      (sKerd2 ε (θ + s)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s)) (θ + s) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).add_const s)
    simpa [Function.comp_def, sKerd2] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x + s - Real.pi))
      (sKerd2 ε (θ + s - Real.pi)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp θ (((hasDerivAt_id θ).add_const s).sub_const Real.pi)
    simpa [Function.comp_def, sKerd2] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_km_s (ε θ s : ℝ) :
    HasDerivAt (fun x : ℝ => km ε θ x) (kms ε θ s) s := by
  have h1 : HasDerivAt (fun x : ℝ => sKer ε (θ - x))
      (-(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ - s)) (θ - s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp s ((hasDerivAt_id s).const_sub θ)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => sKer ε (θ + x))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s)) (θ + s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp s ((hasDerivAt_id s).const_add θ)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd, add_comm] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => sKer ε (θ + x - Real.pi))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp s (((hasDerivAt_id s).const_add θ).sub_const Real.pi)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd, add_comm, add_assoc] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_kms_s (ε θ s : ℝ) :
    HasDerivAt (fun x : ℝ => kms ε θ x) (kmθθ ε θ s) s := by
  have h1 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)))
      (sKerd2 ε (θ - s)) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x))
        (-(sKerd2 ε (θ - s))) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ - s)) (θ - s) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
      have hcomp := hderiv.comp s ((hasDerivAt_id s).const_sub θ)
      simpa [Function.comp_def, sKerd2] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)) := rfl
    rw [hfun] at hn
    simpa using hn
  have h2 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)))
      (-(sKerd2 ε (θ + s))) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x))
        (sKerd2 ε (θ + s)) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s)) (θ + s) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
      have hcomp := hderiv.comp s ((hasDerivAt_id s).const_add θ)
      simpa [Function.comp_def, sKerd2, add_comm] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)) := rfl
    rw [hfun] at hn
    simpa using hn
  have h3 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)))
      (-(sKerd2 ε (θ + s - Real.pi))) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi))
        (sKerd2 ε (θ + s - Real.pi)) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) _).hasDerivAt
      have hcomp := hderiv.comp s (((hasDerivAt_id s).const_add θ).sub_const Real.pi)
      simpa [Function.comp_def, sKerd2, add_comm, add_assoc] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)) := rfl
    rw [hfun] at hn
    simpa using hn
  exact (h1.add h2).add h3

/-- The second derivative of `km ε θ ·` at `s` is `kmθθ ε θ s`. -/
theorem deriv_deriv_km_s (ε θ s : ℝ) :
    deriv (deriv (fun x : ℝ => km ε θ x)) s = kmθθ ε θ s := by
  have h1 : deriv (fun x : ℝ => km ε θ x) = fun x : ℝ => kms ε θ x :=
    funext fun x => (hasDerivAt_km_s ε θ x).deriv
  rw [h1]
  exact (hasDerivAt_kms_s ε θ s).deriv

/-- The second derivative of `km ε · s` at `θ` is `kmθθ ε θ s`. -/
theorem deriv_deriv_km_theta (ε θ s : ℝ) :
    deriv (deriv (fun x : ℝ => km ε x s)) θ = kmθθ ε θ s := by
  have h1 : deriv (fun x : ℝ => km ε x s) = fun x : ℝ => kmθ ε x s :=
    funext fun x => (hasDerivAt_km_theta ε x s).deriv
  rw [h1]
  exact (hasDerivAt_kmθ_theta ε θ s).deriv

/-! ## Continuity -/

theorem continuous_sKer (ε : ℝ) : Continuous (sKer ε) :=
  (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 0)).continuous

theorem continuous_sKerd (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
  (contDiff_sKerd ε (n := 0)).continuous

theorem continuous_sKerd2 (ε : ℝ) : Continuous (sKerd2 ε) :=
  (contDiff_sKerd2 ε (n := 0)).continuous

theorem continuous_km (ε θ : ℝ) : Continuous (fun s : ℝ => km ε θ s) := by
  have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
    (continuous_sKer ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
    (continuous_sKer ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
    (continuous_sKer ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_kmθ (ε θ : ℝ) : Continuous (fun s : ℝ => kmθ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)) :=
    (continuous_sKerd ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) :=
    (continuous_sKerd ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) :=
    (continuous_sKerd ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_kms (ε θ : ℝ) : Continuous (fun s : ℝ => kms ε θ s) := by
  have h1 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))) :=
    ((continuous_sKerd ε).comp (continuous_const.sub continuous_id)).neg
  have h2 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s))) :=
    ((continuous_sKerd ε).comp (continuous_const.add continuous_id)).neg
  have h3 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))) :=
    ((continuous_sKerd ε).comp ((continuous_const.add continuous_id).sub continuous_const)).neg
  have h := (h1.add h2).add h3
  have hfun : ((fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)))
      + (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)))
      + (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))))
      = fun s : ℝ => kms ε θ s := by
    funext s
    simp only [Pi.add_apply, kms]
    ring
  rwa [hfun] at h

theorem continuous_kmθθ (ε θ : ℝ) : Continuous (fun s : ℝ => kmθθ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => sKerd2 ε (θ - s)) :=
    (continuous_sKerd2 ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => sKerd2 ε (θ + s)) :=
    (continuous_sKerd2 ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => sKerd2 ε (θ + s - Real.pi)) :=
    (continuous_sKerd2 ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_km_theta (ε s : ℝ) : Continuous (fun θ : ℝ => km ε θ s) := by
  have h1 : Continuous (fun θ : ℝ => sKer ε (θ - s)) :=
    (continuous_sKer ε).comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun θ : ℝ => sKer ε (θ + s)) :=
    (continuous_sKer ε).comp (continuous_id.add continuous_const)
  have h3 : Continuous (fun θ : ℝ => sKer ε (θ + s - Real.pi)) :=
    (continuous_sKer ε).comp ((continuous_id.add continuous_const).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_kmθ_theta (ε s : ℝ) : Continuous (fun θ : ℝ => kmθ ε θ s) := by
  have h1 : Continuous (fun θ : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)) :=
    (continuous_sKerd ε).comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun θ : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) :=
    (continuous_sKerd ε).comp (continuous_id.add continuous_const)
  have h3 : Continuous (fun θ : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) :=
    (continuous_sKerd ε).comp ((continuous_id.add continuous_const).sub continuous_const)
  exact (h1.sub h2).sub h3

/-! ## The endpoint values of the folded kernel -/

theorem km_zero_left {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    km ε θ 0 = - sKer ε (θ - Real.pi) := by
  simp only [km, sub_zero, add_zero]
  ring

theorem km_zero_left' {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) : km ε θ 0 = 0 := by
  rw [km_zero_left hε0 hε1]
  refine neg_eq_zero.mpr (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 ?_)
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  rw [show θ - Real.pi = -(Real.pi - θ) by ring, abs_neg, abs_of_nonneg (by linarith [h2])]
  linarith [Real.pi_gt_three]

theorem km_zero_right {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) : km ε θ (Real.pi / 2) = 0 := by
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have hright : sKer ε (θ + Real.pi / 2) = 0 := by
    refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 ?_
    rw [abs_of_nonneg (by linarith [Real.pi_pos])]
    linarith [Real.pi_gt_three, hε1, h1]
  have hthird : θ + Real.pi / 2 - Real.pi = θ - Real.pi / 2 := by ring
  simp only [km]
  rw [hthird, hright]
  ring

/-! ## Bounds -/

theorem kmθ_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kmθ ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd_bdd' hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kmθ]
  calc |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)|
      ≤ |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)|
          + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|)
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := by
        linarith [abs_sub (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)),
          abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))]
    _ ≤ M + M + M := by linarith [abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ = 3 * M := by ring

theorem kms_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kms ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd_bdd' hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kms]
  calc |-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)|
      ≤ |-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
          - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)|
          + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|)
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := by
        have h := abs_sub (-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s))
        rw [abs_neg] at h
        linarith [h, h1, h2, h3, abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ ≤ M + M + M := by linarith [abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ = 3 * M := by ring

theorem kmθθ_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kmθθ ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd2_bdd hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kmθθ]
  calc |sKerd2 ε (θ - s) - sKerd2 ε (θ + s) - sKerd2 ε (θ + s - Real.pi)|
      ≤ |sKerd2 ε (θ - s) - sKerd2 ε (θ + s)| + |sKerd2 ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|sKerd2 ε (θ - s)| + |sKerd2 ε (θ + s)|) + |sKerd2 ε (θ + s - Real.pi)| := by
        linarith [abs_sub (sKerd2 ε (θ - s)) (sKerd2 ε (θ + s)),
          abs_nonneg (sKerd2 ε (θ + s - Real.pi))]
    _ ≤ M + M + M := by linarith [abs_nonneg (sKerd2 ε (θ - s))]
    _ = 3 * M := by ring

/-- The pointwise domination of the signed kernel by the (nonnegative) three-image kernel. -/
theorem abs_km_le_KJ {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    |km ε θ s| ≤ Work.FTS.EllSol.EllPkgAux.KJ ε θ s := by
  have h1 : 0 ≤ sKer ε (θ - s) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h2 : 0 ≤ sKer ε (θ + s) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h3 : 0 ≤ sKer ε (θ + s - Real.pi) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h4 : |sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)|
      ≤ sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := by
    rw [abs_le]
    constructor <;> linarith
  simpa only [km, Work.FTS.EllSol.EllPkgAux.KJ] using h4

end Work.FTS.EllSol.EllPkgAux.MollDom
