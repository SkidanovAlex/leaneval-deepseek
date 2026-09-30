import Submission.Work.RiemLib.CutStep3
import Submission.Work.RiemLib.GExpTwoSided
import Submission.Work.RiemLib.GExpRayIdent
import Submission.Work.RiemLib.CutTime
import Submission.Work.RiemLib.HopfRinow2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The broken minimising geodesic loop produced by the cut-point step

The cut-point step produces **two distinct minimising vectors `u ≠ v` of norm `m` with the same
image** under the exponential map of `p`.  This file packages that data as the classical object the
rest of Klingenberg's argument consumes: a **broken minimising geodesic loop** at `p` of length
`2m`:

* a minimising geodesic `σ : [0,m] → M` from `p` to `q := GExp p (m • ξ)`, and
* a minimising geodesic `τ : [0,m] → M` from `q` back to `p`,

both of length `m` and both parametrised by arclength (`d(p, σ t) = t`, `d(p, τ t) = m - t`), meeting
at the *cut point* `q` in a possibly non-straight corner.  The statement is intrinsic (no velocity
transport between tangent spaces is needed), which is what makes it usable: flushness and the
shortening argument both work with the curve, not with the velocities.

## Contents

* `isGeodesicAt_GExp_reverseRay` — the reversed ray `t ↦ GExp p ((m - t) • η)` is a geodesic at
  every `t ∈ (0,m)` (affine reparametrisation of the ray of `η` by `s ↦ -s + m`);
* `exists_broken_minimising_loop` — the packaged broken minimising loop.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpTwoSided
open Submission.GExpRayIdent
open Submission.CutTime
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.KlingenbergLoop

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The reversed ray is a geodesic.**  For `η ≠ 0` the curve `t ↦ GExp p ((m - t) • η)` is a
geodesic at every `t ∈ (0, m)`: it is the affine reparametrisation `s ↦ -s + m` of the ray of `η`
(whose velocity is reversed but nonzero). -/
theorem isGeodesicAt_GExp_reverseRay (hmet : IsMetricCompatible cov) (p : M)
    {η : TangentSpace I p} (hη : η ≠ 0) {m t : ℝ} (ht0 : 0 < t) (htm : t < m) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) t := by
  set ρ : ℝ → M := fun u : ℝ => GExp (cov := cov) hmet p (u • η) with hρdef
  have hsm : ContMDiffOn 𝓘(ℝ) I ∞ ρ (Ioo (0 : ℝ) m) :=
    contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hη m
  have hgeo : ∀ y ∈ Ioo (0 : ℝ) m, IsGeodesicAt cov ρ y :=
    fun y hy => isGeodesicAt_GExp_smul_of_ne (cov := cov) hmet p hη (ne_of_gt hy.1)
  have hr : (-1 : ℝ) * t + m ∈ Ioo (0 : ℝ) m := by
    rw [neg_one_mul]
    exact ⟨by linarith, by linarith⟩
  have h := isGeodesicAt_comp_affine (cov := cov) (σ := ρ) (c := 0) (d := m) (a := (-1 : ℝ))
    (b := m) (by norm_num) hsm hgeo (r := t) hr
  refine (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) ?_).mp h
  filter_upwards with s
  rw [hρdef]
  congr 1
  ring

/-- **The broken minimising geodesic loop of the cut-point step.**  Let `u ≠ v` be two distinct
tangent vectors at `p` of the same norm `m > 0` with `GExp p u = GExp p v`, both rays **minimising**
at time `m`.  Then there are unit vectors `ξ ≠ η` and two minimising geodesics `σ`, `τ` of length
`m` (`σ` from `p` to `q := GExp p (m • ξ)`, `τ` from `q` back to `p`) such that

* `σ 0 = p`, `τ 0 = q`, `τ m = p`, and the two rays meet: `σ m = τ 0`;
* `σ` and `τ` are geodesics on `(0, m)`;
* `d(p, σ t) = t` and `d(p, τ t) = m - t` for `t ∈ [0, m]`.

This is the "broken closed geodesic loop of length `2m`" of Klingenberg's lemma; if the corner at
`q` is straight the loop is a genuine closed geodesic, and if not it can be shortened, so it yields
a closed geodesic of length `≤ 2m` (flushness). -/
theorem exists_broken_minimising_loop (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u v : TangentSpace I p} {m : ℝ} (hm : 0 < m)
    (hu : ‖u‖ = m) (hv : ‖v‖ = m) (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v)
    (hminu : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m) :
    ∃ ξ η : TangentSpace I p, ‖ξ‖ = 1 ∧ ‖η‖ = 1 ∧ ξ ≠ η ∧
      GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η) ∧
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 = p ∧
      (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) 0
        = GExp (cov := cov) hmet p (m • ξ) ∧
      (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) m = p ∧
      (∀ t ∈ Ioo (0 : ℝ) m, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ∧
      (∀ t ∈ Ioo (0 : ℝ) m,
        IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) m,
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t) ∧
      (∀ t ∈ Icc (0 : ℝ) m,
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p ((m - t) • η))
          = ENNReal.ofReal (m - t)) := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hune : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu; exact absurd hu.symm hmne
  have hvne : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hv; exact absurd hv.symm hmne
  set ξ : TangentSpace I p := (1 / m) • u with hξdef
  set η : TangentSpace I p := (1 / m) • v with hηdef
  have hξne : ξ ≠ 0 := smul_ne_zero (by positivity) hune
  have hηne : η ≠ 0 := smul_ne_zero (by positivity) hvne
  have hξu : ‖ξ‖ = 1 := by
    rw [hξdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / m), hu,
      one_div, inv_mul_cancel₀ hmne]
  have hηv : ‖η‖ = 1 := by
    rw [hηdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / m), hv,
      one_div, inv_mul_cancel₀ hmne]
  have hmu : m • ξ = u := by rw [hξdef, smul_smul, one_div, mul_inv_cancel₀ hmne, one_smul]
  have hmv : m • η = v := by rw [hηdef, smul_smul, one_div, mul_inv_cancel₀ hmne, one_smul]
  have hξη : ξ ≠ η := by
    intro hcon; exact huv (by rw [← hmu, ← hmv, hcon])
  have hG' : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η) := by
    rw [hmu, hmv]; exact hG
  have hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m := by
    rw [hmu]; exact hminu
  have hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal m := by
    rw [hmv, ← hG]; exact hminu
  refine ⟨ξ, η, hξu, hηv, hξη, hG', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show GExp (cov := cov) hmet p ((0:ℝ) • ξ) = p
    rw [zero_smul, GExp_zero]
  · show GExp (cov := cov) hmet p ((m - 0) • η) = GExp (cov := cov) hmet p (m • ξ)
    rw [sub_zero]
    exact hG'.symm
  · show GExp (cov := cov) hmet p ((m - m) • η) = p
    rw [sub_self, zero_smul, GExp_zero]
  · intro t ht
    exact isGeodesicAt_GExp_smul_of_ne (cov := cov) hmet p hξne (ne_of_gt ht.1)
  · intro t ht
    exact isGeodesicAt_GExp_reverseRay (cov := cov) hmet p hηne ht.1 ht.2
  · intro t ht
    exact edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hξu ht.1 ht.2 hminξ
  · intro t ht
    have h1 : m - t ∈ Icc (0 : ℝ) m := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hηv h1.1 h1.2 hminη

end

end Submission.KlingenbergLoop
