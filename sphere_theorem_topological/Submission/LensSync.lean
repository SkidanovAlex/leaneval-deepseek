import Submission.GSField
import Submission.GExpRay2
import Submission.CutWitness

/-!
# The lens "sync" lemma: a minimising witness pair propagates along its rays

Let `p` be a point of a complete Riemannian manifold, `ξ ≠ η` two **unit** tangent vectors at `p`,
and suppose that for some `ℓ > 0` the two rays meet at parameter `ℓ`:

`GExp p (ℓ • ξ) = GExp p (ℓ • η)`,

with **both rays minimising at `ℓ`** (`d(p, GExp p (ℓ • ξ)) = ℓ`).  Then the two rays are *in sync*:
for every `t ≥ ℓ` at which the ray of `ξ` is still minimising,

`GExp p (t • ξ) = GExp p (t • η)`.

This is the key structural fact about the **geodesic lens** formed by two minimising geodesics from
`p` of the same length: once the lens closes at length `ℓ`, it stays closed.

## Proof

The point is the *no-corner lemma* `GSField.eq_GExp_of_minimising_broken` applied to the broken path
`p → x → y` where `x = GExp p (ℓ • η) = GExp p (ℓ • ξ)` and `y = GExp p (t • ξ)`:

* `d(p, x) = ℓ` (hypothesis),
* `d(x, y) = t - ℓ`: the upper bound is the **ray bound** `GExpRay2.edist_GExp_smul_le_mul_norm`
  (both `x` and `y` lie on the ray of `ξ`), the lower bound the triangle inequality together with
  `d(p,y) = t`,
* `d(p, y) = t` (hypothesis).

The no-corner lemma then identifies `y` with the point of the **η**-ray at time `t`.

## Why this matters

The cut-point step of Klingenberg's estimate produces a sequence of witness pairs `(aₙ, bₙ)` with
**equal** norms `ℓₙ ↓ inj(p)` and both members **minimising**.  The sync lemma says that the whole
family `{(t ξₙ, t ηₙ) : t ≥ ℓₙ}` consists of witness pairs; in particular the set of "witness
lengths" is *upward closed from every minimising witness length*.  What is left for the cut-point
step is the exclusion of the degenerate case (`ξ = η`), i.e. **Klingenberg's lens lemma**: for
`sec ≤ K` there is no closed minimising lens of length `< π/√K`.  See `Submission/Roadmap.lean`
§75.
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
open Submission.GExpRay
open Submission.GExpRay2
open Submission.GSField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.LensSync

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The distance between two points of a minimising lens.**  With `x = GExp p (ℓ • ξ)`,
`y = GExp p (t • ξ)` for `0 ≤ ℓ ≤ t` and `‖ξ‖ = 1`, if the ray of `ξ` is minimising at both `ℓ`
and `t` then `d(x,y) = t - ℓ`. -/
theorem edist_eq_sub_of_minimising_ray (hmet : IsMetricCompatible cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (hℓt : ℓ ≤ t)
    (hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • ξ)) = ENNReal.ofReal ℓ)
    (hmint : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet p (ℓ • ξ)) (GExp (cov := cov) hmet p (t • ξ))
      = ENNReal.ofReal (t - ℓ) := by
  have htnn : 0 ≤ t := le_trans hℓ hℓt
  have hsub : 0 ≤ t - ℓ := sub_nonneg.mpr hℓt
  -- the ray bound
  have hle : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (ℓ • ξ))
      (GExp (cov := cov) hmet p (t • ξ)) ≤ ENNReal.ofReal ((t - ℓ) * ‖ξ‖) :=
    edist_GExp_smul_le_mul_norm (cov := cov) hmet p hℓ hℓt
  rw [hξ, mul_one] at hle
  -- the triangle inequality
  have htri := Manifold.riemannianEDist_triangle (I := I)
    (x := p) (y := GExp (cov := cov) hmet p (ℓ • ξ)) (z := GExp (cov := cov) hmet p (t • ξ))
  rw [hmint, hminℓ] at htri
  have hsplit : ENNReal.ofReal t = ENNReal.ofReal ℓ + ENNReal.ofReal (t - ℓ) := by
    rw [← ENNReal.ofReal_add hℓ hsub]; ring_nf
  rw [hsplit] at htri
  have hge : ENNReal.ofReal (t - ℓ) ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet p (ℓ • ξ))
      (GExp (cov := cov) hmet p (t • ξ)) :=
    (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri
  exact le_antisymm hle hge

/-- **The sync lemma.**  Let `ξ ≠ η` be unit tangent vectors at `p` and `ℓ > 0` with
`GExp p (ℓ • ξ) = GExp p (ℓ • η)`, both rays minimising at `ℓ`.  Then for every `t ≥ ℓ` at which the
ray of `ξ` is minimising, `GExp p (t • ξ) = GExp p (t • η)`. -/
theorem eq_GExp_of_minimising_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hne : ξ ≠ η)
    {ℓ t : ℝ} (hℓ : 0 < ℓ) (hℓt : ℓ ≤ t)
    (heq : GExp (cov := cov) hmet p (ℓ • ξ) = GExp (cov := cov) hmet p (ℓ • η))
    (hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • ξ)) = ENNReal.ofReal ℓ)
    (hmint : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t) :
    GExp (cov := cov) hmet p (t • ξ) = GExp (cov := cov) hmet p (t • η) := by
  rcases eq_or_lt_of_le hℓt with h_eq | h_lt
  · rw [← h_eq]; exact heq
  have hdist := edist_eq_sub_of_minimising_ray (cov := cov) hmet hξ hℓ.le hℓt hminℓ hmint
  have hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • η)) = ENNReal.ofReal ℓ := by
    rw [← heq]; exact hminℓ
  have hzp : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (ℓ • η))
      (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal (t - ℓ) := by
    rw [← heq]; exact hdist
  exact (Submission.GSField.eq_GExp_of_minimising_broken (cov := cov) hmet htor
    (x₀ := p) (p := GExp (cov := cov) hmet p (t • ξ)) (w := η) (r := t) (t := ℓ)
    hη (le_trans hℓ.le hℓt) hℓ h_lt hminη hzp hmint)

/-- **The sync lemma, in the form of a minimising witness pair.**  Let `u ≠ v` be two tangent
vectors at `p` of the **same** norm `ℓ > 0` with `GExp p u = GExp p v`, both rays minimising at `ℓ`.
Then for every `t ≥ ℓ` at which the ray of `u` is still minimising,

`GExp p ((t/ℓ) • u) = GExp p ((t/ℓ) • v)`.

(Recall that `(t/ℓ) • u` is the point of the ray of `u` at time `t`, since `‖u‖ = ℓ`.) -/
theorem eq_GExp_smul_of_witness_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {u v : TangentSpace I p} {ℓ t : ℝ} (hℓ : 0 < ℓ)
    (hnu : ‖u‖ = ℓ) (hnv : ‖v‖ = ℓ) (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v)
    (hminu : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ℓ)
    (ht : ℓ ≤ t)
    (hminut : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p ((t / ℓ) • u))
      = ENNReal.ofReal t) :
    GExp (cov := cov) hmet p ((t / ℓ) • u) = GExp (cov := cov) hmet p ((t / ℓ) • v) := by
  have hune : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnu; exact absurd hnu.symm (ne_of_gt hℓ)
  set ξ : TangentSpace I p := unitOf u hune with hξdef
  set η : TangentSpace I p := unitOf v (by
    intro h0; rw [h0, norm_zero] at hnv; exact absurd hnv.symm (ne_of_gt hℓ)) with hηdef
  have hξ : ‖ξ‖ = 1 := unitOf_norm u hune
  have hη : ‖η‖ = 1 := unitOf_norm v _
  have hscℓ : ℓ • ξ = u := by
    rw [hξdef, unitOf, smul_smul, hnu, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
  have hscℓ' : ℓ • η = v := by
    rw [hηdef, unitOf, smul_smul, hnv, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
  have hξne : ξ ≠ η := by
    intro hcon
    exact huv (by rw [← hscℓ, ← hscℓ', hcon])
  -- the identification of the ray parameters
  have htu : t • ξ = (t / ℓ) • u := by
    simp only [hξdef, unitOf, smul_smul, div_eq_mul_inv, hnu]
  have htv : t • η = (t / ℓ) • v := by
    simp only [hηdef, unitOf, smul_smul, div_eq_mul_inv, hnv]
  have heq : GExp (cov := cov) hmet p (ℓ • ξ) = GExp (cov := cov) hmet p (ℓ • η) := by
    rw [hscℓ, hscℓ']; exact hG
  have hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • ξ))
      = ENNReal.ofReal ℓ := by rw [hscℓ]; exact hminu
  have hmint : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
      = ENNReal.ofReal t := by rw [htu]; exact hminut
  have := eq_GExp_of_minimising_pair (cov := cov) hmet htor hξ hη hξne hℓ ht heq hminℓ hmint
  rwa [htu, htv] at this

end

end Submission.LensSync
