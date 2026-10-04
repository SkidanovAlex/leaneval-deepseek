import Submission.HopfRinow2
import Submission.Klingenberg

set_option backward.isDefEq.respectTransparency.types false

/-!
# The injectivity radius at a point

This file collects the *structural* facts about the exponential map that are used in Klingenberg's
estimate for the injectivity radius (`Submission/Roadmap.lean` §67–§68).

Everything is phrased through the predicate `InjAtLeast hmet x r` ("the exponential map at `x` is
injective on the ball of radius `r` in the tangent space") — the same formulation that
`Submission.Klingenberg` uses, so that no supremum has to be defined.

## Contents

* `InjAtLeast`, `InjAllAtLeast`: the pointwise and the uniform-in-the-base-point predicates, and
  monotonicity in `r`;
* `edist_GExp_eq_norm_of_injAtLeast`: *below the injectivity radius, the exponentially parametrised
  rays are minimising*: `d(x, GExp x u) = ‖u‖` for `‖u‖ < r`;
* `exists_unique_GExp_of_injAtLeast`: **every point at distance `< r` from `x` is the exponential
  of a unique vector of norm exactly that distance** (the "normal ball" statement);
* `two_mul_le_of_injAllAtLeast_of_geodCurve_loop`: **a geodesic loop bounds the injectivity radius**:
  if the unit-speed geodesic segment `[0,T]` from `x` returns to `x`, then there is no `r` with
  `InjAllAtLeast r` and `2r > T`.  This is the "`inj(p) ≤ ½ ℓ_M(p)`" half of Klingenberg's
  structural lemma (Cheeger–Ebin, Lemma 5.6).

The proof of the last item is the classical one, arranged so that *both* tangent vectors live at the
**midpoint** of the loop: the two halves of the loop are two geodesics from the midpoint back to
`x`, of length `T/2`, with opposite initial velocities; injectivity of the exponential map on the
ball of radius `r > T/2` would force the two (nonzero, opposite) velocities to be equal, which
forces the velocity itself to vanish — contradicting unit speed.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.InjRadius

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- `InjAtLeast hmet x r` : **the exponential map at `x` is injective on the ball of radius `r`** in
the tangent space at `x`.  This is the "the injectivity radius at `x` is at least `r`" predicate. -/
def InjAtLeast (hmet : IsMetricCompatible cov) (x : M) (r : ℝ) : Prop :=
  ∀ u v : TangentSpace I x, ‖u‖ < r → ‖v‖ < r →
    GExp (cov := cov) hmet x u = GExp (cov := cov) hmet x v → u = v

/-- `InjAllAtLeast hmet r`: the exponential map is injective on the ball of radius `r` **at every
point**.  This is the predicate "the injectivity radius of the manifold is at least `r`". -/
def InjAllAtLeast (hmet : IsMetricCompatible cov) (r : ℝ) : Prop :=
  ∀ p : M, InjAtLeast hmet p r

/-- `InjAtLeast` is monotone in the radius. -/
theorem injAtLeast_mono (hmet : IsMetricCompatible cov) {x : M} {r r' : ℝ}
    (h : InjAtLeast hmet x r) (hr : r' ≤ r) : InjAtLeast hmet x r' :=
  fun u v hu hv huv => h u v (lt_of_lt_of_le hu hr) (lt_of_lt_of_le hv hr) huv

/-- The uniform predicate implies the pointwise one. -/
theorem injAtLeast_of_injAllAtLeast (hmet : IsMetricCompatible cov) {r : ℝ}
    (h : InjAllAtLeast hmet r) (x : M) : InjAtLeast hmet x r := h x

/-- **Two distinct minimising geodesics give a cut point.**  If `u ≠ v` are two tangent vectors at
`x` of the *same* norm and with the same image under the exponential map, then the exponential map
is **not** injective on the ball of radius `r` for every `r > ‖u‖`.

This is the form in which the two minimising geodesics of Klingenberg's lemma (at the nearest cut
point) are used in the injectivity radius estimate. -/
theorem not_injAtLeast_of_two_of_norm_eq (hmet : IsMetricCompatible cov) {x : M}
    {u v : TangentSpace I x} (huv : u ≠ v) (hnorm : ‖u‖ = ‖v‖)
    (hG : GExp (cov := cov) hmet x u = GExp (cov := cov) hmet x v)
    {r : ℝ} (hr : ‖u‖ < r) : ¬ InjAtLeast hmet x r :=
  fun h => huv (h u v hr (by rw [← hnorm]; exact hr) hG)

/-- **The injectivity radius is attained.**  If the exponential map at `x` is injective on some ball
and fails to be injective on some other ball, then there is a largest radius `m` at which it is
injective, and it fails at every larger radius.

This is the bridge from "injectivity fails somewhere" (in the application: at radius `π/2`, where
Grove–Shiohama needs it) to the two hypotheses `InjAtLeast hmet x m` /
`∀ r > m, ¬ InjAtLeast hmet x r` of the cut-point step (`CutStep`/`CutStep2`/`CutStep3`), which
therefore never have to be *constructed* by hand. -/
theorem exists_injAtLeast_max (hmet : IsMetricCompatible cov) {x : M}
    (hne : ∃ r : ℝ, InjAtLeast hmet x r) (hbd : ∃ r₀ : ℝ, ¬ InjAtLeast hmet x r₀) :
    ∃ m : ℝ, InjAtLeast hmet x m ∧ ∀ r : ℝ, m < r → ¬ InjAtLeast hmet x r := by
  classical
  obtain ⟨r₁, hr₁⟩ := hne
  obtain ⟨r₀, hr₀⟩ := hbd
  set S : Set ℝ := {r : ℝ | InjAtLeast hmet x r} with hSdef
  have hSne : S.Nonempty := ⟨r₁, hr₁⟩
  have hSbd : BddAbove S := by
    refine ⟨max r₀ r₁, fun r hr => ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    exact hr₀ (injAtLeast_mono hmet hr (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hcon)))
  refine ⟨sSup S, ?_, ?_⟩
  · intro u v hu hv huv
    have hmem : max ‖u‖ ‖v‖ < sSup S := max_lt hu hv
    obtain ⟨r, hrS, hrlt⟩ := exists_lt_of_lt_csSup hSne hmem
    exact hrS u v (lt_of_le_of_lt (le_max_left _ _) hrlt)
      (lt_of_le_of_lt (le_max_right _ _) hrlt) huv
  · intro r hr hrS
    have hle : r ≤ sSup S := le_csSup hSbd hrS
    exact absurd hle (not_le.mpr hr)

/-- **Below the injectivity radius the exponential rays are minimising.** -/
theorem edist_GExp_eq_norm_of_injAtLeast [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {x : M} {r : ℝ}
    (h : InjAtLeast hmet x r) {u : TangentSpace I x} (hu : ‖u‖ < r) (hune : u ≠ 0) :
    Manifold.riemannianEDist I x (GExp (cov := cov) hmet x u) = ENNReal.ofReal ‖u‖ :=
  Submission.Klingenberg.edist_GExp_eq_norm_of_injOn (cov := cov) hmet htor h hu hune

/-- **The normal ball is a ball of the exponential map.**  If the exponential map at `x` is
injective on the ball of radius `r`, then every point `y` at distance `< r` from `x` is the
exponential of a **unique** tangent vector whose norm is exactly `d(x,y)`. -/
theorem exists_unique_GExp_of_injAtLeast [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {x : M} {r : ℝ}
    (h : InjAtLeast hmet x r) {y : M}
    (hy : Manifold.riemannianEDist I x y < ENNReal.ofReal r) :
    ∃! u : TangentSpace I x, GExp (cov := cov) hmet x u = y ∧
      Manifold.riemannianEDist I x y = ENNReal.ofReal ‖u‖ := by
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x y
  have hvlt : ‖v‖ < r := by
    have h' := hy
    rw [hvd] at h'
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp h').1
  refine ⟨v, ⟨hvG, hvd⟩, ?_⟩
  rintro w ⟨hwG, hwd⟩
  have hwlt : ‖w‖ < r := by
    have h' := hy
    rw [hwd] at h'
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp h').1
  exact h w v hwlt hvlt (by rw [hwG, hvG])

/-- **A geodesic loop bounds the injectivity radius from above.**
If the chosen unit-speed geodesic segment of length `T` starting at `x` returns to `x`, then there
is no `r` with `InjAllAtLeast r` and `2r > T`.

Equivalently: a geodesic loop of length `T` at `x` forces `inj(x) ≤ T/2`.  This is the easy (and
classical) half of `inj(p) = min{conj(p), ½ ℓ_M(p)}` (Cheeger–Ebin, Lemma 5.6). -/
theorem two_mul_le_of_injAllAtLeast_of_geodCurve_loop
    (hmet : IsMetricCompatible cov) {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1)
    {T : ℝ} (hT : 0 ≤ T) (hTpos : 0 < T)
    (hloop : (geodCurve (cov := cov) hmet T hT x ξ hξ) T = x)
    {r : ℝ} (h : InjAllAtLeast hmet r) : 2 * r ≤ T := by
  classical
  by_cases hr : r ≤ 0
  · linarith
  have hrpos : 0 < r := not_le.mp hr
  by_contra hcon
  rw [not_le] at hcon
  have hhalf_nn : 0 ≤ T / 2 := by linarith
  have hhalf_le : T / 2 ≤ T := by linarith
  have hhalf_lt : T / 2 < r := by linarith
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmid_mem : T / 2 ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT x ξ hξ with hGdef
  have hspec := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hG0 : G 0 = x := by rw [hGdef]; exact hspec.1
  have hGT : G T = x := by rw [hGdef]; exact hloop
  have hGsp : ‖curveVelocity (I := I) G (T / 2)‖ = 1 := by
    rw [hGdef]; exact hspec.2.2.2.2 (T / 2) hmid_mem
  -- the two rays from the midpoint
  have hfwd : GExp (cov := cov) hmet (G (T / 2))
      ((T / 2) • curveVelocity (I := I) G (T / 2)) = G T := by
    rw [hGdef]
    have hh := GExp_geodCurve_add (cov := cov) hmet x hξ hT (t := T / 2) (s := T / 2)
      hhalf_nn hhalf_le hhalf_nn (le_of_eq (by ring : T / 2 + T / 2 = T))
    rw [show T / 2 + T / 2 = T from by ring] at hh
    exact hh
  have hbwd : GExp (cov := cov) hmet (G (T / 2))
      ((-(T / 2)) • curveVelocity (I := I) G (T / 2)) = G 0 := by
    rw [hGdef]
    have hh := GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet x hξ hT
      (t := T / 2) (s := T / 2) hhalf_nn hhalf_le hhalf_nn (le_refl (T / 2))
    rw [show T / 2 - T / 2 = 0 from by ring] at hh
    exact hh
  have hu1 : ‖(T / 2) • curveVelocity (I := I) G (T / 2)‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhalf_nn, hGsp, mul_one]
    exact hhalf_lt
  have hu2 : ‖(-(T / 2)) • curveVelocity (I := I) G (T / 2)‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hhalf_nn, hGsp, mul_one]
    exact hhalf_lt
  have heq : (T / 2) • curveVelocity (I := I) G (T / 2)
      = (-(T / 2)) • curveVelocity (I := I) G (T / 2) := by
    refine h (G (T / 2)) _ _ hu1 hu2 ?_
    rw [hfwd, hbwd, hGT, hG0]
  have hz : curveVelocity (I := I) G (T / 2) = 0 := by
    have hsub : ((T / 2) - (-(T / 2))) • curveVelocity (I := I) G (T / 2) = 0 := by
      rw [sub_smul, heq, sub_self]
    rw [show (T / 2) - (-(T / 2)) = T from by ring] at hsub
    exact (smul_eq_zero.mp hsub).resolve_left (ne_of_gt hTpos)
  rw [hz, norm_zero] at hGsp
  norm_num at hGsp

end

end Submission.InjRadius
