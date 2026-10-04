import Submission.ConjEnergy
import Submission.GExpTranslate
import Submission.GeodesicLoop
import Submission.GSField
import Submission.BrokenLength
import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Submission.XuLift

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

/-- The exponential map at `p`, as an honest function `E → M` (the tangent space at `p` is the
model space `E` by definition, but keeping the model space as the domain avoids all the
definitional-equality bookkeeping of the tangent-space instances). -/
def gexpMap (hmet : IsMetricCompatible cov) (p : M) (u : E) : M :=
  GExp (cov := cov) hmet p (show TangentSpace I p from u)

@[simp] theorem gexpMap_apply (hmet : IsMetricCompatible cov) (p : M) (u : E) :
    gexpMap (cov := cov) hmet p u
      = GExp (cov := cov) hmet p (show TangentSpace I p from u) := rfl

/-- `GExp p`, as a map from the model space, is `C^∞` on all of `E`. -/
theorem contMDiffOn_GExp_model (hmet : IsMetricCompatible cov) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (gexpMap (cov := cov) hmet p) Set.univ := by
  intro v _
  exact Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p
    (show TangentSpace I p from v)

/-- **The inverse function theorem for the exponential map**: if the manifold derivative of
`GExp p` at `v` is invertible, then `GExp p` is a local diffeomorphism at `v`. -/
theorem isLocalDiffeomorphAt_GExp (hmet : IsMetricCompatible cov) (p : M) {v : E}
    (hinv : (mfderiv 𝓘(ℝ, E) I (gexpMap (cov := cov) hmet p) v).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (gexpMap (cov := cov) hmet p) v :=
  Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible
    (I := 𝓘(ℝ, E)) (I' := I) (f := gexpMap (cov := cov) hmet p) (x := v) (U := Set.univ)
    Filter.univ_mem (contMDiffOn_GExp_model (cov := cov) hmet p)
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, E)) (M := E)) hinv

/-- **The image of a ball under `GExp p` contains a small metric ball, with unique lifts.**

This is the ball form of the inverse function theorem at a point where the differential of `GExp p`
is invertible: there are radii `r, δ > 0` such that `GExp p` is injective on the ball of radius `2r`
around `v`, and every point of `M` at Riemannian distance `< δ` from `GExp p v` has a unique
preimage under `GExp p` in the ball of radius `r` around `v`. -/
theorem exists_pos_ball_lift_GExp (hmet : IsMetricCompatible cov) (p : M) {v : E}
    (hinv : (mfderiv 𝓘(ℝ, E) I (gexpMap (cov := cov) hmet p) v).IsInvertible) :
    ∃ r : ℝ, 0 < r ∧
      Set.InjOn (gexpMap (cov := cov) hmet p) (Metric.ball v (2 * r)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ y : M,
        Manifold.riemannianEDist I (gexpMap (cov := cov) hmet p v) y < ENNReal.ofReal δ →
        ∃! w : E, w ∈ Metric.ball v r ∧ gexpMap (cov := cov) hmet p w = y := by
  classical
  obtain ⟨Φ, hvΦ, hev⟩ := isLocalDiffeomorphAt_GExp (cov := cov) hmet p hinv
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- a ball around `v` inside `Φ.source`
  have hmem : Φ.source ∈ 𝓝 v := Φ.open_source.mem_nhds hvΦ
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  have hsub : Metric.ball v (ε / 2) ⊆ Φ.source :=
    fun u hu => hεsub (Metric.ball_subset_ball (by linarith) hu)
  have heq := fun u (hu : u ∈ Φ.source) => hev hu
  refine ⟨ε / 2, hhalf, ?_, ?_⟩
  · -- injectivity on the ball of radius `ε = 2 * (ε/2)`
    rw [show 2 * (ε / 2) = ε from by ring]
    intro u hu u' hu' heqG
    have h1 : Φ u = gexpMap (cov := cov) hmet p u := (heq u (hεsub hu)).symm
    have h2 : Φ u' = gexpMap (cov := cov) hmet p u' := (heq u' (hεsub hu')).symm
    have : Φ u = Φ u' := by rw [h1, h2]; exact heqG
    exact Φ.toOpenPartialHomeomorph.injOn (hεsub hu) (hεsub hu') this
  · -- the target ball
    have hopen : IsOpen (Φ '' Metric.ball v (ε / 2)) :=
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hsub
    have hvmem : v ∈ Metric.ball v (ε / 2) := Metric.mem_ball_self hhalf
    have hGv : gexpMap (cov := cov) hmet p v = Φ v := heq v hvΦ
    have hnhd : Φ '' Metric.ball v (ε / 2) ∈ 𝓝 (gexpMap (cov := cov) hmet p v) := by
      rw [hGv]
      exact hopen.mem_nhds ⟨v, hvmem, rfl⟩
    obtain ⟨c, hcpos, hcsub'⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds
      (I := I) (x := gexpMap (cov := cov) hmet p v) hnhd
    -- turn the `ℝ≥0∞` radius into a real one
    obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ c := by
      rcases eq_top_or_lt_top c with h | h
      · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
      · have hcR : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hcpos) (ne_top_of_lt h)
        refine ⟨c.toReal / 2, by linarith, ?_⟩
        rw [ENNReal.ofReal_le_iff_le_toReal (ne_top_of_lt h)]
        linarith
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have hyc : Manifold.riemannianEDist I (gexpMap (cov := cov) hmet p v) y < c :=
      lt_of_lt_of_le hy hδle
    obtain ⟨w, hwball, hweq⟩ := hcsub' hyc
    have hwG : gexpMap (cov := cov) hmet p w = y := by
      rw [heq w (hsub hwball)]; exact hweq
    refine ⟨w, ⟨hwball, hwG⟩, ?_⟩
    rintro w' ⟨hw'ball, hw'eq⟩
    have hΦeq : Φ w' = Φ w := by
      rw [← heq w' (hsub hw'ball), ← heq w (hsub hwball), hw'eq, hwG]
    exact Φ.toOpenPartialHomeomorph.injOn (hsub hw'ball) (hsub hwball) hΦeq

/-- **The strict corner inequality at a genuine corner of a broken minimising geodesic.**

Let `ξ, η` be unit directions at `p` whose minimising rays meet at time `m > 0`, both rays
minimising on `[0,m]`, and suppose the two rays arrive at the meeting point with velocities that are
**not** opposite (a genuine corner).  Then for all `τ, s ∈ (0,m)` the two intermediate points are
strictly closer than the length of the broken path through the meeting point:

`d (GExp p (τ•ξ)) (GExp p (s•η)) < (m - τ) + (m - s)`.

The proof is the classical "the corner is not straight, so the broken geodesic is not minimising":
if equality held, the broken path `GExp p (s•η) → GExp p (m•ξ) → GExp p (τ•ξ)` would be a minimising
broken geodesic, and the no-corner lemma (`GSField.eq_GExp_of_minimising_broken`) would make it a
*single* geodesic; the two descriptions of the same point `GExp p (τ•ξ)` from the corner then
contradict `SegmentDomain.cutTime_le_of_meet` at the meeting point. -/
theorem edist_lt_of_velocity_ne_neg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    {m τ s : ℝ} (hm : 0 < m) (hτ0 : 0 < τ) (hτm : τ < m) (hs0 : 0 < s) (hsm : s < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hminξ : ∀ t ∈ Set.Icc (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t)
    (hminη : ∀ t ∈ Set.Icc (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • η)) = ENNReal.ofReal t)
    (hne : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m ≠
      -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
        (GExp (cov := cov) hmet p (s • η))
      < ENNReal.ofReal ((m - τ) + (m - s)) := by
  classical
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  -- distances from the two intermediate points to the common meeting point
  have hQx : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
      (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal (m - τ) :=
    Submission.LensSync.edist_eq_sub_of_minimising_ray (cov := cov) hmet hξ hτ0.le hτm.le
      (hminξ τ ⟨hτ0.le, hτm.le⟩) (hminξ m ⟨hm.le, le_rfl⟩)
  have hBx' : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (s • η))
      (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal (m - s) :=
    Submission.LensSync.edist_eq_sub_of_minimising_ray (cov := cov) hmet hη hs0.le hsm.le
      (hminη s ⟨hs0.le, hsm.le⟩) (hminη m ⟨hm.le, le_rfl⟩)
  have hBx : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (s • η))
      (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal (m - s) := by
    rw [hmeet]; exact hBx'
  -- the triangle inequality
  have hle : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
      (GExp (cov := cov) hmet p (s • η)) ≤ ENNReal.ofReal ((m - τ) + (m - s)) := by
    calc Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
          (GExp (cov := cov) hmet p (s • η))
        ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
            (GExp (cov := cov) hmet p (m • ξ))
          + Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ))
            (GExp (cov := cov) hmet p (s • η)) :=
          Manifold.riemannianEDist_triangle (I := I)
            (x := GExp (cov := cov) hmet p (τ • ξ))
            (y := GExp (cov := cov) hmet p (m • ξ))
            (z := GExp (cov := cov) hmet p (s • η))
      _ = ENNReal.ofReal (m - τ) + ENNReal.ofReal (m - s) := by
          rw [hQx, Manifold.riemannianEDist_comm]
          exact congrArg (fun a => ENNReal.ofReal (m - τ) + a) hBx
      _ = ENNReal.ofReal ((m - τ) + (m - s)) := by
          rw [ENNReal.ofReal_add (by linarith) (by linarith)]
  by_contra hcon
  rw [not_lt] at hcon
  have heq : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ • ξ))
      (GExp (cov := cov) hmet p (s • η)) = ENNReal.ofReal ((m - τ) + (m - s)) :=
    le_antisymm hle hcon
  -- the velocity of the `η`-ray at `s`
  have hw2s : ‖curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) s‖ = 1 := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm,
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hηne s, hη]
  have hw2m : ‖curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m‖ = 1 := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm,
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hηne m, hη]
  have hw1 : ‖curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m‖ = 1 := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm,
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne m, hξ]
  -- the meeting point, reached from `s • η` along the `η`-ray
  have htr1 : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • η))
      ((m - s) • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) s)
      = GExp (cov := cov) hmet p (m • η) := by
    rw [Submission.GExpTranslate.GExp_translate (cov := cov) hmet p hη s (m - s)]
    rw [show s + (m - s) = m from by ring]
  -- the no-corner lemma
  have hQ1 : GExp (cov := cov) hmet p (τ • ξ)
      = GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • η))
          (((m - τ) + (m - s)) •
            curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) s) := by
    refine Submission.GSField.eq_GExp_of_minimising_broken (cov := cov) hmet htor
      (x₀ := GExp (cov := cov) hmet p (s • η)) (p := GExp (cov := cov) hmet p (τ • ξ))
      (r := (m - τ) + (m - s)) (t := m - s)
      (w := curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) s)
      hw2s ?_ ?_ ?_ ?_ ?_ ?_
    · linarith
    · linarith
    · linarith
    · rw [htr1]; exact hBx'
    · have hsub : (m - τ) + (m - s) - (m - s) = m - τ := by ring
      rw [htr1, hsub, Manifold.riemannianEDist_comm, ← hmeet]
      exact hQx
    · rw [Manifold.riemannianEDist_comm]; exact heq
  -- evaluate the right-hand side as a point of the `η`-ray
  have hQ1' : GExp (cov := cov) hmet p (τ • ξ) = GExp (cov := cov) hmet p ((2 * m - τ) • η) := by
    rw [hQ1, Submission.GExpTranslate.GExp_translate (cov := cov) hmet p hη s ((m - τ) + (m - s))]
    rw [show s + ((m - τ) + (m - s)) = 2 * m - τ from by ring]
  -- the same point, reached from the meeting point in the direction of the `η`-ray's velocity
  have hQ2 : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • η))
      ((m - τ) • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
      = GExp (cov := cov) hmet p (τ • ξ) := by
    rw [Submission.GExpTranslate.GExp_translate (cov := cov) hmet p hη m (m - τ)]
    rw [show m + (m - τ) = 2 * m - τ from by ring]
    exact hQ1'.symm
  -- the same point, reached from the meeting point along the *reversed* `ξ`-ray
  have hQ3 : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
      ((m - τ) • (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m))
      = GExp (cov := cov) hmet p (τ • ξ) := by
    rw [Submission.GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet p hξ hm
      (s := m - τ) (by linarith) (by linarith)]
    rw [show m - (m - τ) = τ from by ring]
  -- cut-time contradiction at the meeting point
  have hQ2ξ : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
      ((m - τ) • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
      = GExp (cov := cov) hmet p (τ • ξ) := by
    rw [hmeet.symm] at hQ2
    exact hQ2
  have hcut := Submission.SegmentDomain.cutTime_le_of_meet (cov := cov) hmet htor
    (p := GExp (cov := cov) hmet p (m • ξ)) (m := m - τ)
    (ξ := -curveVelocity (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
    (η := curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
    (by rw [norm_neg]; exact hw1)
    (by rw [hmeet.symm] at hw2m; exact hw2m)
    (by intro h; exact hne (by rw [← h, neg_neg]))
    (by linarith)
    (by rw [hQ3, Manifold.riemannianEDist_comm, hQx])
    (by rw [hQ2ξ, Manifold.riemannianEDist_comm, hQx])
    (by rw [hQ3, hQ2ξ])
  -- but the reversed `ξ`-ray is minimising at time `m`, so its cut time is at least `m`
  have hmem : m ∈ Submission.CutTime.minimisingSet (I := I) hmet (GExp (cov := cov) hmet p (m • ξ))
      (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m) := by
    refine ⟨hm.le, ?_⟩
    rw [Submission.GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet p hξ hm
      (s := m) (by linarith) le_rfl]
    rw [show m - m = 0 from by ring, zero_smul, GExp_zero]
    rw [Manifold.riemannianEDist_comm]
    exact hminξ m ⟨hm.le, le_rfl⟩
  have hle_cut : m ≤ Submission.CutTime.cutTime (I := I) hmet (GExp (cov := cov) hmet p (m • ξ))
      (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m) := by
    rw [Submission.CutTime.minimisingSet_eq_Icc (I := I) (cov := cov) hmet htor
      (p := GExp (cov := cov) hmet p (m • ξ))
      (ξ := -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
      (by rw [norm_neg]; exact hw1)] at hmem
    exact hmem.2
  linarith [hle_cut, hcut]


/-- **The local diffeomorphism property on the tangential segment domain.**  Combining the inverse
function theorem (`isLocalDiffeomorphAt_GExp`) with `σ ≤ κ`
(`ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain`). -/
theorem isLocalDiffeomorphAt_GExp_of_mem_segmentDomain
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M} {v : E}
    (hv : (show TangentSpace I p from v) ∈ Submission.SegmentDomain.segmentDomain hmet p)
    (hv0 : v ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (gexpMap (cov := cov) hmet p) v :=
  isLocalDiffeomorphAt_GExp (cov := cov) hmet p
    (Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain (cov := cov) hmet htor hv hv0)

/-- **The range criterion for the image of the segment domain.**  If `d(p,q) = τ` and
`d(q,y) + d(p,y) < (m - τ) + m`, then `y` lies in the image of the tangential segment domain of `p`
(so in particular it is *not* a cut point of `p`), provided `InjAtLeast p m`.

This is the `F_{p;q}` step of Klingenberg's lemma (Xu, arXiv:1401.5549, (2.1)): points of the cut
locus are at distance `≥ m` from `p` (because points closer than `m` are reached by the injectivity
ball), while the triangle inequality through `q` gives
`d(q,y) + d(p,y) ≥ (m - τ) + m` for such points — contradicting the strict inequality. -/
theorem mem_image_segmentDomain_of_edist_add_lt (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m τ : ℝ} (hm : 0 < m) (hτ0 : 0 ≤ τ) (hτm : τ ≤ m) (hinj : InjAtLeast hmet p m)
    {q y : M} (hq : Manifold.riemannianEDist I p q = ENNReal.ofReal τ)
    (hy : Manifold.riemannianEDist I q y + Manifold.riemannianEDist I p y
      < ENNReal.ofReal ((m - τ) + m)) :
    y ∈ (fun v : TangentSpace I p => GExp (cov := cov) hmet p v) ''
      Submission.SegmentDomain.segmentDomain hmet p := by
  by_contra hnot
  -- a point outside the image is at distance at least `m` from `p`
  have hpm : ENNReal.ofReal m ≤ Manifold.riemannianEDist I p y := by
    by_contra hlt
    rw [not_le] at hlt
    exact hnot (Submission.SegmentDomain.ball_subset_image_segmentDomain (I := I) (cov := cov)
      hmet htor (ρ := m) hinj hlt)
  -- and the triangle inequality together with `d(p,q) = τ` gives the complementary bound
  have htri : Manifold.riemannianEDist I p y
      ≤ Manifold.riemannianEDist I p q + Manifold.riemannianEDist I q y :=
    Manifold.riemannianEDist_triangle (I := I) (x := p) (y := q) (z := y)
  rw [hq] at htri
  have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m - τ) + ENNReal.ofReal τ := by
    rw [← ENNReal.ofReal_add (by linarith) hτ0]
    congr 1
    ring
  have hsub : ENNReal.ofReal (m - τ) ≤ Manifold.riemannianEDist I q y := by
    have h1 : ENNReal.ofReal m ≤ ENNReal.ofReal τ + Manifold.riemannianEDist I q y :=
      le_trans hpm htri
    rw [hsplit] at h1
    have h2 : ENNReal.ofReal τ + ENNReal.ofReal (m - τ)
        ≤ ENNReal.ofReal τ + Manifold.riemannianEDist I q y :=
      calc ENNReal.ofReal τ + ENNReal.ofReal (m - τ)
          = ENNReal.ofReal (m - τ) + ENNReal.ofReal τ := add_comm _ _
        _ ≤ ENNReal.ofReal τ + Manifold.riemannianEDist I q y := h1
    exact (ENNReal.add_le_add_iff_left (by simp)).mp h2
  have hsum : ENNReal.ofReal (m - τ) + ENNReal.ofReal m
      ≤ Manifold.riemannianEDist I q y + Manifold.riemannianEDist I p y :=
    add_le_add hsub hpm
  rw [← ENNReal.ofReal_add (by linarith) hm.le] at hsum
  exact absurd hsum (not_le.mpr hy)

end

end Submission.XuLift
