import Submission.XuStep
import Submission.UniformInj
import Submission.GSCritical
import Submission.HingeKey

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
open Submission.HopfRinow

namespace Submission.CornerStrict

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

/-- **Sub-arcs of a ray.**  The chosen unit-speed segment of length `T` starting at `p` in the
direction `ξ` agrees with the `GExp`-ray at every intermediate time `0 < t ≤ T`. -/
theorem GExp_eq_geodCurve_of_le (hmet : IsMetricCompatible cov) {p : M} {ξ : TangentSpace I p}
    (hξ : ‖ξ‖ = 1) {T t : ℝ} (hT : 0 ≤ T) (ht0 : 0 < t) (htT : t ≤ T) :
    GExp (cov := cov) hmet p (t • ξ) = (geodCurve (cov := cov) hmet T hT p ξ hξ) t := by
  rw [Submission.InjHalf.GExp_eq_geodCurve (cov := cov) hmet hξ ht0]
  exact geodCurve_agree (cov := cov) hmet ht0.le hT htT p ξ hξ
    (Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
      by linarith [geodDelta_pos (cov := cov) hmet]⟩)

/-- **Two-sidedness of a `GExp`-ray.**  For a unit direction `ξ` at `q` and `0 < ε`, let
`w = curveVelocity (fun r ↦ GExp q (r • ξ)) (-ε)` be the velocity of the ray at the parameter `-ε`
and `A = GExp q ((-ε) • ξ)` the corresponding point.  Then the ray from `A` in the direction `w`
runs back to `q` (at time `ε`) and onwards to `GExp q (ε • ξ)` (at time `2ε`):

`GExp A (ε • w) = q`  and  `GExp A (2ε • w) = GExp q (ε • ξ)`.

Proved by geodesic uniqueness (`eqOn_Ioo_of_isGeodesicAt_of_eq`): both `s ↦ GExp A (s • w)` and
`s ↦ GExp q ((s - ε) • ξ)` are geodesics with the same value and velocity at `s = 0`. -/
theorem GExp_ray_back (hmet : IsMetricCompatible cov) (q : M) {ξ : TangentSpace I q}
    (hξ : ‖ξ‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    (GExp (cov := cov) hmet (GExp (cov := cov) hmet q ((-ε) • ξ))
        (ε • curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (-ε)) = q) ∧
    (GExp (cov := cov) hmet (GExp (cov := cov) hmet q ((-ε) • ξ))
        ((2 * ε) • curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (-ε))
      = GExp (cov := cov) hmet q (ε • ξ)) := by
  classical
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  set w : TangentSpace I (GExp (cov := cov) hmet q ((-ε) • ξ)) :=
    curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (-ε) with hwdef
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hξne (-ε)
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξne
      (by linarith : (-ε) ≠ 0)]
    exact hξ
  have hraymd : ∀ r : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) r := fun r =>
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  have hσsm : ContMDiffOn 𝓘(ℝ) I ∞
      (fun s : ℝ => GExp (cov := cov) hmet q ((1 * s + (-ε)) • ξ)) (Ioo (-1 : ℝ) (2 * ε + 1)) := by
    have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => 1 * s + (-ε)) :=
      (contMDiff_const.mul contMDiff_id).add contMDiff_const
    have h := (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).comp
      (hg.contMDiffOn (s := Ioo (-1 : ℝ) (2 * ε + 1))) (fun s _ => Set.mem_univ _)
    rw [show (fun s : ℝ => GExp (cov := cov) hmet q (s • ξ)) ∘ (fun s : ℝ => 1 * s + (-ε))
        = (fun s : ℝ => GExp (cov := cov) hmet q ((1 * s + (-ε)) • ξ)) from rfl] at h
    exact h
  have hγrev : curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet q ((1 * s + (-ε)) • ξ)) 0
      = w := by
    rw [Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (c := 1) (d := -ε) (t := 0)
      (hraymd (1 * 0 + (-ε)))]
    rw [one_mul, zero_add, one_smul, hwdef]
  have hγrev0 : (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet q ((-ε) • ξ))
        (s • w)) 0
      = (fun s : ℝ => GExp (cov := cov) hmet q ((1 * s + (-ε)) • ξ)) 0 := by
    simp only [zero_smul, GExp_zero, one_mul, zero_add]
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := (-1 : ℝ)) (b := 2 * ε + 1)
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet
      (GExp (cov := cov) hmet q ((-ε) • ξ)) hwne).mono (Set.subset_univ _))
    hσsm
    (fun s _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet
      (GExp (cov := cov) hmet q ((-ε) • ξ)) hwne s)
    (fun s hs => by
      have h := isGeodesicAt_comp_affine (cov := cov)
        (σ := fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (a := 1) (b := -ε)
        (c := -1 - ε) (d := 2 * ε + 1) (by norm_num)
        ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).mono
          (Set.subset_univ _))
        (fun y _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξne y)
        (r := s) (Set.mem_Ioo.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa using h)
    (fun s _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet
      (GExp (cov := cov) hmet q ((-ε) • ξ)) hwne s)
    (fun s hs => by
      rw [Submission.Length.curveVelocity_comp_mul_add (I := I)
        (γ := fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (c := 1) (d := -ε) (t := s)
        (hraymd (1 * s + (-ε)))]
      rw [one_smul]
      exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hξne (1 * s + (-ε)))
    (show (0 : ℝ) ∈ Ioo (-1) (2 * ε + 1) from Set.mem_Ioo.mpr ⟨by norm_num, by linarith⟩)
    hγrev0
    (by
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet
        (GExp (cov := cov) hmet q ((-ε) • ξ)) hwne, hγrev])
  refine ⟨?_, ?_⟩
  · have h := hEqOn (show (ε : ℝ) ∈ Ioo (-1) (2 * ε + 1) from
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    simpa [one_mul, add_neg_cancel, zero_smul, GExp_zero] using h
  · have h := hEqOn (show (2 * ε : ℝ) ∈ Ioo (-1) (2 * ε + 1) from
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    have harg : (2 * ε + (-ε)) = ε := by ring
    simpa [harg] using h

/-- **The strict corner estimate.**  Let `v₁ ≠ v₂` be two distinct *unit* tangent vectors at `q` and
let `ρ` be a radius at which `GExp` is injective at *every* point.  Then for `0 < ε < ρ` the two
points `GExp q ((-ε) • v₁)` and `GExp q (ε • v₂)` are *strictly* closer than `2ε`:

`d (GExp q ((-ε) • v₁)) (GExp q (ε • v₂)) < 2 ε`.

Equivalently: the broken path through `q` is not minimising — the corner at `q` can be cut.  The
proof is the contrapositive: if the broken path were minimising, the no-corner lemma
(`GSField.eq_GExp_of_minimising_broken`) would show that the geodesic through `q` and
`A = GExp q ((-ε) • v₁)` continues past `q` to `GExp q (ε • v₁)`, while the two-sidedness of the
ray (`GExp_ray_back`) identifies that same point with `GExp q (ε • v₁)`; injectivity of `GExp q` on
the ball of radius `ρ` then forces `v₁ = v₂`. -/
theorem edist_GExp_corner_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {ρ : ℝ} (hInjAll : InjAllAtLeast hmet ρ)
    (q : M) {v₁ v₂ : TangentSpace I q} (h₁ : ‖v₁‖ = 1) (h₂ : ‖v₂‖ = 1) (hne : v₁ ≠ v₂)
    {ε : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet q ((-ε) • v₁))
      (GExp (cov := cov) hmet q (ε • v₂)) < ENNReal.ofReal (2 * ε) := by
  classical
  have h₂ε : (0 : ℝ) ≤ 2 * ε := by linarith
  have h₁ne : v₁ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h₁; norm_num at h₁
  have hInjq : InjAtLeast hmet q ρ := hInjAll q
  have hnorm1' : ‖(ε • v₁ : TangentSpace I q)‖ = ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, h₁, mul_one]
  have hnorm1 : ‖((-ε) • v₁ : TangentSpace I q)‖ = ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hε, h₁, mul_one]
  have hnorm2 : ‖(ε • v₂ : TangentSpace I q)‖ = ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, h₂, mul_one]
  have hdist : ∀ v : TangentSpace I q, ‖v‖ = ε →
      Manifold.riemannianEDist I q (GExp (cov := cov) hmet q v) = ENNReal.ofReal ε := by
    intro v hv
    rw [Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hInjq
      (w := v) (by rw [hv]; exact hερ.le), hv]
  have hqA : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q ((-ε) • v₁))
      = ENNReal.ofReal ε := hdist _ hnorm1
  have hqB : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q (ε • v₂))
      = ENNReal.ofReal ε := hdist _ hnorm2
  have hle : Manifold.riemannianEDist I (GExp (cov := cov) hmet q ((-ε) • v₁))
      (GExp (cov := cov) hmet q (ε • v₂)) ≤ ENNReal.ofReal (2 * ε) := by
    calc Manifold.riemannianEDist I (GExp (cov := cov) hmet q ((-ε) • v₁))
          (GExp (cov := cov) hmet q (ε • v₂))
        ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet q ((-ε) • v₁)) q
          + Manifold.riemannianEDist I q (GExp (cov := cov) hmet q (ε • v₂)) :=
          Manifold.riemannianEDist_triangle (I := I)
            (x := GExp (cov := cov) hmet q ((-ε) • v₁)) (y := q)
            (z := GExp (cov := cov) hmet q (ε • v₂))
      _ = ENNReal.ofReal (2 * ε) := by
          rw [Manifold.riemannianEDist_comm (I := I)
              (x := GExp (cov := cov) hmet q ((-ε) • v₁)) (y := q),
            hqA, hqB, ← ENNReal.ofReal_add hε.le hε.le]
          congr 1
          ring
  refine lt_of_le_of_ne hle ?_
  intro heq
  obtain ⟨hAw, hA2w⟩ := GExp_ray_back (cov := cov) hmet q h₁ hε
  have hw1 : ‖curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • v₁)) (-ε)‖ = 1 := by
    rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q h₁ne
      (by linarith : (-ε) ≠ 0)]
    exact h₁
  have hB2 : GExp (cov := cov) hmet q (ε • v₂)
      = GExp (cov := cov) hmet (GExp (cov := cov) hmet q ((-ε) • v₁))
          ((2 * ε) • curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • v₁))
            (-ε)) := by
    refine Submission.GSField.eq_GExp_of_minimising_broken (cov := cov) hmet htor
      (x₀ := GExp (cov := cov) hmet q ((-ε) • v₁)) (p := GExp (cov := cov) hmet q (ε • v₂))
      (r := 2 * ε) (t := ε)
      (w := curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • v₁)) (-ε))
      hw1 h₂ε hε (by linarith) ?_ ?_ ?_
    · rw [hAw, Manifold.riemannianEDist_comm (I := I)
        (x := GExp (cov := cov) hmet q ((-ε) • v₁)) (y := q)]
      exact hqA
    · rw [hAw, show (2 : ℝ) * ε - ε = ε from by ring]
      exact hqB
    · exact heq
  have hthis : GExp (cov := cov) hmet q (ε • v₂) = GExp (cov := cov) hmet q (ε • v₁) :=
    hB2.trans hA2w
  have hinj := hInjq (ε • v₂) (ε • v₁) (by rw [hnorm2]; exact hερ)
    (by rw [hnorm1']; exact hερ) hthis
  have hvv : v₂ = v₁ := by
    have h' := congrArg (fun z : TangentSpace I q => (ε⁻¹ : ℝ) • z) hinj
    simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using h'
  exact hne hvv.symm

/-- **The strict corner estimate, with an explicit uniform radius.**  There is a radius `ρ > 0`
depending only on the manifold such that for every point `q`, every pair of distinct *unit* tangent
vectors `v₁ ≠ v₂` at `q` and every `0 < ε < ρ` the two points at distance `ε` from `q` in the
directions `-v₁` and `v₂` are strictly closer than `2ε`. -/
theorem exists_pos_corner_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (q : M) (v₁ v₂ : TangentSpace I q), ‖v₁‖ = 1 → ‖v₂‖ = 1 → v₁ ≠ v₂ →
      ∀ ε : ℝ, 0 < ε → ε < ρ →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q ((-ε) • v₁))
          (GExp (cov := cov) hmet q (ε • v₂)) < ENNReal.ofReal (2 * ε) := by
  obtain ⟨ρ, hρ, hInjAll⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  exact ⟨ρ, hρ, fun q v₁ v₂ h₁ h₂ hne ε hε hερ =>
    edist_GExp_corner_lt (cov := cov) hmet htor hInjAll q h₁ h₂ hne hε hερ⟩

/-- **The strict corner estimate, in the `u₁ ≠ -u₂` form.**  For two unit tangent vectors
`u₁, u₂` at `q` that are not opposite, the two points `GExp q (ε • u₁)` and `GExp q (ε • u₂)` at
distance `ε` from `q` are strictly closer than `2ε`, for `0 < ε < ρ`.  (When `u₂ = -u₁` they are the
two ends of a single geodesic segment and the distance is exactly `2ε`.) -/
theorem edist_GExp_lt_of_unit_ne_neg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {ρ : ℝ} (hInjAll : InjAllAtLeast hmet ρ)
    (q : M) {u₁ u₂ : TangentSpace I q} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1) (hne : u₁ ≠ -u₂)
    {ε : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet q (ε • u₁))
      (GExp (cov := cov) hmet q (ε • u₂)) < ENNReal.ofReal (2 * ε) := by
  have h₁' : ‖(-u₁ : TangentSpace I q)‖ = 1 := by rw [norm_neg]; exact h₁
  have hne' : (-u₁ : TangentSpace I q) ≠ u₂ := by
    intro h; exact hne (by rw [← h, neg_neg])
  have h := edist_GExp_corner_lt (cov := cov) hmet htor hInjAll q h₁' h₂ hne' hε hερ
  rwa [show (-ε : ℝ) • (-u₁) = ε • u₁ from by rw [smul_neg, neg_smul, neg_neg]] at h

/-- **The uniform-radius form of the strict corner estimate** (`u₁ ≠ -u₂`). -/
theorem exists_pos_corner_lt_unit_ne_neg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (q : M) (u₁ u₂ : TangentSpace I q), ‖u₁‖ = 1 → ‖u₂‖ = 1 → u₁ ≠ -u₂ →
      ∀ ε : ℝ, 0 < ε → ε < ρ →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q (ε • u₁))
          (GExp (cov := cov) hmet q (ε • u₂)) < ENNReal.ofReal (2 * ε) := by
  obtain ⟨ρ, hρ, hInjAll⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  exact ⟨ρ, hρ, fun q u₁ u₂ h₁ h₂ hne ε hε hερ =>
    edist_GExp_lt_of_unit_ne_neg (cov := cov) hmet htor hInjAll q h₁ h₂ hne hε hερ⟩

end

end Submission.CornerStrict
