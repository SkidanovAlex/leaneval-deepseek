import Mathlib
import Submission.Work.EvenBound.Imports

namespace Work.EvenBound.ThirdGeodesic

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GExpJointPt Submission.GExpFlow Submission.ChartConnection
  Submission.Geodesic Submission.GlobalExp

/-- **The velocity of a converging family of `GExp`-rays converges.**
`Submission.GExpJointPt.raySeq z₀ q y t n = GExp (q n) (t • frameVector z₀ (q n) (y n))` is the
`n`-th ray (base points `q n → p`, unit directions with chart-`z₀` coordinates `y n → y₀`) and
`rayLim z₀ p y₀ t = GExp p (t • frameVector z₀ p y₀)` the limit ray.  If the rays are met at
parameters `Ln n → L` (`L > 0`), the chart-`z` coordinates of their velocities there converge to
those of the limit ray, where `z` is a chart around the meeting point, `F` a chart frame there and
`hRz` says that the meeting point `rayLim z₀ p y₀ L` lies in the source of the chart `z` (so that
`velCoordsLim` is not the junk value `0` of `continuousLinearMapAt` outside the chart source).
`hinj` is a uniform lower bound of the injectivity radius on the compact chart piece `F.Z`.

*Proof route.*  Position convergence along the rays is available
(`GExpJointPt.tendsto_ray_unit`, or `tendsto_GExp_ray_length` for the varying parameter `Ln n`):
`raySeq (Ln n) n → rayLim L` and `raySeq (Ln n + h) n → rayLim (L + h)` for small `h > 0`.  The
**two-position trick** `GExpJointPt.tendsto_coord_velocity` (with the chart piece `F.Z`, `F.D` and
`F.hbnd`) applied to the base points `raySeq (Ln n) n`, the targets `raySeq (Ln n + h) n`, the
vectors `h • velCoords z (Ln n) n` and the candidate `h • velCoordsLim z L` — the two equations are
exactly `GExpJointPt.raySeq_step` and `GExpJointPt.rayLim_step` — then gives the convergence of
`h • velCoords z (Ln n) n`, and dividing by `h` (`Tendsto.const_smul h⁻¹`) finishes.  The
coefficient `h > 0` must be chosen small so that these coefficients lie in `closedBall 0 η` with
`η ≤ 1/(2 * flowScale F.D)` and `η * sqrt F.Lam < m` (the latter from `F.Lam`, `F.hbnd`); the
vectors have chart norm at most `1/sqrt F.lam` because the rays are unit speed
(`norm_curveVelocity_raySeq`, `norm_curveVelocity_rayLim`).  The eventual membership
`raySeq (Ln n) n ∈ F.Z` follows from convergence to the centre `rayLim L ∈ F.Z`
(`hRz` + `F.hZeq` + `F.hZsrc`, `F.nhds_of_strict`), which is an interior point of the frame's
ball. -/
theorem tendsto_velCoords_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 p))
    {y : ℕ → E} {y₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hunit : ∀ n, ‖Submission.Geodesic.frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    (hu₀ : ‖Submission.Geodesic.frameVector (I := I) z₀ p y₀‖ = 1)
    {Ln : ℕ → ℝ} {L : ℝ} (hLn : Tendsto Ln atTop (𝓝 L)) (hLnpos : ∀ n, 0 ≤ Ln n) (hL : 0 < L)
    {z : M}
    (F : Submission.GExpJointPt.ChartFrame (cov := cov) z
          (Submission.GExpJointPt.rayLim (cov := cov) hmet z₀ p y₀ L))
    (hRz : Submission.GExpJointPt.rayLim (cov := cov) hmet z₀ p y₀ L ∈ (chartAt H z).source)
    {m : ℝ} (hm : 0 < m) (hinj : ∀ w ∈ F.Z, Submission.InjRadius.InjAtLeast hmet w m) :
    Tendsto (fun n => Submission.GExpJointPt.velCoords (cov := cov) hmet z₀ q y z (Ln n) n) atTop
      (𝓝 (Submission.GExpJointPt.velCoordsLim (cov := cov) hmet z₀ p y₀ z L)) := by
  classical
  -- ## The meeting point: in the chart source and in the compact piece `F.Z`.
  have hstrict : ‖(extChartAt I z) (rayLim (cov := cov) hmet z₀ p y₀ L) - F.x‖ < F.η := by
    rw [F.hx, sub_self, norm_zero]
    exact F.hη
  have hxZ : rayLim (cov := cov) hmet z₀ p y₀ L ∈ F.Z := F.mem_of_norm hRz hstrict
  have hslim : rayLim (cov := cov) hmet z₀ p y₀ L ∈ (extChartAt I z).source := by
    simpa only [extChartAt_source (I := I) z] using hRz
  -- ## Position convergence, at the meeting parameters.
  have hP1 : Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y (Ln n) n) atTop
      (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ L)) :=
    tendsto_GExp_ray_length (cov := cov) hmet htor hp hq hy hunit hu₀ hLn hLnpos hL
  have hxnZ : ∀ᶠ n in atTop, raySeq (cov := cov) hmet z₀ q y (Ln n) n ∈ F.Z :=
    hP1 (F.nhds_of_strict hRz hstrict)
  have hevLnpos : ∀ᶠ n in atTop, 0 < Ln n := by
    have hmem : Metric.ball L (L / 2) ∈ 𝓝 L := Metric.ball_mem_nhds L (by linarith)
    filter_upwards [hLn hmem] with n hn
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, abs_lt] at hn
    linarith [hn.1]
  -- ## The constants.
  have hcpos : 0 < flowScale F.D := flowScale_pos F.D
  have hLam : 0 < Real.sqrt F.Lam := Real.sqrt_pos.mpr F.hLam
  have hlam : 0 < Real.sqrt F.lam := Real.sqrt_pos.mpr F.hlam
  set η' : ℝ := min (1 / (2 * flowScale F.D)) (m / (2 * Real.sqrt F.Lam)) with hη'def
  have hη'pos : 0 < η' := by
    rw [hη'def]
    exact lt_min (by positivity) (div_pos hm (by positivity))
  have hη'c : η' ≤ 1 / (2 * flowScale F.D) := by rw [hη'def]; exact min_le_left _ _
  have hη'm : Real.sqrt F.Lam * η' ≤ m / 2 := by
    have h : η' ≤ m / (2 * Real.sqrt F.Lam) := by rw [hη'def]; exact min_le_right _ _
    calc Real.sqrt F.Lam * η' ≤ Real.sqrt F.Lam * (m / (2 * Real.sqrt F.Lam)) :=
          mul_le_mul_of_nonneg_left h hLam.le
      _ = m / 2 := by field_simp
  -- ## The frame vector is small on the chart piece.
  have hnorm : ∀ q' ∈ F.Z, ∀ u ∈ Metric.closedBall (0 : E) η',
      ‖frameVector (I := I) z q' u‖ < m := by
    intro q' hq' u hu
    have hu' : ‖u‖ ≤ η' := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    rw [norm_frameVector]
    have h1 : Real.sqrt (chartGram (I := I) z q' u u) ≤ Real.sqrt F.Lam * η' := by
      calc Real.sqrt (chartGram (I := I) z q' u u) ≤ Real.sqrt (F.Lam * ‖u‖ ^ 2) :=
            Real.sqrt_le_sqrt (F.hbnd q' hq' u).2
        _ = Real.sqrt F.Lam * ‖u‖ := by
            rw [Real.sqrt_mul F.hLam.le, Real.sqrt_sq (norm_nonneg u)]
        _ ≤ Real.sqrt F.Lam * η' := mul_le_mul_of_nonneg_left hu' hLam.le
    linarith
  -- ## The step size, and position convergence at the shifted parameters.
  set hh : ℝ := Real.sqrt F.lam * η' with hhdef
  have hhpos : 0 < hh := by rw [hhdef]; exact mul_pos hlam hη'pos
  have hhle : hh ≤ Real.sqrt F.lam * η' := hhdef.le
  have hP2 : Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y (Ln n + hh) n) atTop
      (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ (L + hh))) :=
    tendsto_GExp_ray_length (cov := cov) hmet htor hp hq hy hunit hu₀
      (Ln := fun n => Ln n + hh) (L := L + hh)
      (hLn.add tendsto_const_nhds)
      (fun n => by linarith [hLnpos n, hhpos.le]) (by linarith)
  -- ## The scaled velocity coordinates are small.
  have hmem_v : ∀ {s : ℝ} {n : ℕ}, 0 < s →
      raySeq (cov := cov) hmet z₀ q y s n ∈ F.Z →
      (hh • velCoords (cov := cov) hmet z₀ q y z s n) ∈ Metric.closedBall (0 : E) η' := by
    intro s n hs hsZ
    have hsrc : raySeq (cov := cov) hmet z₀ q y s n ∈ (extChartAt I z).source := by
      simpa only [extChartAt_source (I := I) z] using F.hZsrc hsZ
    have hclm : frameVector (I := I) z (raySeq (cov := cov) hmet z₀ q y s n)
        (velCoords (cov := cov) hmet z₀ q y z s n)
        = curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s :=
      frameVector_clm (I := I) hsrc _
    have hnormv : ‖curveVelocity (I := I)
        (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s‖ = 1 :=
      norm_curveVelocity_raySeq (cov := cov) hunit (ne_of_gt hs) n
    have hgram : chartGram (I := I) z (raySeq (cov := cov) hmet z₀ q y s n)
        (velCoords (cov := cov) hmet z₀ q y z s n)
        (velCoords (cov := cov) hmet z₀ q y z s n) = 1 := by
      rw [chartGram_apply, real_inner_self_eq_norm_sq, hclm, hnormv]
      norm_num
    have hb := (F.hbnd (raySeq (cov := cov) hmet z₀ q y s n) hsZ
      (velCoords (cov := cov) hmet z₀ q y z s n)).1
    rw [hgram] at hb
    have hb2 : Real.sqrt F.lam * ‖(velCoords (cov := cov) hmet z₀ q y z s n : E)‖ ≤ 1 := by
      have hs2 : Real.sqrt F.lam ^ 2 = F.lam := Real.sq_sqrt F.hlam.le
      nlinarith [hb, hs2, Real.sqrt_nonneg F.lam,
        norm_nonneg (velCoords (cov := cov) hmet z₀ q y z s n : E)]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg hhpos.le]
    have h2 : (Real.sqrt F.lam * η') *
        ‖(velCoords (cov := cov) hmet z₀ q y z s n : E)‖ ≤ η' := by
      have h3 := mul_le_mul_of_nonneg_left hb2 hη'pos.le
      rw [mul_one] at h3
      nlinarith [h3]
    exact le_trans (mul_le_mul_of_nonneg_right hhle (norm_nonneg _)) h2
  have hmemu : (hh • velCoordsLim (cov := cov) hmet z₀ p y₀ z L) ∈
      Metric.closedBall (0 : E) η' := by
    have hclm : frameVector (I := I) z (rayLim (cov := cov) hmet z₀ p y₀ L)
        (velCoordsLim (cov := cov) hmet z₀ p y₀ z L)
        = curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) L :=
      frameVector_clm (I := I) hslim _
    have hnormv : ‖curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) L‖ = 1 :=
      norm_curveVelocity_rayLim (cov := cov) hu₀ (ne_of_gt hL)
    have hgram : chartGram (I := I) z (rayLim (cov := cov) hmet z₀ p y₀ L)
        (velCoordsLim (cov := cov) hmet z₀ p y₀ z L)
        (velCoordsLim (cov := cov) hmet z₀ p y₀ z L) = 1 := by
      rw [chartGram_apply, real_inner_self_eq_norm_sq, hclm, hnormv]
      norm_num
    have hb := (F.hbnd (rayLim (cov := cov) hmet z₀ p y₀ L) hxZ
      (velCoordsLim (cov := cov) hmet z₀ p y₀ z L)).1
    rw [hgram] at hb
    have hb2 : Real.sqrt F.lam * ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ z L : E)‖ ≤ 1 := by
      have hs2 : Real.sqrt F.lam ^ 2 = F.lam := Real.sq_sqrt F.hlam.le
      nlinarith [hb, hs2, Real.sqrt_nonneg F.lam,
        norm_nonneg (velCoordsLim (cov := cov) hmet z₀ p y₀ z L : E)]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg hhpos.le]
    have h2 : (Real.sqrt F.lam * η') *
        ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ z L : E)‖ ≤ η' := by
      have h3 := mul_le_mul_of_nonneg_left hb2 hη'pos.le
      rw [mul_one] at h3
      nlinarith [h3]
    exact le_trans (mul_le_mul_of_nonneg_right hhle (norm_nonneg _)) h2
  have hmemun : ∀ᶠ n in atTop,
      (hh • velCoords (cov := cov) hmet z₀ q y z (Ln n) n) ∈ Metric.closedBall (0 : E) η' := by
    filter_upwards [hxnZ, hevLnpos] with n hnZ hnpos
    exact hmem_v hnpos hnZ
  -- ## The two equations of the two-position trick.
  have heqn : ∀ᶠ n in atTop,
      GExp (cov := cov) hmet (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
        (frameVector (I := I) z (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
          (hh • velCoords (cov := cov) hmet z₀ q y z (Ln n) n))
      = raySeq (cov := cov) hmet z₀ q y (Ln n + hh) n := by
    filter_upwards [hxnZ, hevLnpos] with n hnZ hnpos
    have hsrc : raySeq (cov := cov) hmet z₀ q y (Ln n) n ∈ (extChartAt I z).source := by
      simpa only [extChartAt_source (I := I) z] using F.hZsrc hnZ
    have h := raySeq_step (cov := cov) (s₀ := Ln n) (s := Ln n + hh) hunit hnpos
      (by linarith [hhpos.le]) n hsrc
    rw [show Ln n + hh - Ln n = hh from by ring] at h
    exact h.symm
  have heq : GExp (cov := cov) hmet (rayLim (cov := cov) hmet z₀ p y₀ L)
      (frameVector (I := I) z (rayLim (cov := cov) hmet z₀ p y₀ L)
        (hh • velCoordsLim (cov := cov) hmet z₀ p y₀ z L))
      = rayLim (cov := cov) hmet z₀ p y₀ (L + hh) := by
    have h := rayLim_step (cov := cov) (s₀ := L) (s := L + hh) hu₀ hL
      (by linarith [hhpos.le]) hslim
    rw [show L + hh - L = hh from by ring] at h
    exact h.symm
  -- ## The two-position trick.
  have hstep := tendsto_coord_velocity (cov := cov) hmet htor
    (z₀ := z) (Z := F.Z) F.hZsrc F.hZc F.D hη'c hinj hnorm
    (xn := fun n => raySeq (cov := cov) hmet z₀ q y (Ln n) n)
    (x := rayLim (cov := cov) hmet z₀ p y₀ L) hP1 hxnZ hxZ
    (yn := fun n => raySeq (cov := cov) hmet z₀ q y (Ln n + hh) n)
    (y := rayLim (cov := cov) hmet z₀ p y₀ (L + hh)) hP2
    (un := fun n => hh • velCoords (cov := cov) hmet z₀ q y z (Ln n) n)
    (u := hh • velCoordsLim (cov := cov) hmet z₀ p y₀ z L)
    hmemun hmemu heqn heq
  -- ## Divide by the step size.
  have hfinal : Tendsto (fun n => velCoords (cov := cov) hmet z₀ q y z (Ln n) n) atTop
      (𝓝 (velCoordsLim (cov := cov) hmet z₀ p y₀ z L)) := by
    have h := hstep.const_smul (hh⁻¹)
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hhpos), one_smul] using h
  exact hfinal

end Work.EvenBound.ThirdGeodesic
