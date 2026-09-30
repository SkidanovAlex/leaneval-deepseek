import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartBounds
import Submission.Work.RiemLib.ChartBounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
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
open Submission.XuLift

namespace Submission.XuMain

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

/-- **The ball form of the inverse function theorem, uniformly in a prescribed small radius.**

There is `r₀ > 0` such that for every `r ∈ (0, r₀]` the map `GExp p` is injective on the *closed* ball
of radius `r` around `v`, and there is `δ > 0` such that every point within Riemannian distance `δ`
of `GExp p v` has a unique preimage in the *open* ball of radius `r`.

The point is that the ball of the inverse function theorem can be *prescribed*: the local
diffeomorphism `Φ` at `v` restricts to the ball of radius `r`, whose image is open (so `δ` exists),
and the identity `GExp p = Φ` on `Φ.source` gives both the existence and the uniqueness of the
preimage *inside the prescribed ball*. -/
theorem exists_pos_ball_lift_GExp_forall_le (hmet : IsMetricCompatible cov) (p : M)
    {v : TangentSpace I p}
    (hinv : (mfderiv 𝓘(ℝ, E) I (gexpMap (cov := cov) hmet p) (show E from v)).IsInvertible) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ δ : ℝ, 0 < δ ∧
      Set.InjOn (gexpMap (cov := cov) hmet p) (Metric.closedBall (show E from v) r) ∧
      ∀ y : M,
        Manifold.riemannianEDist I (GExp (cov := cov) hmet p v) y < ENNReal.ofReal δ →
        ∃! w : E, w ∈ Metric.ball (show E from v) r ∧ gexpMap (cov := cov) hmet p w = y := by
  classical
  obtain ⟨Φ, hvΦ, hev⟩ := Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet p hinv
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hvΦ)
  refine ⟨ρ / 2, by linarith, fun r hr hrle => ?_⟩
  have hrρ : r < ρ := by linarith
  have hball : Metric.ball (show E from v) r ⊆ Φ.source := fun w hw =>
    hρsub (Metric.ball_subset_ball hrρ.le hw)
  have hopen : IsOpen (Φ '' Metric.ball (show E from v) r) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball
  have hvmem : (show E from v) ∈ Metric.ball (show E from v) r := Metric.mem_ball_self hr
  have hnhd : Φ '' Metric.ball (show E from v) r ∈ 𝓝 (gexpMap (cov := cov) hmet p v) := by
    rw [show gexpMap (cov := cov) hmet p v = Φ (show E from v) from hev hvΦ]
    exact hopen.mem_nhds ⟨(show E from v), hvmem, rfl⟩
  obtain ⟨c, hcpos, hcsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds
    (I := I) (x := gexpMap (cov := cov) hmet p v) hnhd
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ c := by
    rcases eq_top_or_lt_top c with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · have hcR : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hcpos) (ne_top_of_lt h)
      refine ⟨c.toReal / 2, by linarith, ?_⟩
      rw [ENNReal.ofReal_le_iff_le_toReal (ne_top_of_lt h)]
      linarith
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro w hw w' hw' heq
    have hmem : ∀ z ∈ Metric.closedBall (show E from v) r, z ∈ Φ.source :=
      fun z hz => hρsub (Metric.closedBall_subset_ball hrρ hz)
    have : Φ w = Φ w' := by rw [← hev (hmem w hw), ← hev (hmem w' hw'), heq]
    exact Φ.toOpenPartialHomeomorph.injOn (hmem w hw) (hmem w' hw') this
  · intro y hy
    have hyc : Manifold.riemannianEDist I (gexpMap (cov := cov) hmet p v) y < c :=
      lt_of_lt_of_le hy hδle
    obtain ⟨w, hwball, hweq⟩ := hcsub hyc
    have hwG : gexpMap (cov := cov) hmet p w = y := by
      rw [hev (hball hwball)]; exact hweq
    refine ⟨w, ⟨hwball, hwG⟩, ?_⟩
    rintro w' ⟨hw'ball, hw'eq⟩
    have hΦeq : Φ w' = Φ w := by
      rw [← hev (hball hw'ball), ← hev (hball hwball), hw'eq, hwG]
    exact Φ.toOpenPartialHomeomorph.injOn (hball hw'ball) (hball hwball) hΦeq

/-- **Claim A of Xu's Theorem B (the range condition along a minimising geodesic).**

Let `d(q,β) < (m - τ) + (m - s)` (the point `β` is "before the corner" of the broken path, the strict
inequality coming from `XuLift.edist_lt_of_velocity_ne_neg`), let `d(p,q) = τ`, `d(p,β) = s` and let
`y` be a point of a minimising path from `q` to `β` (`d(q,y) + d(y,β) = d(q,β)`).  Then `y` lies in
the image of the tangential segment domain of `p`, provided `InjAtLeast p m`. -/
theorem mem_image_segmentDomain_of_minimising (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m τ s : ℝ} (hm : 0 < m) (hτ0 : 0 ≤ τ) (hτm : τ ≤ m) (hs0 : 0 ≤ s) (hsm : s ≤ m)
    (hinj : InjAtLeast hmet p m)
    {q β y : M} (hqp : Manifold.riemannianEDist I p q = ENNReal.ofReal τ)
    (hβp : Manifold.riemannianEDist I p β = ENNReal.ofReal s)
    (hqβ : Manifold.riemannianEDist I q β < ENNReal.ofReal ((m - τ) + (m - s)))
    (hyq : Manifold.riemannianEDist I q y + Manifold.riemannianEDist I y β
      ≤ Manifold.riemannianEDist I q β) :
    y ∈ (fun v : TangentSpace I p => GExp (cov := cov) hmet p v) ''
      Submission.SegmentDomain.segmentDomain hmet p := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have htri : Manifold.riemannianEDist I p y
      ≤ Manifold.riemannianEDist I y β + Manifold.riemannianEDist I β p := by
    rw [Manifold.riemannianEDist_comm (I := I) (x := p) (y := y)]
    exact Manifold.riemannianEDist_triangle (I := I) (x := y) (y := β) (z := p)
  have hβp' : Manifold.riemannianEDist I β p = ENNReal.ofReal s := by
    rw [Manifold.riemannianEDist_comm]; exact hβp
  have h1 : Manifold.riemannianEDist I q y + Manifold.riemannianEDist I p y
      ≤ Manifold.riemannianEDist I q β + ENNReal.ofReal s := by
    calc Manifold.riemannianEDist I q y + Manifold.riemannianEDist I p y
        ≤ Manifold.riemannianEDist I q y
          + (Manifold.riemannianEDist I y β + Manifold.riemannianEDist I β p) :=
          add_le_add le_rfl htri
      _ = (Manifold.riemannianEDist I q y + Manifold.riemannianEDist I y β)
          + Manifold.riemannianEDist I β p := (add_assoc _ _ _).symm
      _ ≤ Manifold.riemannianEDist I q β + ENNReal.ofReal s := by
          rw [hβp']; exact add_le_add hyq le_rfl
  have h2 : Manifold.riemannianEDist I q β + ENNReal.ofReal s
      < ENNReal.ofReal ((m - τ) + m) := by
    have hms : ENNReal.ofReal ((m - τ) + (m - s)) + ENNReal.ofReal s
        = ENNReal.ofReal ((m - τ) + m) := by
      rw [← ENNReal.ofReal_add (by linarith) hs0,
        show (m - τ) + (m - s) + s = (m - τ) + m from by ring]
    rw [← hms]
    exact ENNReal.add_lt_add_right (by simp) hqβ
  exact Submission.XuLift.mem_image_segmentDomain_of_edist_add_lt (cov := cov) hmet htor hm hτ0 hτm
    hinj hqp (lt_of_le_of_lt h1 h2)

/-- **The model norm and the fibre norm are comparable.** -/
theorem exists_pos_model_fibre_norm (p : M) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ Lam : ℝ, 0 < Lam ∧ ∀ v : TangentSpace I p,
      ‖(show E from v)‖ ≤ ‖v‖ / Real.sqrt lam ∧ ‖v‖ ≤ Real.sqrt Lam * ‖(show E from v)‖ := by
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H p)
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqLam : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
  refine ⟨lam, hlam, Lam, hLam, fun v => ⟨?_, ?_⟩⟩
  · have h1 : lam * ‖(show E from v)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      have hb := (hbnd p (by simp) (show E from v)).1
      rwa [Submission.Distance.chartGram_self_apply (I := I) p (show E from v) (show E from v),
        real_inner_self_eq_norm_sq] at hb
    have h4 : Real.sqrt (lam * ‖(show E from v)‖ ^ 2) ≤ Real.sqrt (‖v‖ ^ 2) :=
      Real.sqrt_le_sqrt h1
    have h5 : Real.sqrt (‖v‖ ^ 2) = ‖v‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
    have h6 : Real.sqrt (‖(show E from v)‖ ^ 2) = ‖(show E from v)‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (show E from v))]
    rw [Real.sqrt_mul hlam.le, h5, h6] at h4
    rw [le_div_iff₀ hsqlam]
    linarith
  · have h1 : ‖v‖ ^ 2 ≤ Lam * ‖(show E from v)‖ ^ 2 := by
      have hb := (hbnd p (by simp) (show E from v)).2
      rwa [Submission.Distance.chartGram_self_apply (I := I) p (show E from v) (show E from v),
        real_inner_self_eq_norm_sq] at hb
    have h4 : Real.sqrt (‖v‖ ^ 2) ≤ Real.sqrt (Lam * ‖(show E from v)‖ ^ 2) :=
      Real.sqrt_le_sqrt h1
    have h5 : Real.sqrt (‖v‖ ^ 2) = ‖v‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
    have h6 : Real.sqrt (‖(show E from v)‖ ^ 2) = ‖(show E from v)‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (show E from v))]
    rw [Real.sqrt_mul hLam.le, h5, h6] at h4
    linarith



/-- **The form of `Metric.mem_closedBall` used for the extraction.** -/
private theorem mem_closedBall_fibre {p : M} {x : TangentSpace I p} {r : ℝ} :
    x ∈ Metric.closedBall (0 : TangentSpace I p) r ↔ ‖x‖ ≤ r := by
  rw [Metric.mem_closedBall, dist_zero_right]

theorem exists_pos_edist_lt_imp_norm_sub_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {v : TangentSpace I p}
    (hv : v ∈ Submission.SegmentDomain.segmentDomain hmet p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : TangentSpace I p,
      w ∈ Submission.SegmentDomain.segmentDomain hmet p →
      Manifold.riemannianEDist I (GExp (cov := cov) hmet p v) (GExp (cov := cov) hmet p w)
        < ENNReal.ofReal δ →
      ‖w - v‖ < ε := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_pos_model_fibre_norm (I := I) p
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  -- the comparison of the fibre norm with the model norm, on differences
  have hdiff : ∀ x y : TangentSpace I p,
      ‖(show E from x) - (show E from y)‖ ≤ ‖x - y‖ / Real.sqrt lam := by
    intro x y
    have h := (hbnd (x - y)).1
    rwa [show (show E from (x - y)) = (show E from x) - (show E from y) from rfl] at h
  by_contra hcon
  push_neg at hcon
  choose w hwmem hwd hwε using fun n : ℕ => hcon (1 / (n + 1)) (by positivity)
  have hdist : ∀ n : ℕ, Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (w n))
      = ENNReal.ofReal ‖w n‖ := fun n =>
    Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor
      (hwmem n)
  have hvdist : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v)
      = ENNReal.ofReal ‖v‖ :=
    Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor hv
  -- the fibre norms are squeezed between `‖v‖ ∓ 1/(n+1)`
  have hfib_hi : ∀ n : ℕ, ‖w n‖ ≤ ‖v‖ + 1 / (n + 1) := by
    intro n
    have h3 : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (w n))
        ≤ ENNReal.ofReal ‖v‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
          (GExp (cov := cov) hmet p (w n)) := by
      calc Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (w n))
          ≤ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v)
            + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
              (GExp (cov := cov) hmet p (w n)) :=
            Manifold.riemannianEDist_triangle (I := I)
              (x := p) (y := GExp (cov := cov) hmet p v) (z := GExp (cov := cov) hmet p (w n))
        _ = ENNReal.ofReal ‖v‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
              (GExp (cov := cov) hmet p (w n)) := by rw [hvdist]
    have h4 : ENNReal.ofReal ‖v‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
          (GExp (cov := cov) hmet p (w n)) < ENNReal.ofReal (‖v‖ + 1 / (n + 1)) := by
      rw [ENNReal.ofReal_add (norm_nonneg v) (by positivity)]
      exact ENNReal.add_lt_add_of_le_of_lt (by simp) le_rfl (hwd n)
    have h2 := lt_of_le_of_lt h3 h4
    rw [hdist n, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h2
    exact le_of_lt h2
  have hfib_lo : ∀ n : ℕ, ‖v‖ - 1 / (n + 1) ≤ ‖w n‖ := by
    intro n
    have h3 : ENNReal.ofReal ‖v‖
        ≤ ENNReal.ofReal ‖w n‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
          (GExp (cov := cov) hmet p (w n)) := by
      calc ENNReal.ofReal ‖v‖ = Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) :=
            hvdist.symm
        _ ≤ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (w n))
            + Manifold.riemannianEDist I (GExp (cov := cov) hmet p (w n))
              (GExp (cov := cov) hmet p v) :=
            Manifold.riemannianEDist_triangle (I := I)
              (x := p) (y := GExp (cov := cov) hmet p (w n)) (z := GExp (cov := cov) hmet p v)
        _ = ENNReal.ofReal ‖w n‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p (w n))
              (GExp (cov := cov) hmet p v) := by rw [hdist n]
        _ = ENNReal.ofReal ‖w n‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
              (GExp (cov := cov) hmet p (w n)) := by
            rw [Manifold.riemannianEDist_comm]
    have h4 : ENNReal.ofReal ‖w n‖ + Manifold.riemannianEDist I (GExp (cov := cov) hmet p v)
          (GExp (cov := cov) hmet p (w n)) < ENNReal.ofReal (‖w n‖ + 1 / (n + 1)) := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
      exact ENNReal.add_lt_add_of_le_of_lt (by simp) le_rfl (hwd n)
    have h2 := lt_of_le_of_lt h3 h4
    have h5 := (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < ‖w n‖ + 1 / (n + 1))).mp h2
    linarith
  -- extract a convergent subsequence in the fibre norm
  haveI hfin : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨wlim, hwlim, φ, hφ, hlimφ⟩ := IsCompact.tendsto_subseq (x := fun n => w n)
    (isCompact_closedBall (0 : TangentSpace I p) (‖v‖ + 1))
    (fun n => by
      rw [mem_closedBall_fibre]
      have h := hfib_hi n
      have h' : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        have h2 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h1 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
        rw [one_div]
        exact inv_le_one_of_one_le₀ h1
      linarith)
  have hnorm_lim : Tendsto (fun n : ℕ => ‖w (φ n)‖) atTop (𝓝 ‖v‖) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ (fun n => hfib_lo (φ n))
      (fun n => hfib_hi (φ n))
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds.sub h1)
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds.add h1)
  have hwnorm : ‖wlim‖ = ‖v‖ := tendsto_nhds_unique hlimφ.norm hnorm_lim
  -- convert the convergence in the fibre norm into convergence in the model norm
  have hlimφ_model : Tendsto (fun n : ℕ => (show E from w (φ n))) atTop (𝓝 (show E from wlim)) := by
    rw [Metric.tendsto_atTop] at hlimφ ⊢
    intro η hη
    obtain ⟨N, hN⟩ := hlimφ (η * Real.sqrt lam) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    calc ‖(show E from w (φ n)) - (show E from wlim)‖ ≤ ‖w (φ n) - wlim‖ / Real.sqrt lam :=
          hdiff _ _
      _ < (η * Real.sqrt lam) / Real.sqrt lam :=
          div_lt_div_of_pos_right h1 hsqlam
      _ = η := by field_simp
  -- the points converge to `GExp p wlim` (model topology on `E`, composed with the continuity)
  have hpt1 : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (w (φ n))) atTop
      (𝓝 (GExp (cov := cov) hmet p wlim)) := by
    have hcont : ContinuousAt (gexpMap (cov := cov) hmet p) (show E from wlim) :=
      (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p wlim).continuousAt
    exact hcont.tendsto.comp hlimφ_model
  -- ... and to `GExp p v`, by the metric description of the neighbourhoods
  have hpt2 : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (w (φ n))) atTop
      (𝓝 (GExp (cov := cov) hmet p v)) := by
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro s hs
    obtain ⟨c, hcpos, hcsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds
      (I := I) (x := GExp (cov := cov) hmet p v) hs
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((φ n : ℝ) + 1))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using h1
    filter_upwards [hlim.eventually (Iio_mem_nhds hcpos)] with n hn
    exact hcsub (lt_of_le_of_lt (hwd (φ n)).le hn)
  have himg : GExp (cov := cov) hmet p wlim = GExp (cov := cov) hmet p v :=
    tendsto_nhds_unique hpt1 hpt2
  -- hence `wlim = v`
  have hunit : ∀ x : TangentSpace I p, ∀ hx : x ≠ 0,
      ‖x‖ • unitOf x hx = x := by
    intro x hx
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hwv : wlim = v := by
    rcases eq_or_ne v 0 with h0 | hv0
    · subst h0
      rw [norm_zero] at hwnorm
      exact norm_eq_zero.mp hwnorm
    · by_contra hne
      have hξ : ‖unitOf v hv0‖ = 1 := unitOf_norm v hv0
      have hwlim0 : wlim ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hwnorm
        exact hv0 (norm_eq_zero.mp hwnorm.symm)
      have hη : ‖unitOf wlim hwlim0‖ = 1 := unitOf_norm wlim hwlim0
      have hunitne : unitOf v hv0 ≠ unitOf wlim hwlim0 := by
        intro hcon
        apply hne
        rw [← hunit v hv0, ← hunit wlim hwlim0, hcon, hwnorm]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have hvec : ‖v‖ • unitOf wlim hwlim0 = wlim := by
        rw [← hwnorm, hunit wlim hwlim0]
      have harg1 : Manifold.riemannianEDist I p
          (GExp (cov := cov) hmet p (‖v‖ • unitOf v hv0)) = ENNReal.ofReal ‖v‖ := by
        rw [hunit v hv0]; exact hvdist
      have harg2 : Manifold.riemannianEDist I p
          (GExp (cov := cov) hmet p (‖v‖ • unitOf wlim hwlim0)) = ENNReal.ofReal ‖v‖ := by
        rw [hvec, himg]; exact hvdist
      have harg3 : GExp (cov := cov) hmet p (‖v‖ • unitOf v hv0)
          = GExp (cov := cov) hmet p (‖v‖ • unitOf wlim hwlim0) := by
        rw [hunit v hv0, hvec]
        exact himg.symm
      have hcut := Submission.SegmentDomain.cutTime_le_of_meet (cov := cov) hmet htor
        (p := p) (ξ := unitOf v hv0)
        (η := unitOf wlim hwlim0) hξ hη hunitne hvpos harg1 harg2 harg3
      rcases (Submission.SegmentDomain.mem_segmentDomain_iff (I := I) hmet p v).mp hv with
        h0 | ⟨hne0, hlt⟩
      · exact absurd h0 hv0
      · exact absurd hcut (not_le.mpr hlt)
  -- contradiction with the assumed lower bound
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hwv ▸ hlimφ) ε hε
  have hN' : ‖w (φ N) - v‖ < ε := by
    have h := hN N le_rfl
    rwa [dist_eq_norm] at h
  exact absurd hN' (not_lt.mpr (hwε (φ N)))

end

end Submission.XuMain
