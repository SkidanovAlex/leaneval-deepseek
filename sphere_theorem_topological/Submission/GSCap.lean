import Submission.GSChartBall
import Submission.GSStep1
import Submission.GSCapMono
import Submission.Commons.Topology.Metric.radial_homeo_closedBall_of_continuousOn
import Submission.Commons.Topology.Compact.exists_superlevel_subset_of_unique_max

/-!
# The cap `{d(p,·) ≥ D - ε}` is a disk

Let `(p,q)` be a diameter pair of a compact Riemannian manifold with `sec ∈ (1,4]` and
`π/2 < D = d(p,q) ≤ 2π/3`.  Then for some `ε > 0` the *cap* `{d(p,·) ≥ D - ε}` around the maximum
`q` is homeomorphic to the standard disk `Dⁿ`, with the level set `{d(p,·) = D - ε}` going to the
boundary sphere.

Proof: choose `ε` so small that the cap is contained in the exponential chart at `q` of radius `α`
(possible because `q` is the *unique* maximiser of `d(p,·)`, `GSCritical.step1_diameter_unique`).
In the chart, the cap corresponds to the superlevel set `S = {u : ‖u‖ ≤ α, h u ≥ D - ε}` of
`h u = d(p, GExp_q u)`, and:

* `h` is continuous on the chart ball (`GExp_q` agrees with the smooth `expMap` there);
* `h 0 = D` is the maximum, attained only at `0` (uniqueness of the maximiser);
* `h < D - ε` on the sphere of radius `α` (the cap is inside the chart ball);
* along every ray, `t ↦ h (t • u)` is *strictly decreasing* on the part where `h ≥ D - ε`
  (`Submission.GSCapMono.strictAntiOn_dist_geodCurve_of_max`: concavity of `d(p,·)` along the
  minimising geodesic from `q`, plus uniqueness of the maximiser).

Then the abstract radial homeomorphism
`Commons.Topology.Metric.radial_homeo_closedBall_of_continuousOn` turns `S` into the unit ball, and
the chart transfers it back to `M`.  (The radial lemma asks for `h < D` *everywhere* off the origin;
since `GExp_q` is not injective globally, we apply it to `h' u = h u - max 0 (‖u‖ - α)`, which agrees
with `h` on the chart ball and is `< D` outside it.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist
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

namespace Submission.GSCap

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The cap around the maximum is a disk.** -/
theorem exists_homeo_cap
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D - Real.pi / 2 ∧ ∃ e :
        ↥{y : M | D - ε ≤ (Manifold.riemannianEDist I p y).toReal} ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1,
      e ⁻¹' (Metric.sphere (0 : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
        = {y : ↥{y : M | D - ε ≤ (Manifold.riemannianEDist I p y).toReal} |
            (Manifold.riemannianEDist I p (y : M)).toReal = D - ε} := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI : FiniteDimensional ℝ (TangentSpace I q) := ‹FiniteDimensional ℝ E›
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  set f : M → ℝ := fun y => (Manifold.riemannianEDist I p y).toReal with hfdef
  have hfcont : Continuous f := by
    show Continuous fun y : M => (Manifold.riemannianEDist I p y).toReal
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 hfin
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hfq : f q = D := by
    show (Manifold.riemannianEDist I p q).toReal = D
    rw [hpq, ENNReal.toReal_ofReal hDnn]
  -- the maximum of `f` is uniquely attained at `q`
  have hmaxq : ∀ y : M, y ≠ q → f y < f q := by
    intro y hy
    rw [hfq]
    have hle : f y ≤ D := by
      show (Manifold.riemannianEDist I p y).toReal ≤ D
      calc (Manifold.riemannianEDist I p y).toReal
          ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam p y)
        _ = D := ENNReal.toReal_ofReal hDnn
    rcases eq_or_lt_of_le hle with h | h
    · exfalso
      have hyD : Manifold.riemannianEDist I p y = ENNReal.ofReal D := by
        rw [← ENNReal.ofReal_toReal (hfin y),
          show (Manifold.riemannianEDist I p y).toReal = D from h]
      exact (Submission.GSStep1.step1_diameter_unique_of_lt_pi (cov := cov) hmet htor hpinch
        hdiam hDgt hDlt hpq hyD (Ne.symm hy)).elim
    · exact h
  -- the chart radius
  obtain ⟨ε₁, hε₁, hchart⟩ :=
    Submission.GSChartBall.exists_pos_homeo_closedBall_of_radius (cov := cov) hmet htor q
  set α : ℝ := ε₁ / 2 with hαdef
  have hαpos : 0 < α := by rw [hαdef]; linarith
  have hαε₁ : α < ε₁ := by rw [hαdef]; linarith
  obtain ⟨hdist, e, he⟩ := hchart α ⟨hαpos, hαε₁⟩
  have hmem_ball : ∀ u : TangentSpace I q, u ∈ Metric.closedBall (0 : TangentSpace I q) α ↔
      ‖u‖ ≤ α := fun u => by rw [Metric.mem_closedBall, dist_zero_right]
  -- the function whose superlevel set is the cap
  set h : TangentSpace I q → ℝ := fun u => f (GExp (cov := cov) hmet q u) with hhdef
  have hcont_h : ContinuousOn h (Metric.closedBall (0 : TangentSpace I q) α) := by
    rw [continuousOn_iff_continuous_restrict]
    have h2 : Continuous (fun u : Metric.closedBall (0 : TangentSpace I q) α =>
        f ((e u : {y : M // Manifold.riemannianEDist I q y ≤ ENNReal.ofReal α}) : M)) :=
      (hfcont.comp continuous_subtype_val).comp e.continuous
    refine h2.congr (fun u => ?_)
    show f ((e u : {y : M // Manifold.riemannianEDist I q y ≤ ENNReal.ofReal α}) : M)
      = h (u : TangentSpace I q)
    rw [he u]
  have hh0_h : h 0 = D := by
    show f (GExp (cov := cov) hmet q 0) = D
    rw [GExp_zero]; exact hfq
  have hhle_h : ∀ u : TangentSpace I q, h u ≤ D := by
    intro u
    show (Manifold.riemannianEDist I p (GExp (cov := cov) hmet q u)).toReal ≤ D
    calc (Manifold.riemannianEDist I p (GExp (cov := cov) hmet q u)).toReal
        ≤ (ENNReal.ofReal D).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam p (GExp (cov := cov) hmet q u))
      _ = D := ENNReal.toReal_ofReal hDnn
  have hmax_ball : ∀ u : TangentSpace I q, ‖u‖ ≤ α → u ≠ 0 → h u < D := by
    intro u hu hu0
    have hne : GExp (cov := cov) hmet q u ≠ q := by
      intro hG
      have hd := hdist u hu
      rw [hG, Manifold.riemannianEDist_self] at hd
      have hz : ‖u‖ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hd.symm) (norm_nonneg u)
      exact hu0 (norm_eq_zero.mp hz)
    have := hmaxq _ hne
    rw [hfq] at this
    exact this
  -- the cap is inside the chart
  obtain ⟨δ, hδ, hδsub⟩ :=
    Commons.Topology.Compact.exists_superlevel_subset_of_unique_max (X := M) hfcont hmaxq
      (U := {y : M | Manifold.riemannianEDist I q y < ENNReal.ofReal α})
      (isOpen_Iio.preimage (Submission.HopfRinow.continuous_riemannianEDist_left (I := I) q))
      (by
        show Manifold.riemannianEDist I q q < ENNReal.ofReal α
        rw [Manifold.riemannianEDist_self]
        exact ENNReal.ofReal_pos.mpr hαpos)
  set ε : ℝ := min δ ((D - Real.pi / 2) / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min hδ (by linarith)
  have hεδ : ε ≤ δ := by rw [hεdef]; exact min_le_left _ _
  have hεlt : ε < D - Real.pi / 2 := by
    rw [hεdef]; have := min_le_right δ ((D - Real.pi / 2) / 2); linarith
  have hhout_h : ∀ u : TangentSpace I q, ‖u‖ = α → h u < D - ε := by
    intro u hu
    have hnotin : ¬ (Manifold.riemannianEDist I q (GExp (cov := cov) hmet q u)
        < ENNReal.ofReal α) := by
      rw [hdist u (le_of_eq hu), hu]
      exact lt_irrefl _
    have hlt : f (GExp (cov := cov) hmet q u) < D - δ := by
      by_contra hcon
      have hfh : f q - δ ≤ f (GExp (cov := cov) hmet q u) := by
        rw [hfq]; exact not_lt.mp hcon
      exact hnotin (hδsub _ hfh)
    show f (GExp (cov := cov) hmet q u) < D - ε
    linarith
  -- strict monotonicity along the rays
  have hhmono : ∀ u : TangentSpace I q, ‖u‖ = 1 → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ α →
      D - ε ≤ h (t₂ • u) → h (t₁ • u) > h (t₂ • u) := by
    intro u hu t₁ t₂ ht₁ ht₁₂ ht₂α hmem
    have ht₂pos : 0 < t₂ := lt_of_le_of_lt ht₁ ht₁₂
    have hnorm : ‖t₂ • u‖ = t₂ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₂pos.le, hu, mul_one]
    have hmem' : D - ε ≤ f (GExp (cov := cov) hmet q (t₂ • u)) := hmem
    have hmin' : Manifold.riemannianEDist I q
        ((geodCurve (cov := cov) hmet t₂ ht₂pos.le q u hu : ℝ → M) t₂)
        = ENNReal.ofReal t₂ := by
      have h1 : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q (t₂ • u))
          = ENNReal.ofReal t₂ := by
        rw [hdist (t₂ • u) (hnorm.trans_le ht₂α), hnorm]
      rwa [GExp_eq_geodCurve (cov := cov) hmet (x := q) (u := u) hu (T := t₂) ht₂pos.le
        (r := t₂) ht₂pos.le le_rfl] at h1
    have hcont' : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p
        ((geodCurve (cov := cov) hmet t₂ ht₂pos.le q u hu : ℝ → M) t)).toReal)
        (Set.Icc 0 t₂) := by
      have hsub : ∀ t ∈ Set.Icc (0:ℝ) t₂, t • u ∈ Metric.closedBall (0 : TangentSpace I q) α := by
        intro t ht
        rw [hmem_ball, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hu, mul_one]
        exact le_trans ht.2 ht₂α
      have h1 : ContinuousOn (fun t : ℝ => f (GExp (cov := cov) hmet q (t • u)))
          (Set.Icc 0 t₂) :=
        hcont_h.comp (((continuous_id : Continuous fun t : ℝ => t).smul
          (continuous_const : Continuous fun _ : ℝ => u)).continuousOn) hsub
      refine h1.congr (fun t ht => ?_)
      show (Manifold.riemannianEDist I p
            ((geodCurve (cov := cov) hmet t₂ ht₂pos.le q u hu : ℝ → M) t)).toReal
        = f (GExp (cov := cov) hmet q (t • u))
      rw [← GExp_eq_geodCurve (cov := cov) hmet (x := q) (u := u) hu (T := t₂) ht₂pos.le
        (r := t) ht.1 ht.2]
    have hfarT : Real.pi / 2 < (Manifold.riemannianEDist I p
        ((geodCurve (cov := cov) hmet t₂ ht₂pos.le q u hu : ℝ → M) t₂)).toReal := by
      have h3 := hmem'
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := q) (u := u) hu (T := t₂) ht₂pos.le
        (r := t₂) ht₂pos.le le_rfl] at h3
      linarith
    have hne : (geodCurve (cov := cov) hmet t₂ ht₂pos.le q u hu) t₂ ≠ q := by
      intro hq
      have hd := hmin'
      rw [hq] at hd
      have hzero : Manifold.riemannianEDist I q q = 0 := Manifold.riemannianEDist_self
      rw [hzero] at hd
      have ht2le : t₂ ≤ 0 := ENNReal.ofReal_eq_zero.mp hd.symm
      linarith
    have hmono' := Submission.GSCapMono.strictAntiOn_dist_geodCurve_of_max (cov := cov) hmet htor
      hpinch hu hdiam hDgt hDlt hpq ht₂pos.le hmin' hcont' hfarT hne
    have h2 : f (GExp (cov := cov) hmet q (t₁ • u)) > f (GExp (cov := cov) hmet q (t₂ • u)) := by
      have h3 := hmono' (a := t₁) (b := t₂) ⟨ht₁, ht₁₂.le⟩ ⟨le_of_lt ht₂pos, le_refl t₂⟩ ht₁₂
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := q) (u := u) hu (T := t₂) ht₂pos.le
        (r := t₁) ht₁ ht₁₂.le,
        GExp_eq_geodCurve (cov := cov) hmet (x := q) (u := u) hu (T := t₂) ht₂pos.le
        (r := t₂) ht₂pos.le le_rfl]
      exact h3
    exact h2
  -- the truncated function, which is `< D` off the origin on all of `V`
  set h' : TangentSpace I q → ℝ := fun u => h u - max 0 (‖u‖ - α) with hh'def
  have h'h : ∀ u : TangentSpace I q, ‖u‖ ≤ α → h' u = h u := by
    intro u hu
    show h u - max 0 (‖u‖ - α) = h u
    rw [max_eq_left (by linarith)]; ring
  have h'cont : ContinuousOn h' (Metric.closedBall (0 : TangentSpace I q) α) :=
    hcont_h.congr (fun u hu => h'h u ((hmem_ball u).mp hu))
  have h'h0 : h' 0 = D := by
    rw [h'h 0 (by simpa using hαpos.le)]; exact hh0_h
  have h'hle : ∀ u : TangentSpace I q, h' u ≤ D := by
    intro u
    show h u - max 0 (‖u‖ - α) ≤ D
    linarith [hhle_h u, le_max_left (0:ℝ) (‖u‖ - α)]
  have h'hmax : ∀ u : TangentSpace I q, u ≠ 0 → h' u < D := by
    intro u hu
    by_cases hcase : ‖u‖ ≤ α
    · rw [h'h u hcase]; exact hmax_ball u hcase hu
    · have hlt : 0 < max 0 (‖u‖ - α) := lt_max_of_lt_right (by linarith [not_le.mp hcase])
      show h u - max 0 (‖u‖ - α) < D
      linarith [hhle_h u]
  have h'hout : ∀ u : TangentSpace I q, ‖u‖ = α → h' u < D - ε := by
    intro u hu
    rw [h'h u (le_of_eq hu)]; exact hhout_h u hu
  have h'hmono : ∀ u : TangentSpace I q, ‖u‖ = 1 → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ α →
      D - ε ≤ h' (t₂ • u) → h' (t₁ • u) > h' (t₂ • u) := by
    intro u hu t₁ t₂ ht₁ ht₁₂ ht₂α hmem
    have ht₂pos : 0 < t₂ := lt_of_le_of_lt ht₁ ht₁₂
    have h1 : ‖t₁ • u‖ ≤ α := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₁, hu, mul_one]; linarith
    have h2 : ‖t₂ • u‖ ≤ α := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht₂pos), hu, mul_one]
      exact ht₂α
    have hmem'' : D - ε ≤ h (t₂ • u) := by
      rw [← h'h (t₂ • u) h2]; exact hmem
    have hgoal := hhmono u hu t₁ t₂ ht₁ ht₁₂ ht₂α hmem''
    rw [h'h (t₁ • u) h1, h'h (t₂ • u) h2]
    exact hgoal
  -- the abstract radial homeomorphism
  obtain ⟨Φ, hΦ⟩ := Commons.Topology.Metric.radial_homeo_closedBall_of_continuousOn
    (V := TangentSpace I q) (h := h') hαpos hεpos h'cont h'h0 h'hle h'hmax h'hout h'hmono
  -- transfer back to `M` through the chart
  set D1 : Set M := {y : M | Manifold.riemannianEDist I q y ≤ ENNReal.ofReal α} with hD1def
  set Cap : Set M := {y : M | D - ε ≤ f y} with hCapdef
  have hCapsub : Cap ⊆ D1 := by
    intro y hy
    have hy' : D - ε ≤ f y := by rw [hCapdef] at hy; exact hy
    by_contra hcon
    have hlt : ENNReal.ofReal α < Manifold.riemannianEDist I q y := not_le.mp hcon
    have hmem : Manifold.riemannianEDist I q y < ENNReal.ofReal α :=
      hδsub y (by rw [hfq]; linarith [hεδ, hy'])
    exact absurd hmem (not_lt.mpr (le_of_lt hlt))
  have hGsymm : ∀ z : D1, GExp (cov := cov) hmet q (e.symm z : TangentSpace I q) = (z : M) := by
    intro z
    have h1 := he (e.symm z)
    rw [Homeomorph.apply_symm_apply] at h1
    rw [← h1]
  have hiff : ∀ z : D1, (z : M) ∈ Cap ↔
      D - ε ≤ h' (e.symm z : TangentSpace I q) := by
    intro z
    have hh : h' (e.symm z : TangentSpace I q) = f (z : M) := by
      have h2 : ‖(e.symm z : TangentSpace I q)‖ ≤ α := (hmem_ball _).mp (e.symm z).2
      rw [h'h _ h2]
      show f (GExp (cov := cov) hmet q (e.symm z : TangentSpace I q)) = f (z : M)
      rw [hGsymm]
    rw [hh]
    exact Iff.rfl
  let eS : {u : ↥(Metric.closedBall (0 : TangentSpace I q) α) // D - ε ≤ h' (u : TangentSpace I q)}
      ≃ₜ {u : TangentSpace I q // ‖u‖ ≤ α ∧ D - ε ≤ h' u} :=
    { toFun := fun u => ⟨(u.1 : TangentSpace I q),
        (hmem_ball (u.1 : TangentSpace I q)).mp u.1.2, u.2⟩
      invFun := fun u => ⟨⟨(u : TangentSpace I q),
        (hmem_ball (u : TangentSpace I q)).mpr u.2.1⟩, u.2.2⟩
      left_inv := fun u => Subtype.ext rfl
      right_inv := fun u => Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val _) _ }
  let nestC := Submission.GSHalfDisk.subtypeNestHomeomorph (s := D1) (t := Cap) hCapsub
  let eCap : ↥Cap ≃ₜ {u : TangentSpace I q // ‖u‖ ≤ α ∧ D - ε ≤ h' u} :=
    nestC.symm.trans (((e.symm).subtype (p := fun z : D1 => (z : M) ∈ Cap)
      (q := fun u : ↥(Metric.closedBall (0 : TangentSpace I q) α) =>
        D - ε ≤ h' (u : TangentSpace I q)) hiff).trans eS)
  have heCapval : ∀ y : ↥Cap, h' (eCap y : TangentSpace I q) = f (y : M) := by
    intro y
    have h1 : (eCap y : TangentSpace I q)
        = (e.symm ⟨(y : M), hCapsub y.2⟩ : TangentSpace I q) := rfl
    rw [h1]
    have h2 : ‖(e.symm ⟨(y : M), hCapsub y.2⟩ : TangentSpace I q)‖ ≤ α :=
      (hmem_ball _).mp (e.symm ⟨(y : M), hCapsub y.2⟩).2
    rw [h'h _ h2]
    show f (GExp (cov := cov) hmet q (e.symm ⟨(y : M), hCapsub y.2⟩ : TangentSpace I q))
      = f (y : M)
    rw [hGsymm]
  -- transport the unit ball to the Euclidean model and assemble
  obtain ⟨eE, heE⟩ := Commons.Topology.Metric.closedBall_homeo_euclidean_pair
    (V := TangentSpace I q) (n := Module.finrank ℝ E) (r := 1) rfl (by norm_num)
  have hsphereV : ∀ u : Metric.closedBall (0 : TangentSpace I q) 1,
      u ∈ Metric.sphere (0 : Metric.closedBall (0 : TangentSpace I q) 1) 1 ↔
        ‖(u : TangentSpace I q)‖ = 1 := by
    intro u
    rw [Metric.mem_sphere, Subtype.dist_eq, dist_eq_norm]; simp
  refine ⟨ε, hεpos, hεlt, eCap.trans (Φ.trans eE), ?_⟩
  ext y
  rw [Set.mem_preimage, Set.mem_ofPred_eq]
  have h1 : ((eCap.trans (Φ.trans eE)) y : Metric.closedBall (0 : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E))) 1) = eE (Φ (eCap y)) := rfl
  rw [h1]
  have h2 : (eE (Φ (eCap y)) ∈ Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      ↔ ‖(eE (Φ (eCap y)) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ = 1 := by
    rw [Metric.mem_sphere, Subtype.dist_eq, dist_eq_norm]; simp
  rw [h2, ← heE (Φ (eCap y)), ← hsphereV (Φ (eCap y))]
  rw [show (Φ (eCap y) ∈ Metric.sphere (0 : Metric.closedBall
      (0 : TangentSpace I q) 1) 1)
      ↔ h' (eCap y : TangentSpace I q) = D - ε from
    (Set.ext_iff.mp hΦ (eCap y)).trans (by simp only [Set.mem_ofPred_eq])]
  rw [heCapval y]

end

end Submission.GSCap
