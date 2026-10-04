import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.HingeClosed
import Submission.GSConcaveGen
import Submission.GSConcaveSeg
import Submission.GSFar
import Submission.GSNoCrit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.GlobalExp Submission.HingeGlobal Submission.HingeKey
  Submission.HingeClosed Submission.HopfRinow

/-- **The direction from `y` towards the far point `q` is an ascent direction for `d(p,·)`.**

Let `p, q` be a diameter pair of diameter `D ∈ (π/2, π)` and let `y` be a point with
`π/2 < d(p,y) < D`.  If `ξ` is a unit direction from `y` along which the minimising geodesic of
length `s = d(y,q) > 0` reaches `q`, then every shortest direction `u` from `y` to `p` makes an
obtuse angle with `ξ`: `⟪ξ, u⟫ < 0`.

This is the quantitative form of "`q` is a farthest point from `p`".  The proof is the classical one
(Grove–Shiohama, step 2):

* the minimising geodesic `G` from `y` to `q` has both endpoints at distance `> π/2` from `p`
  (`d(p,y) > π/2` and `d(p,q) = D > π/2`), hence every point of it is at distance `≥ π/2` from `p`
  (`GSConcaveSeg.far_of_far_endpoints`);
* therefore `t ↦ d(p, G t)` is concave on `[0,s]` (`GSConcaveSeg.concaveOn_dist_geodCurve`), so it
  dominates the chord: `d(p, G t) ≥ d(p,y) + α t` with `α = (D - d(p,y))/s > 0`;
* on the other hand the hinge comparison at `y` with the two unit directions `ξ` and a shortest
  direction `u` to `p` gives `d(p, G t) ≤ modelDist1 θ t r`, whose right derivative at `t = 0` is
  `-cos θ`;
* comparing the two bounds gives `0 < α ≤ -cos θ = -⟪ξ,u⟫`. -/
theorem geodDir_to_q_isAscentAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D s : ℝ}
    (hDGt : Real.pi / 2 < D) (hDLt : D < Real.pi)
    (hdiam : ∀ r t : M, Manifold.riemannianEDist I r t ≤ ENNReal.ofReal D)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {y : M} {ξ : TangentSpace I y}
    (hs : 0 < s) (hξ : ‖ξ‖ = 1)
    (hq : q = Submission.GlobalExp.GExp (cov := cov) hmet y (s • ξ))
    (hsd : Manifold.riemannianEDist I y q = ENNReal.ofReal s)
    (hypfar : Real.pi / 2 < Work.Diff.C.rdist (I := I) (M := M) p y)
    (hyplt : Work.Diff.C.rdist (I := I) (M := M) p y < D) :
    Submission.GSField.IsAscentAt hmet p y ξ := by
  intro r u hr hu hpG hd
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDGt.le
  have hDπ : D ≤ Real.pi := hDLt.le
  -- ## the polar distance `f = d(p,y)`
  set f : ℝ := (Manifold.riemannianEDist I p y).toReal with hf_def
  have hfgt : Real.pi / 2 < f := by
    rw [hf_def]; exact hypfar
  have hflt : f < D := by
    rw [hf_def]; exact hyplt
  have hfpos : 0 < f := lt_trans (by linarith [Real.pi_pos]) hfgt
  have hfnn : 0 ≤ f := hfpos.le
  have hfπ : f < Real.pi := lt_of_lt_of_le hflt hDπ
  have hffin : Manifold.riemannianEDist I p y ≠ ⊤ := by
    intro htop
    rw [htop] at hf_def
    simp at hf_def
    rw [hf_def] at hfgt
    linarith [Real.pi_pos]
  have hfeq : Manifold.riemannianEDist I p y = ENNReal.ofReal f :=
    (ENNReal.ofReal_toReal hffin).symm
  -- ## the shortest direction `u` to `p` (at distance `r`)
  have hrf : r = f := by
    have h2 : ENNReal.ofReal r = ENNReal.ofReal f := by
      rw [← hd, Manifold.riemannianEDist_comm, hfeq]
    exact (ENNReal.ofReal_eq_ofReal_iff hr hfnn).mp h2
  have hrpos : 0 < r := by rw [hrf]; exact hfpos
  have hrπ : r < Real.pi := by rw [hrf]; exact hfπ
  -- ## the minimising geodesic from `y` to `q` in the direction `ξ`
  set G : ℝ → M := geodCurve (cov := cov) hmet s hs.le y ξ hξ with hGdef
  have hG0 : G 0 = y := (geodCurve_spec (cov := cov) hmet s hs.le y ξ hξ).1
  have hGs : G s = q := by
    rw [hGdef]
    rw [← GExp_eq_geodCurve (cov := cov) hmet (x := y) (u := ξ) hξ (T := s) hs.le
      (r := s) hs.le le_rfl]
    exact hq.symm
  have hmin : Manifold.riemannianEDist I y (G s) = ENNReal.ofReal s := by rw [hGs]; exact hsd
  have hsleD : s ≤ D :=
    (ENNReal.ofReal_le_ofReal_iff hDnn).mp (hsd ▸ hdiam y q)
  have hsπ : s ≤ Real.pi := le_trans hsleD hDπ
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) s, ∀ b ∈ Set.Icc (0:ℝ) s, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := s) hs.le hξ (s := s) hs.le
      le_rfl hmin
    intro a ha b hb hab
    exact h a ha b hb hab
  have hGcont : ContinuousOn G (Set.Icc (0:ℝ) s) := by
    have hδ := geodDelta_pos (cov := cov) hmet
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞ G
        (Set.Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet)) := by
      rw [hGdef]; exact (geodCurve_spec (cov := cov) hmet s hs.le y ξ hξ).2.2.1
    have hsub' : Set.Icc (0:ℝ) s ⊆
        Set.Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet) := by
      intro t ht; exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
    exact ((hsm.mono hsub').continuousOn)
  have hcontD : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p (G t)).toReal)
      (Set.Icc (0:ℝ) s) := by
    have h1 : ContinuousOn (fun t : ℝ => Manifold.riemannianEDist I p (G t))
        (Set.Icc (0:ℝ) s) :=
      ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p).continuousOn).comp
        hGcont (fun t _ => Set.mem_univ _)
    have h2 : ∀ t ∈ Set.Icc (0:ℝ) s, Manifold.riemannianEDist I p (G t) ≠ ⊤ := fun t ht =>
      (lt_of_le_of_lt (hdiam p (G t)) ENNReal.ofReal_lt_top).ne
    exact ENNReal.continuousOn_toReal.comp h1 (fun t ht => h2 t ht)
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) s, (Manifold.riemannianEDist I p (G t)).toReal ≤ D := by
    intro t ht
    calc (Manifold.riemannianEDist I p (G t)).toReal ≤ (ENNReal.ofReal D).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam p (G t))
      _ = D := ENNReal.toReal_ofReal hDnn
  have hfar0 : Real.pi / 2 < (Manifold.riemannianEDist I p (G 0)).toReal := by
    rw [hG0]; exact hfgt
  have hfars : Real.pi / 2 < (Manifold.riemannianEDist I p (G s)).toReal := by
    rw [hGs, hpq, ENNReal.toReal_ofReal hDnn]; exact hDGt
  have hfar := Submission.GSConcaveSeg.far_of_far_endpoints (cov := cov) hmet htor hpinch hξ
    hs.le hsπ hDπ hmin hcontD hbd hfar0 hfars
  have hltp : ∀ t ∈ Set.Icc (0:ℝ) s, (Manifold.riemannianEDist I p (G t)).toReal < Real.pi :=
    fun t ht => lt_of_le_of_lt (hbd t ht) hDLt
  have hconc := Submission.GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi
    (cov := cov) hmet htor hpinch (p := p) (T := s) (q := y) hξ hs.le hmin hcontD hfar hltp
  set F : ℝ → ℝ := fun t => (Manifold.riemannianEDist I p (G t)).toReal with hFdef
  have hF0 : F 0 = f := by simp only [hFdef, hG0, hf_def]
  have hFs : F s = D := by simp only [hFdef, hGs, hpq, ENNReal.toReal_ofReal hDnn]
  have hchord : ∀ w ∈ Set.Icc (0:ℝ) s, f + (w / s) * (D - f) ≤ F w := by
    intro w hw
    have hw1 : w / s ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hw.1 hs.le, (div_le_one hs).mpr hw.2⟩
    have h := hconc.2 (Set.mem_Icc.mpr ⟨le_refl 0, hs.le⟩) (Set.mem_Icc.mpr ⟨hs.le, le_refl s⟩)
      (by linarith [hw1.2] : (0:ℝ) ≤ 1 - w / s) hw1.1 (by ring : (1:ℝ) - w / s + w / s = 1)
    have harg : (1 - w / s) • (0:ℝ) + (w / s) • s = w := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hs.ne']
    rw [harg] at h
    simp only [smul_eq_mul, hF0, hFs] at h
    have he : (1 - w / s) * f + (w / s) * D = f + (w / s) * (D - f) := by ring
    linarith [h, he.le, he.ge]
  set α : ℝ := (D - f) / s with hαdef
  have hαpos : 0 < α := by rw [hαdef]; exact div_pos (by linarith) hs
  have hlin : ∀ w ∈ Set.Icc (0:ℝ) s, f + α * w ≤ F w := by
    intro w hw
    have h := hchord w hw
    have he : (w / s) * (D - f) = α * w := by rw [hαdef]; field_simp
    linarith [h, he.le, he.ge]
  -- ## the hinge comparison at `y`
  set δ : ℝ := min s (Real.pi - r) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hs (by linarith [hrπ])
  have hkey : ∀ t ∈ Set.Ioo (0:ℝ) δ,
      α ≤ (modelDist1 (hingeAngle ξ u) t r - r) / t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hts : t < s := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htπ : t + r < Real.pi := by
      have h := lt_of_lt_of_le ht.2 (min_le_right s (Real.pi - r))
      linarith
    have htm : t ∈ Set.Icc (0:ℝ) s := ⟨ht0.le, hts.le⟩
    have hxt : Manifold.riemannianEDist I y (GExp (cov := cov) hmet y (t • ξ))
        = ENNReal.ofReal t := by
      have h := hsub 0 ⟨le_refl 0, hs.le⟩ t htm ht0.le
      rw [hG0, sub_zero] at h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := y) (u := ξ) hξ (T := s) hs.le
        (r := t) ht0.le hts.le]
      exact h
    have hcmp := Submission.HingeClosed.gcompHolds_pi_le (cov := cov) hmet htor hpinch
      (z := y) ht0 hrpos htπ.le hξ hu hxt (by rw [← hpG]; exact hd)
    have h1 : F t ≤ modelDist1 (hingeAngle ξ u) t r := by
      have h := hcmp
      rw [Manifold.riemannianEDist_comm, ← hpG] at h
      have hfin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet y (t • ξ)) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam p _) ENNReal.ofReal_lt_top).ne
      have h2 : (Manifold.riemannianEDist I p (GExp (cov := cov) hmet y (t • ξ))).toReal
          ≤ modelDist1 (hingeAngle ξ u) t r := by
        rw [← ENNReal.ofReal_toReal hfin] at h
        exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := y) (u := ξ) hξ (T := s) hs.le
        (r := t) ht0.le hts.le] at h2
      simp only [hFdef, hGdef]
      exact h2
    have h2' := hlin t htm
    have h3 : α * t ≤ modelDist1 (hingeAngle ξ u) t r - r := by
      have h4 : f + α * t ≤ modelDist1 (hingeAngle ξ u) t r := le_trans h2' h1
      rw [← hrf] at h4
      linarith
    rw [le_div_iff₀ ht0]
    linarith
  have htend : Tendsto (fun t : ℝ =>
      (modelDist1 (hingeAngle ξ u) t r - r) / t) (𝓝[>] (0:ℝ))
      (𝓝 (-Real.cos (hingeAngle ξ u))) := by
    have h := Submission.GSFar.tendsto_arccos_model_sub_div r (hingeAngle ξ u) hrpos hrπ
    simpa only [modelDist1_apply] using h
  have hbound : α ≤ -Real.cos (hingeAngle ξ u) :=
    ge_of_tendsto htend (Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioo (0:ℝ) δ, Ioo_mem_nhdsGT hδpos, fun t ht => hkey t ht⟩)
  have hcos : Real.cos (hingeAngle ξ u) = inner ℝ ξ u :=
    Submission.HingeGlobal.cos_hingeAngle hξ hu
  rw [hcos] at hbound
  linarith

end Work.Diff.Dim2
