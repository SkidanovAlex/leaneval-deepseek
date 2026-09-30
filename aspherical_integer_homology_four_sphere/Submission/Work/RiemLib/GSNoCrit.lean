import Submission.Work.RiemLib.GSConcaveSeg
import Submission.Work.RiemLib.GSFar
import Submission.Work.RiemLib.GSStep1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Grove–Shiohama step 2, case 2: `d(p,·)` has no critical points at distance `> π/2`

Let `p, q` be a diameter pair of a compact Riemannian manifold with `sec ∈ (1,4]`, of diameter
`D = d(p,q) ≤ 2π/3` (the *restricted* Grove–Shiohama range, which is what the formalised Toponogov
covers).  Let `x` be a point which is *not* a maximiser of `d(p,·)` (`d(p,x) < D`) and is at
distance `> π/2` from `p`.  Then `x` is not a critical point of `d(p,·)` in the sense of
`GSCritical.IsCrit`.

The proof is the classical one:

* the minimising geodesic `γ` from `x` to `q` has both endpoints at distance `> π/2` from `p`
  (namely `d(p,x) > π/2` and `d(p,q) = D > π/2`), hence by `GSConcaveSeg.far_of_far_endpoints`
  *every* point of it is at distance `≥ π/2` from `p`;
* therefore `t ↦ d(p,γ t)` is concave on `[0,s]` (`GSConcaveSeg.concaveOn_dist_geodCurve`), so it
  dominates the chord: `d(p,γ t) ≥ d(p,x) + α t` with `α = (D - d(p,x))/s > 0`;
* on the other hand the hinge comparison at `x` with the two unit directions `γ'(0)` and a shortest
  direction `u` to `p` gives `d(p,γ t) ≤ modelDist1 θ t r`, whose right derivative at `t = 0` is
  `-cos θ`; comparing the two bounds gives `α ≤ -cos θ ≤ 0` — contradiction.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece
open Submission.HingeClosed
open Submission.HopfRinow
open Submission.GSCritical

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSNoCrit

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Grove–Shiohama step 2, case 2.** -/
theorem no_crit_far
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hxlt : Manifold.riemannianEDist I p x < ENNReal.ofReal D)
    (hxp : Real.pi / 2 < (Manifold.riemannianEDist I p x).toReal) :
    ¬ Submission.GSCritical.IsCrit hmet p x := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hDπ : D ≤ Real.pi := hDlt.le
  -- the numbers `r = d(p,x)`, `s = d(x,q)`
  have hxfin : Manifold.riemannianEDist I p x ≠ ⊤ :=
    (lt_of_lt_of_le hxlt ENNReal.ofReal_lt_top.le).ne
  set r : ℝ := (Manifold.riemannianEDist I p x).toReal with hrdef
  have hxr : Manifold.riemannianEDist I p x = ENNReal.ofReal r :=
    (ENNReal.ofReal_toReal hxfin).symm
  have hrgt : Real.pi / 2 < r := by rw [hrdef]; exact hxp
  have hrnn : 0 ≤ r := ENNReal.toReal_nonneg
  have hrD : r < D := by
    have h := (ENNReal.toReal_lt_toReal hxfin ENNReal.ofReal_ne_top).mpr hxlt
    rw [ENNReal.toReal_ofReal hDnn] at h
    exact h
  have hrπ : r < Real.pi := lt_of_lt_of_le hrD hDπ
  -- the minimising geodesic from `x` to `q`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x q
  set s : ℝ := ‖v‖ with hsdef
  have hxs : Manifold.riemannianEDist I x q = ENNReal.ofReal s := hvd
  have hsnn : 0 ≤ s := norm_nonneg v
  have hsle : s ≤ D := (ENNReal.ofReal_le_ofReal_iff hDnn).mp (hxs ▸ hdiam x q)
  have hsπ : s ≤ Real.pi := le_trans hsle hDπ
  have hxne : x ≠ q := by
    intro h
    rw [h, hpq] at hxlt
    exact lt_irrefl _ hxlt
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hsnn with h0 | h0
    · exfalso
      have h1 : v = 0 := norm_eq_zero.mp h0.symm
      rw [h1, GExp_zero] at hvG
      exact hxne hvG
    · exact h0
  have hvne : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsdef; rw [hsdef] at hspos; exact lt_irrefl 0 hspos
  set ξ : TangentSpace I x := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hsξ : s • ξ = v := by
    rw [hξdef, hsdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  set G : ℝ → M := geodCurve (cov := cov) hmet s hsnn x ξ hξ1 with hGdef
  have hG0 : G 0 = x := (geodCurve_spec (cov := cov) hmet s hsnn x ξ hξ1).1
  have hGs : G s = q := by
    rw [hGdef]
    rw [← GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := ξ) hξ1 (T := s) hsnn
      (r := s) hsnn le_rfl, hsξ]
    exact hvG
  have hmin : Manifold.riemannianEDist I x (G s) = ENNReal.ofReal s := by rw [hGs]; exact hxs
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) s, ∀ b ∈ Set.Icc (0:ℝ) s, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := s) hsnn hξ1 (s := s) hsnn
      le_rfl hmin
    intro a ha b hb hab
    exact h a ha b hb hab
  -- continuity
  have hGcont : ContinuousOn G (Set.Icc (0:ℝ) s) := by
    have hδ := geodDelta_pos (cov := cov) hmet
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞ G
        (Set.Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet)) := by
      rw [hGdef]; exact (geodCurve_spec (cov := cov) hmet s hsnn x ξ hξ1).2.2.1
    have hsub' : Set.Icc (0:ℝ) s ⊆
        Set.Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet) := by
      intro t ht; exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
    exact ((hsm.mono hsub').continuousOn)
  have hcontD : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p (G t)).toReal)
      (Set.Icc (0:ℝ) s) := by
    have h1 : ContinuousOn (fun t : ℝ => Manifold.riemannianEDist I p (G t)) (Set.Icc (0:ℝ) s) :=
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
    rw [hG0]; exact hxp
  have hfars : Real.pi / 2 < (Manifold.riemannianEDist I p (G s)).toReal := by
    rw [hGs, hpq, ENNReal.toReal_ofReal hDnn]; exact hDgt
  have hfar := Submission.GSConcaveSeg.far_of_far_endpoints (cov := cov) hmet htor hpinch hξ1
    hsnn hsπ hDπ hmin hcontD hbd hfar0 hfars
  -- concavity and the chord bound
  have hltp : ∀ t ∈ Set.Icc (0:ℝ) s, (Manifold.riemannianEDist I p (G t)).toReal < Real.pi :=
    fun t ht => lt_of_le_of_lt (hbd t ht) hDlt
  have hconc := Submission.GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi
    (cov := cov) hmet htor hpinch hξ1 hsnn hmin hcontD hfar hltp
  set F : ℝ → ℝ := fun t => (Manifold.riemannianEDist I p (G t)).toReal with hFdef
  have hF0 : F 0 = r := by simp only [hFdef, hG0, hrdef]
  have hFs : F s = D := by simp only [hFdef, hGs, hpq, ENNReal.toReal_ofReal hDnn]
  have hchord : ∀ u ∈ Set.Icc (0:ℝ) s, r + (u / s) * (D - r) ≤ F u := by
    intro u hu
    have hu1 : u / s ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hu.1 hsnn, (div_le_one hspos).mpr hu.2⟩
    have h := hconc.2 (Set.mem_Icc.mpr ⟨le_refl 0, hsnn⟩) (Set.mem_Icc.mpr ⟨hsnn, le_refl s⟩)
      (by linarith [hu1.2] : (0:ℝ) ≤ 1 - u / s) hu1.1 (by ring : (1:ℝ) - u / s + u / s = 1)
    have harg : (1 - u / s) • (0:ℝ) + (u / s) • s = u := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hspos.ne']
    rw [harg] at h
    simp only [smul_eq_mul, hF0, hFs] at h
    have he : (1 - u / s) * r + (u / s) * D = r + (u / s) * (D - r) := by ring
    linarith [h, he.le, he.ge]
  set α : ℝ := (D - r) / s with hαdef
  have hαpos : 0 < α := by rw [hαdef]; exact div_pos (by linarith) hspos
  have hlin : ∀ u ∈ Set.Icc (0:ℝ) s, r + α * u ≤ F u := by
    intro u hu
    have h := hchord u hu
    have he : (u / s) * (D - r) = α * u := by rw [hαdef]; field_simp
    linarith [h, he.le, he.ge]
  -- the critical-point assumption
  intro hcrit
  obtain ⟨r', u₂, hr'nn, hu₂1, hpG', hpd', hinner⟩ := hcrit ξ hξ1
  have hr'e : r' = r := by
    have h1 : ENNReal.ofReal r' = ENNReal.ofReal r := by
      rw [← hpd', ← hxr, Manifold.riemannianEDist_comm]
    exact (ENNReal.ofReal_eq_ofReal_iff hr'nn hrnn).mp h1
  rw [hr'e] at hpG' hpd' hr'nn
  have hrpos : 0 < r := lt_trans (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2) hrgt
  have hpr : p = GExp (cov := cov) hmet x (r • u₂) := hpG'
  -- the hinge comparison
  set δ : ℝ := min s (Real.pi - r) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hspos (by linarith)
  have hkey : ∀ t ∈ Set.Ioo (0:ℝ) δ,
      α ≤ (modelDist1 (hingeAngle ξ u₂) t r - r) / t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hts : t < s := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htπ : t + r < Real.pi := by
      have h := lt_of_lt_of_le ht.2 (min_le_right s (Real.pi - r))
      linarith
    have htm : t ∈ Set.Icc (0:ℝ) s := ⟨ht0.le, hts.le⟩
    have hxt : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (t • ξ))
        = ENNReal.ofReal t := by
      have h := hsub 0 ⟨le_refl 0, hsnn⟩ t htm ht0.le
      rw [hG0, sub_zero] at h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := ξ) hξ1 (T := s) hsnn
        (r := t) ht0.le hts.le]
      exact h
    have hcmp := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := x) ht0 hrpos
      htπ.le hξ1 hu₂1 hxt (by rw [← hpr]; exact hpd')
    have h1 : F t ≤ modelDist1 (hingeAngle ξ u₂) t r := by
      have h := hcmp
      rw [Manifold.riemannianEDist_comm, ← hpr] at h
      have hfin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet x (t • ξ)) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam p _) ENNReal.ofReal_lt_top).ne
      have h2 : (Manifold.riemannianEDist I p (GExp (cov := cov) hmet x (t • ξ))).toReal
          ≤ modelDist1 (hingeAngle ξ u₂) t r := by
        rw [← ENNReal.ofReal_toReal hfin] at h
        exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := ξ) hξ1 (T := s) hsnn
        (r := t) ht0.le hts.le] at h2
      simp only [hFdef, hGdef]
      exact h2
    have h2 := hlin t htm
    have h3 : r + α * t - r ≤ modelDist1 (hingeAngle ξ u₂) t r - r := by linarith
    rw [add_sub_cancel_left] at h3
    rw [le_div_iff₀ ht0]
    linarith
  have htend : Tendsto (fun t : ℝ =>
      (modelDist1 (hingeAngle ξ u₂) t r - r) / t) (𝓝[>] (0:ℝ))
      (𝓝 (-Real.cos (hingeAngle ξ u₂))) := by
    have h := Submission.GSFar.tendsto_arccos_model_sub_div r (hingeAngle ξ u₂)
      (lt_trans (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2) hrgt) hrπ
    simpa only [modelDist1_apply] using h
  have hbound : α ≤ -Real.cos (hingeAngle ξ u₂) :=
    ge_of_tendsto htend (Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioo (0:ℝ) δ, Ioo_mem_nhdsGT hδpos, fun t ht => hkey t ht⟩)
  have hcos : Real.cos (hingeAngle ξ u₂) = inner ℝ ξ u₂ := cos_hingeAngle hξ1 hu₂1
  have hnonneg : 0 ≤ Real.cos (hingeAngle ξ u₂) := by rw [hcos]; exact hinner
  linarith

/-- **Grove–Shiohama step 2, case 2 (the symmetric case).**  Same setting, but now the *other*
distance is the large one: `d(x,q) > π/2`.  One then applies the preceding argument to the function
`d(q,·)` along the shortest geodesic from `x` to `p` (whose direction is supplied by the critical
point assumption for `d(p,·)`). -/
theorem no_crit_far_q
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hqxlt : Manifold.riemannianEDist I q x < ENNReal.ofReal D)
    (hxq : Real.pi / 2 < (Manifold.riemannianEDist I q x).toReal) :
    ¬ Submission.GSCritical.IsCrit hmet p x := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hDπ : D ≤ Real.pi := hDlt.le
  -- the polar distance `r₂ = d(q,x)`
  have hqfin : Manifold.riemannianEDist I q x ≠ ⊤ :=
    (lt_of_lt_of_le hqxlt ENNReal.ofReal_lt_top.le).ne
  set r₂ : ℝ := (Manifold.riemannianEDist I q x).toReal with hr₂def
  have hqr₂ : Manifold.riemannianEDist I q x = ENNReal.ofReal r₂ :=
    (ENNReal.ofReal_toReal hqfin).symm
  have hr₂gt : Real.pi / 2 < r₂ := by rw [hr₂def]; exact hxq
  have hr₂nn : 0 ≤ r₂ := ENNReal.toReal_nonneg
  have hr₂D : r₂ < D := by
    have h := (ENNReal.toReal_lt_toReal hqfin ENNReal.ofReal_ne_top).mpr hqxlt
    rw [ENNReal.toReal_ofReal hDnn] at h
    exact h
  have hr₂π : r₂ < Real.pi := lt_of_lt_of_le hr₂D hDπ
  have hr₂pos : 0 < r₂ := lt_trans (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2) hr₂gt
  -- the unit direction to `q`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x q
  have hvnorm : ‖v‖ = r₂ := by
    have h : ENNReal.ofReal ‖v‖ = ENNReal.ofReal r₂ := by
      rw [← hvd, Manifold.riemannianEDist_comm, hqr₂]
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hr₂nn).mp h
  have hvne : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvnorm; rw [hvnorm] at hr₂pos
    exact (lt_irrefl r₂) hr₂pos
  set ξ : TangentSpace I x := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hr₂ξ : r₂ • ξ = v := by
    rw [hξdef, unitOf, hvnorm, smul_smul, mul_inv_cancel₀ hr₂pos.ne', one_smul]
  have hqξ : q = GExp (cov := cov) hmet x (r₂ • ξ) := by rw [hr₂ξ]; exact hvG.symm
  have hqdist : Manifold.riemannianEDist I x q = ENNReal.ofReal r₂ := by
    rw [Manifold.riemannianEDist_comm, hqr₂]
  -- the critical point assumption
  intro hcrit
  obtain ⟨r₁, u₂, hr₁nn, hu₂1, hpG, hpd, hinner⟩ := hcrit ξ hξ1
  have hr₁pos : 0 < r₁ := by
    rcases eq_or_lt_of_le hr₁nn with h0 | h0
    · exfalso
      have h1 : Manifold.riemannianEDist I x p = ENNReal.ofReal 0 := by rw [hpd, h0]
      have h2 : Manifold.riemannianEDist I x p = 0 := by rw [h1, ENNReal.ofReal_zero]
      have h3 : x = p := (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h2
      have h4 : Manifold.riemannianEDist I q p = ENNReal.ofReal D := by
        rw [Manifold.riemannianEDist_comm]; exact hpq
      rw [h3, h4] at hqxlt
      exact (lt_irrefl _) hqxlt
    · exact h0
  have hr₁le : r₁ ≤ D := (ENNReal.ofReal_le_ofReal_iff hDnn).mp (hpd ▸ hdiam x p)
  have hr₁π : r₁ ≤ Real.pi := le_trans hr₁le hDπ
  -- the minimising geodesic from `x` to `p` in the direction `u₂`
  set Gp : ℝ → M := geodCurve (cov := cov) hmet r₁ hr₁nn x u₂ hu₂1 with hGpdef
  have hGp0 : Gp 0 = x := (geodCurve_spec (cov := cov) hmet r₁ hr₁nn x u₂ hu₂1).1
  have hGpr : Gp r₁ = p := by
    rw [hGpdef]
    rw [← GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := u₂) hu₂1 (T := r₁) hr₁nn
      (r := r₁) hr₁nn le_rfl]
    exact hpG.symm
  have hqGp : Manifold.riemannianEDist I q (Gp r₁) = ENNReal.ofReal D := by
    rw [hGpr, Manifold.riemannianEDist_comm]; exact hpq
  have hmin : Manifold.riemannianEDist I x (Gp r₁) = ENNReal.ofReal r₁ := by rw [hGpr]; exact hpd
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) r₁, ∀ b ∈ Set.Icc (0:ℝ) r₁, a ≤ b →
      Manifold.riemannianEDist I (Gp a) (Gp b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := r₁) hr₁nn hu₂1 (s := r₁) hr₁nn
      le_rfl hmin
    intro a ha b hb hab
    exact h a ha b hb hab
  have hGcont : ContinuousOn Gp (Set.Icc (0:ℝ) r₁) := by
    have hδ := geodDelta_pos (cov := cov) hmet
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞ Gp
        (Set.Ioo (-(geodDelta (cov := cov) hmet)) (r₁ + geodDelta (cov := cov) hmet)) := by
      rw [hGpdef]; exact (geodCurve_spec (cov := cov) hmet r₁ hr₁nn x u₂ hu₂1).2.2.1
    have hsub' : Set.Icc (0:ℝ) r₁ ⊆
        Set.Ioo (-(geodDelta (cov := cov) hmet)) (r₁ + geodDelta (cov := cov) hmet) := by
      intro t ht; exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
    exact ((hsm.mono hsub').continuousOn)
  have hcontD : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I q (Gp t)).toReal)
      (Set.Icc (0:ℝ) r₁) := by
    have h1 : ContinuousOn (fun t : ℝ => Manifold.riemannianEDist I q (Gp t))
        (Set.Icc (0:ℝ) r₁) :=
      ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) q).continuousOn).comp
        hGcont (fun t _ => Set.mem_univ _)
    have h2 : ∀ t ∈ Set.Icc (0:ℝ) r₁, Manifold.riemannianEDist I q (Gp t) ≠ ⊤ := fun t ht =>
      (lt_of_le_of_lt (hdiam q (Gp t)) ENNReal.ofReal_lt_top).ne
    exact ENNReal.continuousOn_toReal.comp h1 (fun t ht => h2 t ht)
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) r₁, (Manifold.riemannianEDist I q (Gp t)).toReal ≤ D := by
    intro t ht
    calc (Manifold.riemannianEDist I q (Gp t)).toReal ≤ (ENNReal.ofReal D).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam q (Gp t))
      _ = D := ENNReal.toReal_ofReal hDnn
  have hfar0 : Real.pi / 2 < (Manifold.riemannianEDist I q (Gp 0)).toReal := by
    rw [hGp0]; exact hxq
  have hfars : Real.pi / 2 < (Manifold.riemannianEDist I q (Gp r₁)).toReal := by
    rw [hqGp, ENNReal.toReal_ofReal hDnn]; exact hDgt
  have hfar := Submission.GSConcaveSeg.far_of_far_endpoints (cov := cov) hmet htor hpinch hu₂1
    hr₁nn hr₁π hDπ hmin hcontD hbd hfar0 hfars
  have hltp : ∀ t ∈ Set.Icc (0:ℝ) r₁, (Manifold.riemannianEDist I q (Gp t)).toReal < Real.pi :=
    fun t ht => lt_of_le_of_lt (hbd t ht) hDlt
  have hconc := Submission.GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi
    (cov := cov) hmet htor hpinch hu₂1 hr₁nn hmin hcontD hfar hltp
  set F : ℝ → ℝ := fun t => (Manifold.riemannianEDist I q (Gp t)).toReal with hFdef
  have hF0 : F 0 = r₂ := by simp only [hFdef, hGp0, hr₂def]
  have hFs : F r₁ = D := by simp only [hFdef, hqGp, ENNReal.toReal_ofReal hDnn]
  have hchord : ∀ u ∈ Set.Icc (0:ℝ) r₁, r₂ + (u / r₁) * (D - r₂) ≤ F u := by
    intro u hu
    have hu1 : u / r₁ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hu.1 hr₁nn, (div_le_one hr₁pos).mpr hu.2⟩
    have h := hconc.2 (Set.mem_Icc.mpr ⟨le_refl 0, hr₁nn⟩) (Set.mem_Icc.mpr ⟨hr₁nn, le_refl r₁⟩)
      (by linarith [hu1.2] : (0:ℝ) ≤ 1 - u / r₁) hu1.1 (by ring : (1:ℝ) - u / r₁ + u / r₁ = 1)
    have harg : (1 - u / r₁) • (0:ℝ) + (u / r₁) • r₁ = u := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hr₁pos.ne']
    rw [harg] at h
    simp only [smul_eq_mul, hF0, hFs] at h
    have he : (1 - u / r₁) * r₂ + (u / r₁) * D = r₂ + (u / r₁) * (D - r₂) := by ring
    linarith [h, he.le, he.ge]
  set β : ℝ := (D - r₂) / r₁ with hβdef
  have hβpos : 0 < β := by rw [hβdef]; exact div_pos (by linarith) hr₁pos
  have hlin : ∀ u ∈ Set.Icc (0:ℝ) r₁, r₂ + β * u ≤ F u := by
    intro u hu
    have h := hchord u hu
    have he : (u / r₁) * (D - r₂) = β * u := by rw [hβdef]; field_simp
    linarith [h, he.le, he.ge]
  set δ : ℝ := min r₁ (Real.pi - r₂) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hr₁pos (by linarith)
  have hkey : ∀ t ∈ Set.Ioo (0:ℝ) δ,
      β ≤ (modelDist1 (hingeAngle u₂ ξ) t r₂ - r₂) / t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htr₁ : t < r₁ := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htπ : t + r₂ < Real.pi := by
      have h := lt_of_lt_of_le ht.2 (min_le_right r₁ (Real.pi - r₂))
      linarith
    have htm : t ∈ Set.Icc (0:ℝ) r₁ := ⟨ht0.le, htr₁.le⟩
    have hxt : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (t • u₂))
        = ENNReal.ofReal t := by
      have h := hsub 0 ⟨le_refl 0, hr₁nn⟩ t htm ht0.le
      rw [hGp0, sub_zero] at h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := u₂) hu₂1 (T := r₁) hr₁nn
        (r := t) ht0.le htr₁.le]
      exact h
    have hcmp := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := x) ht0 hr₂pos
      htπ.le hu₂1 hξ1 hxt (by rw [← hqξ]; exact hqdist)
    have h1 : F t ≤ modelDist1 (hingeAngle u₂ ξ) t r₂ := by
      have h := hcmp
      rw [Manifold.riemannianEDist_comm, ← hqξ] at h
      have hfin : Manifold.riemannianEDist I q (GExp (cov := cov) hmet x (t • u₂)) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam q _) ENNReal.ofReal_lt_top).ne
      have h2 : (Manifold.riemannianEDist I q (GExp (cov := cov) hmet x (t • u₂))).toReal
          ≤ modelDist1 (hingeAngle u₂ ξ) t r₂ := by
        rw [← ENNReal.ofReal_toReal hfin] at h
        exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
      rw [GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := u₂) hu₂1 (T := r₁) hr₁nn
        (r := t) ht0.le htr₁.le] at h2
      simp only [hFdef, hGpdef]
      exact h2
    have h2 := hlin t htm
    have h3 : r₂ + β * t - r₂ ≤ modelDist1 (hingeAngle u₂ ξ) t r₂ - r₂ := by linarith
    rw [add_sub_cancel_left] at h3
    rw [le_div_iff₀ ht0]
    linarith
  have htend : Tendsto (fun t : ℝ =>
      (modelDist1 (hingeAngle u₂ ξ) t r₂ - r₂) / t) (𝓝[>] (0:ℝ))
      (𝓝 (-Real.cos (hingeAngle u₂ ξ))) := by
    have h := Submission.GSFar.tendsto_arccos_model_sub_div r₂ (hingeAngle u₂ ξ)
      (lt_trans (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2) hr₂gt) hr₂π
    simpa only [modelDist1_apply] using h
  have hbound : β ≤ -Real.cos (hingeAngle u₂ ξ) :=
    ge_of_tendsto htend (Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioo (0:ℝ) δ, Ioo_mem_nhdsGT hδpos, fun t ht => hkey t ht⟩)
  have hcos : Real.cos (hingeAngle u₂ ξ) = inner ℝ u₂ ξ := cos_hingeAngle hu₂1 hξ1
  have hnonneg : 0 ≤ Real.cos (hingeAngle u₂ ξ) := by rw [hcos]; rwa [real_inner_comm]
  linarith

/-- **Grove–Shiohama, step 2 (the complete case analysis).**  If `p, q` is a diameter pair of
diameter `D ∈ (π/2, 2π/3]` and `x ∉ {p, q}`, then `x` is not a critical point of `d(p,·)`.

The three cases are: `d(p,x) > π/2` (`no_crit_far`), `d(q,x) > π/2` (`no_crit_far_q`), and
`d(p,x) ≤ π/2`, `d(q,x) ≤ π/2` (`GSCritical.not_isCrit_of_le_pi_div_two`). -/
theorem not_isCrit_of_ne
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    ¬ Submission.GSCritical.IsCrit hmet p x := by
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  -- `x` is not a maximiser for either pole
  have hpxlt : Manifold.riemannianEDist I p x < ENNReal.ofReal D := by
    rcases lt_or_eq_of_le (hdiam p x) with h | h
    · exact h
    · exfalso
      exact Submission.GSStep1.step1_diameter_unique_of_lt_pi (cov := cov) hmet htor hpinch
        (p := p) (q₁ := q) (q₂ := x) hdiam hDgt hDlt hpq h hxq.symm
  have hqxlt : Manifold.riemannianEDist I q x < ENNReal.ofReal D := by
    rcases lt_or_eq_of_le (hdiam q x) with h | h
    · exact h
    · exfalso
      have hqp : Manifold.riemannianEDist I q p = ENNReal.ofReal D := by
        rw [Manifold.riemannianEDist_comm]; exact hpq
      exact Submission.GSStep1.step1_diameter_unique_of_lt_pi (cov := cov) hmet htor hpinch
        (p := q) (q₁ := p) (q₂ := x) hdiam hDgt hDlt hqp h hxp.symm
  by_cases hp2 : Real.pi / 2 < (Manifold.riemannianEDist I p x).toReal
  · exact no_crit_far (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq hpxlt hp2
  by_cases hq2 : Real.pi / 2 < (Manifold.riemannianEDist I q x).toReal
  · exact no_crit_far_q (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq hqxlt hq2
  · push Not at hp2 hq2
    have h1 : Manifold.riemannianEDist I x p ≤ ENNReal.ofReal (Real.pi / 2) := by
      have hfin : Manifold.riemannianEDist I x p ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam x p) ENNReal.ofReal_lt_top).ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (by rw [Manifold.riemannianEDist_comm]; exact hp2)
    have h2 : Manifold.riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / 2) := by
      have hfin : Manifold.riemannianEDist I x q ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam x q) ENNReal.ofReal_lt_top).ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (by rw [Manifold.riemannianEDist_comm]; exact hq2)
    exact Submission.GSCritical.not_isCrit_of_le_pi_div_two (cov := cov) hmet htor hpinch
      hpq hDgt h1 h2

/-- **Unwrapping `¬ IsCrit`**: away from the critical set of `f = d(p,·)` there is a unit direction
`v` in which `f` *strictly increases*: every shortest direction to `p` makes an obtuse angle with
`v` (equivalently, the right derivative of `t ↦ d(p, GExp x (t • v))` at `0` is positive). -/
theorem exists_unit_away
    (hmet : IsMetricCompatible cov) {p x : M} (h : ¬ Submission.GSCritical.IsCrit hmet p x) :
    ∃ v : TangentSpace I x, ‖v‖ = 1 ∧ ∀ (r : ℝ) (u : TangentSpace I x),
      0 ≤ r → ‖u‖ = 1 → p = GExp (cov := cov) hmet x (r • u) →
      Manifold.riemannianEDist I x p = ENNReal.ofReal r → inner ℝ v u < 0 := by
  simp only [Submission.GSCritical.IsCrit] at h
  push Not at h
  obtain ⟨v, hv, huv⟩ := h
  exact ⟨v, hv, fun r u hr hu hpu hd => huv r u hr hu hpu hd⟩

/-- **The regular points of `d(p,·)` for a diameter pair, in the range `diam ≤ 2π/3`.**  Every point
outside `{p, q}` admits a unit direction in which `d(p,·)` strictly increases. -/
theorem exists_unit_away_of_ne
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ v : TangentSpace I x, ‖v‖ = 1 ∧ ∀ (r : ℝ) (u : TangentSpace I x),
      0 ≤ r → ‖u‖ = 1 → p = GExp (cov := cov) hmet x (r • u) →
      Manifold.riemannianEDist I x p = ENNReal.ofReal r → inner ℝ v u < 0 :=
  exists_unit_away (cov := cov) hmet (not_isCrit_of_ne (cov := cov) hmet htor hpinch hdiam hDgt
    hDlt hpq hxp hxq)

/-- `p` is a critical point of `d(p,·)` in the (vacuous) sense of `GSCritical.IsCrit` — the pole
itself has to be excluded from the regular set, exactly as in Grove–Shiohama. -/
theorem isCrit_self (hmet : IsMetricCompatible cov) (p : M) :
    Submission.GSCritical.IsCrit hmet p p := by
  intro v hv
  refine ⟨0, v, le_refl 0, hv, ?_, ?_, by simp⟩
  · rw [zero_smul, GExp_zero]
  · rw [Manifold.riemannianEDist_self, ENNReal.ofReal_zero]

end

end Submission.GSNoCrit
