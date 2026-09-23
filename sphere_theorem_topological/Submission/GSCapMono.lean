import Submission.GSConcaveSeg
import Submission.GSStep1

/-!
# Strict monotonicity of `d(p,·)` along a minimising geodesic from the maximum `q`

Let `p, q` be a diameter pair of a compact Riemannian manifold with `sec ∈ (1,4]` and
`π/2 < D = d(p,q) ≤ 2π/3` (the restricted Grove–Shiohama range), and let `G` be a *minimising*
geodesic starting at `q` in a unit direction `ξ`.  If the far endpoint `G T` is still at distance
`> π/2` from `p` and is *not* the maximum point `q`, then `t ↦ d(p, G t)` is **strictly decreasing**
on `[0,T]`.

Proof (classical): both endpoints of `G` are at distance `> π/2` from `p`, so the whole segment is
(`GSConcaveSeg.far_of_far_endpoints`) and `t ↦ d(p,G t)` is concave there
(`GSConcaveSeg.concaveOn_dist_geodCurve`).  Concavity with `F 0 = D = max f` gives

`F t₁ - F t₂ ≥ ((t₂-t₁)/t₂)·(D - F t₂)` for `0 ≤ t₁ < t₂ ≤ T`,

so it suffices that `F t₂ < D` for `0 < t₂ ≤ T`.  But `F t₂ = D` means that `G t₂` is a second
maximiser of `d(p,·)` at distance `D`, which is impossible for `D ≤ 2π/3`
(`GSCritical.step1_diameter_unique`).  This is the strict form of the chord estimate used inside
`GSNoCrit.no_crit_far`, and it is the key input of the cap homeomorphism
(`Submission/GSCap.lean`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist
open Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSCapMono

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Strict monotonicity of `d(p,·)` along a minimising geodesic from the maximum `q`.** -/
theorem strictAntiOn_dist_geodCurve_of_max
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D T : ℝ} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hT : 0 ≤ T)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) T) = ENNReal.ofReal T)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) (Set.Icc 0 T))
    (hfarT : Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) T)).toReal)
    (hne : (geodCurve (cov := cov) hmet T hT q ξ hξ) T ≠ q) :
    StrictAntiOn (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) (Set.Icc 0 T) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT q ξ hξ with hGdef
  set F : ℝ → ℝ := fun t => (Manifold.riemannianEDist I p (G t)).toReal with hFdef
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hDπ : D ≤ Real.pi := hDlt.le
  have hG0 : G 0 = q := (geodCurve_spec (cov := cov) hmet T hT q ξ hξ).1
  have hTDle : T ≤ D := by
    have h2 : Manifold.riemannianEDist I q (G T) ≤ ENNReal.ofReal D := hdiam q (G T)
    rw [hmin] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hDnn).mp h2
  have hTπ : T ≤ Real.pi := le_trans hTDle hDπ
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) T, ∀ b ∈ Set.Icc (0:ℝ) T, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    intro a ha b hb hab
    exact Submission.HingeGlobal.geodCurve_sub_arc_minimising (cov := cov) hmet hT hξ
      (x := q) hmin ha hb hab
  have hF0 : F 0 = D := by
    rw [hFdef]
    simp only [hG0]
    rw [hpq, ENNReal.toReal_ofReal hDnn]
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) T, F t ≤ D := by
    intro t ht
    have h := hdiam p (G t)
    rw [hFdef]
    calc (Manifold.riemannianEDist I p (G t)).toReal
        ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = D := ENNReal.toReal_ofReal hDnn
  have hfar0 : Real.pi / 2 < F 0 := by rw [hF0]; exact hDgt
  have hfar' : ∀ t ∈ Set.Icc (0:ℝ) T, Real.pi / 2 ≤ F t :=
    Submission.GSConcaveSeg.far_of_far_endpoints (cov := cov) hmet htor hpinch hξ
      hT hTπ hDπ hmin hcont (fun t ht => hbd t ht) hfar0 hfarT
  have hltT : ∀ t ∈ Set.Icc (0:ℝ) T, F t < Real.pi := fun t ht => lt_of_le_of_lt (hbd t ht) hDlt
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) T) F :=
    Submission.GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi (cov := cov) hmet htor hpinch hξ
      hT hmin hcont hfar' hltT
  -- the strictness input: `F t₂ < D` for `0 < t₂ ≤ T`
  have hltD : ∀ t₂ ∈ Set.Icc (0:ℝ) T, 0 < t₂ → F t₂ < D := by
    intro t₂ ht₂ ht₂pos
    rcases eq_or_lt_of_le (hbd t₂ ht₂) with h | h
    · exfalso
      have hfin : Manifold.riemannianEDist I p (G t₂) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam p (G t₂)) ENNReal.ofReal_lt_top).ne
      have hmax₂ : Manifold.riemannianEDist I p (G t₂) = ENNReal.ofReal D := by
        have h1 : (Manifold.riemannianEDist I p (G t₂)).toReal = D := h
        calc Manifold.riemannianEDist I p (G t₂)
            = ENNReal.ofReal (Manifold.riemannianEDist I p (G t₂)).toReal :=
              (ENNReal.ofReal_toReal hfin).symm
          _ = ENNReal.ofReal D := by rw [h1]
      have hne' : q ≠ G t₂ := by
        intro hq
        have hsub0 := hsub 0 ⟨le_refl 0, hT⟩ t₂ ht₂ ht₂pos.le
        rw [hG0, hq, sub_zero] at hsub0
        have hz : Manifold.riemannianEDist I (G t₂) (G t₂) = 0 := Manifold.riemannianEDist_self
        rw [hz] at hsub0
        have ht2le : t₂ ≤ 0 := ENNReal.ofReal_eq_zero.mp hsub0.symm
        linarith
      exact (Submission.GSStep1.step1_diameter_unique_of_lt_pi (cov := cov) hmet htor hpinch
        hdiam hDgt hDlt hpq hmax₂ hne').elim
    · exact h
  -- the concavity chord bound and the conclusion
  intro a ha b hb hab
  have hbpos : 0 < b := lt_of_le_of_lt ha.1 hab
  have hbD : F b < D := hltD b hb hbpos
  have hbT : b ≤ T := hb.2
  have hkey : F a ≥ ((b - a) / b) * F 0 + (a / b) * F b := by
    have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_refl 0, hT⟩
    have hconc' := hconc.2 h0mem hb
      (div_nonneg (sub_nonneg.mpr hab.le) hbpos.le)
      (div_nonneg ha.1 hbpos.le)
      (by rw [← add_div]; field_simp; ring)
    have harg : ((b - a) / b) • (0:ℝ) + (a / b) • b = a := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hbpos.ne']
    rw [harg] at hconc'
    exact hconc'
  have hc₁pos : 0 < (b - a) / b := div_pos (sub_pos.mpr hab) hbpos
  have hident : ((b - a) / b) * F 0 + (a / b) * F b
      = F b + ((b - a) / b) * (D - F b) := by
    rw [hF0]
    have h1 : (a:ℝ) / b = 1 - (b - a) / b := by field_simp; ring
    rw [h1]; ring
  have hpos : 0 < ((b - a) / b) * (D - F b) := mul_pos hc₁pos (sub_pos.mpr hbD)
  linarith [hkey, hident, hpos]

end

end Submission.GSCapMono
