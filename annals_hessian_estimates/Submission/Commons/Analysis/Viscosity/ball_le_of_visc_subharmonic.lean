/-
The mean value inequality for continuous viscosity subsolutions of the Laplacian (i.e. viscosity
subharmonic functions): if `u` is continuous and viscosity subharmonic on an open set `s`, then
`u c ≤ ⨍_{ball c R} u` for every ball with `closedBall c R ⊆ s`.

The proof is the classical one:

* the raw viscosity condition is localised from `s` to the open ball (`viscLaplacian_mono`);
* comparison with harmonic functions (`viscLaplacian_le_of_harmonic`): if `h` is smooth and harmonic on
  `ball c R` with `h = u` on the sphere, then `u ≤ h` on `closedBall c R` — this is the strict
  comparison principle `strict_comparison_laplacian` applied to `h + δ (R² - ‖·-c‖²)`, whose
  Laplacian is `-2 n δ < 0`, followed by `δ → 0`;
* the Dirichlet problem for the ball (`exists_harmonicOn_ball_eqOn_sphere`) supplies `h`, and the
  mean value property for harmonic functions (`sphereAverage_harmonic_C2`) turns `u ≤ h` into the
  sphere mean value inequality `|S^{n-1}| u c ≤ ∫_{S^{n-1}} u (c + R θ) dθ`;
* averaging the sphere inequalities over the radii (`le_setAverage_ball_of_forall_sphere`) gives the
  ball mean value inequality.
-/
import Mathlib
import Submission.Commons.Analysis.Viscosity.strict_comparison_laplacian
import Submission.Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega
import Submission.Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere
import Submission.Commons.Analysis.Laplace.laplacian_add_quad
import Submission.Commons.Analysis.Harmonic.sphereAverage_harmonic_C2
import Submission.Commons.Analysis.Harmonic.le_setAverage_ball_of_forall_sphere

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option maxHeartbeats 2000000

namespace Commons.Analysis.Viscosity

/-- **Localisation of the raw viscosity condition.**  A continuous function satisfying the raw
viscosity subsolution condition for the Laplacian on an open set `s` satisfies it on every open
subset `t ⊆ s` as well.

The only point needing care is that the test function is only `C²` on `t`, while the viscosity
condition on `s` speaks about test functions that are `C²` on all of `s`: the given test function is
extended (by a bump cutoff) to a globally `C²` function agreeing with it near `x`, and the Laplacians
agree at `x` because the two functions agree in a neighbourhood of `x`. -/
theorem viscLaplacian_mono {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {s t : Set (EuclideanSpace ℝ (Fin n))} (ht : IsOpen t) (hts : t ⊆ s)
    (hvisc : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ s →
      ∀ x ∈ s, (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) → 0 ≤ Laplacian.laplacian φ x) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ t →
      ∀ x ∈ t, (∀ᶠ y in 𝓝[t] x, u y - φ y ≤ u x - φ x) → 0 ≤ Laplacian.laplacian φ x := by
  intro φ hφ x hx hmax
  obtain ⟨φ', hφ'glob, heq⟩ :=
    Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega 2
      (by decide) ht hx hφ
  have hφ's : ContDiffOn ℝ 2 φ' s := hφ'glob.contDiffOn
  -- `𝓝[s] x ≤ 𝓝[t] x` because `t` is an open neighbourhood of `x` and `t ⊆ s`
  have hle : 𝓝[s] x ≤ 𝓝[t] x :=
    (nhdsWithin_le_iff (s := s) (t := t) (x := x)).mpr
      (mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx))
  have hmax' : ∀ᶠ y in 𝓝[s] x, u y - φ' y ≤ u x - φ' x := by
    filter_upwards [hmax.filter_mono hle,
      heq.filter_mono (nhdsWithin_le_nhds (s := s) (a := x))] with y h1 h2
    rw [h2, heq.self_of_nhds]
    exact h1
  have h1 : 0 ≤ Laplacian.laplacian φ' x := hvisc φ' hφ's x (hts hx) hmax'
  have h2 : Laplacian.laplacian φ' x = Laplacian.laplacian φ x :=
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  rw [h2] at h1
  exact h1

/-- **Comparison with harmonic functions.**  A continuous viscosity subharmonic function on the
open set `s` is bounded above on `closedBall c R` by any smooth harmonic function on `ball c R`
that agrees with it on the sphere. -/
theorem viscLaplacian_le_of_harmonic {n : ℕ} (hn : 0 < n) {u h : EuclideanSpace ℝ (Fin n) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin n))}
    (hu : ContinuousOn u s)
    (hvisc : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ s →
      ∀ x ∈ s, (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) → 0 ≤ Laplacian.laplacian φ x)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s)
    (hh : ContDiffOn ℝ 2 h (ball c R))
    (hΔ : ∀ x ∈ ball c R, Laplacian.laplacian h x = 0)
    (hcont : ContinuousOn h (closedBall c R))
    (hbd : ∀ y ∈ sphere c R, u y = h y) :
    ∀ y ∈ closedBall c R, u y ≤ h y := by
  have hu' : ContinuousOn u (closedBall c R) := hu.mono hsub
  have hraw : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ (ball c R) →
      ∀ x ∈ ball c R, (∀ᶠ y in 𝓝[ball c R] x, u y - φ y ≤ u x - φ x) →
        0 ≤ Laplacian.laplacian φ x :=
    viscLaplacian_mono isOpen_ball (ball_subset_closedBall.trans hsub) hvisc
  have key : ∀ δ : ℝ, 0 < δ → ∀ y ∈ closedBall c R,
      u y ≤ h y + δ * (R ^ 2 - ‖y - c‖ ^ 2) := by
    intro δ hδ
    have hquad : ContDiffOn ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => R ^ 2 - ‖y - c‖ ^ 2)
        (ball c R) :=
      (contDiffOn_const (𝕜 := ℝ) (c := R ^ 2) (s := ball c R)).sub
        (ContDiffOn.norm_sq ℝ (contDiffOn_id.sub contDiffOn_const))
    have hvcd : ContDiffOn ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) (ball c R) :=
      hh.add ((contDiffOn_const (𝕜 := ℝ) (c := δ) (s := ball c R)).mul hquad)
    have hvc : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2))
        (closedBall c R) :=
      hcont.add (continuousOn_const.mul (by fun_prop :
        ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => R ^ 2 - ‖y - c‖ ^ 2)
          (closedBall c R)))
    have hstrict : ∀ x ∈ ball c R,
        Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) =>
            h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) x < 0 := by
      intro x hx
      have hcx : ContDiffAt ℝ 2 h x :=
        (hh.contDiffWithinAt hx).contDiffAt (isOpen_ball.mem_nhds hx)
      have hn' : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
      rw [Commons.Analysis.Laplace.laplacian_add_quad (n := n) hcx δ R, hΔ x hx]
      nlinarith [hδ, hn']
    have hsphere : ∀ y ∈ sphere c R,
        u y ≤ (fun y : EuclideanSpace ℝ (Fin n) =>
          h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) y := by
      intro y hy
      have hdist : ‖y - c‖ = R := by
        have h1 := hy
        rw [mem_sphere] at h1
        rwa [dist_eq_norm] at h1
      show u y ≤ h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)
      rw [hdist, hbd y hy]
      ring_nf
      exact le_refl _
    exact Commons.Analysis.Viscosity.strict_comparison_laplacian hR hu' hvcd hvc hraw hstrict
      hsphere
  intro y hy
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hq : (0:ℝ) ≤ R ^ 2 - ‖y - c‖ ^ 2 := by
    have h1 : ‖y - c‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    nlinarith [hR, norm_nonneg (y - c), h1]
  have hpos : 0 < R ^ 2 - ‖y - c‖ ^ 2 + 1 := by linarith
  have hδ : 0 < ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1) := div_pos hε hpos
  have h1 := key (ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1)) hδ y hy
  have h2 : ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1) * (R ^ 2 - ‖y - c‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  linarith

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem ball_le_of_visc_subharmonic {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (hu : ContinuousOn u s)
    (hvisc : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ s →
      ∀ x ∈ s, (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) → 0 ≤ Laplacian.laplacian φ x)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s) :
    u c ≤ ⨍ y in ball c R, u y := by
  have hu' : ContinuousOn u (closedBall c R) := hu.mono hsub
  have hint : IntegrableOn u (ball c R) volume :=
    ((hu'.integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall)
  refine Commons.Analysis.Harmonic.le_setAverage_ball_of_forall_sphere (n := n) hR hint ?_
  intro r hr hrR
  have hsubr : closedBall c r ⊆ s := (closedBall_subset_closedBall hrR).trans hsub
  have hcont_sphere : ContinuousOn u (sphere c r) :=
    hu.mono (Metric.sphere_subset_closedBall.trans hsubr)
  obtain ⟨h, hh, hΔ, hcnt, hbd⟩ :=
    Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere (n := n) hr hcont_sphere
  have hle := viscLaplacian_le_of_harmonic hn hu hvisc hr hsubr hh hΔ hcnt (fun y hy => (hbd y hy).symm)
  have hc : u c ≤ h c := hle c (mem_closedBall_self hr.le)
  have hav := Commons.Analysis.Harmonic.sphereAverage_harmonic_C2 (n := n) hn hr hh hΔ hcnt
  have hmass : (0:ℝ) ≤ ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1 : ℝ)
      ∂MeasureTheory.volume.toSphere := integral_nonneg fun _ => zero_le_one
  have hcongr : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        u (c + r • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
      = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        h (c + r • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      have h1 := θ.2
      rw [mem_sphere, dist_eq_norm, sub_zero] at h1
      exact h1
    have hmem : c + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ sphere c r := by
      rw [mem_sphere, dist_eq_norm,
        show c + r • (θ : EuclideanSpace ℝ (Fin n)) - c = r • (θ : EuclideanSpace ℝ (Fin n))
          by abel, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hθ, mul_one]
    show u (c + r • (θ : EuclideanSpace ℝ (Fin n))) = h (c + r • (θ : EuclideanSpace ℝ (Fin n)))
    rw [hbd _ hmem]
  rw [hcongr, hav]
  exact mul_le_mul_of_nonneg_left hc hmass

end Commons.Analysis.Viscosity
