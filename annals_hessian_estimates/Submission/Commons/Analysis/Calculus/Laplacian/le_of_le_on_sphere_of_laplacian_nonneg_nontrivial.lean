import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMaxOn
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq

namespace Commons.Analysis.Calculus.Laplacian

open Metric
open scoped RealInnerProductSpace InnerProductSpace

/-- **Weak maximum principle on a ball for subharmonic functions (nontrivial space).**
If `w` is `C²` on the open ball `Metric.ball c r`, continuous on `Metric.closedBall c r`,
has `Δ w ≥ 0` on `Metric.ball c r` and `w ≤ A` on the sphere `Metric.sphere c r`, then
`w ≤ A` on the whole closed ball.  The hypothesis `Nontrivial E` is necessary: in the
degenerate zero-dimensional case (`EuclideanSpace ℝ (Fin 0)`) the sphere is empty and the
Laplacian vanishes identically, so the statement without this hypothesis is false.

Proof sketch: apply the standard `ε`-perturbation argument to `wε := w + ε • (fun y ↦ ‖y - c‖ ^ 2)`.
Since `Δ (fun y ↦ ‖y - c‖ ^ 2) = 2 * finrank ℝ E > 0`
(`Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq`) and `Δ w ≥ 0`, one has
`Δ wε > 0`.  Let `x0` maximise `wε` on the compact set `closedBall c r`; it cannot lie in
`ball c r`, because there `wε` has a local maximum and hence
`Δ wε x0 ≤ 0` (`Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMaxOn`).
So `x0 ∈ sphere c r` and for `x ∈ closedBall c r` one gets
`w x ≤ wε x ≤ wε x0 ≤ A + ε * r ^ 2`; letting `ε → 0⁺` gives `w x ≤ A`. -/
theorem le_of_le_on_sphere_of_laplacian_nonneg_nontrivial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {w : E → ℝ} {c : E}
    {r A : ℝ} (hr : 0 < r) (hw2 : ContDiffOn ℝ 2 w (Metric.ball c r))
    (hwc : ContinuousOn w (Metric.closedBall c r))
    (hlap : ∀ x ∈ Metric.ball c r, 0 ≤ Laplacian.laplacian w x)
    (hbd : ∀ x ∈ Metric.sphere c r, w x ≤ A) : ∀ x ∈ Metric.closedBall c r, w x ≤ A := by
  -- The dimension is positive, hence `Δ (‖· - c‖ ^ 2) = 2 * finrank ℝ E > 0`.
  have hfin : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  intro x hx
  -- For every `ε > 0` we show `w x ≤ A + ε * r ^ 2` by perturbing `w`.
  have key : ∀ ε > 0, w x ≤ A + ε * r ^ 2 := by
    intro ε hε
    set φ : E → ℝ := fun z => ‖z - c‖ ^ 2 with hφ
    have hφcd : ContDiff ℝ 2 φ := by
      rw [hφ]
      exact (contDiff_norm_sq ℝ (n := 2)).comp (contDiff_id.sub contDiff_const)
    have hφc : Continuous φ := hφcd.continuous
    have hlapφ : Laplacian.laplacian φ = fun _ => 2 * (Module.finrank ℝ E : ℝ) := by
      rw [hφ]; exact laplacian_norm_sub_sq c
    let W : E → ℝ := w + ε • φ
    have hWcd : ContDiffOn ℝ 2 W (Metric.ball c r) := by
      simp only [W]
      exact hw2.add (hφcd.contDiffOn.const_smul ε)
    have hWc : ContinuousOn W (Metric.closedBall c r) := by
      simp only [W]
      exact hwc.add (hφc.continuousOn.const_smul ε)
    -- A maximiser `x0` of `W` on the compact closed ball.
    have hne : (Metric.closedBall c r).Nonempty := ⟨c, Metric.mem_closedBall_self hr.le⟩
    obtain ⟨x0, hx0mem, hx0max⟩ :=
      (isCompact_closedBall c r).exists_isMaxOn hne hWc
    have hx0le : dist x0 c ≤ r := Metric.mem_closedBall.mp hx0mem
    -- `x0` cannot be an interior point: there `Δ W > 0` contradicts the local maximum.
    have hx0notball : x0 ∉ Metric.ball c r := by
      intro hxb
      have hmaxon : IsLocalMaxOn W (Metric.ball c r) x0 :=
        (hx0max.localize).on_subset Metric.ball_subset_closedBall
      have hle0 : Laplacian.laplacian W x0 ≤ 0 :=
        laplacian_nonpos_of_isLocalMaxOn Metric.isOpen_ball hxb hWcd hmaxon
      have hwat : ContDiffAt ℝ 2 w x0 := hw2.contDiffAt (Metric.isOpen_ball.mem_nhds hxb)
      have hφat : ContDiffAt ℝ 2 φ x0 := hφcd.contDiffAt
      have hWpos : 0 < Laplacian.laplacian W x0 := by
        have hadd : Laplacian.laplacian (w + ε • φ) x0
            = Laplacian.laplacian w x0 + Laplacian.laplacian (ε • φ) x0 :=
          hwat.laplacian_add (hφat.const_smul ε)
        have hsl := InnerProductSpace.laplacian_smul (𝕜 := ℝ) ε hφat
        have heq : Laplacian.laplacian W x0
            = Laplacian.laplacian w x0 + ε * (2 * (Module.finrank ℝ E : ℝ)) := by
          simp only [W]
          rw [hadd, hsl, hlapφ]
          simp [smul_eq_mul]
        rw [heq]
        have h1 := hlap x0 hxb
        have h2 : 0 < ε * (2 * (Module.finrank ℝ E : ℝ)) := by
          have : 0 < 2 * (Module.finrank ℝ E : ℝ) := by linarith
          exact mul_pos hε this
        linarith
      linarith
    -- Hence `x0` lies on the boundary sphere.
    have hx0sphere : x0 ∈ Metric.sphere c r := by
      rw [Metric.mem_sphere]
      have h2 : ¬ dist x0 c < r := fun h => hx0notball (Metric.mem_ball.mpr h)
      linarith
    have hn : ‖x0 - c‖ = r := by
      have hd : dist x0 c = r := Metric.mem_sphere.mp hx0sphere
      rwa [dist_eq_norm] at hd
    have hWx0 : W x0 = w x0 + ε * r ^ 2 := by
      simp only [W, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hφ]
      rw [hn]
    have h1 : w x ≤ W x := by
      simp only [W, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hφ]
      have : 0 ≤ ε * ‖x - c‖ ^ 2 := by positivity
      linarith
    have h2 : W x ≤ W x0 := (isMaxOn_iff.mp hx0max) x hx
    have h3 : w x0 ≤ A := hbd x0 hx0sphere
    linarith
  -- Let `ε → 0⁺`.
  by_contra hcon
  rw [not_le] at hcon
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hδ : 0 < w x - A := by linarith
  have hε : 0 < (w x - A) / (2 * r ^ 2) := by positivity
  have hkey := key _ hε
  have hmul : (w x - A) / (2 * r ^ 2) * r ^ 2 = (w x - A) / 2 := by
    field_simp
  linarith

end Commons.Analysis.Calculus.Laplacian
