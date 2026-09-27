/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `π_i(S^j) = 0` for `i < j`: maps `Sⁱ → Sʲ` of lower-dimensional source are nullhomotopic

The connectivity of spheres, in the form needed for the Hopf-degree/Hurewicz route to Adams'
theorem: any continuous map from `Sⁱ` into `Sʲ` with `i < j` is nullhomotopic.

The proof is the classical "dimension" argument, formalised with the Hausdorff-dimension
machinery available in Mathlib:

* every continuous map `f : Sⁱ → ℝʲ⁺¹` admits a continuous extension `G` to `ℝⁱ⁺¹` (Tietze
  extension), which is uniformly approximated by a smooth `g : ℝⁱ⁺¹ → ℝʲ⁺¹` with
  `‖g x - f x‖ < 1/4` for `x ∈ Sⁱ`;
* the radial normalisation `ĝ x = ‖g x‖⁻¹ • g x` is then a continuous map `Sⁱ → Sʲ` homotopic to
  `f` (straight-line homotopy, normalised);
* `dimH (ĝ '' Sⁱ) ≤ i`: `g` does not increase Hausdorff dimension
  (`ContDiffOn.dimH_image_le`) and the normalisation is `4`-Lipschitz on `{y | 1/2 ≤ ‖y‖}`
  (`lipschitzOnWith_normalize`);
* `dimH (Sʲ) = j` (`dimH_sphere_le`, `dimH_sphere_ge`);
* hence `ĝ` cannot be surjective, so it misses a point `q`, and a map into `Sʲ` missing a point
  factors through the contractible punctured sphere `Sʲ \ {q}` and is nullhomotopic
  (`Work.Cofibre.nullhomotopic_of_misses_point`).
-/
import Mathlib
import Submission.Work.Sphere.Basic
import Submission.Work.Cofibre.nullhomotopic_of_misses_point

namespace Work.Degree

open Metric ContinuousMap


/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` has Hausdorff dimension at most `n`: inverse stereographic
projection is a `C¹` (hence locally Lipschitz) surjection onto `Sⁿ` minus one point, with
`n`-dimensional domain. -/
theorem dimH_sphere_le (n : ℕ) :
    dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :
      Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ (n : ENNReal) := by
  have hv : ‖Submission.Sphere.pole n‖ = 1 := Submission.Sphere.norm_pole n
  have hcd : ContDiff ℝ 1 (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
      (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1)))) := by
    have h : ContDiff ℝ (1 : WithTop ℕ∞) (stereoInvFunAux (Submission.Sphere.pole n)) :=
      contDiff_stereoInvFunAux (m := 1)
    have hsub : ContDiff ℝ (1 : WithTop ℕ∞) (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
        (w : EuclideanSpace ℝ (Fin (n+1)))) :=
      (Submodule.subtypeL ((ℝ ∙ Submission.Sphere.pole n)ᗮ)).contDiff
    have hc := h.comp hsub
    simpa [Function.comp_def, stereoInvFun, stereoInvFunAux] using hc
  have hfin : Module.finrank ℝ ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) = n := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ Submission.Sphere.pole n) = 1 := by
      apply finrank_span_singleton
      intro h0
      rw [h0, norm_zero] at hv
      norm_num at hv
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ Submission.Sphere.pole n)
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1 := finrank_euclideanSpace_fin
    omega
  have hrange : dimH (Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
      (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1))))) ≤ (n : ENNReal) := by
    calc dimH (Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
            (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1)))))
        ≤ (Module.finrank ℝ ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) : ENNReal) :=
          ContDiff.dimH_range_le hcd
      _ = (n : ENNReal) := by rw [hfin]
  have hcover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :
        Set (EuclideanSpace ℝ (Fin (n+1)))) ⊆
      Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
        (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1)))) ∪ {Submission.Sphere.pole n} := by
    intro x hx
    by_cases hxv : (x : EuclideanSpace ℝ (Fin (n+1))) = Submission.Sphere.pole n
    · exact Or.inr hxv
    · refine Or.inl ⟨stereoToFun (Submission.Sphere.pole n) x, ?_⟩
      have h := stereo_left_inv hv
        (x := (⟨x, hx⟩ : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1))) hxv
      simpa using congrArg Subtype.val h
  calc dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :
        Set (EuclideanSpace ℝ (Fin (n+1))))
      ≤ dimH (Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
          (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1)))) ∪ {Submission.Sphere.pole n}) :=
        dimH_mono hcover
    _ = max (dimH (Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
          (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1))))))
          (dimH ({Submission.Sphere.pole n} : Set (EuclideanSpace ℝ (Fin (n+1))))) :=
        dimH_union _ _
    _ = max (dimH (Set.range (fun w : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) =>
          (stereoInvFun hv w : EuclideanSpace ℝ (Fin (n+1)))))) 0 := by rw [dimH_singleton]
    _ ≤ (n : ENNReal) := max_le_iff.mpr ⟨hrange, bot_le⟩

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` has Hausdorff dimension at least `n`: the orthogonal projection
onto the hyperplane perpendicular to the pole is `1`-Lipschitz and carries `Sⁿ` onto a set
containing the unit ball of the hyperplane, which has Hausdorff dimension `n`. -/
theorem dimH_sphere_ge (n : ℕ) :
    (n : ENNReal) ≤ dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :
      Set (EuclideanSpace ℝ (Fin (n+1)))) := by
  have hv : ‖Submission.Sphere.pole n‖ = 1 := Submission.Sphere.norm_pole n
  have hfin : Module.finrank ℝ ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ) = n := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ Submission.Sphere.pole n) = 1 := by
      apply finrank_span_singleton
      intro h0
      rw [h0, norm_zero] at hv
      norm_num at hv
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ Submission.Sphere.pole n)
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1 := finrank_euclideanSpace_fin
    omega
  have hball : Metric.closedBall (0 : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ)) 1 ⊆
      (fun y : EuclideanSpace ℝ (Fin (n+1)) =>
        ((ℝ ∙ Submission.Sphere.pole n)ᗮ).orthogonalProjectionOnto y) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Submodule.coe_norm] at hz
    refine ⟨(z : EuclideanSpace ℝ (Fin (n+1))) +
        Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) • Submission.Sphere.pole n, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have ht2 : Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2)
            * Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) =
          1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2 := by
        rw [← sq, Real.sq_sqrt]
        nlinarith [hz, norm_nonneg (z : EuclideanSpace ℝ (Fin (n+1)))]
      have ht0 : (0:ℝ) ≤ Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) :=
        Real.sqrt_nonneg _
      have hinner : inner ℝ (z : EuclideanSpace ℝ (Fin (n+1)))
          (Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) •
            Submission.Sphere.pole n) = 0 := by
        rw [inner_smul_right, real_inner_comm,
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2, mul_zero]
      have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (z : EuclideanSpace ℝ (Fin (n+1)))
        (Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) • Submission.Sphere.pole n) hinner
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hv, mul_one] at hpyth
      have hy2 : ‖(z : EuclideanSpace ℝ (Fin (n+1))) +
            Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) • Submission.Sphere.pole n‖
          * ‖(z : EuclideanSpace ℝ (Fin (n+1))) +
            Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) • Submission.Sphere.pole n‖ = 1 := by
        rw [hpyth, ht2]; ring
      nlinarith [norm_nonneg ((z : EuclideanSpace ℝ (Fin (n+1))) +
        Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) • Submission.Sphere.pole n)]
    · change ((ℝ ∙ Submission.Sphere.pole n)ᗮ).orthogonalProjectionOnto
        ((z : EuclideanSpace ℝ (Fin (n+1))) +
          Real.sqrt (1 - ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖^2) •
            Submission.Sphere.pole n) = z
      rw [map_add, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero,
        add_zero]
  have hproj : dimH ((fun y : EuclideanSpace ℝ (Fin (n+1)) =>
        ((ℝ ∙ Submission.Sphere.pole n)ᗮ).orthogonalProjectionOnto y) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1))
      ≤ dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    dimH_orthogonalProjectionOnto_le _ _
  have hdim : dimH (Metric.closedBall (0 : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ)) 1) =
      (n : ENNReal) := by
    rw [Real.dimH_of_mem_nhds
      (Metric.closedBall_mem_nhds (0 : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ)) (by norm_num))]
    simp [hfin]
  calc (n : ENNReal) = dimH (Metric.closedBall (0 : ↥((ℝ ∙ Submission.Sphere.pole n)ᗮ)) 1) :=
        hdim.symm
    _ ≤ dimH ((fun y : EuclideanSpace ℝ (Fin (n+1)) =>
          ((ℝ ∙ Submission.Sphere.pole n)ᗮ).orthogonalProjectionOnto y) ''
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) := dimH_mono hball
    _ ≤ dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := hproj

/-- The radial normalisation `y ↦ ‖y‖⁻¹ • y` is `4`-Lipschitz on the region
`{y | 1/2 ≤ ‖y‖}`.  (The optimal constant is `2`, but `4` is what the elementary estimate
on `1/‖y‖ ≤ 2` gives.) -/
theorem lipschitzOnWith_normalize (m : ℕ) :
    LipschitzOnWith 4 (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖⁻¹ • y) {y | 1/2 ≤ ‖y‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  simp only [Set.mem_ofPred_eq] at hy hz
  rw [dist_eq_norm, dist_eq_norm]
  have ha : (0:ℝ) < ‖y‖ := by linarith
  have hb : (0:ℝ) < ‖z‖ := by linarith
  have hkey : ‖y‖⁻¹ • y - ‖z‖⁻¹ • z
      = ‖y‖⁻¹ • (y - z) + (‖y‖⁻¹ - ‖z‖⁻¹) • z := by module
  rw [hkey]
  have hbound : ‖‖y‖⁻¹ • (y - z) + (‖y‖⁻¹ - ‖z‖⁻¹) • z‖
      ≤ ‖y‖⁻¹ * ‖y - z‖ + |‖y‖⁻¹ - ‖z‖⁻¹| * ‖z‖ := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    · rw [norm_smul, Real.norm_eq_abs]
  have hfac : ‖y‖⁻¹ - ‖z‖⁻¹ = (‖z‖ - ‖y‖) / (‖y‖ * ‖z‖) := by
    field_simp
  have habs : |‖y‖⁻¹ - ‖z‖⁻¹| * ‖z‖ = |‖z‖ - ‖y‖| / ‖y‖ := by
    rw [hfac, abs_div, abs_of_pos (mul_pos ha hb)]
    field_simp
  have hbnd : |‖z‖ - ‖y‖| ≤ ‖y - z‖ := by
    have h1 : ‖z‖ - ‖y‖ ≤ ‖y - z‖ := by
      have := norm_sub_norm_le z y; rwa [norm_sub_rev] at this
    have h2 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
    exact abs_sub_le_iff.mpr ⟨h1, h2⟩
  rw [habs] at hbound
  refine le_trans hbound ?_
  rw [inv_mul_eq_div, ← add_div, div_le_iff₀ ha, NNReal.coe_ofNat]
  have h2 : ‖y - z‖ + |‖z‖ - ‖y‖| ≤ 2 * ‖y - z‖ := by linarith
  have h4 : (2:ℝ) * ‖y - z‖ ≤ 4 * ‖y - z‖ * ‖y‖ := by
    have h5 := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ 2 * ‖y - z‖)
    nlinarith [h5]
  linarith

theorem nullhomotopic_of_dim_lt_sph (i j : ℕ) (hij : i < j)
    (f : ContinuousMap ↥(Submission.Sphere.Sph i) ↥(Submission.Sphere.Sph j)) :
    f.Nullhomotopic := by
  -- Step 1: a continuous extension of `f` to the ambient space `ℝ^{i+1}`.
  have hsphere_closed : IsClosed (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1) :=
    Metric.isClosed_sphere
  let Φ : C(↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1),
      EuclideanSpace ℝ (Fin (j+1))) :=
    ⟨fun x => (f x : EuclideanSpace ℝ (Fin (j+1))),
      continuous_subtype_val.comp f.continuous⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hsphere_closed Φ
  have hGx : ∀ x : ↥(Submission.Sphere.Sph i),
      (G x : EuclideanSpace ℝ (Fin (j+1))) = (f x : EuclideanSpace ℝ (Fin (j+1))) := by
    intro x
    have h := congrFun (congrArg DFunLike.coe hG) x
    simpa [ContinuousMap.restrict_apply, Φ] using h
  -- Step 2: a smooth approximation `g` of `G`.
  obtain ⟨g, hg_smooth, hg_close, -⟩ :=
    Continuous.exists_contDiff_approx (E := EuclideanSpace ℝ (Fin (i+1)))
      (F := EuclideanSpace ℝ (Fin (j+1))) (f := fun y => G y) (ε := fun _ => (1/4 : ℝ))
      1 G.continuous continuous_const (fun _ => by norm_num)
  -- Step 3: quantitative consequences on the sphere.
  have hclose : ∀ x : ↥(Submission.Sphere.Sph i),
      ‖g x - (f x : EuclideanSpace ℝ (Fin (j+1)))‖ < 1/4 := by
    intro x
    have h := hg_close x
    rw [dist_eq_norm, hGx x] at h
    exact h
  have hfnorm : ∀ x : ↥(Submission.Sphere.Sph i),
      ‖(f x : EuclideanSpace ℝ (Fin (j+1)))‖ = 1 := by
    intro x
    have h := (f x).2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  have hgnorm : ∀ x : ↥(Submission.Sphere.Sph i), 3/4 ≤ ‖g x‖ := by
    intro x
    have h1 := hclose x
    have h2 := hfnorm x
    have h3 := norm_sub_norm_le (f x : EuclideanSpace ℝ (Fin (j+1))) (g x)
    rw [norm_sub_rev] at h3
    linarith
  have hgne : ∀ x : ↥(Submission.Sphere.Sph i), g x ≠ 0 := by
    intro x h
    have h4 := hgnorm x
    rw [h, norm_zero] at h4
    norm_num at h4
  -- Step 4: the normalised map `ĝ`.
  have hghat_mem : ∀ x : ↥(Submission.Sphere.Sph i),
      NormedSpace.normalize (g x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (j+1))) 1 :=
    fun x => Metric.mem_sphere.mpr (by
      rw [dist_eq_norm, sub_zero]
      exact NormedSpace.norm_normalize (hgne x))
  have hnorm_cont : Continuous fun x : ↥(Submission.Sphere.Sph i) =>
      NormedSpace.normalize (g x) := by
    have hgx : Continuous fun x : ↥(Submission.Sphere.Sph i) => g x :=
      hg_smooth.continuous.comp continuous_subtype_val
    have h1 : Continuous fun x : ↥(Submission.Sphere.Sph i) => (‖g x‖)⁻¹ :=
      hgx.norm.inv₀ (fun x => by
        intro h
        have h4 := hgnorm x
        rw [h] at h4
        norm_num at h4)
    have hmain : Continuous fun x : ↥(Submission.Sphere.Sph i) => (‖g x‖)⁻¹ • g x := by
      simpa only [Pi.smul_def'] using h1.smul hgx
    simpa [NormedSpace.normalize] using hmain
  have hghat_cont : Continuous fun x : ↥(Submission.Sphere.Sph i) =>
      (⟨NormedSpace.normalize (g x), hghat_mem x⟩ : ↥(Submission.Sphere.Sph j)) :=
    hnorm_cont.subtype_mk hghat_mem
  let ghat : C(↥(Submission.Sphere.Sph i), ↥(Submission.Sphere.Sph j)) :=
    ⟨fun x => ⟨NormedSpace.normalize (g x), hghat_mem x⟩, hghat_cont⟩
  -- Step 5: `f` is homotopic to `ĝ`.
  have hvlarge : ∀ p : ↥unitInterval × ↥(Submission.Sphere.Sph i),
      3/4 ≤ ‖(1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2‖ := by
    rintro ⟨t, x⟩
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    have hdiff : ‖(1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x
        - (f x : EuclideanSpace ℝ (Fin (j+1)))‖ ≤ 1/4 := by
      have he : (1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x
          - (f x : EuclideanSpace ℝ (Fin (j+1))) =
            (t:ℝ) • (g x - (f x : EuclideanSpace ℝ (Fin (j+1)))) := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      nlinarith [hclose x, ht0, ht1, norm_nonneg (g x - (f x : EuclideanSpace ℝ (Fin (j+1))))]
    have h3 : (1:ℝ) ≤ ‖(1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x‖ + 1/4 := by
      calc (1:ℝ) = ‖(f x : EuclideanSpace ℝ (Fin (j+1)))‖ := (hfnorm x).symm
        _ = ‖((1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x)
              - ((1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x
                - (f x : EuclideanSpace ℝ (Fin (j+1))))‖ := by congr 1; abel
        _ ≤ ‖(1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x‖
              + ‖(1 - (t:ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1))) + (t:ℝ) • g x
                - (f x : EuclideanSpace ℝ (Fin (j+1)))‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hdiff]
    linarith
  have hvne : ∀ p : ↥unitInterval × ↥(Submission.Sphere.Sph i),
      (1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2 ≠ 0 := by
    intro p h0
    have h4 := hvlarge p
    rw [h0, norm_zero] at h4
    norm_num at h4
  have hHmem : ∀ p : ↥unitInterval × ↥(Submission.Sphere.Sph i),
      NormedSpace.normalize ((1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1)))
        + (p.1:ℝ) • g p.2) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (j+1))) 1 :=
    fun p => Metric.mem_sphere.mpr (by
      rw [dist_eq_norm, sub_zero]
      exact NormedSpace.norm_normalize (hvne p))
  have hHcont : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
      NormedSpace.normalize ((1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1)))
        + (p.1:ℝ) • g p.2) := by
    have hfx : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (f p.2 : EuclideanSpace ℝ (Fin (j+1))) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hgx : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) => g p.2 :=
      hg_smooth.continuous.comp (continuous_subtype_val.comp continuous_snd)
    have hcoef1 : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (1 - (p.1:ℝ)) := continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have hcoef2 : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (p.1:ℝ) := continuous_subtype_val.comp continuous_fst
    have hv : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2 :=
      (hcoef1.smul hfx).add (hcoef2.smul hgx)
    have h1 : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (‖(1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2‖)⁻¹ :=
      hv.norm.inv₀ (fun p => by
        rw [norm_ne_zero_iff]
        exact hvne p)
    have hmain : Continuous fun p : ↥unitInterval × ↥(Submission.Sphere.Sph i) =>
        (‖(1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2‖)⁻¹
          • ((1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1))) + (p.1:ℝ) • g p.2) := by
      simpa only [Pi.smul_def'] using h1.smul hv
    simpa [NormedSpace.normalize] using hmain
  have hhom : f.Homotopic ghat := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p => ⟨NormedSpace.normalize ((1 - (p.1:ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (j+1)))
        + (p.1:ℝ) • g p.2), hHmem p⟩, hHcont.subtype_mk hHmem⟩ ?_ ?_⟩
    · intro x
      apply Subtype.ext
      change NormedSpace.normalize ((1 - ((0:↥unitInterval):ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1)))
        + ((0:↥unitInterval):ℝ) • g x) = (f x : EuclideanSpace ℝ (Fin (j+1)))
      rw [show ((0:↥unitInterval):ℝ) = 0 from rfl]
      simp only [sub_zero, zero_smul, add_zero, one_smul]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (hfnorm x)
    · intro x
      apply Subtype.ext
      change NormedSpace.normalize ((1 - ((1:↥unitInterval):ℝ)) • (f x : EuclideanSpace ℝ (Fin (j+1)))
        + ((1:↥unitInterval):ℝ) • g x) = NormedSpace.normalize (g x)
      rw [show ((1:↥unitInterval):ℝ) = 1 from rfl]
      simp only [sub_self, zero_smul, one_smul, zero_add]
  -- Step 6: `ĝ` misses a point.
  have hrange_eq : Set.range (fun x : ↥(Submission.Sphere.Sph i) =>
        (ghat x : EuclideanSpace ℝ (Fin (j+1)))) =
      NormedSpace.normalize '' (g '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨g x, ⟨x, x.2, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hdim_range : dimH (Set.range (fun x : ↥(Submission.Sphere.Sph i) =>
        (ghat x : EuclideanSpace ℝ (Fin (j+1))))) ≤ (i : ENNReal) := by
    rw [hrange_eq]
    have hsub : g '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1)
        ⊆ {y : EuclideanSpace ℝ (Fin (j+1)) | 1/2 ≤ ‖y‖} := by
      rintro y ⟨x, hx, rfl⟩
      have hh := hgnorm ⟨x, hx⟩
      show (1/2:ℝ) ≤ ‖g x‖
      linarith
    calc dimH (NormedSpace.normalize ''
            (g '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1)))
        ≤ dimH (g '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1)) :=
          LipschitzOnWith.dimH_image_le ((lipschitzOnWith_normalize (j+1)).mono hsub)
      _ ≤ dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (i+1))) 1) :=
          ContDiffOn.dimH_image_le hg_smooth.contDiffOn convex_univ (Set.subset_univ _)
      _ ≤ (i : ENNReal) := dimH_sphere_le i
  have hnotsurj : ∃ q : ↥(Submission.Sphere.Sph j), ∀ x, ghat x ≠ q := by
    by_contra h
    simp only [not_exists, not_forall, Classical.not_not] at h
    have hsurj : Set.range (fun x : ↥(Submission.Sphere.Sph i) =>
        (ghat x : EuclideanSpace ℝ (Fin (j+1)))) =
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (j+1))) 1 : Set _) := by
      refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
      · rcases hy with ⟨x, rfl⟩
        exact (ghat x).2
      · obtain ⟨x, hx⟩ := h ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩
    have hle : (j : ENNReal) ≤ (i : ENNReal) := by
      calc (j : ENNReal) ≤ dimH (Metric.sphere (0 : EuclideanSpace ℝ (Fin (j+1))) 1 : Set _) :=
            dimH_sphere_ge j
        _ = dimH (Set.range (fun x : ↥(Submission.Sphere.Sph i) =>
              (ghat x : EuclideanSpace ℝ (Fin (j+1))))) := by rw [hsurj]
        _ ≤ (i : ENNReal) := hdim_range
    have : j ≤ i := by exact_mod_cast hle
    omega
  obtain ⟨q, hq⟩ := hnotsurj
  have hghat_null : ghat.Nullhomotopic :=
    Work.Cofibre.nullhomotopic_of_misses_point j (Submission.Sphere.Sph i) ghat q hq
  obtain ⟨c, hc⟩ := hghat_null
  exact ⟨c, hhom.trans hc⟩

end Work.Degree
