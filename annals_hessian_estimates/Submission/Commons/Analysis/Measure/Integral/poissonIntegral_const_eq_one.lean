import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial
import Submission.Commons.Analysis.InnerProductSpace.exists_linearIsometryEquiv_of_norm_eq
import Submission.Commons.Analysis.Measure.Integral.integral_toSphere_comp_linearIsometryEquiv

namespace Commons.Analysis.Measure.Integral

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace _root_.InnerProductSpace BigOperators ENNReal

/-- **The mass identity for the Poisson kernel.**
Assume that the Poisson integral of the constant function `1`,
`M x = ∫ u, (R^n/(A R^2)) * (R^2 - ‖x - c‖^2) * ‖x - c - R • u‖⁻ⁿ ∂σ(u)`, is `C²` on
`ball c R` with vanishing Laplacian.  Then `M ≡ 1` on the ball.

Suggested approach: `M` is radial about `c` (change of variables `u ↦ S u` with
`S` a linear isometry equivalence, using the rotation invariance of `volume.toSphere`),
so `M (c + R w) = φ(‖w‖)`.  By the weak maximum principle
`Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial` applied
to `M` and `-M` on `ball c r` for `r < R` one gets `M x = M y` for all `x, y` with
`‖x - c‖ ≤ r` and `‖y - c‖ = r`; hence `M` is constant on the ball, equal to
`M c = ∫ u, 1/(A) ∂σ(u) = 1` (since `‖c - c - R • u‖ = R`). -/
theorem poissonIntegral_const_eq_one {n : ℕ} (hn : 0 < n)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hcm : ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ((R^n / ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real
              Set.univ * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) (ball c R))
    (hlap : ∀ x ∈ ball c R, Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ((R^n / ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real
              Set.univ * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) x = 0) :
    ∀ x ∈ ball c R,
      (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ((R^n / ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real
              Set.univ * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) = 1 := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have := hne
    infer_instance
  set σ : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere with hσdef
  set A : ℝ := σ.real Set.univ with hAdef
  have hAfact : A = (n : ℝ) * (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) := by
    rw [hAdef, hσdef, Measure.toSphere_real_apply_univ, hfin]
  have hvolpos : 0 < (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) := by
    rw [Measure.real]
    exact ENNReal.toReal_pos
      (isOpen_ball.measure_ne_zero volume ⟨0, mem_ball_self zero_lt_one⟩)
      measure_ball_lt_top.ne
  have hApos : 0 < A := by
    rw [hAfact]
    have hnn : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    exact mul_pos hnn hvolpos
  have hAne : A ≠ 0 := ne_of_gt hApos
  set M : EuclideanSpace ℝ (Fin n) → ℝ := (fun x =>
      ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ((R^n / (σ.real Set.univ * R^2))
          * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹))
      ∂σ) with hMdef
  -- the mass identity at the centre
  have hpoint : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ((R^n / (A * R^2)) * ((R^2 - ‖c - c‖^2) * (‖c - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹)) = 1/A := by
    intro u
    have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere u
    have h1 : ‖c - c‖ = 0 := by rw [sub_self, norm_zero]
    have h2 : ‖c - c - R • (u : EuclideanSpace ℝ (Fin n))‖ = R := by
      have h3 : c - c - R • (u : EuclideanSpace ℝ (Fin n)) = -(R • (u : EuclideanSpace ℝ (Fin n))) := by abel
      rw [h3, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hR]
    have h4 : (‖c - c‖^2 : ℝ) = 0 := by rw [h1]; norm_num
    rw [h4, h2, sub_zero]
    field_simp
  have hMc : M c = 1 := by
    have h1 : M c = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1/A) ∂σ := by
      simp only [hMdef]
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    rw [h1, integral_const, ← hAdef, smul_eq_mul, one_div, mul_inv_cancel₀ hAne]
  -- radiality
  have hradial : ∀ x y : EuclideanSpace ℝ (Fin n), x ∈ ball c R → y ∈ ball c R →
      ‖x - c‖ = ‖y - c‖ → M x = M y := by
    intro x y hx hy hxy
    obtain ⟨S, hS⟩ := Commons.Analysis.InnerProductSpace.exists_linearIsometryEquiv_of_norm_eq
      (x := y - c) (y := x - c) hxy.symm
    set G : EuclideanSpace ℝ (Fin n) → ℝ := fun v =>
      R^n / (A * R^2) * ((R^2 - ‖x - c‖^2) *
        (‖x - c - R • v‖^n)⁻¹) with hGdef
    have hyc : y - c = S.symm (x - c) := by rw [← hS, S.symm_apply_apply]
    have harg : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        y - c - R • (u : EuclideanSpace ℝ (Fin n))
          = S.symm (x - c - R • S (u : EuclideanSpace ℝ (Fin n))) := by
      intro u
      rw [hyc]
      simp
    have hnorm : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖y - c - R • (u : EuclideanSpace ℝ (Fin n))‖
          = ‖x - c - R • S (u : EuclideanSpace ℝ (Fin n))‖ := by
      intro u
      rw [harg u, S.symm.norm_map]
    have hMx : M x = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        G (u : EuclideanSpace ℝ (Fin n)) ∂σ := by
      simp only [hMdef, hGdef]
      rfl
    have hMy : M y = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        G (S (u : EuclideanSpace ℝ (Fin n))) ∂σ := by
      simp only [hMdef]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [hGdef]
      rw [← hxy, hnorm u]
    have hchange : (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          G (S (u : EuclideanSpace ℝ (Fin n))) ∂σ)
        = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          G (u : EuclideanSpace ℝ (Fin n)) ∂σ := by
      rw [hσdef]
      exact Commons.Analysis.Measure.Integral.integral_toSphere_comp_linearIsometryEquiv S G
    rw [hMx, hMy, hchange]
  -- constancy
  have hconst : ∀ x ∈ ball c R, M x = M c := by
    intro x hx
    have hxR : ‖x - c‖ < R := by
      have := mem_ball.mp hx; rwa [dist_eq_norm] at this
    set r : ℝ := (‖x - c‖ + R) / 2 with hrdef
    have hxr : ‖x - c‖ < r := by rw [hrdef]; linarith
    have hrR : r < R := by rw [hrdef]; linarith
    have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxr
    set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1 with hedef
    have he : ‖e‖ = 1 := by
      have h := PiLp.norm_single (p := 2) (fun _ : Fin n => ℝ) ⟨0, hn⟩ (1 : ℝ)
      simp only [hedef, EuclideanSpace.single, h, norm_one]
    have hce : ‖c + r • e - c‖ = r := by
      have h1 : c + r • e - c = r • e := by abel
      rw [h1, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
    have hy0mem : c + r • e ∈ ball c R := by
      rw [mem_ball, dist_eq_norm, hce]; exact hrR
    have hsphere : ∀ y ∈ sphere c r, M y = M (c + r • e) := by
      intro y hy
      have hyr : ‖y - c‖ = r := by
        have h := mem_sphere.mp hy; rwa [dist_eq_norm] at h
      exact hradial y (c + r • e)
        (by rw [mem_ball, dist_eq_norm, hyr]; exact hrR) hy0mem (by rw [hyr, hce])
    have hcd : ContDiffOn ℝ 2 M (ball c r) := hcm.mono (ball_subset_ball hrR.le)
    have hcont : ContinuousOn M (closedBall c r) := hcm.continuousOn.mono (closedBall_subset_ball hrR)
    have hlapr : ∀ z ∈ ball c r, 0 ≤ Laplacian.laplacian M z :=
      fun z hz => le_of_eq (hlap z (ball_subset_ball hrR.le hz)).symm
    have hupper : ∀ z ∈ closedBall c r, M z ≤ M (c + r • e) :=
      Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial
        hrpos hcd hcont hlapr (fun y hy => le_of_eq (hsphere y hy))
    have hlower : ∀ z ∈ closedBall c r, M (c + r • e) ≤ M z := by
      have hcd' : ContDiffOn ℝ 2 (-M) (ball c r) := hcd.neg
      have hcont' : ContinuousOn (-M) (closedBall c r) := hcont.neg
      have hlapr' : ∀ z ∈ ball c r, 0 ≤ Laplacian.laplacian (-M) z := by
        intro z hz
        rw [InnerProductSpace.laplacian_neg]
        show 0 ≤ -(Laplacian.laplacian M z)
        rw [hlap z (ball_subset_ball hrR.le hz)]
        simp
      have hb' : ∀ y ∈ sphere c r, (-M) y ≤ -M (c + r • e) := by
        intro y hy
        show -M y ≤ -M (c + r • e)
        rw [hsphere y hy]
      have hmm := Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial
        hrpos hcd' hcont' hlapr' hb'
      intro z hz
      have h1 : -M z ≤ -M (c + r • e) := hmm z hz
      linarith
    have hxcl : x ∈ closedBall c r := by rw [mem_closedBall, dist_eq_norm]; exact hxr.le
    have hccl : c ∈ closedBall c r := by rw [mem_closedBall, dist_self]; exact hrpos.le
    have hx_eq : M x = M (c + r • e) := le_antisymm (hupper x hxcl) (hlower x hxcl)
    have hc_eq : M c = M (c + r • e) := le_antisymm (hupper c hccl) (hlower c hccl)
    rw [hx_eq, ← hc_eq]
  intro x hx
  have hmass : M x = 1 := by rw [hconst x hx, hMc]
  exact hmass

end Commons.Analysis.Measure.Integral
