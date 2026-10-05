import Mathlib

/-!
# Smoothing a continuous sphere homotopy in any dimension

Port of `exists_smooth_avoiding_homotopy_of_continuous.lean` (the `S²` case) to
`EuclideanSpace ℝ (Fin d)`: a continuous sphere-valued homotopy from the identity to the
antipodal map can be replaced by a *smooth* one which moreover misses the antipodal map at time
`0` and the identity at time `1`.

The construction is the Stone-Weierstrass type argument of the `S²` case, verbatim: a continuous
map on a finite-dimensional space is uniformly approximable by smooth maps, on a neighbourhood of
the unit sphere it can be normalised, and the normalised approximant is glued to `0` near the
origin along the `‖·‖`-direction, producing a globally smooth map.
-/

namespace Work.RPCore.Port.PushDisc

open scoped ContDiff

/-- Radial weight used to glue a sphere-valued map to a constant near the origin.  It equals `1`
for `‖y‖ ≥ 1` and `0` for `‖y‖ ≤ 1/2`. -/
private noncomputable def pushPsi (d : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.smoothTransition (4 * inner ℝ p.2 p.2 - 1)

/-- The map `(t,y) ↦ (smoothTransition t, y/‖y‖)`; the second component lands on the unit sphere
for `y ≠ 0`. -/
private noncomputable def pushPhi (d : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  (Real.smoothTransition p.1, (‖p.2‖)⁻¹ • p.2)

/-- Smoothing a continuous homotopy from the identity to the antipodal map of `S²`: any such
continuous homotopy can be replaced by a smooth one which, near its two ends, misses the antipodal
map respectively the identity.

The construction is a Stone-Weierstrass type argument: a continuous map on a finite-dimensional
space is uniformly approximable by smooth maps (`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`),
on a neighbourhood of the unit sphere it can be normalised, and the normalised approximant is
glued to `0` near the origin along the `‖·‖`-direction, which produces a globally smooth map. -/
theorem exists_smooth_avoiding_homotopy_general (d : ℕ) :
    (∃ F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        Continuous F ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (0, x) = x) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (1, x) = -x) ∧
        (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖F (t, x)‖ = 1)) →
    ∃ H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
        (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (0, x) ≠ -x) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (1, x) ≠ x) := by
  rintro ⟨F, hFcont, hF0, hF1, hFnorm⟩
  -- the compact set of unit-sphere points inside the time slab `[0,1]`
  have hKc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_Icc.prod (isCompact_sphere 0 1)
  -- `F` is uniformly continuous on a compact neighbourhood of that set
  have huc : UniformContinuousOn F
      (Metric.cthickening (1:ℝ) (Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1)) :=
    hKc.cthickening.uniformContinuousOn_of_continuous hFcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨eps', heps'pos, heps'⟩ := huc (1/4) (by norm_num)
  -- a smooth approximant `g` of `F`
  obtain ⟨g, hg_smooth, hg⟩ := hFcont.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
      (ε := min eps' (1/2)) (lt_min heps'pos (by norm_num))
  have hgsmall : ∀ z ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1, dist (g z) (F z) ≤ 1/4 := by
    intro z hz
    have hzmem : z ∈ Metric.cthickening (1:ℝ) (Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1) :=
      Metric.self_subset_cthickening _ hz
    apply hg z (1/4)
    intro x hx
    have hxmem : x ∈ Metric.cthickening (1:ℝ) (Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1) :=
      Metric.thickening_subset_cthickening 1 _
        (Metric.mem_thickening_iff.mpr ⟨z, hz,
          lt_of_lt_of_le (Metric.mem_ball.mp hx) (le_trans (min_le_right _ _) (by norm_num))⟩)
    exact (heps' x hxmem z hzmem
      (lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_left _ _))).le
  -- on the sphere slab `g` does not vanish
  have hgnz : ∀ z ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1, g z ≠ 0 := by
    intro z hz h0
    have h2 : ‖F z‖ = 1 := by
      obtain ⟨hzt, hzx⟩ := Set.mem_prod.mp hz
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hzx
      exact hFnorm z.1 z.2 hzx
    have h1 : dist (g z) (F z) ≤ 1/4 := hgsmall z hz
    rw [h0, dist_eq_norm, zero_sub, norm_neg, h2] at h1
    norm_num at h1
  -- membership in the sphere slab
  have hKm : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), 0 ≤ t → t ≤ 1 → ‖x‖ = 1 →
      (t, x) ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1 := by
    intro t x ht0 ht1 hx
    exact Set.mem_prod.mpr ⟨⟨ht0, ht1⟩,
      by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx⟩
  -- ### smoothness of the weight
  have hPsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pushPsi d) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => Real.smoothTransition (4 * inner ℝ p.2 p.2 - 1))
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin d) => inner ℝ p.2 p.2) :=
      ContDiff.inner ℝ contDiff_snd contDiff_snd
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul h1).sub contDiff_const)
  -- ### smoothness of the surrogate
  have hH_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => pushPsi d p • ((‖g (pushPhi d p)‖)⁻¹ • g (pushPhi d p))) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    obtain ⟨t, y⟩ := p
    by_cases hy : y = 0
    · rw [hy]
      have hmem : Metric.ball (t, (0:EuclideanSpace ℝ (Fin d))) (1/2) ∈ nhds (t, (0:EuclideanSpace ℝ (Fin d))) :=
        Metric.ball_mem_nhds _ (by norm_num)
      refine (contDiffAt_const (c := (0:EuclideanSpace ℝ (Fin d)))).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with q hq
      have hq2 : ‖q.2‖ < 1/2 := by
        have h1 : dist q.2 (0:EuclideanSpace ℝ (Fin d)) ≤ dist q (t, (0:EuclideanSpace ℝ (Fin d))) := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        have h2 : dist q (t, (0:EuclideanSpace ℝ (Fin d))) < 1/2 := by simpa [Metric.mem_ball] using hq
        rw [dist_eq_norm, sub_zero] at h1
        linarith
      have hkey : Real.smoothTransition (4 * inner ℝ q.2 q.2 - 1) = 0 := by
        apply Real.smoothTransition.zero_of_nonpos
        rw [real_inner_self_eq_norm_sq]
        nlinarith [norm_nonneg q.2]
      simp only [pushPsi, hkey, zero_smul]
    · have hPsiAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pushPsi d) (t, y) := hPsi.contDiffAt
      have hzmem : pushPhi d (t, y) ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.sphere (0:EuclideanSpace ℝ (Fin d)) 1 := by
        refine Set.mem_prod.mpr ⟨⟨Real.smoothTransition.nonneg _,
          Real.smoothTransition.le_one _⟩, ?_⟩
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact norm_smul_inv_norm hy
      have hgz : g (pushPhi d (t, y)) ≠ 0 := hgnz _ hzmem
      have houter : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (‖g q‖)⁻¹ • g q) (pushPhi d (t, y)) := by
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : ℝ × EuclideanSpace ℝ (Fin d) => ‖g q‖) (pushPhi d (t, y)) :=
          ContDiffAt.norm ℝ (hg_smooth.contDiffAt) hgz
        exact (h1.inv (by simpa [norm_ne_zero_iff] using hgz)).smul hg_smooth.contDiffAt
      have hPhiAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pushPhi d) (t, y) := by
        change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (Real.smoothTransition p.1, (‖p.2‖)⁻¹ • p.2)) (t, y)
        refine ContDiffAt.prodMk ?_ ?_
        · exact (Real.smoothTransition.contDiff.comp contDiff_fst).contDiffAt
        · have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ‖p.2‖) (t, y) :=
            ContDiffAt.norm ℝ contDiff_snd.contDiffAt (by simpa using hy)
          exact (hn.inv (by simpa [norm_ne_zero_iff] using hy)).smul contDiff_snd.contDiffAt
      have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (‖g (pushPhi d p)‖)⁻¹ • g (pushPhi d p)) (t, y) :=
        houter.comp (t, y) hPhiAt
      exact hPsiAt.smul hcomp
  refine ⟨fun p : ℝ × EuclideanSpace ℝ (Fin d) => pushPsi d p • ((‖g (pushPhi d p)‖)⁻¹ • g (pushPhi d p)),
    hH_smooth, ?_, ?_, ?_⟩
  · -- the surrogate is sphere-valued on the unit sphere
    intro t x hx
    simp only [pushPsi, pushPhi]
    have hpsx : Real.smoothTransition (4 * inner ℝ x x - 1) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hsx : (‖x‖)⁻¹ • x = x := by rw [hx]; simp
    rw [hpsx, hsx, one_smul]
    exact norm_smul_inv_norm (hgnz _ (hKm (Real.smoothTransition t) x
      (Real.smoothTransition.nonneg t) (Real.smoothTransition.le_one t) hx))
  · -- no antipodal value at `t = 0`
    intro x hx hcon
    simp only [pushPsi, pushPhi] at hcon
    have hpsx : Real.smoothTransition (4 * inner ℝ x x - 1) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hsx : (‖x‖)⁻¹ • x = x := by rw [hx]; simp
    rw [hpsx, Real.smoothTransition.zero, hsx, one_smul] at hcon
    have hgz0 : g (0, x) ≠ 0 := hgnz _ (hKm 0 x le_rfl (by norm_num) hx)
    have hc0 : (‖g (0, x)‖) ≠ 0 := by simpa [norm_ne_zero_iff] using hgz0
    have hgx : g (0, x) = (‖g (0, x)‖) • (-x) := by
      have h1 : (‖g (0, x)‖) • ((‖g (0, x)‖)⁻¹ • g (0, x)) = (‖g (0, x)‖) • (-x) := by
        rw [hcon]
      rwa [smul_inv_smul₀ hc0] at h1
    have hdist : ‖g (0, x) - x‖ ≤ 1/4 := by
      have h := hgsmall (0, x) (hKm 0 x le_rfl (by norm_num) hx)
      rw [hF0 x hx, dist_eq_norm] at h
      exact h
    have hval : ‖g (0, x) - x‖ = ‖g (0, x)‖ + 1 := by
      have hsub : g (0, x) - x = -((‖g (0, x)‖ + 1) • x) := by
        nth_rewrite 1 [hgx]; module
      rw [hsub, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), hx, mul_one]
    rw [hval] at hdist
    linarith [norm_nonneg (g (0, x))]
  · -- no fixed value at `t = 1`
    intro x hx hcon
    simp only [pushPsi, pushPhi] at hcon
    have hpsx : Real.smoothTransition (4 * inner ℝ x x - 1) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hsx : (‖x‖)⁻¹ • x = x := by rw [hx]; simp
    rw [hpsx, Real.smoothTransition.one, hsx, one_smul] at hcon
    have hgz1 : g (1, x) ≠ 0 := hgnz _ (hKm 1 x (by norm_num) le_rfl hx)
    have hc1 : (‖g (1, x)‖) ≠ 0 := by simpa [norm_ne_zero_iff] using hgz1
    have hgx : g (1, x) = (‖g (1, x)‖) • x := by
      have h1 : (‖g (1, x)‖) • ((‖g (1, x)‖)⁻¹ • g (1, x)) = (‖g (1, x)‖) • x := by
        rw [hcon]
      rwa [smul_inv_smul₀ hc1] at h1
    have hdist : ‖g (1, x) - (-x)‖ ≤ 1/4 := by
      have h := hgsmall (1, x) (hKm 1 x (by norm_num) le_rfl hx)
      rw [hF1 x hx, dist_eq_norm] at h
      exact h
    have hval : ‖g (1, x) - (-x)‖ = ‖g (1, x)‖ + 1 := by
      have hsub : g (1, x) - (-x) = (‖g (1, x)‖ + 1) • x := by
        nth_rewrite 1 [hgx]; module
      rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), hx, mul_one]
    rw [hval] at hdist
    linarith [norm_nonneg (g (1, x))]

end Work.RPCore.Port.PushDisc

