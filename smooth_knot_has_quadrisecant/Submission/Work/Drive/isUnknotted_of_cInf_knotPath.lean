import Mathlib
import Submission.Work.Drive.uniformCorrection_clauses
import Submission.Work.Drive.isUnknotted_of_knotPath
import Submission.Work.Drive.cInfKnot

open LeanEval.KnotTheory.Quadrisecant

/-!
# `IsUnknotted` from a `C¹` path of `C^∞` knots with analytic approximations

Target of this file: `Work.Drive.isUnknotted_of_cInf_knotPath`.  It is the `C^∞` counterpart of
`Work.Drive.isUnknotted_of_knotPath`: the path `F` of slices is merely jointly `C¹` and its slices
are only `C^∞` knots (`Work.Drive.IsCInfKnot`), not analytic ones.  What makes up for that is the
hypothesis `happrox`: every `C¹`-neighbourhood of `F` on the slab contains a *jointly analytic*,
`period`-periodic family `G`.  (`Work.Drive.exists_analytic_periodic_close` produces such a `G` by
mollification.)

The argument:

* `uniformCorrection_clauses_Icc` (proved here; the same statement as the existing
  `Work.Drive.uniformCorrection_clauses` but with the periodicity hypotheses only on the slab)
  gives a radius `ε₁` such that every `C¹`-small `period`-periodic correction `W` of `F` on the
  slab has knot slices.
* Choose `G` analytically close to `F` with `ε = min (ε₁/4) (ε₂/2)`, where `ε₂` is the openness
  radius of `Work.Drive.isUnknotted_of_close` for `r`.
* Put `H(t,s) = G(t,s) + s • (standardCircle t - G(t,1))`.  Then `H` is *jointly analytic*,
  `H(·,0) = G(·,0)`, `H(·,1) = standardCircle`, and `H = F + W` with
  `W(t,s) = G(t,s) - F(t,s) + s • (standardCircle t - G(t,1))`, which is `C¹`-small on the slab
  (both in value and in `t`-derivative, because `F(·,1) = standardCircle`), hence `ε₁`-small:
  every slice `H(·,s)`, `s ∈ [0,1]`, is an analytic knot.
* `isUnknotted_of_knotPath` therefore shows that the analytic knot `G(·,0)` is unknotted, and
  since `G(·,0)` is `C¹`-close to `r = F(·,0)` we conclude with `isUnknotted_of_close`.
-/

namespace Work.Drive

/-- **`uniformCorrection_clauses` with slab-restricted hypotheses.**  Identical to
`Work.Drive.uniformCorrection_clauses`, except that the `t`-periodicity of `F` and of the
correction `W` are only assumed on the slab `s ∈ [0,1]` -- which is all the proof uses. -/
theorem uniformCorrection_clauses_Icc {F : ℝ → ℝ → Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, F (t + period) s = F t s)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W : ℝ → ℝ → Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => W p.1 p.2) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, W (t + period) s = W t s) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖W t s‖ < ε ∧
        ‖deriv (fun u : ℝ => W u s) t‖ < ε) →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        Function.Periodic (fun t : ℝ => F t s + W t s) period ∧
          Set.InjOn (fun t : ℝ => F t s + W t s) (Set.Ico 0 period) ∧
            ∀ t : ℝ, velocity (fun t : ℝ => F t s + W t s) t ≠ 0 := by
  obtain ⟨m, δ, σ, hm, _hδ, _hδ2, hσ, hb⟩ := uniformBoundsC1 hF hslice
  refine ⟨min (m / 4) (σ / 4), lt_min (by linarith) (by linarith), ?_⟩
  intro W hWsm hWper hWsmall s hs
  have hrper : Function.Periodic (fun t : ℝ => F t s) period := fun t => hper s hs t
  have hrdiff : Differentiable ℝ (fun t : ℝ => F t s) :=
    (hslice s hs).1.differentiable (by decide)
  have hwsm : ContDiff ℝ 1 (fun t : ℝ => W t s) :=
    hWsm.comp (contDiff_id.prodMk contDiff_const)
  have hwper : Function.Periodic (fun t : ℝ => W t s) period := fun t => hWper s hs t
  exact correction_clauses_of_bounds (r := fun t : ℝ => F t s) hrdiff hrper hm hσ
    (lt_min (by linarith) (by linarith)) (min_le_left _ _) (min_le_right _ _)
    (hb s hs).1 (hb s hs).2.1 (hb s hs).2.2 (fun t => W t s) hwsm hwper
    (fun t => (hWsmall s hs t).1)
    (fun t => by simpa only [velocity] using (hWsmall s hs t).2)

/-- The slice of a jointly analytic family is an analytic curve. -/
private lemma slice_contDiff_analytic {G : ℝ → ℝ → Space}
    (hG : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => G p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ⊤ (fun t : ℝ => G t s) :=
  hG.comp (contDiff_id.prodMk contDiff_const)

/-- The slice of a jointly `C¹` family is a `C¹` curve. -/
private lemma slice_contDiff_c1 {F : ℝ → ℝ → Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) (s : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => F t s) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

/-- A slice of a jointly analytic family is differentiable. -/
private lemma diffAt_slice_analytic {G : ℝ → ℝ → Space}
    (hG : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => G p.1 p.2)) (s t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => G u s) t :=
  ((slice_contDiff_analytic hG s).differentiable (by decide)).differentiableAt

/-- A slice of a jointly `C¹` family is differentiable. -/
private lemma diffAt_slice_c1 {F : ℝ → ℝ → Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) (s t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => F u s) t :=
  ((slice_contDiff_c1 hF s).differentiable (by decide)).differentiableAt

theorem isUnknotted_of_cInf_knotPath {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {F : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (h0 : ∀ t : ℝ, F t 0 = r t)
    (h1 : ∀ t : ℝ, F t 1 = LeanEval.KnotTheory.Quadrisecant.standardCircle t)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ G : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ => G p.1 p.2) ∧
        (∀ s t : ℝ, G (t + LeanEval.KnotTheory.Quadrisecant.period) s = G t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖F t s - G t s‖ < ε) ∧
            (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
              ‖deriv (fun u : ℝ => F u s) t - deriv (fun u : ℝ => G u s) t‖ < ε)) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted r := by
  -- periodicity of the slices of `F`
  have hperF : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, F (t + period) s = F t s :=
    fun s hs t => (hslice s hs).2.1 t
  -- the uniform correction radius for the family `F`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := uniformCorrection_clauses_Icc hF hperF hslice
  -- the openness radius of unknottedness at `r`
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := isUnknotted_of_close hr
  -- the approximation radius
  set ε : ℝ := min (ε₁ / 4) (ε₂ / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by linarith) (by linarith)
  have hε_le₁ : ε ≤ ε₁ / 4 := by rw [hεdef]; exact min_le_left _ _
  have hε_le₂ : ε ≤ ε₂ / 2 := by rw [hεdef]; exact min_le_right _ _
  have h2ε_le₁ : 2 * ε ≤ ε₁ := by linarith
  have hε_lt₂ : ε < ε₂ := by linarith
  obtain ⟨G, hGsm, hGper, hGval, hGder⟩ := happrox ε hεpos
  -- the correcting curve and the corrected family
  set c : ℝ → Space := fun t => standardCircle t - G t 1 with hcdef
  set W : ℝ → ℝ → Space := fun t s => G t s - F t s + s • c t with hWdef
  set H : ℝ → ℝ → Space := fun t s => G t s + s • c t with hHdef
  have hc_sm : ContDiff ℝ ⊤ c := by
    rw [hcdef]
    exact standardCircle_contDiff.sub (slice_contDiff_analytic hGsm 1)
  have hc_diff : Differentiable ℝ c := hc_sm.differentiable (by simp)
  -- joint regularity of `H` and of `W`
  have hGsm_c1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => G p.1 p.2) := hGsm.of_le le_top
  have hc_sm_c1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => c p.1) := hc_sm.of_le le_top |>.comp contDiff_fst
  have hHsm : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) := by
    rw [hHdef]
    exact (hGsm_c1.add (contDiff_snd.smul hc_sm_c1))
  have hWsm : ContDiff ℝ 1 (fun p : ℝ × ℝ => W p.1 p.2) := by
    rw [hWdef]
    exact ((hGsm_c1.sub hF).add (contDiff_snd.smul hc_sm_c1))
  -- `t`-periodicity of the correction
  have hc_per : Function.Periodic c period := by
    intro t
    simp only [hcdef]
    rw [standardCircle_periodic t, hGper 1 t]
  have hWper : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, W (t + period) s = W t s := by
    intro s hs t
    simp only [hWdef]
    rw [hGper s t, hperF s hs t, hc_per t]
  -- `C¹`-smallness of the correction on the slab
  have hsabs : ∀ s ∈ Set.Icc (0 : ℝ) 1, |s| ≤ 1 := by
    intro s hs
    rw [abs_of_nonneg hs.1]; exact hs.2
  have hWval : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖W t s‖ < ε₁ := by
    intro s hs t
    have hc_bound : ‖c t‖ < ε := by
      simp only [hcdef]
      have h := hGval 1 (by norm_num) t
      rwa [h1 t] at h
    have hGF : ‖G t s - F t s‖ < ε := by
      have h := hGval s hs t
      rwa [norm_sub_rev] at h
    have hs1 : |s| ≤ 1 := hsabs s hs
    calc ‖W t s‖ = ‖(G t s - F t s) + s • c t‖ := by simp only [hWdef]
      _ ≤ ‖G t s - F t s‖ + ‖s • c t‖ := norm_add_le _ _
      _ = ‖G t s - F t s‖ + |s| * ‖c t‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖G t s - F t s‖ + 1 * ‖c t‖ := by
            have h := mul_le_mul_of_nonneg_right hs1 (norm_nonneg (c t))
            linarith
      _ < ε + ε := by linarith
      _ ≤ ε₁ := by linarith
  have hWder : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖deriv (fun u : ℝ => W u s) t‖ < ε₁ := by
    intro s hs t
    have hGd : DifferentiableAt ℝ (fun u : ℝ => G u s) t := diffAt_slice_analytic hGsm s t
    have hFd : DifferentiableAt ℝ (fun u : ℝ => F u s) t := diffAt_slice_c1 hF s t
    have hcd : DifferentiableAt ℝ c t := hc_diff.differentiableAt
    have hdW : deriv (fun u : ℝ => W u s) t
        = (deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t)
            + s • deriv c t := by
      have hWs : (fun u : ℝ => W u s) = (fun u : ℝ => G u s - F u s + s • c u) := by
        ext u; simp only [hWdef]
      rw [hWs]
      have hH : HasDerivAt ((fun u : ℝ => G u s) - (fun u : ℝ => F u s) + s • c)
          ((deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t)
            + s • deriv c t) t :=
        (hGd.hasDerivAt.sub hFd.hasDerivAt).add (hcd.hasDerivAt.const_smul s)
      exact hH.deriv
    have hGF' : ‖deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t‖ < ε := by
      have h := hGder s hs t
      rwa [norm_sub_rev] at h
    have hc_der : ‖deriv c t‖ < ε := by
      have hc_eq : c = (fun u : ℝ => F u 1) - (fun u : ℝ => G u 1) := by
        ext u
        simp only [hcdef, Pi.sub_apply]
        rw [h1 u]
      have hFd1 : DifferentiableAt ℝ (fun u : ℝ => F u 1) t := diffAt_slice_c1 hF 1 t
      have hGd1 : DifferentiableAt ℝ (fun u : ℝ => G u 1) t := diffAt_slice_analytic hGsm 1 t
      have hder : deriv c t
          = deriv (fun u : ℝ => F u 1) t - deriv (fun u : ℝ => G u 1) t := by
        rw [hc_eq]
        exact (hFd1.hasDerivAt.sub hGd1.hasDerivAt).deriv
      rw [hder]
      exact hGder 1 (by norm_num) t
    have hs1 : |s| ≤ 1 := hsabs s hs
    calc ‖deriv (fun u : ℝ => W u s) t‖
        = ‖(deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t)
            + s • deriv c t‖ := by rw [hdW]
      _ ≤ ‖deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t‖
            + ‖s • deriv c t‖ := norm_add_le _ _
      _ = ‖deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t‖
            + |s| * ‖deriv c t‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖deriv (fun u : ℝ => G u s) t - deriv (fun u : ℝ => F u s) t‖
            + 1 * ‖deriv c t‖ := by
            have h := mul_le_mul_of_nonneg_right hs1 (norm_nonneg (deriv c t))
            linarith
      _ < ε + ε := by linarith
      _ ≤ ε₁ := by linarith
  have hWsmall : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖W t s‖ < ε₁ ∧ ‖deriv (fun u : ℝ => W u s) t‖ < ε₁ :=
    fun s hs t => ⟨hWval s hs t, hWder s hs t⟩
  have hHclauses := hε₁ W hWsm hWper hWsmall
  -- analyticity of the slices of `H`
  have hHslice_sm : ∀ s : ℝ, ContDiff ℝ ⊤ (fun t : ℝ => H t s) := by
    intro s
    rw [hHdef]
    exact (slice_contDiff_analytic hGsm s).add (hc_sm.const_smul s)
  -- every slice of `H` is a knot
  have hHslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsSmoothKnot (fun t : ℝ => H t s) := by
    intro s hs
    have hcl := hHclauses s hs
    have heq : (fun t : ℝ => F t s + W t s) = fun t : ℝ => H t s := by
      funext t
      simp only [hWdef, hHdef]
      abel
    exact ⟨hHslice_sm s, by rw [← heq]; exact hcl.1,
      by rw [← heq]; exact hcl.2.1, by intro t; rw [← heq]; exact hcl.2.2 t⟩
  -- the endpoints of `H`
  have hH0 : ∀ t : ℝ, H t 0 = G t 0 := by
    intro t; simp only [hHdef]; simp
  have hH1 : ∀ t : ℝ, H t 1 = standardCircle t := by
    intro t; simp only [hHdef, hcdef]; simp
  -- the analytic knot `G(·,0)` is unknotted
  have hrG : IsSmoothKnot (fun t : ℝ => G t 0) := by
    have h := hHslice 0 (by norm_num)
    rwa [show (fun t : ℝ => H t 0) = (fun t : ℝ => G t 0) from funext hH0] at h
  have hunG : IsUnknotted (fun t : ℝ => G t 0) :=
    isUnknotted_of_knotPath hrG hHsm hH0 hH1 hHslice
  -- `r = F(·,0)` is `C¹`-close to `G(·,0)`, so it is unknotted too
  refine hε₂ (fun t : ℝ => G t 0) hrG ?_ hunG
  intro t
  constructor
  · have h := hGval 0 (by norm_num) t
    rw [norm_sub_rev] at h
    rw [← h0 t]
    exact lt_trans h hε_lt₂
  · have h := hGder 0 (by norm_num) t
    rw [norm_sub_rev] at h
    have hr_eq : r = fun u : ℝ => F u 0 := (funext h0).symm
    rw [hr_eq]
    simpa only [velocity] using lt_trans h hε_lt₂

end Work.Drive
