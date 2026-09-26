import Mathlib
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.isUnknotted_of_cInf_isotopy
import Submission.Work.Drive.isUnknotted_of_path_to_unknotted
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.exists_analytic_close_twoVar
import Submission.Work.Drive.uniformCorrection_clauses
import Submission.Work.Drive.isUnknotted_of_cInf_knotPath

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Unknottedness propagates backwards along a `C¹` path of `C^∞` knots

This is the `C^∞`-slices counterpart of `Work.Drive.isUnknotted_of_path_to_unknotted`, in the
spirit of `Work.Drive.isUnknotted_of_cInf_knotPath`.  Let `F` be a jointly `C¹` family on the slab
`s ∈ [0,1]` whose slices `F · s` are `C^∞` knots (`Work.Drive.IsCInfKnot`), running from `r0` to
`r1`, and suppose the terminal knot `r1` is *unknotted*.  Then `r0` is unknotted.

The `C¹` parameter-dependence is smoothed by trigonometric approximation
(`Work.Drive.exists_analytic_close_twoVar`): an analytic, `period`-periodic `G` close to `F` in
`C¹` on the slab.  Correcting `G` by `s • (r1 - G · 1)` gives a jointly *analytic* family `H` with
`H · 0 = G · 0` and `H · 1 = r1`, whose slices are still knots because the correction is uniformly
`C¹`-small (`Work.Drive.uniformCorrection_clauses_Icc`).  Since the terminal knot `r1` is
unknotted, `Work.Drive.isUnknotted_of_path_to_unknotted` makes `G · 0` unknotted, and
`Work.Drive.isUnknotted_of_close` at `r0` finishes.
-/

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

theorem cInfKnotPath_to_unknotted {r0 r1 : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr0 : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r0)
    (hr1 : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r1)
    (hU : LeanEval.KnotTheory.Quadrisecant.IsUnknotted r1)
    {F : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ s t : ℝ, F (t + LeanEval.KnotTheory.Quadrisecant.period) s = F t s)
    (h0 : ∀ t : ℝ, F t 0 = r0 t) (h1 : ∀ t : ℝ, F t 1 = r1 t)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted r0 := by
  -- periodicity of the slices of `F` on the slab
  have hperF : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, F (t + period) s = F t s :=
    fun s _ t => hper s t
  -- the uniform correction radius for the family `F`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := uniformCorrection_clauses_Icc hF hperF hslice
  -- the openness radius of unknottedness at `r0`
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := isUnknotted_of_close hr0
  -- the approximation radius
  set ε : ℝ := min (ε₁ / 4) (ε₂ / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by linarith) (by linarith)
  have hε_le₁ : ε ≤ ε₁ / 4 := by rw [hεdef]; exact min_le_left _ _
  have hε_le₂ : ε ≤ ε₂ / 2 := by rw [hεdef]; exact min_le_right _ _
  have h2ε_le₁ : 2 * ε ≤ ε₁ := by linarith
  have hε_lt₂ : ε < ε₂ := by linarith
  obtain ⟨G, hGsm, hGper, hGval, hGder⟩ := exists_analytic_close_twoVar hF hper hεpos
  -- the correcting curve and the corrected family
  set c : ℝ → Space := fun t => r1 t - G t 1 with hcdef
  set W : ℝ → ℝ → Space := fun t s => G t s - F t s + s • c t with hWdef
  set H : ℝ → ℝ → Space := fun t s => G t s + s • c t with hHdef
  have hc_sm : ContDiff ℝ ⊤ c := by
    rw [hcdef]
    exact hr1.smooth.sub (slice_contDiff_analytic hGsm 1)
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
    rw [hr1.periodic t, hGper 1 t]
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
  have hH1 : ∀ t : ℝ, H t 1 = r1 t := by
    intro t; simp only [hHdef, hcdef]; simp
  -- the analytic knot `G(·,0)` is unknotted, because `r1` is
  have hrG : IsSmoothKnot (fun t : ℝ => G t 0) := by
    have h := hHslice 0 (by norm_num)
    rwa [show (fun t : ℝ => H t 0) = (fun t : ℝ => G t 0) from funext hH0] at h
  have hunG : IsUnknotted (fun t : ℝ => G t 0) :=
    isUnknotted_of_path_to_unknotted hrG hr1 hU hHsm hH0 hH1 hHslice
  -- `r0 = F(·,0)` is `C¹`-close to `G(·,0)`, so it is unknotted too
  refine hε₂ (fun t : ℝ => G t 0) hrG ?_ hunG
  intro t
  constructor
  · have h := hGval 0 (by norm_num) t
    rw [norm_sub_rev] at h
    rw [← h0 t]
    exact lt_trans h hε_lt₂
  · have h := hGder 0 (by norm_num) t
    rw [norm_sub_rev] at h
    have hr_eq : r0 = fun u : ℝ => F u 0 := (funext h0).symm
    rw [hr_eq]
    simpa only [velocity] using lt_trans h hε_lt₂

end Work.Drive
