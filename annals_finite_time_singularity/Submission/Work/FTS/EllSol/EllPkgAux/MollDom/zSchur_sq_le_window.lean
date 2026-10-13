import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The logarithmic Schur bound on the window, with the explicit constant.**

For `δ > 0` and a kernel `K = sKerd δ` which is bounded by `M` and vanishes off `[-δ, δ]`, the
functional `y ↦ ∫ t, K (log z - t) · y t` satisfies

  `(∫ t, K (log z - t) · y t)² ≤ 2 δ M² ∫ t, 1_{|log z - t| ≤ δ} y t²`

for every `y` whose windowed square is integrable (and whose windowed restriction is
a.e.-strongly measurable).  The right-hand side only sees the window
`S = [log z - δ, log z + δ]`, on which the kernel lives and on which it is bounded by `M`; the
integral of `K²` over `S` is therefore at most `M² · |S| = 2 δ M²`, and Cauchy–Schwarz
(`Work.Spaces.cs_integral`) on the window finishes. -/
theorem zSchur_sq_le_window {δ z M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hk : ∀ u : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ u| ≤ M)
    (hvan : ∀ u : ℝ, δ < |u| → Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0)
    {y : ℝ → ℝ} (hz : 0 < z)
    (hy : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then y t ^ 2 else 0))
    (hym : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then y t else 0) MeasureTheory.volume) :
    (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      ≤ 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
  -- The window on which the kernel lives.
  set S : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ) with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict S) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, hSdef, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- Membership in `S` is membership in the window.
  have hmem : ∀ t : ℝ, t ∈ S ↔ |Real.log z - t| ≤ δ := by
    intro t
    rw [hSdef, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- The window has length `2 δ`.
  have hrealS : volume.real S = 2 * δ := by
    have hvolS : volume S = ENNReal.ofReal (2 * δ) := by
      rw [hSdef, Real.volume_Icc]; congr 1; ring
    rw [MeasureTheory.Measure.real_def, hvolS, ENNReal.toReal_ofReal (by linarith)]
  -- The kernel as a function of `t`, and the windowed datum.
  set F : ℝ → ℝ := fun t => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) with hFdef
  set g : ℝ → ℝ := fun t => if |Real.log z - t| ≤ δ then y t else 0 with hgdef
  -- The kernel vanishes off the window.
  have hFzero : ∀ t : ℝ, t ∉ S → F t = 0 := by
    intro t ht
    rw [hFdef]
    exact hvan _ (lt_of_not_ge (fun hc => ht ((hmem t).mpr hc)))
  -- The square of the windowed datum is the windowed square.
  have hgsq : ∀ t : ℝ, g t ^ 2 = (if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
    intro t
    simp only [hgdef]
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; norm_num
  -- The kernel is continuous, hence a.e.-strongly measurable.
  have hFcont : Continuous F := by
    rw [hFdef]
    exact (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).comp
      (continuous_const.sub continuous_id)
  -- `F ∈ L²` on the window: it is bounded there by `M`.
  have hFmem : MemLp F 2 (volume.restrict S) :=
    MemLp.of_bound
      (hFcont.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self) M
      (MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun t _ => by
        rw [Real.norm_eq_abs, hFdef]; exact hk (Real.log z - t)))
  -- `g ∈ L²` on the window: the hypotheses give exactly this.
  have hg_int : Integrable (fun t : ℝ => g t ^ 2) volume :=
    hy.congr (Eventually.of_forall (fun t => (hgsq t).symm))
  have hgvol : MemLp g 2 volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq (by simpa only [hgdef] using hym)).mpr hg_int
  have hgind : S.indicator g = g := by
    funext t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      rw [hgdef]
      simp only [if_neg (fun hc => ht ((hmem t).mpr hc))]
  have hgmem : MemLp g 2 (volume.restrict S) :=
    (MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (f := g) (p := 2) (s := S)
      hSmeas).mp (by rwa [hgind])
  -- Cauchy–Schwarz on the window.
  have hcs := Work.Spaces.cs_integral (u := F) (v := g) hFmem hgmem
  -- The windowed `L²`-norm of the kernel is at most `2 δ M²`.
  have hFbound : ∫ t in S, F t ^ 2 ≤ 2 * δ * M ^ 2 := by
    have hpt : ∀ t : ℝ, F t ^ 2 ≤ M ^ 2 := by
      intro t
      have habs : |F t| ≤ M := by rw [hFdef]; exact hk (Real.log z - t)
      rw [show F t ^ 2 = |F t| ^ 2 by rw [sq_abs]]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have h1 : ∫ t in S, F t ^ 2 ≤ ∫ t in S, M ^ 2 :=
      MeasureTheory.setIntegral_mono_ae hFmem.integrable_sq
        (MeasureTheory.integrable_const (M ^ 2)) (Eventually.of_forall hpt)
    calc ∫ t in S, F t ^ 2 ≤ ∫ t in S, M ^ 2 := h1
      _ = volume.real S * M ^ 2 := by rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      _ = 2 * δ * M ^ 2 := by rw [hrealS]
  have hgnn : 0 ≤ ∫ t in S, g t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  -- The windowed square integral is the one displayed in the statement.
  have hwind : ∫ t in S, g t ^ 2 = ∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0 := by
    rw [← MeasureTheory.integral_indicator (μ := volume) hSmeas (f := fun t => g t ^ 2)]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [Set.indicator_apply]
    rw [hgsq t]
    by_cases ht : t ∈ S
    · rw [if_pos ht, if_pos ((hmem t).mp ht)]
    · rw [if_neg ht, if_neg (fun hc => ht ((hmem t).mpr hc))]
  -- The integral against `y` is already an integral over the window.
  have hstep1 : ∫ t : ℝ, F t * y t = ∫ t in S, F t * g t := by
    calc ∫ t : ℝ, F t * y t = ∫ t : ℝ, F t * g t :=
          MeasureTheory.integral_congr_ae (Eventually.of_forall (fun t => by
            show F t * y t = F t * g t
            by_cases ht : |Real.log z - t| ≤ δ
            · rw [hgdef]; simp only [if_pos ht]
            · have htS : t ∉ S := fun hc => ht ((hmem t).mp hc)
              rw [hFzero t htS, hgdef]; simp only [if_neg ht, mul_zero, zero_mul]))
      _ = ∫ t in S, F t * g t :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
            (f := fun t => F t * g t) (fun t ht => by rw [hFzero t ht, zero_mul])).symm
  calc (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      = (∫ t : ℝ, F t * y t) ^ 2 := rfl
    _ = (∫ t in S, F t * g t) ^ 2 := by rw [hstep1]
    _ ≤ (∫ t in S, F t ^ 2) * (∫ t in S, g t ^ 2) := hcs
    _ ≤ (2 * δ * M ^ 2) * (∫ t in S, g t ^ 2) := mul_le_mul_of_nonneg_right hFbound hgnn
    _ = 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
          rw [hwind]

end Work.FTS.EllSol.EllPkgAux.MollDom
