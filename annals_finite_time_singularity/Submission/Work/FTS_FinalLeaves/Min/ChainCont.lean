import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS_FinalLeaves.Min.FstarFacts
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Continuity of the angular moment and of the `L₁₂`-density of a `C⁴` datum -/

/-- **Continuity of the angular moment** from the four analytic inputs, with the smoothness
hypothesis of `Work.FTS.CoercivityFix.Coer1T.HardyAlt.Fstar_continuousAt_of_aux` replaced by the
*chain relation* `F_*(F)(b) = F_*(F)(a) + ∫_a^b (∂_z-moment)`.  The proof is that of the
`HardyAlt` lemma verbatim. -/
theorem Fstar_continuousAt_of_chain (α : ℝ) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hchain : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b = Work.Elliptic.Fstar f a
        + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iz)
    (hmom : ∀ s : ℝ, 0 < s →
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
        ≤ Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) :
    ContinuousAt (Work.Elliptic.Fstar f) z := by
  have hle : z / 2 ≤ 2 * z := by linarith
  set M : ℝ → ℝ := fun r =>
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ with hMdef
  set Ψ : ℝ → ℝ := fun r => Real.sqrt (Real.pi / 2)
    * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) with hΨdef
  have hΨnn : ∀ r : ℝ, 0 ≤ Ψ r := fun r => by
    rw [hΨdef]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hchain' : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b - Work.Elliptic.Fstar f a = ∫ r in Set.Icc a b, M r := by
    intro a b ha hab
    have h := hchain a b ha hab
    simp only [hMdef]
    linarith [h]
  -- integrability of the majorant near `z`
  have hBint : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Icc (z / 2) (2 * z)) :=
    hB.mono_set (fun x hx => by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      linarith [hz, hx.1])
  have hdom : MeasureTheory.IntegrableOn
      (fun r => Real.sqrt (Real.pi / 2)
        * (|(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1))
      (Set.Icc (z / 2) (2 * z)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun r => |(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1)
        (Set.Icc (z / 2) (2 * z)) :=
      hBint.abs.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp))
    exact h1.const_mul (Real.sqrt (Real.pi / 2))
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Icc (z / 2) (2 * z)) := by
    refine hdom.mono' ?_ ?_
    · rw [hΨdef]
      exact aestronglyMeasurable_const.mul
        ((hBint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable)
    · filter_upwards with r
      rw [hΨdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (sqrt_le_abs_add_one _)
        (Real.sqrt_nonneg _)
  have hΨu : MeasureTheory.IntegrableOn Ψ (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle]
    exact hΨint
  have hprim : ContinuousOn (fun t => ∫ r in z..t, Ψ r) (Set.uIcc (z / 2) (2 * z)) :=
    intervalIntegral.continuousOn_primitive_interval' hΨu.intervalIntegrable
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
  have hprim_at : ContinuousAt (fun t => ∫ r in z..t, Ψ r) z :=
    hprim.continuousAt
      (by
        rw [Set.uIcc_of_le hle]
        exact Icc_mem_nhds (by linarith) (by linarith))
  have htend : Tendsto (fun t => ‖∫ r in z..t, Ψ r‖) (𝓝 z) (𝓝 0) := by
    have h := hprim_at.norm
    rw [ContinuousAt] at h
    simpa using h
  have hsymm : ∀ t : ℝ, t ≤ z → ‖∫ r in z..t, Ψ r‖ = ∫ r in t..z, Ψ r := by
    intro t ht
    rw [Real.norm_eq_abs, intervalIntegral.integral_symm t z, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg ht (fun r _ => hΨnn r))]
  have hbd_of : ∀ a b : ℝ, z / 2 ≤ a → a ≤ b → b ≤ 2 * z →
      |∫ r in a..b, M r| ≤ ∫ r in a..b, Ψ r := by
    intro a b ha hab hb
    have ha' : 0 < a := by linarith
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have hrpos : 0 < r := lt_trans ha' hr.1
      simp only [Real.norm_eq_abs, hMdef, hΨdef]
      exact hmom r hrpos
    · have hss : Set.uIcc a b ⊆ Set.Icc (z / 2) (2 * z) := by
        rw [Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc ha hb
      exact (hΨint.mono_set hss).intervalIntegrable
  have hev : ∀ᶠ s in 𝓝 z, ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖
      ≤ ‖∫ r in z..s, Ψ r‖ := by
    filter_upwards [Icc_mem_nhds (by linarith : z / 2 < z) (by linarith : z < 2 * z)]
      with s hs
    have hs1 : 0 < s := by linarith [hs.1]
    have hs2 : s ≤ 2 * z := by linarith [hs.2]
    rcases lt_trichotomy z s with hzs | hzs | hsz
    · have hch := hchain' z s hz hzs
      have hIcc : (∫ r in Set.Icc z s, M r) = ∫ r in z..s, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hzs.le]
      have hbd := hbd_of z s (by linarith) hzs.le hs2
      have hΨi : 0 ≤ ∫ r in z..s, Ψ r :=
        intervalIntegral.integral_nonneg hzs.le (fun r _ => hΨnn r)
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in z..s, M r| ≤ ∫ r in z..s, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [abs_of_nonneg hΨi]
    · subst hzs
      simp
    · have hch := hchain' s z hs1 hsz
      have hIcc : (∫ r in Set.Icc s z, M r) = ∫ r in s..z, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hsz.le]
      have hbd := hbd_of s z hs.1 hsz.le (by linarith [hs2])
      rw [norm_sub_rev]
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in s..z, M r| ≤ ∫ r in s..z, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [← Real.norm_eq_abs, hsymm s hsz.le]
  have hnorm : Tendsto (fun s => ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖)
      (𝓝 z) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) hev htend
  have hdiff : Tendsto (fun s => Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
      (𝓝 z) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcont : ContinuousAt (Work.Elliptic.Fstar f) z := by
    have h2 := hdiff.add_const (Work.Elliptic.Fstar f z)
    have h3 : (fun s => (Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
        + Work.Elliptic.Fstar f z) = Work.Elliptic.Fstar f := by
      funext s; ring
    rw [h3] at h2
    simpa [ContinuousAt] using h2
  exact hcont

end Work.FTS_FinalLeaves.Min
