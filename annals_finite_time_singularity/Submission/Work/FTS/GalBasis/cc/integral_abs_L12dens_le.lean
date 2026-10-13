import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory Filter

/-- **The integrated pointwise bound on the `L₁₂`-density.**
If `|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α 4 h s θ))` for every `s > 0` and
`h ∈ ℋ⁴_α`, then the same bound holds after integrating in `s`:

`∫_{s>0} |L12dens h s| ≤ BK · √W2 · √(HkSq α 4 h)`.

This is Cauchy–Schwarz in the radial variable: the weight `Wlam` is square-integrable on
`(0,∞)` with `∫ Wlam² = W2`, and `∫_{(0,∞)} (√(∫_θ HkIntegrand))² = HkSq α 4 h`
(the two sets `(0,∞)` and `ℤ = [0,∞)` differ by the null set `{0}`). -/
theorem integral_abs_L12dens_le (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 h)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- `H` is integrable on `(0,∞)` (hence so is `A²`)
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(0,∞)} A² = HkSq α 4 h`, up to the null set `{0}`
  have hW2eq : ∫ s in Set.Ioi 0, Wlam s ^ 2 = W2 := rfl
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 h := by
    rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 4 h := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi 0) hWlam_memLp hA_memLp
    rw [hA2sq, hW2eq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s)
    rwa [abs_of_nonneg hnn] at hcs
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi 0, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi 0, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi 0, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) := by ring

end Work.FTS.GalBasis.cc
