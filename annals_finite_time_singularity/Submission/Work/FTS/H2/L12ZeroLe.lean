import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.H2.CS1D
import Submission.Work.FTS.H2.SliceFacts
import Submission.Work.FTS.H2.PhiWeight
import Submission.Work.FTS.H2.L12densSlice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-- Elgindi, first line of the proof of Proposition `muestimate` (tex 1516): for `f` of `ℋ⁴`,
`|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}` (`C` universal), which the paper states in the form
`|L₁₂(f)(0)| ≤ C |((z+1)/z) f|_{L²}` together with
`|((z+1)/z) f|_{L²}² = ∫∫ f² w ≤ ∫∫ f² w²/sin(2θ)^η ≤ |f|²_{ℋ⁴}`.

`Work.Elliptic.L12 f 0 = ∫_{r>0} ∫_θ K(θ) f(r,θ)/r dθ dr` with `K(θ) = 3 sinθ cos²θ`: split the
`θ`-integral by Cauchy--Schwarz against `K ∈ L²(Iθ)`, then the `r`-integral by Cauchy--Schwarz
against `∫_0^∞ (1+r)^{-2} dr`, using `1/r = ((1+r)/r)·(1+r)^{-1}` and
`∫∫ f² ((1+r)/r)² = |((z+1)/z)f|²_{L²} ≤ HkSq α 4 f`. -/
theorem L12ZeroLe : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f → Work.Spaces.HkMem α 4 f →
    |Work.Elliptic.L12 f 0| ≤ C * Work.Spaces.HkNorm α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f hα hα1 hsm hmem
  obtain ⟨hslice_cont, hslice_int, hPhi_aesm⟩ := SliceFacts (f := f) hsm
  obtain ⟨hPhiw_int, hPhiw_le⟩ := PhiWeight α f hsm hmem
  obtain ⟨hB_int, hB_le⟩ := InvOneAddSq
  -- the angular energy of a slice is nonnegative
  have hΦ0 : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- abbreviations
  set A : ℝ → ℝ := fun r => Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      * ((1 + r) / r) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  -- ## nonnegativity of `A` and `B` a.e.
  have hAe0 : ∀ᵐ r ∂μ, 0 ≤ A r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hAdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg _))
      (div_nonneg (by linarith) (le_of_lt hr'))
  have hBe0 : ∀ᵐ r ∂μ, 0 ≤ B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hBdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact div_nonneg zero_le_one (by linarith)
  -- ## `A` is a.e. strongly measurable
  have hAmeas : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hμdef, hAdef]
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hPhi_aesm
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => (1 + r) / r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
        (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
    exact (aestronglyMeasurable_const.mul h1).mul h2
  -- ## `A²` is integrable and is the Hardy-weighted angular energy
  have hpt : ∀ r : ℝ,
      A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
    intro r
    rw [hAdef, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (hΦ0 r)]
    ring
  have h33 : MeasureTheory.Integrable
      (fun r : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)) μ := by
    rw [hμdef]
    exact hPhiw_int.const_mul 3
  have hAint : MeasureTheory.Integrable (fun r => A r ^ 2) μ := by
    refine h33.congr ?_
    filter_upwards with r
    exact (hpt r).symm
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  -- ## `B` is a.e. strongly measurable and `B²` is integrable
  have hBmeas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
        (fun r hr => by
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only using h2
  have hBint : MeasureTheory.Integrable (fun r => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact hB_int
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  -- ## the pointwise bound on the density
  have hbd : ∀ᵐ r ∂μ, |Work.Elliptic.L12dens f r| ≤ A r * B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    have h5 := L12densSlice f hsm hr
    have hr0 : r ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hr)
    have hr1 : 1 + r ≠ 0 := by have h := Set.mem_Ioi.mp hr; linarith
    have h5' : |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := by
      simpa only [div_eq_mul_inv] using h5
    have hkey : ((1 + r) / r) * (1 / (1 + r)) = r⁻¹ := by
      field_simp
    rw [hAdef, hBdef]
    dsimp only
    calc |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := h5'
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * (((1 + r) / r) * (1 / (1 + r))) := by rw [hkey]
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * ((1 + r) / r) * (1 / (1 + r)) := by ring
  -- ## Cauchy–Schwarz in the radial variable
  have hcs := CS1D (μ := μ) (g := fun r => Work.Elliptic.L12dens f r)
    hmemA hmemB hAe0 hBe0 hbd
  -- ## the two `L²` norms
  have hA2le : ∫ r, A r ^ 2 ∂μ ≤ 3 * Work.Spaces.HkSq α 4 f := by
    rw [hμdef]
    have hpt' : ∀ r ∈ Set.Ioi (0 : ℝ),
        A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
      fun r _ => hpt r
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ),
            3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt'
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ),
            (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_left hPhiw_le (by norm_num)
  have hB2le : ∫ r, B r ^ 2 ∂μ ≤ 2 := by
    rw [hμdef]
    have hfun : (fun r : ℝ => B r ^ 2) = fun r : ℝ => (1 / (1 + r)) ^ 2 := by
      funext r
      rw [hBdef]
    rw [hfun]
    exact hB_le
  -- ## assembly
  have hfinal : |Work.Elliptic.L12 f 0| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := by
    have h1 : (∫ r, Work.Elliptic.L12dens f r ∂μ) = Work.Elliptic.L12 f 0 := rfl
    rw [← h1]
    refine hcs.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg (∫ r, B r ^ 2 ∂μ)) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2
      = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (Work.Spaces.HkSq α 4 f),
      Work.Spaces.HkNorm]
    rw [show Real.sqrt 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6le : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Elliptic.L12 f 0|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := hsqrt
    _ ≤ 3 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right h6le (Work.Spaces.HkNorm_nonneg α 4 f)

end Work.FTS.H2
