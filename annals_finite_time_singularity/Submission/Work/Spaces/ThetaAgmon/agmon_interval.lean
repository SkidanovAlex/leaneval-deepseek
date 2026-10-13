import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.ThetaAgmon.AnnulusGeom
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.ThetaAgmon

open scoped Real Topology
open MeasureTheory Set Filter

/-- Elementary bound: `|t| ≤ 1/2 + t²/2` for every real `t`. -/
theorem abs_le_half_add_half_sq (t : ℝ) : |t| ≤ (1 / 2 : ℝ) + (1 / 2) * t ^ 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- **Agmon's inequality on a dyadic angular annulus.**

For `a > 0` and `φ` continuous on `[0,2a]`, differentiable on `(0,2a)` with square-integrable
derivative, one has for every `x ∈ annulus a = [a,2a]`

`φ(x)² ≤ (2/a)·∫_0^a φ² + 4a·∫_0^{2a} (φ')²`.

The proof is the classical one: for `y ∈ [0,a]` the fundamental theorem of calculus gives
`φ x - φ y = ∫_y^x φ'`, so by `(u+v)² ≤ 2u² + 2v²` and Cauchy–Schwarz on `[y,x]`

`φ(x)² ≤ 2φ(y)² + 2(x-y)·∫_y^x (φ')² ≤ 2φ(y)² + 4a·∫_0^{2a}(φ')²`,

and averaging this over `y ∈ [0,a]` produces the stated bound. -/
theorem agmon_interval {a : ℝ} (ha : 0 < a) (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Icc 0 (2 * a)))
    (hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (2 * a), HasDerivAt φ (deriv φ x) x)
    (hint : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2) (Set.Ioo (0 : ℝ) (2 * a))) :
    ∀ x ∈ Work.Spaces.ThetaAgmon.annulus a,
      (φ x) ^ 2 ≤ (2 / a) * (∫ s in (0 : ℝ)..a, (φ s) ^ 2)
        + 4 * a * (∫ s in (0 : ℝ)..(2 * a), (deriv φ s) ^ 2) := by
  intro x hx
  rw [annulus, Set.mem_Icc] at hx
  obtain ⟨hxa, hx2a⟩ := hx
  have ha0 : (0 : ℝ) ≤ a := ha.le
  have ha2a : (0 : ℝ) ≤ 2 * a := by linarith
  set B : ℝ := ∫ s in (0 : ℝ)..(2 * a), (deriv φ s) ^ 2 with hBdef
  -- ## Integrability of `(deriv φ)²` on `Ioc 0 (2a)` and on every sub-interval
  have hfsq_Ioc : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2)
      (Set.Ioc (0 : ℝ) (2 * a)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hint
  have hfsq_ii : IntervalIntegrable (fun s => (deriv φ s) ^ 2) volume (0 : ℝ) (2 * a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha2a).2 hfsq_Ioc
  have hfsq_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (2 * a))] (fun s => (deriv φ s) ^ 2) :=
    Eventually.of_forall fun s => sq_nonneg _
  -- ## Step 1: the pointwise bound, valid at every `y ∈ [0,a]`
  have key : ∀ y ∈ Set.Icc (0 : ℝ) a, (φ x) ^ 2 ≤ 2 * (φ y) ^ 2 + 4 * a * B := by
    intro y hy
    obtain ⟨hy0, hya⟩ := hy
    have hyx : y ≤ x := le_trans hya hxa
    have hfsq_yx : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2) (Set.Ioc y x) :=
      hfsq_Ioc.mono_set (Set.Ioc_subset_Ioc hy0 hx2a)
    -- `deriv φ` is integrable on `Ioc y x`, being dominated by `1/2 + (1/2)(deriv φ)²`
    have hvol_ne : (volume : MeasureTheory.Measure ℝ) (Set.Ioc y x) ≠ ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hhalf : MeasureTheory.IntegrableOn
        (fun s => (1 / 2 : ℝ) + (1 / 2) * (deriv φ s) ^ 2) (Set.Ioc y x) :=
      (MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) hvol_ne).add
        (hfsq_yx.const_mul (1 / 2))
    have hderiv_int : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc y x) :=
      Integrable.mono' hhalf (measurable_deriv φ).aestronglyMeasurable
        (Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]
          exact abs_le_half_add_half_sq (deriv φ s))
    -- fundamental theorem of calculus on `[y,x]`
    have hcont_sub : ContinuousOn φ (Set.Icc y x) :=
      hcont.mono (Set.Icc_subset_Icc hy0 hx2a)
    have hdiff_sub : ∀ z ∈ Set.Ioo y x, HasDerivAt φ (deriv φ z) z :=
      fun z hz => hdiff z ⟨lt_of_le_of_lt hy0 hz.1, lt_of_lt_of_le hz.2 hx2a⟩
    have hii : IntervalIntegrable (deriv φ) volume y x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hyx).2 hderiv_int
    have hFTC : ∫ s in y..x, deriv φ s = φ x - φ y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyx hcont_sub hdiff_sub hii
    -- Cauchy–Schwarz on `Ioc y x`
    have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc y x)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
        (by simpa using (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol_ne))
    have hmem2 : MemLp (deriv φ) 2 (volume.restrict (Set.Ioc y x)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        (measurable_deriv φ).aestronglyMeasurable).mpr hfsq_yx
    have hcs := Work.Spaces.cs_integral hmem1 hmem2
    have e1 : (∫ s in Set.Ioc y x, (1 : ℝ) * deriv φ s) = ∫ s in y..x, deriv φ s := by
      rw [intervalIntegral.integral_of_le hyx]
      simp
    have e2 : (∫ s in Set.Ioc y x, (1 : ℝ) ^ 2) = x - y := by
      rw [one_pow, setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ x - y)]
      simp
    have hI2_nonneg : 0 ≤ ∫ s in Set.Ioc y x, (deriv φ s) ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s _ => sq_nonneg _))
    have hB_ge : (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) ≤ B := by
      rw [hBdef]
      have h := intervalIntegral.integral_mono_interval (f := fun s => (deriv φ s) ^ 2)
        (c := (0 : ℝ)) (d := 2 * a) hy0 hyx hx2a hfsq_nonneg hfsq_ii
      rwa [intervalIntegral.integral_of_le hyx] at h
    have hI2_le : (∫ s in y..x, deriv φ s) ^ 2 ≤ (2 * a) * B := by
      have h1 : (∫ s in y..x, deriv φ s) ^ 2
          ≤ (x - y) * (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) := by
        rw [← e1, ← e2]
        exact hcs
      have h2 : (x - y) * (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) ≤ (2 * a) * B :=
        mul_le_mul (by linarith) hB_ge hI2_nonneg ha2a
      linarith
    have hFTC' : φ x = φ y + ∫ s in y..x, deriv φ s := by linarith
    have hsq : (φ x) ^ 2 ≤ 2 * (φ y) ^ 2 + 2 * (∫ s in y..x, deriv φ s) ^ 2 := by
      rw [hFTC']
      nlinarith [sq_nonneg (φ y - ∫ s in y..x, deriv φ s)]
    nlinarith [hsq, hI2_le]
  -- ## Step 2: average the pointwise bound over `y ∈ [0,a]`
  have hcont_a : ContinuousOn φ (Set.Icc (0 : ℝ) a) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hf2 : IntervalIntegrable (fun y => 2 * (φ y) ^ 2) volume (0 : ℝ) a :=
    ((hcont_a.pow 2).const_mul 2).intervalIntegrable_of_Icc ha0
  have hg2 : IntervalIntegrable (fun _ : ℝ => 4 * a * B) volume (0 : ℝ) a :=
    intervalIntegrable_const
  have hgi : IntervalIntegrable (fun y => 2 * (φ y) ^ 2 + 4 * a * B) volume (0 : ℝ) a :=
    (((hcont_a.pow 2).const_mul 2).add continuousOn_const).intervalIntegrable_of_Icc ha0
  have hfi : IntervalIntegrable (fun _ : ℝ => (φ x) ^ 2) volume (0 : ℝ) a :=
    intervalIntegrable_const
  have hmono : (∫ y in (0 : ℝ)..a, (φ x) ^ 2)
      ≤ ∫ y in (0 : ℝ)..a, (2 * (φ y) ^ 2 + 4 * a * B) :=
    intervalIntegral.integral_mono_on ha0 hfi hgi (fun y hy => key y hy)
  have hL : (∫ y in (0 : ℝ)..a, (φ x) ^ 2) = a * (φ x) ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp
  have hR : (∫ y in (0 : ℝ)..a, (2 * (φ y) ^ 2 + 4 * a * B))
      = 2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B := by
    rw [intervalIntegral.integral_add hf2 hg2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp
    ring
  have hmain : a * (φ x) ^ 2 ≤ 2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B := by
    rw [hL, hR] at hmono
    linarith [hmono]
  have hquot : (φ x) ^ 2
      ≤ (2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B) / a :=
    (le_div_iff₀ ha).2 (by linarith [hmain])
  have heq : (2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B) / a
      = (2 / a) * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a * B := by
    field_simp
  rw [heq] at hquot
  simpa [hBdef] using hquot

end Work.Spaces.ThetaAgmon
