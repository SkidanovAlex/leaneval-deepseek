import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T2Easy

open MeasureTheory Set Filter

/-- Two-stage Cauchy–Schwarz for the iterated `L²` integral over the quadrant
`[0,∞) × [0,π/2]` (measure `dz dθ`, `Work.Spaces.Iz`, `Work.Spaces.Iθ`):
for `L2Mem` functions `U`, `V` (i.e. every angular slice of `U²`, `V²` is integrable and
`z ↦ ∫_θ U²`, `z ↦ ∫_θ V²` are integrable), `∫_z ∫_θ |U| |V| ≤ √(L2Sq U) · √(L2Sq V)`.

Suggested route, which needs NO measurability hypothesis beyond `L2Mem`: at each `z ∈ Iz`
apply `Work.Spaces.cs_integral` to `u := fun θ => √((U z θ)^2)` and `v := fun θ => √((V z θ)^2)`
(pointwise `u v = |U| |V|` by `Real.sqrt_sq_eq_abs`; `MemLp u 2` holds since `u` is a.e. strongly
measurable as a continuous function of the integrable `(U z ·)²`, and `∫ u² = ∫ (U z ·)²`);
this gives `∫_θ |U||V| ≤ √(A z) · √(B z)` with `A z := ∫_θ (U z θ)²`, `B z := ∫_θ (V z θ)²`.
Then bound `∫_z ∫_θ |U||V| ≤ ∫_z √(A z)·√(B z)` by `MeasureTheory.integral_mono_of_nonneg`
(only the majorant `√A · √B` must be integrable: `√A` is `MemLp 2` since `A` is integrable and
`(√A)² = A`, likewise `√B`, and a product of two `MemLp 2`-functions is `MemLp 1`, hence
integrable — note `∫_z |∫_θ|U||V||` is NOT needed anywhere, so no joint measurability is
required), and finish with `Work.Spaces.cs_integral` on `Iz` applied to `√A` and `√B`,
using `∫_z A z = L2Sq U` and `∫_z B z = L2Sq V` (definitionally). -/
theorem L2Mem_prod_le {U V : ℝ → ℝ → ℝ} (hU : Work.Spaces.L2Mem U) (hV : Work.Spaces.L2Mem V) :
    ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ|
      ≤ Real.sqrt (Work.Spaces.L2Sq U) * Real.sqrt (Work.Spaces.L2Sq V) := by
  -- the two angular "second moments" of `U` and `V`
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 with hA
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2 with hB
  have hAval : ∀ z, A z = ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 := fun z => by
    simpa using congrFun hA z
  have hBval : ∀ z, B z = ∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2 := fun z => by
    simpa using congrFun hB z
  have hA0 : ∀ z, 0 ≤ A z := fun z => by
    rw [hAval z]; exact integral_nonneg fun θ => sq_nonneg (U z θ)
  have hB0 : ∀ z, 0 ≤ B z := fun z => by
    rw [hBval z]; exact integral_nonneg fun θ => sq_nonneg (V z θ)
  have hAint : Integrable A (volume.restrict Work.Spaces.Iz) := by
    rw [hA]; exact hU.2
  have hBint : Integrable B (volume.restrict Work.Spaces.Iz) := by
    rw [hB]; exact hV.2
  -- `√A`, `√B` are `L²` on `Iz`, since their squares are `A`, `B`
  have hAmem : MemLp (fun z => Real.sqrt (A z)) 2 (volume.restrict Work.Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    · exact hAint.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hA0 z)).symm)
  have hBmem : MemLp (fun z => Real.sqrt (B z)) 2 (volume.restrict Work.Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable
    · exact hBint.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hB0 z)).symm)
  -- hence `√A · √B` is integrable (`L² · L² ⊆ L¹`)
  have hGint : Integrable (fun z => Real.sqrt (A z) * Real.sqrt (B z))
      (volume.restrict Work.Spaces.Iz) := by
    simpa [Pi.mul_def] using hAmem.integrable_mul hBmem
  -- Cauchy–Schwarz on each angular slice
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ|) ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have hu : MemLp (fun θ => Real.sqrt ((U z θ) ^ 2)) 2 (volume.restrict Work.Spaces.Iθ) := by
      refine (memLp_two_iff_integrable_sq ?_).2 ?_
      · exact Real.continuous_sqrt.comp_aestronglyMeasurable (hU.1 z hz).aestronglyMeasurable
      · exact (hU.1 z hz).congr
          (Filter.Eventually.of_forall fun θ => (Real.sq_sqrt (sq_nonneg (U z θ))).symm)
    have hv : MemLp (fun θ => Real.sqrt ((V z θ) ^ 2)) 2 (volume.restrict Work.Spaces.Iθ) := by
      refine (memLp_two_iff_integrable_sq ?_).2 ?_
      · exact Real.continuous_sqrt.comp_aestronglyMeasurable (hV.1 z hz).aestronglyMeasurable
      · exact (hV.1 z hz).congr
          (Filter.Eventually.of_forall fun θ => (Real.sq_sqrt (sq_nonneg (V z θ))).symm)
    have hcs : (∫ θ in Work.Spaces.Iθ,
          Real.sqrt ((U z θ) ^ 2) * Real.sqrt ((V z θ) ^ 2)) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, (Real.sqrt ((U z θ) ^ 2)) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sqrt ((V z θ) ^ 2)) ^ 2) :=
      Work.Spaces.cs_integral hu hv
    have h1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt ((U z θ) ^ 2) * Real.sqrt ((V z θ) ^ 2))
        = ∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ| := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Real.sqrt_sq_eq_abs]
    have h2 : (∫ θ in Work.Spaces.Iθ, (Real.sqrt ((U z θ) ^ 2)) ^ 2) = A z := by
      rw [hAval z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Real.sq_sqrt (sq_nonneg (U z θ))]
    have h3 : (∫ θ in Work.Spaces.Iθ, (Real.sqrt ((V z θ) ^ 2)) ^ 2) = B z := by
      rw [hBval z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Real.sq_sqrt (sq_nonneg (V z θ))]
    have hsq : (∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ|) ^ 2 ≤ A z * B z := by
      rw [← h1, ← h2, ← h3]
      exact hcs
    have hsq2 : (∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ|) ^ 2
        ≤ (Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hA0 z), Real.sq_sqrt (hB0 z)]
      exact hsq
    have hs0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ| :=
      integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hp0 : 0 ≤ Real.sqrt (A z) * Real.sqrt (B z) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa [abs_of_nonneg hs0, abs_of_nonneg hp0] using sq_le_sq.mp hsq2
  -- integrate the slicewise estimate
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, |U z θ| * |V z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      hGint
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hslice)
  -- Cauchy–Schwarz in `z`
  have hfin : (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z))
      ≤ Real.sqrt (Work.Spaces.L2Sq U) * Real.sqrt (Work.Spaces.L2Sq V) := by
    have hcs : (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2
        ≤ (∫ z in Work.Spaces.Iz, (Real.sqrt (A z)) ^ 2)
          * (∫ z in Work.Spaces.Iz, (Real.sqrt (B z)) ^ 2) :=
      Work.Spaces.cs_integral hAmem hBmem
    have e1 : (∫ z in Work.Spaces.Iz, (Real.sqrt (A z)) ^ 2) = Work.Spaces.L2Sq U := by
      rw [Work.Spaces.L2Sq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hAval z, Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg (U z θ))]
    have e2 : (∫ z in Work.Spaces.Iz, (Real.sqrt (B z)) ^ 2) = Work.Spaces.L2Sq V := by
      rw [Work.Spaces.L2Sq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hBval z, Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg (V z θ))]
    have hsq3 : (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2
        ≤ Work.Spaces.L2Sq U * Work.Spaces.L2Sq V := by
      rw [e1, e2] at hcs
      exact hcs
    have hs0 : 0 ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z) :=
      integral_nonneg fun z => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hL2U : 0 ≤ Work.Spaces.L2Sq U := by
      rw [Work.Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg (U z θ)
    have hL2V : 0 ≤ Work.Spaces.L2Sq V := by
      rw [Work.Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg (V z θ)
    have hsq4 : (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2
        ≤ (Real.sqrt (Work.Spaces.L2Sq U * Work.Spaces.L2Sq V)) ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg hL2U hL2V)]
      exact hsq3
    have h := sq_le_sq.mp hsq4
    rw [abs_of_nonneg hs0,
      abs_of_nonneg (Real.sqrt_nonneg (Work.Spaces.L2Sq U * Work.Spaces.L2Sq V)),
      Real.sqrt_mul hL2U (Work.Spaces.L2Sq V)] at h
    exact h
  exact hmain.trans hfin

end Work.FTS.H2.T2Easy
