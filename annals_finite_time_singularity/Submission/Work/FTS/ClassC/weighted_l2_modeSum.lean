import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **Minkowski (triangle) inequality in the weighted `L²` space `L²(𝕀_z, w²dz)`**
for a finite weighted sum of modes: with `c m ≥ 0` and each `a m` square-integrable
against `w²` on `𝕀_z`,

`∫_{𝕀_z} w² · (∑_{m≤N} c m |a m|)² ≤ (∑_{m≤N} c m √(∫_{𝕀_z} a m² w²))².`

This is the elementary form of `‖∑_m c m |f_m|‖_{L²(w²)} ≤ ∑_m c m ‖f_m‖_{L²(w²)}`:
the proof runs the abstract `eLpNorm` triangle inequality `eLpNorm_sum_le` on the
`AEStronglyMeasurable` functions `z ↦ √(a m z ² w z ²)` (which agree with
`w · |a m|` on `𝕀_z`) and then converts `eLpNorm · 2` back to the square root of the
Bochner integral via `MemLp.eLpNorm_eq_integral_rpow_norm`. -/
theorem weighted_l2_modeSum {N : ℕ} {a : ℕ → ℝ → ℝ} {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ Finset.range (N + 1), c m * |a m z|) ^ 2)
      ≤ (∑ m ∈ Finset.range (N + 1),
          c m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2 := by
  classical
  -- the `2`-norm is the square root of the integral of the square
  have eLpNorm_two_eq : ∀ (f : ℝ → ℝ) (ν : Measure ℝ), MemLp f 2 ν →
      eLpNorm f 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂ν)) := by
    intro f ν hf
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    rw [show (2 : ENNReal).toReal = 2 by norm_num,
      show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
  set S : Finset ℕ := Finset.range (N + 1) with hS
  set μ : Measure ℝ := volume.restrict Work.Spaces.Iz with hμ
  set g : ℕ → ℝ → ℝ := fun m z => Real.sqrt ((a m z) ^ 2 * (Work.Spaces.w z) ^ 2) with hg
  -- `m ∈ S ↔ m ≤ N`
  have hmemS : ∀ m, m ∈ S → m ≤ N := by
    intro m hm
    rw [hS] at hm
    simp only [Finset.mem_range] at hm
    omega
  -- integrability of the `m`-th mode against `w²`, as a measure on `𝕀_z`
  have hInt : ∀ m, m ∈ S → Integrable (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) μ := by
    intro m hm
    rw [hμ]
    exact hint m (hmemS m hm)
  -- the algebraic identity `g m z ^ 2 = a m z ^ 2 * w z ^ 2`
  have hg_sq : ∀ m z, (g m z) ^ 2 = (a m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m z
    simp only [hg]
    exact Real.sq_sqrt (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hg_meas : ∀ m, m ∈ S → AEStronglyMeasurable (g m) μ := by
    intro m hm
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable
      ((hInt m hm).aestronglyMeasurable)
    simpa only [hg] using h
  have hg_memLp : ∀ m, m ∈ S → MemLp (g m) 2 μ := by
    intro m hm
    refine (memLp_two_iff_integrable_sq (hg_meas m hm)).mpr ?_
    exact (hInt m hm).congr (Filter.Eventually.of_forall fun z => (hg_sq m z).symm)
  -- the function whose `L²` norm is the left-hand side
  set F : ℝ → ℝ := ∑ m ∈ S, (fun z => c m * g m z) with hF
  have hF_memLp : MemLp F 2 μ := by
    have h := memLp_finsetSum' (α := ℝ) (p := 2) (μ := μ) (s := S)
      (f := fun m => fun z => c m * g m z) (fun m hm => ?_)
    · rwa [← hF] at h
    · exact (hg_memLp m hm).const_smul (c m)
  have hF_apply : ∀ z, F z = ∑ m ∈ S, c m * g m z := by
    intro z
    simpa only [hF] using Finset.sum_apply z S (fun m z' => c m * g m z')
  have hF_nonneg : ∀ z, 0 ≤ F z := by
    intro z
    rw [hF_apply z]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _)
  -- the pointwise identity `g m z = |a m z| * |w z|`
  have hg_val : ∀ m z, g m z = Real.sqrt ((a m z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro m z
    rw [hg]
  have hg_abs : ∀ m z, g m z = |a m z| * |Work.Spaces.w z| := by
    intro m z
    rw [hg_val m z]
    rw [show (a m z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (|a m z| * |Work.Spaces.w z|) ^ 2 by rw [mul_pow, sq_abs, sq_abs]]
    rw [Real.sqrt_sq_eq_abs (|a m z| * |Work.Spaces.w z|),
      abs_of_nonneg (mul_nonneg (abs_nonneg (a m z)) (abs_nonneg (Work.Spaces.w z)))]
  -- the `L²` norm of `F` is `√(∫_{𝕀_z} w² (∑ c m |a m|)²)`
  have hnormF : (∫ x, ‖F x‖ ^ 2 ∂μ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (∑ m ∈ S, c m * |a m z|) ^ 2 := by
    rw [hμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h1 : (∑ m ∈ S, c m * g m z)
        = (∑ m ∈ S, c m * |a m z|) * |Work.Spaces.w z| := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by rw [hg_abs m z]; ring
    show ‖F z‖ ^ 2 = (Work.Spaces.w z) ^ 2 * (∑ m ∈ S, c m * |a m z|) ^ 2
    rw [hF_apply z, h1,
      Real.norm_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ =>
        mul_nonneg (hc m) (abs_nonneg _)) (abs_nonneg _)), mul_pow, sq_abs]
    ring
  -- the `L²` norm of the `m`-th mode against `w²`
  have hnormg : ∀ m, m ∈ S → (∫ x, ‖g m x‖ ^ 2 ∂μ)
      = ∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m hm
    rw [hμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖g m z‖ ^ 2 = (a m z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [hg_val m z, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (sq_nonneg (a m z)) (sq_nonneg (Work.Spaces.w z)))]
  -- Minkowski in `eLpNorm` form
  have hkey : eLpNorm F 2 μ ≤ ∑ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ := by
    have h1 := eLpNorm_sum_le (s := S) (f := fun m z => c m * g m z) (p := 2) (μ := μ)
      (by norm_num : (1 : ENNReal) ≤ 2)
    rw [← hF] at h1
    exact h1
  -- identification of the left-hand side
  have hLHS : eLpNorm F 2 μ
      = ENNReal.ofReal (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∑ m ∈ S, c m * |a m z|) ^ 2)) := by
    rw [eLpNorm_two_eq F μ hF_memLp, hnormF]
  -- identification of the right-hand side
  have hsingle : ∀ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ
      = ENNReal.ofReal (c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    intro m hm
    have hcs := eLpNorm_const_smul (c m) (g m) (2 : ENNReal) μ
    rw [show (c m • g m) = (fun z => c m * g m z) from by
          funext z; simp only [Pi.smul_apply, smul_eq_mul]] at hcs
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc m)] at hcs
    rw [hcs, eLpNorm_two_eq (g m) μ (hg_memLp m hm), hnormg m hm,
      ENNReal.ofReal_mul (hc m)]
  have hRHS : (∑ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ)
      = ENNReal.ofReal (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    rw [Finset.sum_congr rfl (fun m hm => hsingle m hm),
      ENNReal.ofReal_sum_of_nonneg (fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _))]
  -- the `ENNReal` inequality
  have hmain : ENNReal.ofReal (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2))
      ≤ ENNReal.ofReal (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    rw [← hLHS, ← hRHS]
    exact hkey
  -- pass to the real inequality, square, and unfold `S`
  have hB : 0 ≤ ∑ m ∈ S, c m
      * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _)
  have hle : Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2)
      ≤ ∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hmain
  have hA : 0 ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∑ m ∈ S, c m * |a m z|) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq : (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2)) ^ 2
      ≤ (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2 :=
    sq_le_sq' (by linarith [Real.sqrt_nonneg (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∑ m ∈ S, c m * |a m z|) ^ 2), hB]) hle
  rw [Real.sq_sqrt hA] at hsq
  rw [hS] at hsq
  exact hsq

end Work.FTS.ClassC
