import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The slice of the `nc` configuration is not compact

The configuration of `RefuteNC/Config.lean` is the standard torus of revolution
(`ψ = idDiffeo`), the box `PBox ncRad ncCtr ncCyc3` (`ncRad = 1`, `ncCtr = (1, 19/10, 0)`,
`ncCyc3 = (0 1 2)`) and the cutting plane `{x = 1/2}` (`ncU = -1/2`).  In the parameter plane
`(θ, φ)` of the standard torus the plane equation is `(2 + cos φ) cos θ = 1/2`, so

  `Σ = { torusMap θ φ : (2 + cos φ) cos θ = 1/2, |(2 + cos φ) sin θ - 19/10| < 1 }`

(the other two box conditions are automatic there).  Writing `A = 2 + cos φ` and
`θ = arccos (1/(2A))`, a point of the trace has

  `y₁ = A sin θ = A √(1 - 1/(4A²)) = √(A² - 1/4)`,

so the `y₁`-window of the box reads `9/10 < √(A² - 1/4) < 29/10`, i.e. `A² ∈ (53/50, 433/50)`.
Thus `Σ` is a union of two arcs, parametrised by `A` ranging over the open interval
`(√(53/50), √(433/50))`; each arc is open at both ends (the ends lie on the box faces
`y₁ = 9/10`, `y₁ = 29/10`, which the open box excludes).

## The proof

`Σ` is **not closed**, hence not compact.  We exhibit an explicit point of the closure which is
not in `Σ`: the point of the trace with `A = A₀ = √(433/50)`, i.e. with `y₁ = 29/10` exactly, is
on the box face, hence outside the (open) box, but it is the limit of the points of `Σ` with
`A` slightly smaller.

Concretely, with `φ₀ = arccos (A₀ - 2) ∈ (0, π/2)` and `θ(φ) = arccos (1/(2 (2 + cos φ)))`, the
curve

  `ncPt φ = torusMap (θ(φ)) φ`

has `ncPt φ₀ ∉ Σ` (its first coordinate is `1/2`, its second is `29/10`), while for every
`φ ∈ (φ₀, π/2]` it has

  `9/10 < √((2 + cos φ)² - 1/4) < 29/10`,

so `ncPt φ ∈ Σ`; and `ncPt` is continuous, so `ncPt (φ₀ + (π/2 - φ₀)/(n+1)) → ncPt φ₀`.
Hence `ncPt φ₀ ∈ closure Σ \ Σ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The slice, read on the standard torus -/

/-- The slice of the configuration, read on the standard torus. -/
private theorem Sigma_nc_eq :
    Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU
      = Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := rfl

/-! ## The numerical constants `A₀ = √(433/50)` and `φ₀ = arccos (A₀ - 2)` -/

/-- `A₀ = √(433/50)`: the value of `A = 2 + cos φ` at which the trace point has `y₁ = 29/10`. -/
private def ncA0 : ℝ := Real.sqrt (433 / 50)

private theorem ncA0_sq : ncA0 ^ 2 = 433 / 50 := by
  unfold ncA0; exact Real.sq_sqrt (by norm_num)

private theorem ncA0_gt_two : 2 < ncA0 := by
  have h : (2 : ℝ) < Real.sqrt (433 / 50) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  simpa [ncA0] using h

private theorem ncA0_lt_three : ncA0 < 3 := by
  have h : Real.sqrt (433 / 50) < (3 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]; norm_num
  simpa [ncA0] using h

/-- The parameter `φ₀ = arccos (A₀ - 2) ∈ (0, π/2)` at which `ncPt φ₀` has `y₁ = 29/10`. -/
private def ncPhi0 : ℝ := Real.arccos (ncA0 - 2)

private theorem ncPhi0_mem : ncPhi0 ∈ Set.Icc 0 Real.pi := by
  unfold ncPhi0; exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

private theorem ncPhi0_pos : 0 < ncPhi0 := by
  unfold ncPhi0
  rw [Real.arccos_pos]
  linarith [ncA0_lt_three]

private theorem ncPhi0_lt_pi_div_two : ncPhi0 < Real.pi / 2 := by
  unfold ncPhi0
  rw [Real.arccos_lt_pi_div_two]
  linarith [ncA0_gt_two]

private theorem ncPhi0_cos : Real.cos ncPhi0 = ncA0 - 2 := by
  unfold ncPhi0
  exact Real.cos_arccos (by linarith [ncA0_gt_two]) (by linarith [ncA0_lt_three])

/-! ## The curve `ncPt` of the trace -/

/-- The argument of the `arccos` defining the longitude parameter on the trace: `1/(2(2 + cos φ))`.
It is written as an inverse so that its continuity is the bare statement that `1/x` is continuous
away from `0`. -/
private def ncTheta (φ : ℝ) : ℝ := (2 * (2 + Real.cos φ))⁻¹

/-- The point of the trace of the cutting plane above the parameter `φ`: it has first coordinate
`1/2` and second coordinate `√((2 + cos φ)² - 1/4)`. -/
private def ncPt (φ : ℝ) : R3 :=
  Work.Core.torusMap (Real.arccos (ncTheta φ)) φ

private theorem ncTheta_bounds (φ : ℝ) : -1 ≤ ncTheta φ ∧ ncTheta φ ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hden : (0 : ℝ) < 2 * (2 + Real.cos φ) := by linarith
  have hone : (1 : ℝ) ≤ 2 * (2 + Real.cos φ) := by linarith
  rw [ncTheta]
  exact ⟨by have h := inv_pos.mpr hden; linarith, inv_le_one_of_one_le₀ hone⟩

/-- The elementary square-root identity `A √(1 - 1/(4A²)) = √(A² - 1/4)` for `A > 0`. -/
private theorem nc_sqrt_algebra (A : ℝ) (hA : 0 < A) :
    A * Real.sqrt (1 - 1 / (4 * A ^ 2)) = Real.sqrt (A ^ 2 - 1 / 4) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hsq : Real.sqrt (A ^ 2) = A := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hA]
  calc A * Real.sqrt (1 - 1 / (4 * A ^ 2))
      = Real.sqrt (A ^ 2) * Real.sqrt (1 - 1 / (4 * A ^ 2)) := by rw [hsq]
    _ = Real.sqrt (A ^ 2 * (1 - 1 / (4 * A ^ 2))) := by rw [Real.sqrt_mul (sq_nonneg A)]
    _ = Real.sqrt (A ^ 2 - 1 / 4) := by
        congr 1
        field_simp

private theorem ncPt_apply_zero (φ : ℝ) : ncPt φ 0 = 1 / 2 := by
  have hb := ncTheta_bounds φ
  have hA0 : (2 + Real.cos φ) ≠ 0 := by linarith [Real.neg_one_le_cos φ]
  unfold ncPt
  rw [Work.Core.torusMap_apply_zero, Real.cos_arccos hb.1 hb.2, ncTheta]
  field_simp

private theorem ncPt_apply_one (φ : ℝ) :
    ncPt φ 1 = Real.sqrt ((2 + Real.cos φ) ^ 2 - 1 / 4) := by
  have hA : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have key : (ncTheta φ) ^ 2 = 1 / (4 * (2 + Real.cos φ) ^ 2) := by
    rw [ncTheta, inv_pow, mul_pow]; norm_num
  unfold ncPt
  rw [Work.Core.torusMap_apply_one, Real.sin_arccos, key]
  exact nc_sqrt_algebra _ hA

private theorem ncPt_apply_two (φ : ℝ) : ncPt φ 2 = Real.sin φ := by
  unfold ncPt; rw [Work.Core.torusMap_apply_two]

/-! ## The confinement of the second coordinate -/

/-- For `φ ∈ (φ₀, π/2]` the second coordinate of `ncPt φ` lies strictly inside the `y₁`-window of
the box: `9/10 < √((2 + cos φ)² - 1/4) < 29/10`. -/
private theorem ncY_bounds (φ : ℝ) (h1 : ncPhi0 < φ) (h2 : φ ≤ Real.pi / 2) :
    (9 / 10 : ℝ) < Real.sqrt ((2 + Real.cos φ) ^ 2 - 1 / 4) ∧
      Real.sqrt ((2 + Real.cos φ) ^ 2 - 1 / 4) < 29 / 10 := by
  have hφ0 : 0 < φ := by linarith [ncPhi0_pos]
  have hφmem : φ ∈ Set.Icc 0 Real.pi := ⟨le_of_lt hφ0, by linarith [h2, Real.pi_pos]⟩
  have hcos_lt : Real.cos φ < Real.cos ncPhi0 := Real.strictAntiOn_cos ncPhi0_mem hφmem h1
  rw [ncPhi0_cos] at hcos_lt
  have hA_lt : 2 + Real.cos φ < ncA0 := by linarith
  have hcos_nonneg : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2⟩
  have hA_ge : 2 ≤ 2 + Real.cos φ := by linarith
  have hsq_nonneg : (0 : ℝ) ≤ (2 + Real.cos φ) ^ 2 - 1 / 4 := by nlinarith [hA_ge]
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    nlinarith [hA_ge]
  · have hsq_lt : (2 + Real.cos φ) ^ 2 - 1 / 4 < 841 / 100 := by
      have hprod : 0 < (ncA0 - (2 + Real.cos φ)) * (ncA0 + (2 + Real.cos φ)) :=
        mul_pos (by linarith) (by linarith)
      have hsq_lt' : (2 + Real.cos φ) ^ 2 < ncA0 ^ 2 := by nlinarith [hprod]
      rw [ncA0_sq] at hsq_lt'
      linarith
    have h := Real.sqrt_lt_sqrt hsq_nonneg hsq_lt
    have hsqrt841 : Real.sqrt (841 / 100) = 29 / 10 := by
      rw [show (841 / 100 : ℝ) = (29 / 10) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rwa [hsqrt841] at h

/-! ## The point `ncPt φ` lies in the slice -/

/-- For `φ ∈ (φ₀, π/2]` the point `ncPt φ` lies in the slice. -/
private theorem ncPt_mem_slice (φ : ℝ) (h1 : ncPhi0 < φ) (h2 : φ ≤ Real.pi / 2) :
    ncPt φ ∈ Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
  obtain ⟨hy_lo, hy_hi⟩ := ncY_bounds φ h1 h2
  rw [Work.BoxShrink.Core.mem_sliceRegion]
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.CoreTopology.standard_carrier]
    exact ⟨(Real.arccos (ncTheta φ), φ), rfl⟩
  · rw [Work.BoxShrink.PinchOff.mem_PBox_nc]
    refine ⟨?_, ?_, ?_⟩
    · rw [ncPt_apply_one, abs_lt]; constructor <;> linarith
    · rw [ncPt_apply_two]
      have hle : |Real.sin φ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩
      have hlt : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) :=
        Real.one_lt_rpow (by norm_num) (by norm_num)
      linarith
    · rw [ncPt_apply_zero, abs_lt]
      have hlt : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) :=
        Real.one_lt_rpow (by norm_num) (by norm_num)
      constructor <;> linarith
  · rw [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
      Work.BoxShrink.PinchOff.ncU_eq, ncPt_apply_zero]
    norm_num

/-! ## The limit point `ncPt φ₀` is not in the slice -/

private theorem ncPt_phi0_not_mem :
    ncPt ncPhi0 ∉ Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
  rw [Sigma_nc_eq]
  rintro h
  rw [Work.BoxShrink.Core.mem_sliceRegion] at h
  obtain ⟨-, hbox, -⟩ := h
  have h1 : ncPt ncPhi0 1 = 29 / 10 := by
    rw [ncPt_apply_one]
    have hA : 2 + Real.cos ncPhi0 = ncA0 := by rw [ncPhi0_cos]; ring
    rw [hA, ncA0_sq]
    rw [show (433 / 50 : ℝ) - 1 / 4 = (29 / 10) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hb := (Work.BoxShrink.PinchOff.mem_PBox_nc (ncPt ncPhi0)).mp hbox
  rw [h1] at hb
  have hlt := hb.1
  rw [abs_lt] at hlt
  linarith [hlt.2]

/-! ## Continuity of `ncPt` -/

private theorem continuous_ncTheta : Continuous ncTheta := by
  have hden : Continuous fun φ : ℝ => 2 * (2 + Real.cos φ) := by fun_prop
  have hne : ∀ φ : ℝ, 2 * (2 + Real.cos φ) ≠ 0 := by
    intro φ
    have h : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
    positivity
  exact hden.inv₀ hne

private theorem continuous_ncPt : Continuous ncPt := by
  have hpair : Continuous fun φ : ℝ => (Real.arccos (ncTheta φ), φ) :=
    (Real.continuous_arccos.comp continuous_ncTheta).prodMk continuous_id
  have h := Work.CoreTopology.torusMap_continuous.comp hpair
  have hfun : ((fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) ∘
      fun φ : ℝ => (Real.arccos (ncTheta φ), φ)) = ncPt := rfl
  rw [hfun] at h
  exact h

/-! ## The slice is not compact -/

theorem not_isCompact_slice_nc :
    ¬ IsCompact (Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) := by
  intro hcomp
  have hseq : Filter.Tendsto
      (fun n : ℕ => ncPhi0 + (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1))
      Filter.atTop (nhds ncPhi0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul : Filter.Tendsto
        (fun n : ℕ => (Real.pi / 2 - ncPhi0) * ((1 : ℝ) / ((n : ℝ) + 1)))
        Filter.atTop (nhds ((Real.pi / 2 - ncPhi0) * 0)) :=
      hbase.const_mul (Real.pi / 2 - ncPhi0)
    have h0 : Filter.Tendsto (fun n : ℕ => (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using hmul
    simpa using h0.const_add ncPhi0
  have hlim : Filter.Tendsto
      (fun n : ℕ => ncPt (ncPhi0 + (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1)))
      Filter.atTop (nhds (ncPt ncPhi0)) :=
    (continuous_ncPt.tendsto ncPhi0).comp hseq
  have hmem : ncPt ncPhi0 ∈ closure (Work.BoxShrink.PinchOff.Sigma
      Work.BoxShrink.PinchOff.idDiffeo Work.BoxShrink.PinchOff.ncRad
      Work.BoxShrink.PinchOff.ncCtr Work.BoxShrink.PinchOff.ncCyc3
      Work.BoxShrink.PinchOff.ncU) := by
    rw [Sigma_nc_eq, mem_closure_iff_seq_limit]
    refine ⟨fun n => ncPt (ncPhi0 + (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1)), ?_, hlim⟩
    intro n
    apply ncPt_mem_slice
    · have hnum : 0 < Real.pi / 2 - ncPhi0 := by linarith [ncPhi0_lt_pi_div_two]
      have hd : 0 < (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1) :=
        div_pos hnum (by positivity)
      linarith
    · have hnum : 0 < Real.pi / 2 - ncPhi0 := by linarith [ncPhi0_lt_pi_div_two]
      have hle : (Real.pi / 2 - ncPhi0) / ((n : ℝ) + 1) ≤ Real.pi / 2 - ncPhi0 := by
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        rw [div_le_iff₀ hpos]
        nlinarith [hnum, hn]
      linarith
  have hclosed : IsClosed (Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) := hcomp.isClosed
  rw [hclosed.closure_eq] at hmem
  exact ncPt_phi0_not_mem hmem

end

end Work.BoxShrink.PinchOff.RefuteNC
