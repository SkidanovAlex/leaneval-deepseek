import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SliceA

open Filter Topology Set MeasureTheory

local notation "Lθ" => nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))

/-- The elementary right-hand limit `t / sin t → 1` as `t → 0⁺`, obtained by inverting the
slope form `sin t / t → 1` of the derivative `sin' 0 = 1`. -/
private lemma tendsto_div_sin_zero_right :
    Tendsto (fun t : ℝ => t / Real.sin t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * Real.sin t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
    have h' : (fun t : ℝ => t⁻¹ • (Real.sin (0 + t) - Real.sin 0))
        = fun t => t⁻¹ * Real.sin t := by
      funext t; simp [smul_eq_mul]
    rw [h'] at h; simpa using h
  have hinv : Tendsto (fun t : ℝ => (t⁻¹ * Real.sin t)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := hslope.inv₀ (by norm_num : (1 : ℝ) ≠ 0); simpa using h
  have hfun : (fun t : ℝ => (t⁻¹ * Real.sin t)⁻¹) = fun t => t / Real.sin t := by
    funext t; rw [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]
  rw [hfun] at hinv; exact hinv

/-- `π/2 - θ` tends to `0` from the right as `θ → π/2` from the left. -/
private lemma tendsto_pi_div_two_sub :
    Tendsto (fun θ : ℝ => Real.pi / 2 - θ) Lθ (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hid : Tendsto (fun θ : ℝ => θ) Lθ (nhds (Real.pi / 2)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℝ => Real.pi / 2) Lθ (nhds (Real.pi / 2)) :=
      tendsto_const_nhds
    have h := hc.sub hid; simpa using h
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    show 0 < Real.pi / 2 - θ
    exact sub_pos.mpr hθ

/-- `(π/2 - θ) / cos θ → 1` as `θ → π/2` from the left (since `cos θ = sin (π/2 - θ)`). -/
private lemma tendsto_shift_div_cos :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) / Real.cos θ) Lθ (nhds 1) := by
  have h := tendsto_div_sin_zero_right.comp tendsto_pi_div_two_sub
  simpa [Function.comp_def, Real.sin_pi_div_two_sub] using h

/-- `(π/2 - θ)² · (cos θ)⁻² → 1` as `θ → π/2` from the left. -/
private lemma tendsto_shift_sq_div_cos_sq :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2 * (1 / (Real.cos θ) ^ 2)) Lθ (nhds 1) := by
  have h1 : Tendsto (fun θ : ℝ => ((Real.pi / 2 - θ) / Real.cos θ) ^ 2) Lθ (nhds 1) := by
    have h := tendsto_shift_div_cos.pow 2; simpa using h
  refine h1.congr (fun θ => ?_)
  rw [div_pow, div_eq_mul_inv, one_div]

/-- `(π/2 - θ) · tan θ → 1` as `θ → π/2` from the left. -/
private lemma tendsto_shift_mul_tan :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) * Real.tan θ) Lθ (nhds 1) := by
  have hsin : Tendsto (fun θ : ℝ => Real.sin θ) Lθ (nhds 1) := by
    have h : Tendsto Real.sin Lθ (nhds (Real.sin (Real.pi / 2))) :=
      (Real.continuous_sin.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
    simpa [Real.sin_pi_div_two] using h
  have h1 : Tendsto (fun θ : ℝ => ((Real.pi / 2 - θ) / Real.cos θ) * Real.sin θ) Lθ
      (nhds 1) := by
    have h := tendsto_shift_div_cos.mul hsin; simpa using h
  refine h1.congr (fun θ => ?_)
  rw [Real.tan_eq_sin_div_cos]; ring

/-- **Indicial order shift by two at the singular endpoint `θ = π/2`.**  For `C²` data behaving
near `θ = π/2` like the power `A·(π/2-θ)^{-N}` with `N ≥ 2`, together with its first two
derivatives (the three limits below), the source `Lzero1 u = -u'' + (tan θ · u)' - 6u` satisfies
`(π/2-θ)^{N+2}·Lzero1 u → (1-N²)·A ≠ 0`: near this endpoint the operator shifts the power by two
and nothing of order `t^{-N}` (in particular no `∂_z`/radial term) can cancel the leading
`t^{-N-2}` term. -/
theorem Lzero1_order_shift {u : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) {A ε : ℝ} (hε : 0 < ε)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds A))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) * deriv u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * A)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * deriv (fun s => deriv u s) θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * (N + 1) * A))) :
    Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * Work.FTS.EllipticEst.Lzero1 u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((1 - (N : ℝ) ^ 2) * A)) := by
  have hA' : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2 * (1 / (Real.cos θ) ^ 2)) Lθ
      (nhds 1) := tendsto_shift_sq_div_cos_sq
  have hB' : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) * Real.tan θ) Lθ (nhds 1) :=
    tendsto_shift_mul_tan
  have hT0 : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) Lθ (nhds 0) :=
    tendsto_pi_div_two_sub.mono_right nhdsWithin_le_nhds
  have hT2 : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2) Lθ (nhds 0) := by
    have h := hT0.pow 2; simpa using h
  -- the limit of the model function obtained from the pointwise expansion of `Lzero1`
  have hG : Tendsto (fun θ : ℝ =>
      -((Real.pi / 2 - θ) ^ (N + 2) * deriv (fun s => deriv u s) θ)
      + ((Real.pi / 2 - θ) ^ 2 * (1 / (Real.cos θ) ^ 2)) * ((Real.pi / 2 - θ) ^ N * u θ)
      + ((Real.pi / 2 - θ) * Real.tan θ) * ((Real.pi / 2 - θ) ^ (N + 1) * deriv u θ)
      - 6 * ((Real.pi / 2 - θ) ^ 2 * ((Real.pi / 2 - θ) ^ N * u θ))) Lθ
      (nhds ((1 - (N : ℝ) ^ 2) * A)) := by
    have h1' : Tendsto (fun θ : ℝ =>
        ((Real.pi / 2 - θ) ^ 2 * (1 / (Real.cos θ) ^ 2)) * ((Real.pi / 2 - θ) ^ N * u θ))
        Lθ (nhds (1 * A)) := hA'.mul h0
    have h2' : Tendsto (fun θ : ℝ =>
        ((Real.pi / 2 - θ) * Real.tan θ) * ((Real.pi / 2 - θ) ^ (N + 1) * deriv u θ))
        Lθ (nhds (1 * ((N : ℝ) * A))) := hB'.mul h1
    have h3' : Tendsto (fun θ : ℝ =>
        6 * ((Real.pi / 2 - θ) ^ 2 * ((Real.pi / 2 - θ) ^ N * u θ))) Lθ
        (nhds (6 * (0 * A))) := (hT2.mul h0).const_mul 6
    have hsum : Tendsto (fun θ : ℝ =>
        -((Real.pi / 2 - θ) ^ (N + 2) * deriv (fun s => deriv u s) θ)
        + ((Real.pi / 2 - θ) ^ 2 * (1 / (Real.cos θ) ^ 2)) * ((Real.pi / 2 - θ) ^ N * u θ)
        + ((Real.pi / 2 - θ) * Real.tan θ) * ((Real.pi / 2 - θ) ^ (N + 1) * deriv u θ)
        - 6 * ((Real.pi / 2 - θ) ^ 2 * ((Real.pi / 2 - θ) ^ N * u θ))) Lθ
        (nhds (-((N : ℝ) * ((N : ℝ) + 1) * A) + 1 * A + 1 * ((N : ℝ) * A)
          - 6 * (0 * A))) := ((h2.neg).add h1').add h2' |>.sub h3'
    have hval : -((N : ℝ) * ((N : ℝ) + 1) * A) + 1 * A + 1 * ((N : ℝ) * A) - 6 * (0 * A)
        = (1 - (N : ℝ) ^ 2) * A := by ring
    rw [hval] at hsum
    exact hsum
  refine hG.congr' ?_
  -- on a neighbourhood of `π/2` (inside `Iio (π/2)`) the expansion of `Lzero1` holds
  have hmem1 : Set.Iio (Real.pi / 2) ∈ Lθ := self_mem_nhdsWithin
  have hmem2 : Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2 + 1) ∈ Lθ :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hmem3 : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2 + 1) ∈ Lθ :=
    mem_nhdsWithin_of_mem_nhds
      (isOpen_Ioo.mem_nhds (by constructor <;> linarith [Real.pi_pos]))
  filter_upwards [hmem1, hmem2, hmem3] with θ hθ1 hθ2 hθ3
  have hθI : θ ∈ Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) := ⟨hθ2.1, hθ1⟩
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨hθ3.1, hθ1⟩)
  have hdU : DifferentiableAt ℝ u θ :=
    (hu.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
  have hdT : DifferentiableAt ℝ Real.tan θ := (Real.differentiableAt_tan).mpr hcos
  have hpr : deriv (fun t => Real.tan t * u t) θ
      = (1 / (Real.cos θ) ^ 2) * u θ + Real.tan θ * deriv u θ := by
    rw [deriv_fun_mul hdT hdU, Real.deriv_tan]
  have hL : Work.FTS.EllipticEst.Lzero1 u θ
      = -(deriv (fun s => deriv u s) θ)
        + ((1 / (Real.cos θ) ^ 2) * u θ + Real.tan θ * deriv u θ) - 6 * u θ := by
    change -(deriv (fun s => deriv u s) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ = _
    rw [hpr]
  rw [hL, pow_add, pow_succ]
  ring

end Work.FTS.EllipticEst.H2W.SliceA
