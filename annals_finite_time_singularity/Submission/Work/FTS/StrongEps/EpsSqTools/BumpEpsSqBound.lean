/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/BumpEpsSqBound.lean`

The explicit bump profile `bump` of `BumpDefs.lean` is supported on the closed box
`[1/2,1] × [π/4,3π/8]`, which lies inside the open quadrant and is bounded away from the
singularities `z = 0`, `θ = 0`, `θ = π/2` of the weight `epsW α = w/sin(2θ)^{γ/2}`.  Hence

* `EpsMem α bump` holds **for every** real `α` (the integrand is continuous on the box and
  vanishes outside it);
* `EpsSq α bump` is bounded by a constant **uniform in** `α ∈ (0,1]`.

Concretely: on the box `w z ≤ 16`; and since `θ ∈ [π/4,3π/8]` forces `sin 2θ ≥ 1/2`, while
`γ/2 = (1+α/10)/2 ≤ 1` for `α ≤ 1`, we have `sin(2θ)^{γ/2} ≥ sin 2θ ≥ 1/2`.  Hence
`epsW α z θ ≤ 16/(1/2) = 32` and `(bump · epsW α)² ≤ 32² = 1024` everywhere; the volume of the
box is at most `(1/2)·(π/2) = π/4 < 1`, so

`EpsSq α bump ≤ 1024 · (π/2) · (1/2) = 256·π ≤ 1024`

for every `α ∈ (0,1]`.  The constant `1024` is therefore a valid `K`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The support box of `bump` -/

/-- The closed box `[1/2,1] × [π/4,3π/8]` containing the support of `bump`. -/
def bumpBox : Set (ℝ × ℝ) :=
  Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)

theorem isCompact_bumpBox : IsCompact bumpBox :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_bumpBox : MeasurableSet bumpBox :=
  measurableSet_Icc.prod measurableSet_Icc

/-! ## Elementary bounds on the pieces -/

/-- `bump ≤ 1` everywhere (`bump` is a product of two cut-offs, each a product of two
`Real.smoothTransition`s). -/
theorem bump_le_one (z θ : ℝ) : Work.FTS.StrongEps.bump z θ ≤ 1 := by
  have h1 : Work.FTS.StrongEps.zCut z ≤ 1 := by
    rw [Work.FTS.StrongEps.zCut]
    simpa using mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 : Work.FTS.StrongEps.thCut θ ≤ 1 := by
    rw [Work.FTS.StrongEps.thCut]
    simpa using mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [Work.FTS.StrongEps.bump]
  simpa using mul_le_mul h1 h2 (Work.FTS.StrongEps.thCut_nonneg θ) (by norm_num : (0 : ℝ) ≤ 1)

/-- `bump` vanishes at every point outside the box `[1/2,1] × [π/4,3π/8]`. -/
theorem bump_eq_zero_of_not_mem_box {z θ : ℝ}
    (h : ¬ (z ∈ Set.Icc ((1 : ℝ) / 2) 1 ∧ θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8))) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump_eq_zero_iff]
  by_contra hc
  push Not at hc
  exact h ⟨Set.mem_Icc.mpr ⟨le_of_lt hc.1, le_of_lt hc.2.1⟩,
    Set.mem_Icc.mpr ⟨le_of_lt hc.2.2.1, le_of_lt hc.2.2.2⟩⟩

/-- The radial weight on `[1/2,1]`: `w z = (1+z)²/z² ≤ 16`. -/
theorem w_le_sixteen {z : ℝ} (hz : z ∈ Set.Icc ((1 : ℝ) / 2) 1) : Work.Spaces.w z ≤ 16 := by
  have hz0 : (0 : ℝ) < z := by linarith [hz.1]
  rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz.1, hz.2, sq_nonneg (z - 1 / 2)]

/-- The angular factor on the support box: `1/2 ≤ sin(2θ)` for `θ ∈ [π/4,3π/8]` (there
`2θ ∈ [π/2,3π/4]`, so `sin(2θ) = sin(π - 2θ) ≥ sin(π/4) = √2/2 ≥ 1/2`). -/
theorem sin_two_ge_half {θ : ℝ} (hθ : θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) :
    (1 : ℝ) / 2 ≤ Real.sin (2 * θ) := by
  have hx1 : Real.pi / 2 ≤ 2 * θ := by linarith [hθ.1]
  have hx2 : 2 * θ ≤ 3 * Real.pi / 4 := by linarith [hθ.2]
  have hmem1 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmem2 : Real.pi - 2 * θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos, hx1, hx2]
  have hm : Real.sin (Real.pi / 4) ≤ Real.sin (Real.pi - 2 * θ) :=
    Real.monotoneOn_sin hmem1 hmem2 (by linarith [hx2])
  rw [Real.sin_pi_sub] at hm
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  rw [Real.sin_pi_div_four] at hm
  linarith [hm, hsqrt]

/-! ## The weight `epsW` on the box: continuity and the numerical bound -/

/-- `epsW α` is continuous on the support box of `bump` (there `z ≥ 1/2 > 0` and
`sin 2θ ≥ 1/2 > 0`, so both factors of the weight are continuous). -/
theorem continuousOn_epsW_bumpBox (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StrongEps.epsW α p.1 p.2) bumpBox := by
  have hnum : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) bumpBox := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).pow 2).continuousOn
      (continuous_fst.pow 2).continuousOn ?_
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := by linarith [hp.1.1]
    positivity
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) bumpBox :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinpos : ∀ p ∈ bumpBox, 0 < Real.sin (2 * p.2) := fun p hp =>
    lt_of_lt_of_le (by norm_num) (sin_two_ge_half ⟨hp.2.1, hp.2.2⟩)
  have hden : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) bumpBox :=
    hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.FTS.StrongEps.epsW α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2) := by
    funext p; rfl
  rw [hfun]
  exact hnum.div hden (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

/-- The numerical bound on the support box: for `α ∈ (0,1]`, `epsW α z θ ≤ 32`. -/
theorem epsW_le_box {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {z θ : ℝ}
    (hz : z ∈ Set.Icc ((1 : ℝ) / 2) 1) (hθ : θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) :
    Work.FTS.StrongEps.epsW α z θ ≤ 32 := by
  have hgam : Work.Spaces.gam α / 2 ≤ 1 := by rw [Work.Spaces.gam]; linarith [hα.2]
  have hsin := sin_two_ge_half hθ
  have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by norm_num) hsin
  have hpow : Real.sin (2 * θ) ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) :=
    Real.self_le_rpow_of_le_one (le_of_lt hsinpos) (Real.sin_le_one _) hgam
  have hden : (1 : ℝ) / 2 ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := le_trans hsin hpow
  have hw : Work.Spaces.w z ≤ 16 := w_le_sixteen hz
  have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  calc Work.FTS.StrongEps.epsW α z θ
      = Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := rfl
    _ ≤ Work.Spaces.w z / (1 / 2) := div_le_div_of_nonneg_left hw0 (by norm_num) hden
    _ ≤ 16 / (1 / 2) := div_le_div_of_nonneg_right hw (by norm_num)
    _ = 32 := by norm_num

/-- The pointwise bound on the `EpsSq`-integrand of `bump`: `(bump · epsW α)² ≤ 1024`. -/
theorem bump_mul_epsW_sq_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (z θ : ℝ) :
    (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 ≤ 1024 := by
  by_cases hbox : z ∈ Set.Icc ((1 : ℝ) / 2) 1 ∧ θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)
  · obtain ⟨hz, hθ⟩ := hbox
    have hb1 : Work.FTS.StrongEps.bump z θ ≤ 1 := bump_le_one z θ
    have hb0 : 0 ≤ Work.FTS.StrongEps.bump z θ := Work.FTS.StrongEps.bump_nonneg z θ
    have he1 : Work.FTS.StrongEps.epsW α z θ ≤ 32 := epsW_le_box hα hz hθ
    have he0 : 0 ≤ Work.FTS.StrongEps.epsW α z θ := by
      rw [Work.FTS.StrongEps.epsW]
      exact div_nonneg (by rw [Work.Spaces.w]; positivity)
        (le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) (sin_two_ge_half hθ)) _))
    have hmul : Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ ≤ 32 :=
      calc Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ
          ≤ 1 * 32 := mul_le_mul hb1 he1 he0 (by norm_num)
        _ = 32 := by norm_num
    nlinarith [hmul, mul_nonneg hb0 he0]
  · have hb : Work.FTS.StrongEps.bump z θ = 0 := bump_eq_zero_of_not_mem_box hbox
    rw [hb, zero_mul, sq]
    norm_num

/-! ## `EpsMem` and the uniform `EpsSq`-bound -/

/-- The integrand of `EpsSq α bump` is continuous on the support box. -/
theorem continuousOn_epsSqIntegrand_bumpBox (α : ℝ) :
    ContinuousOn
      (fun p : ℝ × ℝ => (Work.FTS.StrongEps.bump p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) bumpBox :=
  (((contDiff_bump 0).continuous.continuousOn).mul (continuousOn_epsW_bumpBox α)).pow 2

/-- **`bump` belongs to the weighted space `X` of the scheme, for every `α`.**  The integrand is
continuous on the compact support box and vanishes outside it. -/
theorem epsMem_bump (α : ℝ) : Work.FTS.StrongEps.EpsMem α Work.FTS.StrongEps.bump := by
  show MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.FTS.StrongEps.bump p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) bumpBox volume :=
    (continuousOn_epsSqIntegrand_bumpBox α).integrableOn_compact isCompact_bumpBox
  refine hint.of_forall_sdiff_eq_zero (measurableSet_Ici.prod measurableSet_Icc) ?_
  rintro ⟨z, θ⟩ ⟨-, hs⟩
  have hb : Work.FTS.StrongEps.bump z θ = 0 :=
    bump_eq_zero_of_not_mem_box (by
      rintro ⟨h1, h2⟩
      exact hs (Set.mem_prod.mpr ⟨h1, h2⟩))
  rw [hb, zero_mul, sq]
  norm_num

/-- **The uniform bound on the `EpsSq`-size of `bump`**: `EpsSq α bump ≤ 1024` for every
`α ∈ (0,1]`. -/
theorem epsSq_bump_le (α : ℝ) (hα : α ∈ Set.Ioc 0 1) :
    Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump ≤ 1024 := by
  have hIθ_fin : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ]; exact isCompact_Icc.measure_lt_top
  have hinner : ∀ z : ℝ, ‖∫ θ in Work.Spaces.Iθ,
      (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
      ≤ 1024 * (volume : Measure ℝ).real Work.Spaces.Iθ := by
    intro z
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hIθ_fin (fun θ _ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact bump_mul_epsW_sq_le hα z θ
  -- the slice integral vanishes for `z ∉ [1/2,1]`
  have hEq : Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump
      = ∫ z in Set.Icc ((1 : ℝ) / 2) 1, (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := by
    rw [Work.FTS.StrongEps.EpsSq]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici ?_ ?_
    · intro z hz
      rw [Work.Spaces.Iz, Set.mem_Ici]
      linarith [hz.1]
    · rintro z ⟨-, hznot⟩
      have hzlt : z < 1 / 2 ∨ 1 < z := by
        by_contra hc
        push Not at hc
        exact hznot (Set.mem_Icc.mpr ⟨hc.1, hc.2⟩)
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun θ _ => ?_)
      rw [bump_eq_zero_of_not_mem_box (by
        rintro ⟨h1, -⟩
        rcases hzlt with h | h
        · linarith [h1.1, h]
        · linarith [h1.2, h]), zero_mul, sq]
      norm_num
  have hIcc_fin : (volume : Measure ℝ) (Set.Icc ((1 : ℝ) / 2) 1) < ⊤ :=
    isCompact_Icc.measure_lt_top
  have hbd : ‖∫ z in Set.Icc ((1 : ℝ) / 2) 1, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)‖
      ≤ (1024 * (volume : Measure ℝ).real Work.Spaces.Iθ)
        * (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hIcc_fin (fun z _ => hinner z)
  have hv1 : (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) = 1 / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
    norm_num
  have hv2 : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
    ring
  calc Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump
      = ∫ z in Set.Icc ((1 : ℝ) / 2) 1, (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := hEq
    _ ≤ ‖∫ z in Set.Icc ((1 : ℝ) / 2) 1, (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self
          (∫ z in Set.Icc ((1 : ℝ) / 2) 1, (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.StrongEps.bump z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
    _ ≤ (1024 * (volume : Measure ℝ).real Work.Spaces.Iθ)
          * (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) := hbd
    _ = 1024 * (Real.pi / 2) * (1 / 2) := by rw [hv1, hv2]
    _ ≤ 1024 := by nlinarith [Real.pi_lt_four]

/-! ## The target -/

theorem BumpEpsSqBound : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    Work.FTS.StrongEps.EpsMem α Work.FTS.StrongEps.bump ∧
    Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump ≤ K := by
  exact ⟨1024, by norm_num, fun α hα => ⟨epsMem_bump α, epsSq_bump_le α hα⟩⟩

end Work.FTS.StrongEps.EpsSqTools
