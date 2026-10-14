import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.Measurable =====
section

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
set_option maxHeartbeats 1000000


/-- The shift map with a fixed *base point* is measurable (the argument is the shift). -/
theorem measurable_shift_arg_map (z θ : ℝ) :
    Measurable fun p : ℝ × ℝ => (zShift z p.1, thShift θ p.2) := by
  have htan : Measurable fun ζ : ℝ => Real.tan ζ := by
    convert (Real.measurable_sin.div Real.measurable_cos :
      Measurable fun ζ : ℝ => Real.sin ζ / Real.cos ζ) using 1
    funext ζ
    exact Real.tan_eq_sin_div_cos ζ
  refine Measurable.prodMk ?_ ?_
  · show Measurable fun p : ℝ × ℝ => z * Real.exp (-p.1)
    exact (measurable_const : Measurable fun _ : ℝ × ℝ => z).mul
      (Real.measurable_exp.comp measurable_fst.neg)
  · show Measurable fun p : ℝ × ℝ => Real.arctan (Real.tan θ * Real.exp (-p.2))
    exact Real.measurable_arctan.comp
      ((measurable_const : Measurable fun _ : ℝ × ℝ => Real.tan θ).mul
        (Real.measurable_exp.comp measurable_snd.neg))

/-- The shift map of a base point and a parameter is measurable. -/
theorem measurable_shift_pair_map :
    Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) := by
  have htan : Measurable fun θ : ℝ => Real.tan θ := by
    convert (Real.measurable_sin.div Real.measurable_cos :
      Measurable fun θ : ℝ => Real.sin θ / Real.cos θ) using 1
    funext θ
    exact Real.tan_eq_sin_div_cos θ
  refine Measurable.prodMk ?_ ?_
  · show Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 * Real.exp (-z.2.1)
    exact (measurable_fst.comp measurable_fst).mul
      (Real.measurable_exp.comp (measurable_fst.comp measurable_snd).neg)
  · show Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.arctan (Real.tan z.1.2 * Real.exp (-z.2.2))
    exact Real.measurable_arctan.comp
      (((htan.comp (measurable_snd.comp measurable_fst)).mul
        (Real.measurable_exp.comp (measurable_snd.comp measurable_snd).neg)))

/-- `logJac` is measurable. -/
theorem measurable_logJac : Measurable fun u : ℝ × ℝ => HkSqAux.logJac u.1 u.2 := by
  have hk : Measurable fun ζ : ℝ => HkSqAux.kappa ζ := by
    simp only [HkSqAux.kappa]
    exact Real.measurable_exp.div
      (measurable_const.add (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  simp only [HkSqAux.logJac]
  exact (Real.measurable_exp.comp measurable_fst).mul (hk.comp measurable_snd)

/-- The log-coordinate pull-back of a set of the plane. -/
def logPre (B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {u : ℝ × ℝ | (Real.exp u.1, Real.arctan (Real.exp u.2)) ∈ B}

theorem measurableSet_logPre {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    MeasurableSet (logPre B) :=
  hB.preimage (Measurable.prodMk (Real.measurable_exp.comp measurable_fst)
    (Real.measurable_arctan.comp (Real.measurable_exp.comp measurable_snd)))

/-- **The log-coordinate pull-back of a Lebesgue-null set is Lebesgue-null.** -/
theorem volume_logPreimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) :
    (MeasureTheory.volume : Measure (ℝ × ℝ)) (logPre B) = 0 := by
  classical
  have hBlog_meas : MeasurableSet (logPre B) := measurableSet_logPre hB
  have hmeasB : Measurable fun q : ℝ × ℝ => B.indicator 1 q :=
    (measurable_const : Measurable fun _ : ℝ × ℝ => (1 : ENNReal)).indicator hB
  have hmeasLog : Measurable fun q : ℝ × ℝ => (logPre B).indicator 1 q :=
    (measurable_const : Measurable fun _ : ℝ × ℝ => (1 : ENNReal)).indicator hBlog_meas
  -- (a) the `logJac`-weighted integral of `1_{logPre B}` vanishes
  have hJac : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
      * (logPre B).indicator 1 (s, ζ)) = 0 := by
    have hid : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
          * (B.indicator 1) (Real.exp s, Real.arctan (Real.exp ζ)))
        = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
            * (logPre B).indicator 1 (s, ζ) := by
      refine lintegral_congr (fun s => lintegral_congr (fun ζ => ?_))
      congr 1
    rw [← hid, ← Work.FTS.StrongEps.EpsSrc.lintegral_logSubst (fun z θ => B.indicator 1 (z, θ))]
    have h2 : ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) B = 0 := by
      rw [MeasureTheory.Measure.restrict_apply hB]
      exact le_antisymm (MeasureTheory.measure_mono Set.inter_subset_left |>.trans_eq hB0) zero_le
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, B.indicator 1 (z, θ)) = 0 := by
      have h := MeasureTheory.setLIntegral_prod (μ := MeasureTheory.volume)
        (ν := MeasureTheory.volume) (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ)
        (f := fun q : ℝ × ℝ => B.indicator 1 q) hmeasB.aemeasurable
      rw [← h, MeasureTheory.lintegral_indicator_one hB]
      exact h2
    rw [hL]
  -- (b) hence `1_{logPre B}` vanishes a.e.
  have hprod0 : (∫⁻ u : ℝ × ℝ, ENNReal.ofReal (HkSqAux.logJac u.1 u.2)
      * (logPre B).indicator 1 u) = 0 :=
    le_antisymm (MeasureTheory.lintegral_prod_le (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)
      (fun u : ℝ × ℝ => ENNReal.ofReal (HkSqAux.logJac u.1 u.2)
        * (logPre B).indicator 1 u) |>.trans_eq hJac) zero_le
  have hmeas_int : Measurable fun u : ℝ × ℝ =>
      ENNReal.ofReal (HkSqAux.logJac u.1 u.2) * (logPre B).indicator 1 u :=
    (ENNReal.measurable_ofReal.comp measurable_logJac).mul hmeasLog
  have hone0 : (logPre B).indicator 1 =ᵐ[(MeasureTheory.volume : Measure (ℝ × ℝ))] (0 : ℝ × ℝ → ENNReal) := by
    have hf := (MeasureTheory.lintegral_eq_zero_iff hmeas_int).mp hprod0
    filter_upwards [hf] with u hu
    simp only [Pi.zero_apply] at hu ⊢
    rcases mul_eq_zero.mp hu with h | h
    · exact absurd h (ne_of_gt (ENNReal.ofReal_pos.mpr (HkSqAux.logJac_pos u.1 u.2)))
    · exact h
  -- (c) conclude
  have hz : (∫⁻ u : ℝ × ℝ, (logPre B).indicator 1 u) = 0 := by
    rw [MeasureTheory.lintegral_congr_ae hone0]
    simp
  rwa [MeasureTheory.lintegral_indicator_one hBlog_meas] at hz

/-- **Translation invariance of the Lebesgue measure under `p ↦ (s - p₁, ζ - p₂)`.** -/
theorem volume_preimage_sub_eq (s ζ : ℝ) {Blog : Set (ℝ × ℝ)} (hBlog : MeasurableSet Blog) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
      {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ Blog} = MeasureTheory.volume Blog := by
  set A : Set (ℝ × ℝ) := (fun q : ℝ × ℝ => ((s, ζ) : ℝ × ℝ) + q) ⁻¹' Blog with hA
  have hAmeas : MeasurableSet A := hBlog.preimage (measurable_const.add measurable_id)
  have hset : {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ Blog} = Neg.neg ⁻¹' A := by
    ext p
    have hp : ((s, ζ) : ℝ × ℝ) + (-p) = (s - p.1, ζ - p.2) := by
      refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg]
    simp only [hA, Set.mem_setOf_eq, Set.mem_preimage]
    rw [hp]
  have hneg : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Neg.neg ⁻¹' A) = MeasureTheory.volume A := by
    have h1 : (∫⁻ p : ℝ × ℝ, (Neg.neg ⁻¹' A).indicator 1 p)
        = ∫⁻ p : ℝ × ℝ, A.indicator 1 p := by
      rw [← MeasureTheory.lintegral_neg_eq_self (fun p : ℝ × ℝ => A.indicator 1 p)]
      exact MeasureTheory.lintegral_congr (fun p => rfl)
    rw [← MeasureTheory.lintegral_indicator_one (hAmeas.preimage measurable_neg), h1,
      MeasureTheory.lintegral_indicator_one hAmeas]
  rw [hset, hneg]
  exact MeasureTheory.measure_preimage_add MeasureTheory.volume (s, ζ) Blog

/-- **One slice of the pull-back of a null set is null.** -/
theorem volume_shift_preimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
      {p : ℝ × ℝ | (zShift z p.1, thShift θ p.2) ∈ B} = 0 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℝ, Real.exp s = z := ⟨Real.log z, Real.exp_log hz⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, Real.arctan (Real.exp ζ) = θ := by
    refine ⟨Real.log (Real.tan θ), ?_⟩
    rw [Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2)]
    exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
  have hset : {p : ℝ × ℝ | (zShift z p.1, thShift θ p.2) ∈ B}
      = {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ logPre B} := by
    ext p
    simp only [logPre, Set.mem_setOf_eq]
    rw [← hs, ← hζ, zShift_exp', thShift_arctan_exp']
  rw [hset, volume_preimage_sub_eq s ζ (measurableSet_logPre hB)]
  exact volume_logPreimage_null hB hB0

/-- `Quad` is conull for the measure `μq = volume∣_{Iz ×ˢ Iθ}`. -/
theorem ae_mem_quad :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), q ∈ Quad := by
  rw [MeasureTheory.ae_iff]
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioi.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
      Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton 0) (MeasureTheory.measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h' | h'
      · exact absurd ⟨h, h'⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h')
    · exact Or.inl (le_antisymm h hxI.1)
  have hsub : {a : ℝ × ℝ | a ∉ Quad} ⊆
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
        ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) := by
    intro q hq
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq] at hq ⊢
    tauto
  refine MeasureTheory.measure_mono_null hsub (MeasureTheory.measure_union_null ?_ ?_)
  · rw [MeasureTheory.Measure.prod_prod, h1, zero_mul]
  · rw [MeasureTheory.Measure.prod_prod, h2, mul_zero]

/-- **The pull-back of a null set under the shift map is null** (for the product measure). -/
theorem measure_shift_pair_preimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) :
    (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume)
      {z : (ℝ × ℝ) × (ℝ × ℝ) | (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ B} = 0 := by
  classical
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    {z | (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ B} with hS
  have hSmeas : MeasurableSet S := hB.preimage measurable_shift_pair_map
  have hSind : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => S.indicator 1 z :=
    (measurable_const : Measurable fun _ : (ℝ × ℝ) × (ℝ × ℝ) => (1 : ENNReal)).indicator hSmeas
  rw [← MeasureTheory.lintegral_indicator_one hSmeas]
  rw [show (∫⁻ z : (ℝ × ℝ) × (ℝ × ℝ), S.indicator 1 z
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume)
        = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, S.indicator 1 (q, p) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
        MeasureTheory.lintegral_prod
          (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (ν := MeasureTheory.volume) _ hSind.aemeasurable]
  have hcongr : (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ, S.indicator 1 (q, p))
      = fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
          ({p' : ℝ × ℝ | (zShift q.1 p'.1, thShift q.2 p'.2) ∈ B}).indicator 1 p := by
    funext q
    refine MeasureTheory.lintegral_congr (fun p => ?_)
    simp only [hS, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [hcongr]
  have hzero : ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (∫⁻ p : ℝ × ℝ,
        ({p' : ℝ × ℝ | (zShift q.1 p'.1, thShift q.2 p'.2) ∈ B}).indicator 1 p) = 0 := by
    filter_upwards [ae_mem_quad] with q hq
    have hmeasq : MeasurableSet {p : ℝ × ℝ | (zShift q.1 p.1, thShift q.2 p.2) ∈ B} :=
      hB.preimage (measurable_shift_arg_map q.1 q.2)
    rw [MeasureTheory.lintegral_indicator_one hmeasq]
    exact volume_shift_preimage_null hB hB0 hq.1 hq.2
  rw [MeasureTheory.lintegral_congr_ae hzero, MeasureTheory.lintegral_zero]

/-- `Quad` is conull for the measure `μq = volume∣_{Iz ×ˢ Iθ}` (the null set is computed
directly). -/
theorem measure_quad_compl :
    (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))) Quadᶜ = 0 := by
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioi.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
      Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton 0) (MeasureTheory.measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h' | h'
      · exact absurd ⟨h, h'⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h')
    · exact Or.inl (le_antisymm h hxI.1)
  have hsub : Quadᶜ ⊆ ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
      ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) := by
    intro q hq
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hq ⊢
    tauto
  refine MeasureTheory.measure_mono_null hsub (MeasureTheory.measure_union_null ?_ ?_)
  · rw [MeasureTheory.Measure.prod_prod, h1, zero_mul]
  · rw [MeasureTheory.Measure.prod_prod, h2, mul_zero]

/-- **The shifted integrand is a.e. measurable.** -/
theorem aemeasurable_shift_comp {Γ : ℝ × ℝ → ENNReal}
    (hΓ : AEMeasurable Γ (MeasureTheory.volume : Measure (ℝ × ℝ))) :
    AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        Γ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  obtain ⟨Γ₁, hΓ₁_meas, hΓ₁_eq⟩ := hΓ
  have hN0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) {u : ℝ × ℝ | Γ u ≠ Γ₁ u} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hΓ₁_eq
  obtain ⟨B, hNB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hN0
  refine ⟨fun z => Γ₁ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2), ?_, ?_⟩
  · exact hΓ₁_meas.comp measurable_shift_pair_map
  · show ∀ᵐ z : (ℝ × ℝ) × (ℝ × ℝ) ∂(((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume),
      Γ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) = Γ₁ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2)
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (measure_shift_pair_preimage_null hBmeas hB0)
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    exact hNB hz

/-- The a.e. measurability of the shifted integrand, with the measurability hypothesis in the
form in which `EpsMem` provides it (with respect to the *restricted* measure). -/
theorem aemeasurable_shift_comp' {F : ℝ × ℝ → ENNReal}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        F (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  have hquadmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hFa : AEMeasurable ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F) MeasureTheory.volume :=
    (aemeasurable_indicator_iff hquadmeas).mpr hF
  obtain ⟨g, hg, hg1⟩ := aemeasurable_shift_comp hFa
  refine ⟨g, hg, ?_⟩
  have hquad : ∀ᵐ z : (ℝ × ℝ) × (ℝ × ℝ)
      ∂(((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume), z.1 ∈ Quad := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : (ℝ × ℝ) × (ℝ × ℝ) | ¬ z.1 ∈ Quad}
        = Quadᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true]
    rw [hset, MeasureTheory.Measure.prod_prod, measure_quad_compl, zero_mul]
  have hae : (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F
          (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume]
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        F (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2)) := by
    filter_upwards [hquad] with z hz
    have hmem : (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
      ⟨(zShift_pos hz.1).le, ⟨(thShift_mem hz.2).1.le, (thShift_mem hz.2).2.le⟩⟩
    exact Set.indicator_of_mem hmem F
  exact hae.symm.trans hg1


end Work.FTS.StrongEps.EpsSqTools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.Shift =====
section

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
set_option maxHeartbeats 1000000

/-- **The shift step**: the integral of the shifted `EpsSq`-integrand is bounded by
`e^{δ(|p₁|+|p₂|)} EpsSq α f`, where `δ` is the constant of the Jacobian comparison
`logJac s ζ ≤ e^{δ(|p₁|+|p₂|)} logJac (s-p₁) (ζ-p₂)`. -/
theorem shift_step {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * HkSqAux.logJac (s - p₁) (ζ - p₂)) (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (EpsSq α f) := by
  set G : ℝ → ℝ → ENNReal := fun s ζ => ENNReal.ofReal
    ((f (Real.exp s) (Real.arctan (Real.exp ζ))
      * epsW α (Real.exp s) (Real.arctan (Real.exp ζ))) ^ 2) with hG
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2) := by
    rw [Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
      (fun z θ => ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
        * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))]
    refine lintegral_congr (fun s => lintegral_congr (fun ζ => ?_))
    congr 1
    simp only [hG, zShift_exp', thShift_arctan_exp']
  have htrans : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ :=
    HkSqAux.lintegral_prod_shift_mul (fun s ζ => ENNReal.ofReal (HkSqAux.logJac s ζ)) G p.1 p.2
  have h2 : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ)
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := by
    have hpt : ∀ s ζ : ℝ,
        ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ
          ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) := by
      intro s ζ
      have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
      rw [add_sub_cancel_right, add_sub_cancel_right] at h
      calc ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ
          ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)) * HkSqAux.logJac s ζ) * G s ζ :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le
        _ = (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (HkSqAux.logJac s ζ)) * G s ζ := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) := by ring
    calc (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ)
        ≤ ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) :=
          lintegral_mono (fun s => lintegral_mono (fun ζ => hpt s ζ))
      _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := by
          rw [show (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ))
              = ∫⁻ s, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                  * (∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) from by
                refine lintegral_congr (fun s => ?_)
                exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h3 : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ)
      = ENNReal.ofReal (EpsSq α f) := by
    rw [← Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
      (fun z θ => ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2))]
    exact (Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hf).symm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2) := h1
    _ = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ := htrans
    _ ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := h2
    _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (EpsSq α f) := by
        rw [h3]

end Work.FTS.StrongEps.EpsSqTools
end
end
