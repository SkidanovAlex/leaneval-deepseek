import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.j_sub_I_quadratic
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Analysis.norm_dslope_le_of_bound
import Submission.Work.Analysis.norm_dslope_sub_deriv_le_of_bound
import Submission.Work.Asymptotics.continuousOn_afunFun_ofComplex
import Submission.Work.Asymptotics.deriv_jprime_ofComplex_I_ne_zero
import Submission.Work.Asymptotics.differentiableOn_AfunFun_fst
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Kernels.KernelFacts.KPlus_T2

/-!
# The slice of the cleared CKMRV kernel at the elliptic point

This file proves that for `τ₀ = n + i` (`n = ±1`) the slice `z ↦ AfunFun ℓ d τ₀ z` has a
*simple* zero at the elliptic point `z = i`, i.e. there are `ρ, c > 0` with
`c ‖z - i‖ ≤ ‖AfunFun ℓ d τ₀ z‖` for `‖z - i‖ < ρ`.

## Strategy

The whole proof is carried out in the *chart* `x ↦ ofComplex x` around the two points
`τc = (τ₀ : ℂ) = i + n` and `i`.

* Two exact identities hold for all `τ`: the *value identity* at the translate pole
  `AfunFun ℓ d τ (τ - n) = -(n/2π) j'(τ - n)`, and the vanishing `AfunFun ℓ d (TⁿS•σ) (S•σ) = 0`
  (`AfunFun_S_vadd_eq_zero`).
* Parametrising both by the curve `x ↦ (τc + x, i + x)` resp. `x ↦ (τc + x, -1/(i+x))`, which
  pass through `(τc, i)` with velocities `(1,1)` and `(1,-1)`, and differentiating with the
  chain rule (proved from the *chart* structure of `AfunFun` with Cauchy's estimates), gives
  two explicit relations between the two partial derivatives
  `a = ∂_τ AfunFun (τ₀, i)` and `b = ∂_z AfunFun (τ₀, i)`:
  `a + b = D` and `a - b = 0`, where `D = -(n/2π) · d/dx j'(i+x)|₀ ≠ 0` since `i` is an
  elliptic point of order two (`deriv_jprime_ofComplex_I_ne_zero`).
  Hence `2 b = D ≠ 0`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane Filter Topology Complex
open scoped Topology Manifold MatrixGroups

namespace Work.Asymptotics

open Work.Kernels

/-! ## The vanishing of the cleared value function on the `S`-translate

This is the second value identity used in the proof: for `n = ±1` the cleared kernel vanishes
at the pair `(n +ᵥ σ, S • σ)`.  We prove it here self-containedly (from
`KPlusClear_TS`/`KMinusClear_TS`, `KClear_S_vanishing` and the second-difference equation
`(T-I)² K_±^{clear} = 0`), so that no dependency on the surrounding library is needed. -/

/-- `S` is an involution of `ℍ`. -/
lemma S_smul_S_smul' (σ : UpperHalfPlane) : ModularGroup.S • (ModularGroup.S • σ) = σ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.modular_S_smul,
    UpperHalfPlane.coe_mk]
  simp only [inv_neg, inv_inv, neg_neg]

/-- The second-difference equation `(T-I)² = 0` for the cleared `K_+`. -/
theorem KPlusClear_T2_aux (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.KPlusClear d σ z) = 0 := by
  have hUp : ∀ (σ : UpperHalfPlane) (i j : Fin 3),
      Work.Kernels.UpsilonPlusClear d ((1 : ℝ) +ᵥ σ) z i j
        = Work.Kernels.UpsilonPlusClear d σ z i j := by
    intro σ i j
    simp only [Work.Kernels.UpsilonPlusClear]
    split_ifs with h8 h24 <;>
      simp only [Work.Residues.AfunMinusNegOne.PiMatDelta_vadd_one,
        Work.Kernels.KernelFacts.jInvariantFun_vadd_one]
  have hdec : (fun σ : UpperHalfPlane => Work.Kernels.KPlusClear d σ z)
      = ∑ i : Fin 3, (fun σ : UpperHalfPlane => Work.Kernels.phiVec σ i *
          (∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d σ z i j *
            Work.Kernels.phitVec z j)) := by
    funext σ
    simp only [Work.Kernels.KPlusClear, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hdec]
  refine Work.Kernels.T2op_sum Finset.univ (fun i _ => ?_)
  refine Work.Kernels.T2op_mul_of (Work.Kernels.KernelFacts.phiVec_T2 i) ?_
  intro σ
  exact Finset.sum_congr rfl (fun j _ => by rw [hUp])

/-- `K_+^{clear}` vanishes at `T⁻¹S·z`. -/
theorem KPlusClear_Tinv_S_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear d ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hT2 := congr_fun (KPlusClear_T2_aux d hd z) ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hT2
  have h1 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (1 : ℝ) +ᵥ (ModularGroup.S • z) := by
    rw [← add_vadd]; norm_num
  have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) = ModularGroup.S • z := by
    rw [← add_vadd]; norm_num
  rw [h1, h2, (KClear_S_vanishing ℓ d hd z).1, Work.Residues.KPlusClear_TS d hd z] at hT2
  simpa using hT2

/-- `K_-^{clear}` vanishes at `T⁻¹S·z`. -/
theorem KMinusClear_Tinv_S_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.KMinusClear ℓ d ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hT2 := congr_fun (Work.Residues.AfunMinusNegOne.KMinusClear_T2 ℓ d hd z)
    ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hT2
  have h1 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (1 : ℝ) +ᵥ (ModularGroup.S • z) := by
    rw [← add_vadd]; norm_num
  have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) = ModularGroup.S • z := by
    rw [← add_vadd]; norm_num
  rw [h1, h2, (KClear_S_vanishing ℓ d hd z).2, Work.Residues.KMinusClear_TS ℓ d hd z] at hT2
  simpa using hT2

/-- **`AfunFun` vanishes on the `S`-translate**: for `n = ±1`, `AfunFun ℓ d (n +ᵥ σ) (S • σ) = 0`. -/
theorem AfunFun_S_vadd_eq_zero_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : UpperHalfPlane) :
    Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
  have hS : ModularGroup.S • (ModularGroup.S • σ) = σ := S_smul_S_smul' σ
  have hnr : (n : ℝ) = 1 ∨ (n : ℝ) = -1 := by
    rcases hn with h | h <;> simp [h]
  rcases hnr with h | h
  · have hplus : Work.Kernels.KPlusClear d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := Work.Residues.KPlusClear_TS d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    have hminus : Work.Kernels.KMinusClear ℓ d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := Work.Residues.KMinusClear_TS ℓ d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    rw [h, Work.Asymptotics.AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus,
      hplus, hminus]
    ring
  · have hplus : Work.Kernels.KPlusClear d ((-1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KPlusClear_Tinv_S_aux ℓ d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    have hminus : Work.Kernels.KMinusClear ℓ d ((-1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
      have hh := KMinusClear_Tinv_S_aux ℓ d hd (ModularGroup.S • σ)
      rwa [hS] at hh
    rw [h, Work.Asymptotics.AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus,
      hplus, hminus]
    ring

/-! ## The chart lift -/

/-- The lift of `AfunFun` to the chart `ℂ × ℂ → ℍ × ℍ`, `(x,y) ↦ A(ofComplex x, ofComplex y)`. -/
def chartFF (ℓ : LogLambdaData) (d : ℕ) : ℂ → ℂ → ℂ :=
  fun x y => AfunFun ℓ d (UpperHalfPlane.ofComplex x) (UpperHalfPlane.ofComplex y)

/-! ## An elementary lemma: a non-zero derivative forces a distance lower bound -/

theorem exists_lower_bound_of_hasDerivAt_ne_zero (f : ℂ → ℂ) (z₀ a : ℂ)
    (hf : HasDerivAt f a z₀) (ha : a ≠ 0) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ z : ℂ, ‖z - z₀‖ < ρ → c * ‖z - z₀‖ ≤ ‖f z‖ := by
  rcases eq_or_ne (f z₀) 0 with hz | hz
  · have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hslope := HasDerivAt.tendsto_slope hf
    have hev : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖a‖ / 2 ≤ ‖slope f z₀ z‖ := by
      have h1 : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖a‖ / 2 < ‖slope f z₀ z‖ := by
        refine hslope.norm.eventually ?_
        exact eventually_gt_nhds (by linarith)
      filter_upwards [h1] with z hz'; exact le_of_lt hz'
    rw [eventually_nhdsWithin_iff] at hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ρ, hρ, hball⟩ := hev
    refine ⟨ρ, ‖a‖ / 2, hρ, by positivity, ?_⟩
    intro z hzρ
    rcases eq_or_ne z z₀ with rfl | hzne
    · simp [hz]
    · have hzd : dist z z₀ < ρ := by rw [dist_eq_norm]; exact hzρ
      have h1 : ‖a‖ / 2 ≤ ‖slope f z₀ z‖ := hball hzd (by simpa using hzne)
      have h2 : (z - z₀) * slope f z₀ z = f z := by
        rw [slope_def_field, mul_div_cancel₀]
        · rw [hz]; ring
        · exact sub_ne_zero.mpr hzne
      calc ‖a‖ / 2 * ‖z - z₀‖ = ‖z - z₀‖ * (‖a‖ / 2) := by ring
        _ ≤ ‖z - z₀‖ * ‖slope f z₀ z‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg (z - z₀))
        _ = ‖f z‖ := by rw [← h2, norm_mul]
  · have hpos : 0 < ‖f z₀‖ := norm_pos_iff.mpr hz
    have hcont : ContinuousAt f z₀ := hf.continuousAt
    obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z, dist z z₀ < ρ → ‖f z₀‖ / 2 ≤ ‖f z‖ := by
      have h2 : ∀ᶠ z in 𝓝 z₀, ‖f z₀‖ / 2 ≤ ‖f z‖ := by
        have h4 : ‖f z₀‖ / 2 < ‖f z₀‖ := by linarith
        filter_upwards [hcont.norm.eventually (eventually_gt_nhds h4)] with z hz'
        exact le_of_lt hz'
      exact Metric.eventually_nhds_iff.mp h2
    refine ⟨ρ, ‖f z₀‖ / (2 * ρ), hρ, by positivity, ?_⟩
    intro z hzρ
    have hzd : dist z z₀ < ρ := by rw [dist_eq_norm]; exact hzρ
    have h1 : ‖f z₀‖ / 2 ≤ ‖f z‖ := hball z hzd
    have h2 : ‖z - z₀‖ ≤ ρ := le_of_lt hzρ
    have h3 : ‖f z₀‖ / (2 * ρ) * ‖z - z₀‖ ≤ ‖f z₀‖ / (2 * ρ) * ρ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : ‖f z₀‖ / (2 * ρ) * ρ = ‖f z₀‖ / 2 := by field_simp
    linarith

/-! ## A bound for the chart lift on a compact set -/

lemma im_pos_of_mem_closedBall {c : ℂ} {r : ℝ} (hr : r < c.im) {x : ℂ}
    (hx : x ∈ Metric.closedBall c r) : 0 < x.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h1 : |(x - c).im| ≤ ‖x - c‖ := Complex.abs_im_le_norm _
  have h2 : (x - c).im = x.im - c.im := by simp
  have h3 : -(‖x - c‖) ≤ (x - c).im := (abs_le.mp h1).1
  linarith [h2 ▸ h3, hx]

/-- On a compact chart set the lift of `AfunFun` is bounded. -/
lemma exists_bound_chartFF (ℓ : LogLambdaData) (d : ℕ) (c₁ c₂ : ℂ)
    (h₁ : 0 < c₁.im) (h₂ : 0 < c₂.im) {r : ℝ} (hr : 0 < r) (hr₁ : r < c₁.im)
    (hr₂ : r < c₂.im) :
    ∃ B : ℝ, ∀ x y : ℂ, ‖x - c₁‖ ≤ r → ‖y - c₂‖ ≤ r → ‖chartFF ℓ d x y‖ ≤ B := by
  have hsub : (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r) ⊆
      {p : ℂ × ℂ | 0 < p.1.im ∧ 0 < p.2.im} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨im_pos_of_mem_closedBall hr₁ hx, im_pos_of_mem_closedBall hr₂ hy⟩
  have hK : IsCompact (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r) :=
    IsCompact.prod (isCompact_closedBall c₁ r) (isCompact_closedBall c₂ r)
  have hcont : ContinuousOn (fun p : ℂ × ℂ => chartFF ℓ d p.1 p.2)
      (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r) :=
    (continuousOn_afunFun_ofComplex ℓ d).mono hsub
  have hcomp : IsCompact ((fun p : ℂ × ℂ => chartFF ℓ d p.1 p.2) ''
      (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r)) := hK.image_of_continuousOn hcont
  obtain ⟨B, hB⟩ := (hcomp.image_of_continuousOn continuous_norm.continuousOn).bddAbove
  refine ⟨B, fun x y hx hy => ?_⟩
  have hx' : x ∈ Metric.closedBall c₁ r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
  have hy' : y ∈ Metric.closedBall c₂ r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  have hmem : chartFF ℓ d x y ∈ (fun p : ℂ × ℂ => chartFF ℓ d p.1 p.2) ''
      (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r) := ⟨(x, y), ⟨hx', hy'⟩, rfl⟩
  exact hB ⟨chartFF ℓ d x y, hmem, rfl⟩



/-! ## Slice differentiability in the chart -/

lemma im_pos_of_norm_sub_I_le {y : ℂ} (hy : ‖y - Complex.I‖ ≤ 1 / 8) : 0 < y.im := by
  have h1 : |(y - Complex.I).im| ≤ ‖y - Complex.I‖ := Complex.abs_im_le_norm _
  have h2 : (y - Complex.I).im = y.im - 1 := by simp
  have h3 : -(‖y - Complex.I‖) ≤ (y - Complex.I).im := (abs_le.mp h1).1
  linarith [h2 ▸ h3, hy]

lemma im_pos_of_mem_ball {c : ℂ} {r : ℝ} (hr : r ≤ c.im) {x : ℂ}
    (hx : x ∈ Metric.ball c r) : 0 < x.im := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 : |(x - c).im| ≤ ‖x - c‖ := Complex.abs_im_le_norm _
  have h2 : (x - c).im = x.im - c.im := by simp
  have h3 : -(r) < (x - c).im := (abs_lt.mp (lt_of_le_of_lt h1 hx)).1
  linarith [h2 ▸ h3]

/-- Differentiability of the second-variable slice, in chart form. -/
lemma differentiableOn_chartFF_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (x : ℂ) :
    DifferentiableOn ℂ (fun w : ℂ => chartFF ℓ d x w) (Metric.ball Complex.I (1 / 2)) := by
  have h := (UpperHalfPlane.mdifferentiable_iff
    (f := fun z : UpperHalfPlane => AfunFun ℓ d (UpperHalfPlane.ofComplex x) z)).mp
    (mdifferentiable_AfunFun_snd ℓ d hd (UpperHalfPlane.ofComplex x))
  refine h.mono ?_
  intro w hw
  exact im_pos_of_mem_ball (by norm_num) hw

/-- Differentiability of the first-variable slice, in chart form. -/
lemma differentiableOn_chartFF_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τc : ℂ} (hτc : τc.im = 1) (y : ℂ) (hy : 0 < y.im) :
    DifferentiableOn ℂ (fun w : ℂ => chartFF ℓ d w y) (Metric.ball τc (1 / 2)) := by
  refine (differentiableOn_AfunFun_fst ℓ d hd (UpperHalfPlane.ofComplex y)).mono ?_
  intro τ hτ
  exact im_pos_of_mem_ball (by rw [hτc]; norm_num) hτ

/-! ## Two quantitative bounds for the chart slices -/

/-- **First-order bound for the `τ`-slice.**  On the disc of radius `1/4` about `τc`, the
difference quotient of `w ↦ chartFF ℓ d w y` at `τc` is within `128 B ‖x‖` of its derivative. -/
lemma chartFF_dslope_sub_deriv_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τc : ℂ} (hτc : τc.im = 1) {B : ℝ}
    (hB : ∀ x y : ℂ, ‖x - τc‖ ≤ 1 / 2 → ‖y - Complex.I‖ ≤ 1 / 2 → ‖chartFF ℓ d x y‖ ≤ B)
    {x y : ℂ} (hx : ‖x‖ ≤ 1 / 8) (hy : ‖y - Complex.I‖ ≤ 1 / 8) :
    ‖dslope (fun w : ℂ => chartFF ℓ d w y) τc (τc + x)
      - deriv (fun w : ℂ => chartFF ℓ d w y) τc‖ ≤ 128 * B * ‖x‖ := by
  have hR : (0 : ℝ) < 1 / 4 := by norm_num
  have hypos : 0 < y.im := im_pos_of_norm_sub_I_le hy
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => chartFF ℓ d w y) (Metric.ball τc (2 * (1 / 4))) := by
    have h := differentiableOn_chartFF_fst ℓ d hd hτc y hypos
    refine h.mono ?_
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    linarith
  have hM : ∀ w ∈ Metric.sphere τc (1 / 4), ‖chartFF ℓ d w y‖ ≤ B := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    exact hB w y (by rw [hw]; norm_num) (le_trans hy (by norm_num))
  have hux : ‖(τc + x) - τc‖ ≤ 1 / 4 / 2 := by
    rw [add_sub_cancel_left]
    linarith
  have := Work.Analysis.norm_dslope_sub_deriv_le_of_bound hR hdiff hM (τc + x) hux
  have hxe : ‖(τc + x) - τc‖ = ‖x‖ := by rw [add_sub_cancel_left]
  rw [hxe] at this
  calc ‖dslope (fun w : ℂ => chartFF ℓ d w y) τc (τc + x)
        - deriv (fun w : ℂ => chartFF ℓ d w y) τc‖
      ≤ 8 * B / (1 / 4) ^ 2 * ‖x‖ := this
    _ = 128 * B * ‖x‖ := by ring

/-- **Continuity of the `τ`-derivative in the second variable.** -/
lemma chartFF_deriv_sub_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τc : ℂ} (hτc : τc.im = 1) {B : ℝ}
    (hB : ∀ x y : ℂ, ‖x - τc‖ ≤ 1 / 2 → ‖y - Complex.I‖ ≤ 1 / 2 → ‖chartFF ℓ d x y‖ ≤ B)
    {y : ℂ} (hy : ‖y - Complex.I‖ ≤ 1 / 8) :
    ‖deriv (fun w : ℂ => chartFF ℓ d w y) τc
      - deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc‖ ≤ 32 * B * ‖y - Complex.I‖ := by
  have hR : (0 : ℝ) < 1 / 4 := by norm_num
  have hypos : 0 < y.im := im_pos_of_norm_sub_I_le hy
  set h : ℂ → ℂ := fun w => chartFF ℓ d w y - chartFF ℓ d w Complex.I with hh
  have hderiv : deriv (fun w : ℂ => chartFF ℓ d w y) τc
      - deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc = deriv h τc := by
    rw [hh]
    exact (deriv_sub
      ((differentiableOn_chartFF_fst ℓ d hd hτc y hypos).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/2))))
      ((differentiableOn_chartFF_fst ℓ d hd hτc Complex.I (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/2))))).symm
  have hdiff2 : DifferentiableOn ℂ h (Metric.ball τc (1 / 2)) := by
    rw [hh]
    refine (DifferentiableOn.sub ?_ ?_)
    · exact (differentiableOn_chartFF_fst ℓ d hd hτc y hypos).mono (by
        intro z hz; rw [Metric.mem_ball, dist_eq_norm] at hz ⊢; linarith)
    · exact (differentiableOn_chartFF_fst ℓ d hd hτc Complex.I (by simp)).mono (by
        intro z hz; rw [Metric.mem_ball, dist_eq_norm] at hz ⊢; linarith)
  have hdcl : DiffContOnCl ℂ h (Metric.ball τc (1 / 4)) := by
    refine ⟨hdiff2.mono ?_, hdiff2.continuousOn.mono ?_⟩
    · intro z hz; rw [Metric.mem_ball, dist_eq_norm] at hz ⊢; linarith
    · rw [closure_ball τc (by norm_num : (1:ℝ)/4 ≠ 0)]
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
  have hbd : ∀ z ∈ Metric.sphere τc (1 / 4), ‖h z‖ ≤ 8 * B * ‖y - Complex.I‖ := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hz1 : ‖z - τc‖ = 1 / 4 := hz
    have hfac : h z = (y - Complex.I) * dslope (fun w : ℂ => chartFF ℓ d z w)
        Complex.I y := by
      rw [hh]
      simp only
      rw [← sub_smul_dslope (fun w : ℂ => chartFF ℓ d z w) Complex.I y, smul_eq_mul]
    have hds : ‖dslope (fun w : ℂ => chartFF ℓ d z w) Complex.I y‖ ≤ 2 * B / (1 / 4) := by
      refine Work.Analysis.norm_dslope_le_of_bound hR ?_ ?_ _ ?_
      · have h := differentiableOn_chartFF_snd ℓ d hd z
        refine h.mono ?_
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        linarith
      · intro w hw
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        refine hB z w ?_ ?_
        · rw [hz1]; norm_num
        · rw [hw]; norm_num
      · exact le_trans hy (by norm_num)
    rw [hfac, norm_mul]
    calc ‖y - Complex.I‖ * ‖dslope (fun w : ℂ => chartFF ℓ d z w) Complex.I y‖
        ≤ ‖y - Complex.I‖ * (2 * B / (1 / 4)) :=
          mul_le_mul_of_nonneg_left hds (norm_nonneg _)
      _ = 8 * B * ‖y - Complex.I‖ := by ring
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdcl hbd
  rw [hderiv]
  calc ‖deriv h τc‖ ≤ 8 * B * ‖y - Complex.I‖ / (1 / 4) := hmain
    _ = 32 * B * ‖y - Complex.I‖ := by ring

/-! ## The chain rule along the two curves -/

/-- **Chain rule along the diagonal curve.**  `x ↦ chartFF ℓ d (τc + x) (i + x)` has derivative
`∂_τ + ∂_z` at `x = 0`. -/
lemma hasDerivAt_chartFF_diag (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τc : ℂ} (hτc : τc.im = 1) :
    HasDerivAt (fun x : ℂ => chartFF ℓ d (τc + x) (Complex.I + x))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        + deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 := by
  have hR1 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨B, hB⟩ := exists_bound_chartFF ℓ d τc Complex.I
    (by rw [hτc]; norm_num) (by simp) hR1 (by rw [hτc]; norm_num) (by norm_num)
  -- the two terms
  set a : ℂ := deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc with hadef
  set bb : ℂ := deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I with hbdef
  have hT1 : Tendsto (fun x : ℂ => dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x))
      τc (τc + x)) (𝓝 0) (𝓝 a) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hbdd : ∀ x : ℂ, ‖x‖ ≤ 1 / 8 →
        ‖dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x) - a‖
          ≤ 160 * B * ‖x‖ := by
      intro x hx
      have hy : ‖(Complex.I + x) - Complex.I‖ ≤ 1 / 8 := by
        rw [add_sub_cancel_left]; exact hx
      have h1 := chartFF_dslope_sub_deriv_bound ℓ d hd hτc hB hx hy
      have h2 : ‖deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc - a‖
          ≤ 32 * B * ‖x‖ := by
        have h3 := chartFF_deriv_sub_bound (ℓ := ℓ) (d := d) (hd := hd) (τc := τc) hτc hB hy
        rw [add_sub_cancel_left] at h3
        simpa only [hadef] using h3
      have hsplit : dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x) - a
          = (dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc)
            + (deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc - a) := by ring
      rw [hsplit]
      calc ‖(dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc)
            + (deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc - a)‖
          ≤ ‖dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc‖
            + ‖deriv (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc - a‖ := norm_add_le _ _
        _ ≤ 128 * B * ‖x‖ + 32 * B * ‖x‖ := add_le_add h1 h2
        _ = 160 * B * ‖x‖ := by ring
    refine squeeze_zero' (g := fun x : ℂ => 160 * B * ‖x‖) ?_ ?_ ?_
    · filter_upwards with x; exact norm_nonneg _
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/8)] with x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hbdd x hx
    · have hc : Continuous (fun x : ℂ => 160 * B * ‖x‖) := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
  have hT2 : Tendsto (fun x : ℂ => dslope (fun w : ℂ => chartFF ℓ d τc w)
      Complex.I (Complex.I + x)) (𝓝 0) (𝓝 bb) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hbdd : ∀ x : ℂ, ‖x‖ ≤ 1 / 8 →
        ‖dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (Complex.I + x) - bb‖
          ≤ 128 * B * ‖x‖ := by
      intro x hx
      have hM : ∀ w ∈ Metric.sphere Complex.I (1 / 4), ‖chartFF ℓ d τc w‖ ≤ B := by
        intro w hw
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        refine hB τc w ?_ ?_
        · rw [sub_self, norm_zero]; norm_num
        · rw [hw]; norm_num
      have hdiff : DifferentiableOn ℂ (fun w : ℂ => chartFF ℓ d τc w)
          (Metric.ball Complex.I (2 * (1 / 4))) := by
        have h := differentiableOn_chartFF_snd ℓ d hd τc
        refine h.mono ?_
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        linarith
      have hux : ‖(Complex.I + x) - Complex.I‖ ≤ 1 / 4 / 2 := by
        rw [add_sub_cancel_left]; linarith
      have := Work.Analysis.norm_dslope_sub_deriv_le_of_bound (by norm_num : (0:ℝ) < 1/4) hdiff hM
        (Complex.I + x) hux
      rw [add_sub_cancel_left] at this
      calc ‖dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (Complex.I + x) - bb‖
          ≤ 8 * B / (1 / 4) ^ 2 * ‖x‖ := this
        _ = 128 * B * ‖x‖ := by ring
    refine squeeze_zero' (g := fun x : ℂ => 128 * B * ‖x‖) ?_ ?_ ?_
    · filter_upwards with x; exact norm_nonneg _
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/8)] with x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hbdd x hx
    · have hc : Continuous (fun x : ℂ => 128 * B * ‖x‖) := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
  refine (hasDerivAt_iff_tendsto_slope).mpr ?_
  have hslope : (fun x : ℂ => slope (fun x : ℂ => chartFF ℓ d (τc + x) (Complex.I + x)) 0 x)
      =ᶠ[𝓝[≠] (0:ℂ)] (fun x : ℂ =>
        dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x)
        + dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (Complex.I + x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    rw [slope_def_field]
    have h1 : chartFF ℓ d (τc + x) (Complex.I + x) - chartFF ℓ d τc (Complex.I + x)
        = x * dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x) := by
      rw [← sub_smul_dslope (fun w : ℂ => chartFF ℓ d w (Complex.I + x)) τc (τc + x)]
      ring
    have h2 : chartFF ℓ d τc (Complex.I + x) - chartFF ℓ d τc Complex.I
        = x * dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (Complex.I + x) := by
      rw [← sub_smul_dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (Complex.I + x)]
      rw [smul_eq_mul]
      ring
    have hsplit : chartFF ℓ d (τc + x) (Complex.I + x) - chartFF ℓ d (τc + 0) (Complex.I + 0)
        = (chartFF ℓ d (τc + x) (Complex.I + x) - chartFF ℓ d τc (Complex.I + x))
          + (chartFF ℓ d τc (Complex.I + x) - chartFF ℓ d τc Complex.I) := by
      rw [add_zero, add_zero]; ring
    rw [hsplit, h1, h2, sub_zero, add_div, mul_div_cancel_left₀ _ hx0,
      mul_div_cancel_left₀ _ hx0]
  exact ((hT1.add hT2).mono_left nhdsWithin_le_nhds).congr' hslope.symm

/-- **Chain rule along the `S`-curve.**  `x ↦ chartFF ℓ d (τc + x) (-1/(i + x))` has derivative
`∂_τ - ∂_z` at `x = 0`. -/
lemma hasDerivAt_chartFF_S (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τc : ℂ} (hτc : τc.im = 1) :
    HasDerivAt (fun x : ℂ => chartFF ℓ d (τc + x) (-1 / (Complex.I + x)))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        - deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 := by
  have hR1 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨B, hB⟩ := exists_bound_chartFF ℓ d τc Complex.I
    (by rw [hτc]; norm_num) (by simp) hR1 (by rw [hτc]; norm_num) (by norm_num)
  set a : ℂ := deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc with hadef
  set bb : ℂ := deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I with hbdef
  set γ : ℂ → ℂ := fun x => -1 / (Complex.I + x) with hγdef
  have hγ0 : γ 0 = Complex.I := by
    rw [hγdef]
    simp only [add_zero]
    rw [neg_div, one_div, Complex.inv_I]
    ring
  have hγderiv : HasDerivAt γ (-1) 0 := by
    rw [hγdef]
    have hinner : HasDerivAt (fun x : ℂ => Complex.I + x) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add Complex.I
    have hne : Complex.I + 0 ≠ 0 := by simp
    have houter : HasDerivAt (fun y : ℂ => -1 / y) (-1) (Complex.I + 0) := by
      have h := (hasDerivAt_inv (x := Complex.I + 0) hne).const_mul (-1)
      have hc : (-1 : ℂ) * (-((Complex.I + 0) ^ 2)⁻¹) = -1 := by
        rw [add_zero, Complex.I_sq]; norm_num
      rw [hc] at h
      simpa [div_eq_mul_inv] using h
    have hcomp := houter.comp 0 hinner
    simpa only [Function.comp_def, mul_one] using hcomp
  have hγcont : Tendsto γ (𝓝 (0:ℂ)) (𝓝 Complex.I) := by
    have h := hγderiv.continuousAt
    change Tendsto γ (𝓝 (0:ℂ)) (𝓝 (γ 0)) at h
    rwa [hγ0] at h
  have hγdiff : Tendsto (fun x : ℂ => (γ x - γ 0) / (x - 0)) (𝓝[≠] (0:ℂ)) (𝓝 (-1)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hγderiv
    refine h.congr' ?_
    filter_upwards with x
    rw [slope_def_field]
  have hev : ∀ᶠ x : ℂ in 𝓝 0, ‖γ x - Complex.I‖ ≤ 1 / 8 := by
    filter_upwards [hγcont.eventually (Metric.ball_mem_nhds Complex.I (by norm_num : (0:ℝ) < 1/8))]
      with x hx
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have hT1 : Tendsto (fun x : ℂ => dslope (fun w : ℂ => chartFF ℓ d w (γ x))
      τc (τc + x)) (𝓝 0) (𝓝 a) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hbdd : ∀ᶠ x : ℂ in 𝓝 0,
        ‖dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x) - a‖
          ≤ 128 * B * ‖x‖ + 32 * B * ‖γ x - Complex.I‖ := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/16), hev]
        with x hx hy
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      have hx8 : ‖x‖ ≤ 1 / 8 := by linarith
      have h1 := chartFF_dslope_sub_deriv_bound ℓ d hd hτc hB hx8 hy
      have h2 := chartFF_deriv_sub_bound (ℓ := ℓ) (d := d) (hd := hd) (τc := τc) hτc hB hy
      have hsplit : dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x) - a
          = (dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc)
            + (deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc - a) := by ring
      rw [hsplit, hadef]
      calc ‖(dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc)
            + (deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc
              - deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc)‖
          ≤ ‖dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x)
              - deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc‖
            + ‖deriv (fun w : ℂ => chartFF ℓ d w (γ x)) τc
              - deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc‖ := norm_add_le _ _
        _ ≤ 128 * B * ‖x‖ + 32 * B * ‖γ x - Complex.I‖ := add_le_add h1 h2
    refine squeeze_zero' (g := fun x : ℂ => 128 * B * ‖x‖ + 32 * B * ‖γ x - Complex.I‖) ?_ ?_ ?_
    · filter_upwards with x; exact norm_nonneg _
    · exact hbdd
    · have h0 : Tendsto (fun x : ℂ => γ x - Complex.I) (𝓝 0) (𝓝 (0:ℂ)) := by
        have h2 := hγcont.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℂ => Complex.I) (𝓝 (0:ℂ)) (𝓝 Complex.I))
        simpa using h2
      have h1 : Tendsto (fun x : ℂ => ‖γ x - Complex.I‖) (𝓝 0) (𝓝 (0:ℝ)) := by
        simpa using h0.norm
      have h2 : Tendsto (fun x : ℂ => 32 * B * ‖γ x - Complex.I‖) (𝓝 0) (𝓝 (32 * B * 0)) :=
        h1.const_mul (32 * B)
      have h3 : Tendsto (fun x : ℂ => 128 * B * ‖x‖) (𝓝 0) (𝓝 (0:ℝ)) := by
        have hc : Tendsto (fun x : ℂ => ‖x‖) (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
          simpa using (continuous_norm.tendsto (0:ℂ))
        have h4 := hc.const_mul (128 * B)
        simpa using h4
      have hsum := h3.add h2
      simpa using hsum
  have hT2 : Tendsto (fun x : ℂ => dslope (fun w : ℂ => chartFF ℓ d τc w)
      Complex.I (γ x)) (𝓝 0) (𝓝 bb) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hbdd : ∀ᶠ x : ℂ in 𝓝 0,
        ‖dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x) - bb‖
          ≤ 128 * B * ‖γ x - Complex.I‖ := by
      filter_upwards [hev] with x hy
      have hM : ∀ w ∈ Metric.sphere Complex.I (1 / 4), ‖chartFF ℓ d τc w‖ ≤ B := by
        intro w hw
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        refine hB τc w ?_ ?_
        · rw [sub_self, norm_zero]; norm_num
        · rw [hw]; norm_num
      have hdiff : DifferentiableOn ℂ (fun w : ℂ => chartFF ℓ d τc w)
          (Metric.ball Complex.I (2 * (1 / 4))) := by
        have h := differentiableOn_chartFF_snd ℓ d hd τc
        refine h.mono ?_
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        linarith
      have hux : ‖γ x - Complex.I‖ ≤ 1 / 4 / 2 := by linarith
      have := Work.Analysis.norm_dslope_sub_deriv_le_of_bound (by norm_num : (0:ℝ) < 1/4) hdiff hM (γ x) hux
      calc ‖dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x) - bb‖
          ≤ 8 * B / (1 / 4) ^ 2 * ‖γ x - Complex.I‖ := this
        _ = 128 * B * ‖γ x - Complex.I‖ := by ring
    refine squeeze_zero' (g := fun x : ℂ => 128 * B * ‖γ x - Complex.I‖) ?_ ?_ ?_
    · filter_upwards with x; exact norm_nonneg _
    · exact hbdd
    · have h0 : Tendsto (fun x : ℂ => γ x - Complex.I) (𝓝 0) (𝓝 (0:ℂ)) := by
        have h2 := hγcont.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℂ => Complex.I) (𝓝 (0:ℂ)) (𝓝 Complex.I))
        simpa using h2
      have h1 : Tendsto (fun x : ℂ => ‖γ x - Complex.I‖) (𝓝 0) (𝓝 (0:ℝ)) := by
        simpa using h0.norm
      have h2 : Tendsto (fun x : ℂ => 128 * B * ‖γ x - Complex.I‖) (𝓝 0) (𝓝 (128 * B * 0)) :=
        h1.const_mul (128 * B)
      simpa using h2
  refine (hasDerivAt_iff_tendsto_slope).mpr ?_
  have hslope : (fun x : ℂ => slope (fun x : ℂ => chartFF ℓ d (τc + x) (γ x)) 0 x)
      =ᶠ[𝓝[≠] (0:ℂ)] (fun x : ℂ =>
        dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x)
        + ((γ x - γ 0) / (x - 0)) * dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    rw [slope_def_field]
    have h1 : chartFF ℓ d (τc + x) (γ x) - chartFF ℓ d τc (γ x)
        = x * dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x) := by
      rw [← sub_smul_dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x), smul_eq_mul]
      ring
    have h2 : chartFF ℓ d τc (γ x) - chartFF ℓ d τc (γ 0)
        = (γ x - γ 0) * dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x) := by
      rw [hγ0, ← sub_smul_dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x), smul_eq_mul]
    have hsplit : chartFF ℓ d (τc + x) (γ x) - chartFF ℓ d (τc + 0) (γ 0)
        = (chartFF ℓ d (τc + x) (γ x) - chartFF ℓ d τc (γ x))
          + (chartFF ℓ d τc (γ x) - chartFF ℓ d τc (γ 0)) := by
      rw [add_zero]; ring
    rw [hsplit, h1, h2]
    field_simp
    ring
  have hlim : Tendsto (fun x : ℂ =>
      dslope (fun w : ℂ => chartFF ℓ d w (γ x)) τc (τc + x)
      + ((γ x - γ 0) / (x - 0)) * dslope (fun w : ℂ => chartFF ℓ d τc w) Complex.I (γ x))
      (𝓝[≠] (0:ℂ)) (𝓝 (a + (-1) * bb)) := by
    exact (hT1.mono_left nhdsWithin_le_nhds).add
      (hγdiff.mul (hT2.mono_left nhdsWithin_le_nhds))
  have hgoal : a + (-1) * bb = a - bb := by ring
  rw [hgoal] at hlim
  exact hlim.congr' hslope.symm


/-! ## The main theorem -/

/-- **The slice of the cleared kernel at `τ = n + i` has a simple zero at the elliptic point.** -/
theorem bad_line_AfunFun_slice_simple_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ z : UpperHalfPlane,
      ‖(z : ℂ) - Complex.I‖ < ρ →
        c * ‖(z : ℂ) - Complex.I‖ ≤
          ‖AfunFun ℓ d ((n : ℝ) +ᵥ Work.Kernels.imagAxis 1 one_pos) z‖ := by
  set τ₀ : UpperHalfPlane := (n : ℝ) +ᵥ Work.Kernels.imagAxis 1 one_pos with hτ₀def
  have himag : ((Work.Kernels.imagAxis 1 one_pos : UpperHalfPlane) : ℂ) = Complex.I := by
    change (1 : ℂ) * Complex.I = Complex.I
    rw [one_mul]
  have hτ₀coe : (τ₀ : ℂ) = Complex.I + (n : ℂ) := by
    rw [hτ₀def, UpperHalfPlane.coe_vadd, himag]
    push_cast
    ring
  set τc : ℂ := (τ₀ : ℂ) with hτcdef
  have hτceq : τc = Complex.I + (n : ℂ) := hτ₀coe
  have hτcim : τc.im = 1 := by rw [hτceq]; simp
  have hSlt_eq : ∀ w : ℂ, chartFF ℓ d τc w = AfunFun ℓ d τ₀ (UpperHalfPlane.ofComplex w) := by
    intro w
    simp only [chartFF, hτcdef, UpperHalfPlane.ofComplex_apply]
  have hplus := Work.Residues.AfunPlus_neg_one d hd
  have hminus := Work.Residues.AfunMinus_neg_one ℓ d hd
  -- the two identities, on a neighbourhood of `0`
  have hEq1 : (fun x : ℂ => chartFF ℓ d (τc + x) (Complex.I + x)) =ᶠ[𝓝 (0:ℂ)]
      (fun x : ℂ => -(n / (2 * (Real.pi : ℂ))) *
        Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2)] with x hx
    have hx' : ‖x‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hxn : -(‖x‖) ≤ x.im := (abs_le.mp (Complex.abs_im_le_norm x)).1
    have him1 : 0 < (τc + x).im := by rw [Complex.add_im, hτcim]; linarith
    have him2 : 0 < (Complex.I + x).im := by rw [Complex.add_im]; simp; linarith
    have hcoeτ : ((UpperHalfPlane.ofComplex (τc + x) : UpperHalfPlane) : ℂ) = τc + x := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him1]
    have hσ : (-(n : ℝ)) +ᵥ UpperHalfPlane.ofComplex (τc + x)
        = UpperHalfPlane.ofComplex (Complex.I + x) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd, hcoeτ, UpperHalfPlane.ofComplex_apply_of_im_pos him2,
        hτceq]
      push_cast
      ring
    simp only [chartFF]
    rw [← hσ]
    exact AfunFun_neg_vadd ℓ d hd _ n hn hplus hminus
  have hEq2 : (fun x : ℂ => chartFF ℓ d (τc + x) (-1 / (Complex.I + x))) =ᶠ[𝓝 (0:ℂ)]
      (fun _ : ℂ => (0:ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2)] with x hx
    have hx' : ‖x‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hxn : -(‖x‖) ≤ x.im := (abs_le.mp (Complex.abs_im_le_norm x)).1
    have him1 : 0 < (τc + x).im := by rw [Complex.add_im, hτcim]; linarith
    have him2 : 0 < (Complex.I + x).im := by rw [Complex.add_im]; simp; linarith
    have hcoeτ : ((UpperHalfPlane.ofComplex (τc + x) : UpperHalfPlane) : ℂ) = τc + x := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him1]
    have hne : (Complex.I + x) ≠ 0 := by
      intro h0
      have : (Complex.I + x).im = 0 := by rw [h0]; simp
      rw [Complex.add_im] at this; simp at this; linarith
    have him3 : 0 < (-1 / (Complex.I + x)).im := by
      have h : ((ModularGroup.S • (UpperHalfPlane.ofComplex (Complex.I + x)) :
          UpperHalfPlane) : ℂ) = -1 / (Complex.I + x) := by
        rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
          UpperHalfPlane.ofComplex_apply_of_im_pos him2, inv_neg, neg_div, one_div]
      rw [← h]
      exact (ModularGroup.S • (UpperHalfPlane.ofComplex (Complex.I + x))).im_pos
    set σ : UpperHalfPlane := (-(n : ℝ)) +ᵥ UpperHalfPlane.ofComplex (τc + x) with hσdef
    have hfirst : ((n : ℝ) +ᵥ σ : UpperHalfPlane) = UpperHalfPlane.ofComplex (τc + x) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd, hσdef, UpperHalfPlane.coe_vadd, hcoeτ]
      push_cast
      ring
    have hσcoe : (σ : ℂ) = Complex.I + x := by
      rw [hσdef, UpperHalfPlane.coe_vadd, hcoeτ, hτceq]
      push_cast
      ring
    have hSσ : ModularGroup.S • σ = UpperHalfPlane.ofComplex (-1 / (Complex.I + x)) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hσcoe,
        UpperHalfPlane.ofComplex_apply_of_im_pos him3, UpperHalfPlane.coe_mk,
        inv_neg, neg_div, one_div]
    simp only [chartFF]
    rw [← hfirst, ← hSσ]
    exact AfunFun_S_vadd_eq_zero_aux ℓ d hd n hn σ
  -- the two chain rules
  have hPhi := hasDerivAt_chartFF_diag ℓ d hd hτcim
  have hPsi := hasDerivAt_chartFF_S ℓ d hd hτcim
  have hPhi' : HasDerivAt (fun x : ℂ => chartFF ℓ d (τc + x) (Complex.I + x))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        + deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 := hPhi
  have hPsi' : HasDerivAt (fun x : ℂ => chartFF ℓ d (τc + x) (-1 / (Complex.I + x)))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        - deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 := hPsi
  -- the derivative of the right-hand side of the first identity
  have hf_diff : DifferentiableAt ℂ
      (fun x : ℂ => Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x))) 0 := by
    by_contra h
    exact deriv_jprime_ofComplex_I_ne_zero (deriv_zero_of_not_differentiableAt h)
  have hg : HasDerivAt (fun x : ℂ => -(n / (2 * (Real.pi : ℂ))) *
        Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x)))
      (-(n / (2 * (Real.pi : ℂ))) *
        deriv (fun x : ℂ => Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x))) 0)
      0 := hf_diff.hasDerivAt.const_mul _
  have hg' : HasDerivAt (fun x : ℂ => -(n / (2 * (Real.pi : ℂ))) *
        Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x)))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        + deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 :=
    hPhi'.congr_of_eventuallyEq hEq1.symm
  have hab : deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        + deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I
      = -(n / (2 * (Real.pi : ℂ))) *
        deriv (fun x : ℂ => Work.Residues.jprime (UpperHalfPlane.ofComplex (Complex.I + x))) 0 :=
    hg'.unique hg
  have hcnz : -(n / (2 * (Real.pi : ℂ))) ≠ 0 := by
    rcases hn with h | h
    · rw [h]; simp [Real.pi_ne_zero]
    · rw [h]; simp [Real.pi_ne_zero]
  have habne : deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
      + deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I ≠ 0 := by
    rw [hab]
    exact mul_ne_zero hcnz deriv_jprime_ofComplex_I_ne_zero
  -- the second identity kills the difference
  have hPsi'' : HasDerivAt (fun _ : ℂ => (0:ℂ))
      (deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
        - deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) 0 :=
    hPsi'.congr_of_eventuallyEq hEq2.symm
  have hab2 : deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
      - deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I = 0 :=
    hPsi''.unique (hasDerivAt_const (0:ℂ) (0:ℂ))
  have haeq : deriv (fun w : ℂ => chartFF ℓ d w Complex.I) τc
      = deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I := sub_eq_zero.mp hab2
  have hbbne : deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I ≠ 0 := by
    intro h0
    refine habne ?_
    rw [haeq, h0, add_zero]
  -- hence the slice has a non-zero derivative at the elliptic point
  have hSlt_diff : DifferentiableAt ℂ (fun w : ℂ => chartFF ℓ d τc w) Complex.I :=
    (differentiableOn_chartFF_snd ℓ d hd τc).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/2)))
  obtain ⟨ρ, c, hρ, hcpos, hb⟩ := exists_lower_bound_of_hasDerivAt_ne_zero
    (fun w : ℂ => chartFF ℓ d τc w) Complex.I
    (deriv (fun w : ℂ => chartFF ℓ d τc w) Complex.I) hSlt_diff.hasDerivAt hbbne
  refine ⟨ρ, c, hρ, hcpos, fun z hz => ?_⟩
  have h := hb (z : ℂ) hz
  rw [hSlt_eq (z : ℂ), UpperHalfPlane.ofComplex_apply] at h
  exact h

end Work.Asymptotics
