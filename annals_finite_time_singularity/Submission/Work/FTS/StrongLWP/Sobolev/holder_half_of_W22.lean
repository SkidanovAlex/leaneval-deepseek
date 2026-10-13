import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongLWP.Defs
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.one_dim_agmon
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.nash_2d
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.grad_L2_le
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.segment_integral
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.holder_half_of_L4
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev

open MeasureTheory

set_option maxHeartbeats 2000000

/-!
# `holder_half_of_W22`

`‖v‖_{C^{0,1/2}} ≤ C (‖v‖_{L²} + ‖D²v‖_{L²})` for `v : ℝ × ℝ → ℝ` of class `C²` with compact
support (the critical 2-dimensional Sobolev embedding `W^{2,2}(ℝ²) ⊂ C^{0,1/2}`).

The proof is assembled from four independent estimates, each stated separately:

* `nash_2d`      : `∫ u⁴ ≤ 4 (∫u²)(∫‖∇u‖²)` (2-D Nash, obtained from the 1-D Agmon inequality
  `one_dim_agmon` by slicing);
* `grad_L2_le`   : `∫‖∇v‖² ≤ 4 √(∫v²) √(∫‖D²v‖²)` (integration by parts);
* `segment_integral` : the FTC along a segment;
* `holder_half_of_L4` : the 2-D Morrey estimate `|v p - v q| ≤ 4 (∫‖∇v‖⁴)^{1/4} √(dist p q)`,
  proved by averaging the segment identity over a ball.

Here we combine them.
-/

/-- `Integrable` for `x ↦ ‖fderiv ℝ v x‖ ^ k`, `k ≠ 0`, when `v` is `C²` with compact support. -/
private lemma integrable_norm_fderiv_pow {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) := by
  have hcont : Continuous (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) :=
    (hv.continuous_fderiv (by simp)).norm.pow k
  have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ k) :=
    (HasCompactSupport.fderiv ℝ hc).comp_left
      (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖ ^ k) (by simp [zero_pow hk])
  exact hcont.integrable_of_hasCompactSupport hcs

/-- `(|a| + |b|)^4 ≤ 8 (a^4 + b^4)`. -/
private lemma add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]

/-- `|a| ^ 4 = a ^ 4`. -/
private lemma abs_pow_four (a : ℝ) : |a| ^ 4 = a ^ 4 := by
  rw [show (|a| : ℝ) ^ 4 = (|a| ^ 2) ^ 2 by ring, sq_abs, show (a ^ 2) ^ 2 = a ^ 4 by ring]

/-- For a linear functional on `ℝ × ℝ` (with the sup norm on the domain) the operator norm is
bounded by the sum of the absolute values of its two partial components. -/
private lemma opNorm_le_abs_sum (L : ℝ × ℝ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (1, 0)| + |L (0, 1)| := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro h
  have hL : L h = h.1 * L (1, 0) + h.2 * L (0, 1) := by
    conv_lhs => rw [show h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hL, Real.norm_eq_abs]
  calc |h.1 * L (1, 0) + h.2 * L (0, 1)|
      ≤ |h.1 * L (1, 0)| + |h.2 * L (0, 1)| := abs_add_le _ _
    _ = |h.1| * |L (1, 0)| + |h.2| * |L (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖h‖ * |L (1, 0)| + ‖h‖ * |L (0, 1)| := by
        gcongr
        · simpa [Real.norm_eq_abs] using norm_fst_le h
        · simpa [Real.norm_eq_abs] using norm_snd_le h
    _ = (|L (1, 0)| + |L (0, 1)|) * ‖h‖ := by ring

/-- **Assembly.**  Given the four estimates (`nash_2d`, `grad_L2_le`, `segment_integral`,
`holder_half_of_L4`) the critical Sobolev embedding follows with the universal constant `16`. -/
theorem holder_half_of_W22_aux
    (hnash : ∀ (u : ℝ × ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
      ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) *
        (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2))
    (hibp : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 2 w → HasCompactSupport w →
      ∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (w x) ^ 2)
        * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ w) x‖ ^ 2))
    (hseg : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → ∀ p z : ℝ × ℝ,
      w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p))
    (hl4 : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      (∀ p z : ℝ × ℝ, w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p)) →
      ∀ p q : ℝ × ℝ, |w p - w q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 4) ^ (1 / 4 : ℝ)
        * Real.sqrt (dist p q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q) := by
  refine ⟨16, by norm_num, ?_⟩
  intro v hv hc p q
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  set α : ℝ := Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) with hαdef
  set β : ℝ := Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) with hβdef
  set G4 : ℝ := ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 with hG4def
  have hα0 : 0 ≤ α := by rw [hαdef]; exact Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := by rw [hβdef]; exact Real.sqrt_nonneg _
  have hG0 : 0 ≤ G4 := by
    rw [hG4def]; exact integral_nonneg fun x => by positivity
  -- `∫‖∇v‖² ≤ 4 α β`
  have hgrad : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤ 4 * α * β := by
    have h := hibp v hv hc
    rw [hαdef, hβdef]
    linarith [h]
  -- the two partial derivatives of `v` as scalar functions
  set u1 : ℝ × ℝ → ℝ := fun x => fderiv ℝ v x (1, 0) with hu1def
  set u2 : ℝ × ℝ → ℝ := fun x => fderiv ℝ v x (0, 1) with hu2def
  have hcd1 : ContDiff ℝ 1 u1 := by
    rw [hu1def]
    exact ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const :
      ContDiff ℝ 1 fun x : ℝ × ℝ => fderiv ℝ v x (1, 0))
  have hcd2 : ContDiff ℝ 1 u2 := by
    rw [hu2def]
    exact ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const :
      ContDiff ℝ 1 fun x : ℝ × ℝ => fderiv ℝ v x (0, 1))
  have hc1 : HasCompactSupport u1 := by
    rw [hu1def]; exact hc.fderiv_apply ℝ (1, 0)
  have hc2 : HasCompactSupport u2 := by
    rw [hu2def]; exact hc.fderiv_apply ℝ (0, 1)
  have hint1 : Integrable (fun x : ℝ × ℝ => (u1 x) ^ 4) :=
    (hcd1.continuous.pow 4).integrable_of_hasCompactSupport
      (hc1.comp_left (zero_pow (by norm_num : (4 : ℕ) ≠ 0)))
  have hint2 : Integrable (fun x : ℝ × ℝ => (u2 x) ^ 4) :=
    (hcd2.continuous.pow 4).integrable_of_hasCompactSupport
      (hc2.comp_left (zero_pow (by norm_num : (4 : ℕ) ≠ 0)))
  have hu1_le : ∀ x : ℝ × ℝ, |u1 x| ≤ ‖fderiv ℝ v x‖ := by
    intro x
    rw [hu1def]
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v x) ((1, 0) : ℝ × ℝ)
    simpa using h
  have hu2_le : ∀ x : ℝ × ℝ, |u2 x| ≤ ‖fderiv ℝ v x‖ := by
    intro x
    rw [hu2def]
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v x) ((0, 1) : ℝ × ℝ)
    simpa using h
  have hfderiv_u1_le : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ u1 x‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    have hdiff : DifferentiableAt ℝ (fderiv ℝ v) x :=
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hz : fderiv ℝ (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) x = 0 :=
      fderiv_const_apply ((1, 0) : ℝ × ℝ)
    rw [hu1def, fderiv_clm_apply hdiff (differentiableAt_const ((1, 0) : ℝ × ℝ)), hz]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    calc ‖(fderiv ℝ (fderiv ℝ v) x).flip ((1, 0) : ℝ × ℝ)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ v) x).flip‖ * ‖((1, 0) : ℝ × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [ContinuousLinearMap.opNorm_flip]; simp
  have hfderiv_u2_le : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ u2 x‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    have hdiff : DifferentiableAt ℝ (fderiv ℝ v) x :=
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hz : fderiv ℝ (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) x = 0 :=
      fderiv_const_apply ((0, 1) : ℝ × ℝ)
    rw [hu2def, fderiv_clm_apply hdiff (differentiableAt_const ((0, 1) : ℝ × ℝ)), hz]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    calc ‖(fderiv ℝ (fderiv ℝ v) x).flip ((0, 1) : ℝ × ℝ)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ v) x).flip‖ * ‖((0, 1) : ℝ × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [ContinuousLinearMap.opNorm_flip]; simp
  have hDv2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 2) :=
    integrable_norm_fderiv_pow hv hc 2 (by norm_num)
  have hD2v2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
    have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ v)) :=
      HasCompactSupport.fderiv ℝ (HasCompactSupport.fderiv ℝ hc)
    have hg : (fun L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) => ‖L‖ ^ 2)
        (0 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) = 0 := by
      show ‖(0 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ))‖ ^ 2 = 0
      rw [ContinuousLinearMap.opNorm_zero]; norm_num
    have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
      h2.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) => ‖L‖ ^ 2) hg
    exact ((h1.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport hcs
  -- `∫ u₁² ≤ ∫‖∇v‖²` and `∫ u₂² ≤ ∫‖∇v‖²`
  have hu1s : ∫ x : ℝ × ℝ, (u1 x) ^ 2 ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hDv2
    filter_upwards with x
    calc (u1 x) ^ 2 = |u1 x| ^ 2 := by rw [sq_abs]
      _ ≤ ‖fderiv ℝ v x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hu1_le x) 2
  have hu2s : ∫ x : ℝ × ℝ, (u2 x) ^ 2 ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hDv2
    filter_upwards with x
    calc (u2 x) ^ 2 = |u2 x| ^ 2 := by rw [sq_abs]
      _ ≤ ‖fderiv ℝ v x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hu2_le x) 2
  -- `∫‖∇u₁‖² ≤ ∫‖D²v‖²` and `∫‖∇u₂‖² ≤ ∫‖D²v‖²`
  have hu1d : ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2
      ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hD2v2
    filter_upwards with x
    exact pow_le_pow_left₀ (by positivity) (hfderiv_u1_le x) 2
  have hu2d : ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2
      ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hD2v2
    filter_upwards with x
    exact pow_le_pow_left₀ (by positivity) (hfderiv_u2_le x) 2
  have hβsq : β ^ 2 = ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    rw [hβdef, Real.sq_sqrt]
    exact integral_nonneg fun x => by positivity
  -- the `L⁴` bounds on the two partial derivatives
  have h14 : ∫ x : ℝ × ℝ, (u1 x) ^ 4 ≤ 16 * α * β ^ 3 := by
    have h := hnash u1 hcd1 hc1
    have h1 : ∫ x : ℝ × ℝ, (u1 x) ^ 2 ≤ 4 * α * β := hu1s.trans hgrad
    have h2 : ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2 ≤ β ^ 2 := hu1d.trans_eq hβsq.symm
    have hb : (0 : ℝ) ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2 := integral_nonneg fun x => by positivity
    calc ∫ x : ℝ × ℝ, (u1 x) ^ 4
        ≤ 4 * (∫ x : ℝ × ℝ, (u1 x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2) := h
      _ ≤ 4 * (4 * α * β) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u1 x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hb
      _ ≤ 4 * (4 * α * β) * β ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * α * β ^ 3 := by ring
  have h24 : ∫ x : ℝ × ℝ, (u2 x) ^ 4 ≤ 16 * α * β ^ 3 := by
    have h := hnash u2 hcd2 hc2
    have h1 : ∫ x : ℝ × ℝ, (u2 x) ^ 2 ≤ 4 * α * β := hu2s.trans hgrad
    have h2 : ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2 ≤ β ^ 2 := hu2d.trans_eq hβsq.symm
    have hb : (0 : ℝ) ≤ ∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2 := integral_nonneg fun x => by positivity
    calc ∫ x : ℝ × ℝ, (u2 x) ^ 4
        ≤ 4 * (∫ x : ℝ × ℝ, (u2 x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2) := h
      _ ≤ 4 * (4 * α * β) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u2 x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hb
      _ ≤ 4 * (4 * α * β) * β ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * α * β ^ 3 := by ring
  -- `∫‖∇v‖⁴ ≤ 8 (∫u₁⁴ + ∫u₂⁴)`
  have hG4le : G4 ≤ 256 * α * β ^ 3 := by
    have hInt8 : Integrable (fun x : ℝ × ℝ => 8 * ((u1 x) ^ 4 + (u2 x) ^ 4)) :=
      (hint1.add hint2).const_mul 8
    have hpt : ∀ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 ≤ 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by
      intro x
      have h1 : ‖fderiv ℝ v x‖ ≤ |u1 x| + |u2 x| := by
        rw [hu1def, hu2def]; exact opNorm_le_abs_sum _
      calc ‖fderiv ℝ v x‖ ^ 4 ≤ (|u1 x| + |u2 x|) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h1 4
        _ ≤ 8 * (|u1 x| ^ 4 + |u2 x| ^ 4) := add_pow_four_le _ _
        _ = 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by rw [abs_pow_four, abs_pow_four]
    have hmono : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4
        ≤ ∫ x : ℝ × ℝ, 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hInt8
      filter_upwards with x
      exact hpt x
    rw [hG4def]
    calc ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4
        ≤ ∫ x : ℝ × ℝ, 8 * ((u1 x) ^ 4 + (u2 x) ^ 4) := hmono
      _ = 8 * ((∫ x : ℝ × ℝ, (u1 x) ^ 4) + (∫ x : ℝ × ℝ, (u2 x) ^ 4)) := by
          rw [integral_const_mul, integral_add hint1 hint2]
      _ ≤ 8 * (16 * α * β ^ 3 + 16 * α * β ^ 3) := by gcongr
      _ = 256 * α * β ^ 3 := by ring
  -- hence `G4 ≤ 256 (α + β)⁴`
  have hG4le' : G4 ≤ 256 * (α + β) ^ 4 := by
    have hα' : α ≤ α + β := le_add_of_nonneg_right hβ0
    have hβ' : β ≤ α + β := le_add_of_nonneg_left hα0
    have h1 : α * β ^ 3 ≤ (α + β) ^ 4 := by
      calc α * β ^ 3 ≤ (α + β) * (α + β) ^ 3 := by
            apply mul_le_mul hα' (pow_le_pow_left₀ hβ0 hβ' 3) (by positivity) (by positivity)
        _ = (α + β) ^ 4 := by ring
    have h2 : 256 * α * β ^ 3 ≤ 256 * (α + β) ^ 4 := by
      calc 256 * α * β ^ 3 = 256 * (α * β ^ 3) := by ring
        _ ≤ 256 * (α + β) ^ 4 := mul_le_mul_of_nonneg_left h1 (by norm_num)
    exact hG4le.trans h2
  -- the fourth root
  have hP : G4 ^ (1 / 4 : ℝ) ≤ 4 * (α + β) := by
    have h256 : ((256 : ℝ) ^ (1 / 4 : ℝ)) = 4 := by
      rw [show (256 : ℝ) = (4 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast (4 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hfour : (((α + β) ^ 4 : ℝ) ^ (1 / 4 : ℝ)) = α + β := by
      rw [← Real.rpow_natCast (α + β) 4, ← Real.rpow_mul (by positivity)]
      norm_num
    calc G4 ^ (1 / 4 : ℝ) ≤ (256 * (α + β) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hG0 hG4le' (by norm_num)
      _ = 4 * (α + β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), h256, hfour]
  have hmor : |v p - v q| ≤ 4 * G4 ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
    have h := hl4 v hv1 hc (hseg v hv1) p q
    rw [hG4def]
    exact h
  have hd0 : 0 ≤ Real.sqrt (dist p q) := Real.sqrt_nonneg _
  calc |v p - v q| ≤ 4 * G4 ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := hmor
    _ ≤ 4 * (4 * (α + β)) * Real.sqrt (dist p q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hd0
    _ = 16 * (α + β) * Real.sqrt (dist p q) := by ring
    _ = 16 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q) := by
        rw [hαdef, hβdef]

/-- The (intended) Hölder form with an explicit real exponent: this is the statement that the
name `holder_half_of_W22` describes, and it is the one downstream users should consume. -/
theorem holder_half_of_W22_aux_rpow
    (hnash : ∀ (u : ℝ × ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
      ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) *
        (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2))
    (hibp : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 2 w → HasCompactSupport w →
      ∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (w x) ^ 2)
        * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ w) x‖ ^ 2))
    (hseg : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → ∀ p z : ℝ × ℝ,
      w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p))
    (hl4 : ∀ (w : ℝ × ℝ → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      (∀ p z : ℝ × ℝ, w z - w p = ∫ t in (0 : ℝ)..1, (fderiv ℝ w (p + t • (z - p))) (z - p)) →
      ∀ p q : ℝ × ℝ, |w p - w q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ w x‖ ^ 4) ^ (1 / 4 : ℝ)
        * Real.sqrt (dist p q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, H⟩ := holder_half_of_W22_aux hnash hibp hseg hl4
  refine ⟨C, hC, fun v hv hc p q => ?_⟩
  rw [← Real.sqrt_eq_rpow (dist p q)]
  exact H v hv hc p q

/-- The `(1/2)`-Hölder estimate in its clean public form: this is what the name
`holder_half_of_W22` describes and what downstream consumers should use.  (The binder
`dist p q ^ (1 / 2)` of the request elaborates with a **natural-number** exponent — Mathlib
reads `1 / 2 : ℕ` as `0`, so `dist p q ^ (1 / 2) = 1` — hence the request as written is the
*uniform* bound, proved below as `holder_half_of_W22`; the honest Hölder statement is this
one.) -/
theorem holder_half_of_W22_real :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) :=
  holder_half_of_W22_aux_rpow
    (fun u hu hc => HolderHalf.nash_2d hu hc
      (fun f hf hcf y => HolderHalf.one_dim_agmon hf hcf y))
    (fun w hw hw' => HolderHalf.grad_L2_le hw hw')
    (fun w hw p z => HolderHalf.segment_integral hw p z)
    (fun w hw hw' hs p q => HolderHalf.holder_half_of_L4 hw hw' hs p q)

theorem holder_half_of_W22 :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ C * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2) := by
  obtain ⟨C, hC, H⟩ := holder_half_of_W22_aux
    (fun u hu hc => HolderHalf.nash_2d hu hc
      (fun f hf hcf y => HolderHalf.one_dim_agmon hf hcf y))
    (fun w hw hw' => HolderHalf.grad_L2_le hw hw')
    (fun w hw p z => HolderHalf.segment_integral hw p z)
    (fun w hw hw' hs p q => HolderHalf.holder_half_of_L4 hw hw' hs p q)
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro v hv hc p q
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  set α : ℝ := Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) with hαdef
  set β : ℝ := Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) with hβdef
  have hα0 : 0 ≤ α := by rw [hαdef]; exact Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := by rw [hβdef]; exact Real.sqrt_nonneg _
  have hP0 : 0 ≤ C * (α + β) := by positivity
  have hM : ∀ z z' : ℝ × ℝ, |v z - v z'| ≤ (C * (α + β)) * Real.sqrt (dist z z') := by
    intro z z'
    have h := H v hv hc z z'
    rw [hαdef, hβdef]
    exact h
  have hsup : ∀ x : ℝ × ℝ, |v x| ≤ C * (α + β) + α / 2 := by
    intro x
    have h := HolderHalf.sup_le_of_holder hv1 hc (C * (α + β)) hP0 hM x
    rwa [hαdef] at h
  have h3 : |v p - v q| ≤ 2 * C * (α + β) + α := by
    calc |v p - v q| = |v p + (-v q)| := by ring_nf
      _ ≤ |v p| + |-v q| := abs_add_le _ _
      _ = |v p| + |v q| := by rw [abs_neg]
      _ ≤ (C * (α + β) + α / 2) + (C * (α + β) + α / 2) := add_le_add (hsup p) (hsup q)
      _ = 2 * C * (α + β) + α := by ring
  have h4 : 2 * C * (α + β) + α ≤ (2 * C + 1) * (α + β) := by nlinarith [hα0, hβ0, hC]
  have h6 : |v p - v q| ≤ (2 * C + 1) * (α + β) := le_trans h3 h4
  rw [hαdef, hβdef] at h6
  rw [show ((1 : ℕ) / 2) = 0 by norm_num, pow_zero, mul_one]
  exact h6

end Work.FTS.StrongLWP.Sobolev
