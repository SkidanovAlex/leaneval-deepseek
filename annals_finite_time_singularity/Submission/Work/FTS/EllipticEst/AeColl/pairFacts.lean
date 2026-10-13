/-
# `AeColl/pairFacts` — elementary facts about the two cut-offs of `pairChain`

This module collects the (elementary) analytic facts about

* the angular bump `psiD δ θ = T((θ - δ/4)/(δ/4)) · T(((π/2 - δ/4) - θ)/(δ/4))`
  (`T = Real.smoothTransition`), which is `1` on `[δ/2, π/2 - δ/2]`, vanishes off
  `[δ/4, π/2 - δ/4]` and tends to `1` pointwise as `δ → 0⁺`;
* the radial cut-off `Work.FTS.EllipticEst.cut n`, which is compactly supported in `(0,∞)`;

together with the order-`2` regularity of `psiD δ` and the order-`1` regularity of `cut n` needed
by the two integration-by-parts identities `I1Wk.truncZIbp2` / `I1Wk.truncThetaIbpSep`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

/-! ## The `ψ_δ''`-term of the truncated chain -/

/-- The angular second-derivative term of the truncated chain for the bump `psiD δ`:
`W_χδ = ∫_z χ w² ∫_θ σ θ · ψ_δ''(θ) · (z ∂_z u)²`.  This is the term whose bound by the
endpoint collar energies is the only place where the Hardy-type rate of the slices of `z∂_z u`
is used. -/
def Wtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2),
        sigθ θ * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2

/-! ## The angular bump `psiD δ` -/

theorem psiD_apply (δ θ : ℝ) :
    psiD δ θ = Real.smoothTransition ((θ - δ / 4) / (δ / 4))
      * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) := rfl

/-- `psiD δ` is `C²` on the line (for every `δ`, including the degenerate `δ = 0`). -/
theorem psiD_contDiff (δ : ℝ) : ContDiff ℝ 2 (psiD δ) := by
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => (θ - δ / 4) / (δ / 4)) :=
    (contDiff_id.sub contDiff_const).div_const _
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => ((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) :=
    (contDiff_const.sub contDiff_id).div_const _
  have h3 := (Real.smoothTransition.contDiff (n := 2)).comp h1
  have h4 := (Real.smoothTransition.contDiff (n := 2)).comp h2
  exact h3.mul h4

theorem psiD_nonneg (δ θ : ℝ) : 0 ≤ psiD δ θ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem psiD_le_one (δ θ : ℝ) : psiD δ θ ≤ 1 := by
  have h1 := Real.smoothTransition.le_one ((θ - δ / 4) / (δ / 4))
  have h2 := Real.smoothTransition.nonneg (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
  have h3 := Real.smoothTransition.le_one (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
  have h4 := Real.smoothTransition.nonneg ((θ - δ / 4) / (δ / 4))
  rw [psiD_apply]
  nlinarith [h1, h2, h3, h4]

theorem psiD_pos_of_mem {δ θ : ℝ} (hδ : 0 < δ) (h1 : δ / 2 ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - δ / 2) : 0 < psiD δ θ := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hA : 1 ≤ (θ - δ / 4) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  have hB : 1 ≤ ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  rw [psiD_apply, Real.smoothTransition.one_of_one_le hA,
    Real.smoothTransition.one_of_one_le hB, mul_one]
  norm_num

theorem psiD_eq_one_of_mem {δ θ : ℝ} (hδ : 0 < δ) (h1 : δ / 2 ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - δ / 2) : psiD δ θ = 1 := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hA : 1 ≤ (θ - δ / 4) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  have hB : 1 ≤ ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) := by
    rw [le_div_iff₀ hδ4]; linarith
  rw [psiD_apply, Real.smoothTransition.one_of_one_le hA,
    Real.smoothTransition.one_of_one_le hB, mul_one]

theorem psiD_eq_zero_of_le {δ θ : ℝ} (hδ : 0 < δ) (h : θ ≤ δ / 4) : psiD δ θ = 0 := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hA : (θ - δ / 4) / (δ / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ4)
  rw [psiD_apply, Real.smoothTransition.zero_of_nonpos hA, zero_mul]

theorem psiD_eq_zero_of_ge {δ θ : ℝ} (hδ : 0 < δ)
    (h : Real.pi / 2 - δ / 4 ≤ θ) : psiD δ θ = 0 := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hB : ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ4)
  rw [psiD_apply, Real.smoothTransition.zero_of_nonpos hB, mul_zero]

/-- `psiD δ` vanishes off the closed interval `[δ/4, π/2 - δ/4]`. -/
theorem psiD_eq_zero_of_notMem (δ θ : ℝ)
    (h : θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4)) : psiD δ θ = 0 := by
  have key : ∀ {a b : ℝ}, a ≤ 0 → Real.smoothTransition a * b = 0 :=
    fun ha => by rw [Real.smoothTransition.zero_of_nonpos ha, zero_mul]
  have key' : ∀ {a b : ℝ}, b ≤ 0 → a * Real.smoothTransition b = 0 :=
    fun hb => by rw [Real.smoothTransition.zero_of_nonpos hb, mul_zero]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rcases lt_trichotomy (δ / 4) 0 with h' | h' | h'
    · rw [psiD_apply]
      exact key' (le_of_lt (div_neg_of_pos_of_neg (show (0:ℝ) < (Real.pi / 2 - δ / 4) - θ by
        linarith [Real.pi_pos]) h'))
    · rw [psiD_apply, h', div_zero]
      exact key (le_refl (0 : ℝ))
    · rw [psiD_apply]
      exact key (le_of_lt (div_neg_of_neg_of_pos (show θ - δ / 4 < 0 by linarith) h'))
  · rcases lt_trichotomy (δ / 4) 0 with h' | h' | h'
    · rw [psiD_apply]
      exact key (le_of_lt (div_neg_of_pos_of_neg (show (0:ℝ) < θ - δ / 4 by
        linarith [Real.pi_pos]) h'))
    · rw [psiD_apply, h', div_zero]
      exact key (le_refl (0 : ℝ))
    · rw [psiD_apply]
      exact key' (le_of_lt (div_neg_of_neg_of_pos (show (Real.pi / 2 - δ / 4) - θ < 0 by
        linarith) h'))

theorem psiD_support_subset (δ : ℝ) :
    Function.support (psiD δ) ⊆ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) :=
  Function.support_subset_iff.mpr fun θ hθ =>
    not_not.mp fun h => hθ (psiD_eq_zero_of_notMem δ θ h)

theorem psiD_tsupport_subset (δ : ℝ) :
    tsupport (psiD δ) ⊆ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) := by
  rw [tsupport]
  exact closure_minimal (psiD_support_subset δ) isClosed_Icc

/-- For `0 < δ ≤ π/8` the support of `psiD δ` is contained in the smaller interval
`(δ/8, π/2 - δ/8)`, whose closure is a compact subset of `(0, π/2)`. -/
theorem psiD_tsupport_subset' {δ : ℝ} (hδ : 0 < δ) (_hδ2 : 4 * δ ≤ Real.pi) :
    tsupport (psiD δ) ⊆ Set.Ioo (δ / 8) (Real.pi / 2 - δ / 8) := by
  intro θ hθ
  have h := psiD_tsupport_subset δ hθ
  constructor
  · linarith [h.1]
  · linarith [h.2]

theorem psiD_tsupport_subset_Ioo {δ : ℝ} (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi) :
    tsupport (psiD δ) ⊆ Set.Ioo 0 (Real.pi / 2) := by
  intro θ hθ
  have h := psiD_tsupport_subset' hδ hδ2 hθ
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem psiD_hasCompactSupport (δ : ℝ) : HasCompactSupport (psiD δ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (psiD_support_subset δ)

/-- The bump tends to `1` pointwise as `δ → 0⁺`. -/
theorem psiD_tendsto_one (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Tendsto (fun δ : ℝ => psiD δ θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have h1 : (fun δ : ℝ => Real.smoothTransition ((θ - δ / 4) / (δ / 4)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * θ by linarith)] with δ hδ
    have hδ4 : 0 < δ / 4 := by linarith [hδ.1]
    have hA : 1 ≤ (θ - δ / 4) / (δ / 4) := by
      rw [le_div_iff₀ hδ4]; linarith [hδ.2]
    rw [Real.smoothTransition.one_of_one_le hA]
  have h2 : (fun δ : ℝ => Real.smoothTransition
        (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * (Real.pi / 2 - θ) by linarith)]
      with δ hδ
    have hδ4 : 0 < δ / 4 := by linarith [hδ.1]
    have hB : 1 ≤ ((Real.pi / 2 - δ / 4) - θ) / (δ / 4) := by
      rw [le_div_iff₀ hδ4]; linarith [hδ.2]
    rw [Real.smoothTransition.one_of_one_le hB]
  have t1 : Tendsto (fun δ : ℝ => Real.smoothTransition ((θ - δ / 4) / (δ / 4)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : ℝ))).congr' h1.symm
  have t2 : Tendsto (fun δ : ℝ => Real.smoothTransition
      (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : ℝ))).congr' h2.symm
  have := t1.mul t2
  simpa only [psiD_apply, mul_one] using this

/-! ## The radial cut-off `cut n` -/

theorem cut_contDiff_one (n : ℕ) : ContDiff ℝ 1 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by norm_num)

theorem cut_support_subset_Icc (n : ℕ) :
    Function.support (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) := by
  refine Function.support_subset_iff.mpr fun z hz => ?_
  by_contra h
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt h))
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt h))

theorem cut_support_subset_Ioi (n : ℕ) :
    Function.support (Work.FTS.EllipticEst.cut n) ⊆ Set.Ioi (0 : ℝ) := by
  intro z hz
  have h := cut_support_subset_Icc n hz
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact lt_of_lt_of_le (by positivity) h.1

theorem cut_tsupport_subset_Ioi (n : ℕ) :
    tsupport (Work.FTS.EllipticEst.cut n) ⊆ Set.Ioi (0 : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  intro z hz
  rw [tsupport] at hz
  have hle : z ∈ Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) :=
    closure_minimal (cut_support_subset_Icc n) isClosed_Icc hz
  exact lt_of_lt_of_le h1 hle.1

theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (cut_support_subset_Icc n)

/-! ## The angular weight `sigθ` -/

theorem sigθ_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ sigθ θ := by
  refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_) _
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem sigθ_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < sigθ θ := by
  refine Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) _
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem sigθ_eq_sig (θ : ℝ) : sigθ θ = Work.FTS.EllipticEst.AngSecond.sig θ := rfl

theorem wt_nonneg (z : ℝ) : 0 ≤ wt z := sq_nonneg _

end Work.FTS.EllipticEst.AeColl
