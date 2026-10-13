import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From a pointwise bound to a bound on the top angular slot

The top angular slot of the level-`k` integrand of `A` is

  `Step.Tk α k A = ∫_z∈Iz ∫_θ∈Iθ (D_θ^k A · Wt α)²`

(`Work.FTS.EllipticEst.remov.Step.Tk`, with `D_θ^k A = mixed 0 k A`).  This file shows that a
*pointwise* domination of that single slot by `K` times the sum of the level-`(k-1)` integrands
of `A` and of a second function `Φ` integrates to

  `Tk α k A ≤ K * (HkSq α (k-1) A + HkSq α (k-1) Φ)`.

Two features of the statement deserve a comment.

* The pointwise hypothesis is assumed only on the **open** quadrant (`0 < z`, `0 < θ < π/2`)
  — the region where the divisions by `sin(2θ)` and by `z` are meaningful.  The domain of
  integration, however, is the closed quadrant `Iz × Iθ`.  The boundary `{z = 0} ∪ {θ = 0} ∪
  {θ = π/2}` is a null set, so it is irrelevant; the proof nevertheless treats it honestly:
  on the `θ`-boundary the hypothesis holds a.e. in `θ` (`θ ↦ θ ∈ Ioo 0 (π/2)` is true off the
  two-point null set `{0, π/2}`), which is exactly what `integral_mono_of_nonneg` consumes, and
  on the `z`-boundary `Wt α 0 θ = 0`, so the slot itself vanishes there.

* Nothing beyond `HkMem α (k-1)` of the two functions is assumed: those hypotheses give the
  integrability of the dominating function at both stages of the iteration, while the dominated
  slot is never assumed integrable (`integral_mono_of_nonneg` needs only nonnegativity of the
  smaller function).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.ATop

set_option autoImplicit false

/-- Off the two endpoints of `Iθ`, the angular variable lies in the open interval `(0,π/2)`
almost everywhere.  This is what allows the pointwise hypothesis (which is stated on the open
quadrant) to be used inside the integral over the closed interval. -/
private lemma ae_mem_Ioo_restrict_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo 0 (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_
    (Set.Finite.measure_zero (s := ({(0 : ℝ), Real.pi / 2} : Set ℝ)) (Set.toFinite _)
      MeasureTheory.volume)
  intro θ hθ
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo, not_imp, not_and, not_lt] at hθ
  obtain ⟨h1, h2⟩ := hθ
  rcases eq_or_lt_of_le h1.1 with h | h
  · simp [← h]
  · have : θ = Real.pi / 2 := le_antisymm h1.2 (h2 h)
    simp [this]

/-- The weight `Wt` vanishes on the axis `z = 0` (where `w 0 = 0` by Lean's convention for
division by zero). -/
private lemma Wt_zero_left (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt, Work.Spaces.w]

theorem Tk_le_of_pointwise {α : ℝ} {k : ℕ} {K : ℝ} {A Φ : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hmemA : Work.Spaces.HkMem α (k - 1) A)
    (hmemΦ : Work.Spaces.HkMem α (k - 1) Φ)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)) :
    Work.FTS.EllipticEst.remov.Step.Tk α k A
      ≤ K * (Work.Spaces.HkSq α (k - 1) A + Work.Spaces.HkSq α (k - 1) Φ) := by
  -- The `θ`-slice bound, valid on the whole half-line `Iz`.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (((hmemA.1 z hz).add (hmemΦ.1 z hz)).const_mul K) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- the boundary slice `z = 0`: the slot vanishes identically
      subst hz0
      refine Filter.Eventually.of_forall fun θ => ?_
      beta_reduce
      rw [Work.Spaces.mixed_zero_left]
      rw [Wt_zero_left, mul_zero, sq, mul_zero]
      exact mul_nonneg hK (add_nonneg (Work.Spaces.HkIntegrand_nonneg α (k - 1) A 0 θ)
        (Work.Spaces.HkIntegrand_nonneg α (k - 1) Φ 0 θ))
    · -- interior slices: the pointwise hypothesis holds a.e. in `θ`
      filter_upwards [ae_mem_Ioo_restrict_Iθ] with θ hθ
      rw [Work.Spaces.mixed_zero_left]
      exact hpt z θ hzpos hθ.1 hθ.2
  -- Integration in `z`.
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) ?_ ?_
    · -- the dominating double integral is honest
      refine MeasureTheory.Integrable.congr
        ((hmemA.2.const_mul K).add (hmemΦ.2.const_mul K)) ?_
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
          + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
        = ∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hmemA.1 z hz) (hmemΦ.1 z hz), mul_add]
    · change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall fun z hz => hinner z hz
  -- Evaluation of the dominating double integral.
  have hcong : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
          + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
      = K * (Work.Spaces.HkSq α (k - 1) A + Work.Spaces.HkSq α (k - 1) Φ) := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
        = ∫ z in Work.Spaces.Iz,
            (K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)) := by
      refine MeasureTheory.integral_congr_ae ?_
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
        = K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hmemA.1 z hz) (hmemΦ.1 z hz), mul_add]
    rw [h1, MeasureTheory.integral_add (hmemA.2.const_mul K) (hmemΦ.2.const_mul K),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      Work.Spaces.HkSq, Work.Spaces.HkSq]
    ring
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact le_trans hmain hcong.le

end Work.FTS.EllipticEst.remov.ATop
