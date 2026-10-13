import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowTheta
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowGroupParam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The level-six transport row with the coefficient `L₁₂(f)·f`.**

The coefficient `L₁₂(f)` is radial and smooth in `z`, so Leibniz expands the slot
`D_z^bD_θ^a(L₁₂(f)·f)` into `∑_{k≤b} C(b,k) (D_z^k L₁₂(f)) (D_z^{b-k}D_θ^a f)`.  The `D_z`-jets
of `L₁₂(f)` are uniformly bounded by `C₄|f|_{ℋ⁴}` (order `≤ 4`, `L12Sup4`) and by `C₆|f|_{ℋ⁶}`
(order `≤ 6`, `L12Sup6`); the `f`-slots with `k ≤ 4` are absorbed by the pointwise AM–GM bound
in `T3RowTheta`, while the at most two slots with `k ≥ 5` are bounded by `slotCS_z` and summed
in `T3RowGroup`.  The resulting bound is dominated by the stated
`α^{-3}(1+|f|_{ℋ⁴})^4(1+|f|²_{ℋ⁶})`. -/
theorem T3Row : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C4, hC4pos, hsup4⟩ := L12Sup4
  obtain ⟨C6, hC6pos, hsup6⟩ := L12Sup6
  obtain ⟨Ccs, hCcspos, hcs⟩ := slotCS_z
  have hgroup := T3RowGroupParam Ccs hCcspos.le
  have hCpos : 0 < (448 * C4 + 7 * C6 * Ccs) + 1 := by
    have h1 : 0 < 448 * C4 := mul_pos (by norm_num) hC4pos
    have h2 : 0 < 7 * C6 * Ccs := mul_pos (mul_pos (by norm_num) hC6pos) hCcspos
    linarith
  refine ⟨(448 * C4 + 7 * C6 * Ccs) + 1, hCpos, ?_⟩
  intro α hα f a b ρ hso hm6 hm7 hvanish haxis hl12 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the hypotheses of the two pieces
  have hs4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hsup4 α f hα0 hα1 hso hm6 hl12 k hk z hz
  have hs6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun k hk z hz => hsup6 α f hα0 hα1 hso hm6 hm7 hl12 k hk z hz
  have hcs' : ∀ k : ℕ, 5 ≤ k → k ≤ b →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
      ≤ Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f :=
    fun k hk5 hkb => hcs α f hα0 hα1 hso hm6 a b k ρ hleaf hkb hab (by omega)
  have hgr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
      ≤ 7 * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
    hgroup α hα f a b ρ hso hm6 hab hleaf hcs'
  -- ## the pointwise-in-`z` bound for the `θ`-integral
  have hth := T3RowTheta C4 C6 hC4pos hC6pos α hα f a b ρ hso hm6 hm7 hl12 hab hleaf hs4 hs6
  -- ## the group-`2` slice integral is integrable in `z`
  have hB2aesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (B2f_continuousOn hso hleaf)).integral_prod_right'
  have hB2int : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
      (volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' (hm6.2.const_mul 448) hB2aesm ?_
    filter_upwards [ae_restrict_Iz_of_pos (fun z hz => hz)] with z hz
    have hb2nn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ B2f a b ρ f z θ :=
      Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 =>
        Finset.sum_nonneg fun k _ => by
          by_cases h5 : 5 ≤ k
          · rw [if_pos h5]
            exact mul_nonneg (by positivity)
              (mul_nonneg (mul_nonneg
                ((Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2)
                (abs_nonneg _)) (abs_nonneg _))
          · rw [if_neg h5])
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae hb2nn)]
    have hstep : (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, 448 * Work.Spaces.HkIntegrand α 6 f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        hb2nn
        ((hm6.1 z (by simpa [Work.Spaces.Iz] using le_of_lt hz)).const_mul 448)
        (Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 =>
          group_sum_le hα0 hleaf hab (fun k => 5 ≤ k) hz ⟨h1, h2⟩))
    rwa [MeasureTheory.integral_const_mul] at hstep
  -- ## the `z`-integration
  have hDom : Integrable (fun z => (C4 * Work.Spaces.HkNorm α 4 f)
      * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
      + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ))
      (volume.restrict Work.Spaces.Iz) :=
    ((hm6.2.const_mul 448).const_mul _).add (hB2int.const_mul _)
  have hmain : |Work.FTS.TransportS.slotPairing ρ a b
      (fun z θ => Work.Construction.L12 f z * f z θ) f|
      ≤ (448 * C4 + 7 * C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
    rw [Work.FTS.TransportS.slotPairing]
    refine le_trans abs_integral_le_integral_abs ?_
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hDom hth) ?_
    have h1 : (∫ z in Work.Spaces.Iz, (C4 * Work.Spaces.HkNorm α 4 f)
          * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
          + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ))
        = (C4 * Work.Spaces.HkNorm α 4 f)
            * (448 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 6 f z θ))
          + (C6 * Work.Spaces.HkNorm α 6 f)
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
      rw [MeasureTheory.integral_add ((hm6.2.const_mul 448).const_mul _) (hB2int.const_mul _)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    rw [h1]
    have hS : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ) = Work.Spaces.HkSq α 6 f := rfl
    rw [hS]
    have h2 : (C6 * Work.Spaces.HkNorm α 6 f)
        * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        ≤ (C6 * Work.Spaces.HkNorm α 6 f)
          * (7 * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) :=
      mul_le_mul_of_nonneg_left hgr (mul_nonneg hC6pos.le (Real.sqrt_nonneg _))
    have hN6sq : (Work.Spaces.HkNorm α 6 f) ^ 2 = Work.Spaces.HkSq α 6 f :=
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)
    have h3 : (C6 * Work.Spaces.HkNorm α 6 f)
        * (7 * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))
        = 7 * C6 * Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
      rw [← hN6sq]; ring
    calc (C4 * Work.Spaces.HkNorm α 4 f) * (448 * Work.Spaces.HkSq α 6 f)
          + (C6 * Work.Spaces.HkNorm α 6 f)
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        ≤ (C4 * Work.Spaces.HkNorm α 4 f) * (448 * Work.Spaces.HkSq α 6 f)
          + (C6 * Work.Spaces.HkNorm α 6 f)
            * (7 * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) :=
          add_le_add le_rfl h2
      _ = (448 * C4 + 7 * C6 * Ccs)
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by rw [h3]; ring
  -- ## the final arithmetic
  refine le_trans hmain ?_
  have hXn : Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f := rfl
  rw [hXn]
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Real.sqrt_nonneg _
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hα0.le, show α ^ (3 : ℝ) = α ^ 3 from Real.rpow_natCast α 3,
      one_le_inv₀ (by positivity : (0 : ℝ) < α ^ 3)]
    exact pow_le_one₀ hα0.le hα1
  have key : Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
      ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : Work.Spaces.HkNorm α 4 f ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by
      have h2 : Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := by linarith
      have h3 : (1 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 4 f := by linarith
      calc Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := h2
        _ = (1 + Work.Spaces.HkNorm α 4 f) ^ 1 := by ring
        _ ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    calc Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul h1 h4 hSnn (by positivity : (0 : ℝ) ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4)
      _ ≤ (α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          calc (1 + Work.Spaces.HkNorm α 4 f) ^ 4
              = 1 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by ring
            _ ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
                mul_le_mul_of_nonneg_right hα3 (by positivity : (0 : ℝ) ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4)
      _ = α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  calc (448 * C4 + 7 * C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
      ≤ (448 * C4 + 7 * C6 * Ccs) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left key (by
          have h1 : 0 < 448 * C4 := mul_pos (by norm_num) hC4pos
          have h2 : 0 < 7 * C6 * Ccs := mul_pos (mul_pos (by norm_num) hC6pos) hCcspos
          linarith)
    _ ≤ ((448 * C4 + 7 * C6 * Ccs) + 1) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
        linarith
    _ = ((448 * C4 + 7 * C6 * Ccs) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
