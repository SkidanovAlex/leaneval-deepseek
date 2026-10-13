import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `B2f a b ρ f` is the group of the (at most two) slots `k` with `5 ≤ k ≤ b` of the Leibniz
expansion; the coefficient `C(b,k)` is bounded by `7` *in total* over that group (`b ≤ 6`), and
each individual slot is priced by the hypothesis `hbound`.  Hence the group pairing is bounded
by `7` times the per-slot bound. -/
theorem T3RowGroup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ k : ℕ, k ≤ b → (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        ≤ 7 * (C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f a b ρ hso hm6 hab hleaf hbound
  have hα0 : 0 < α := hα.1
  have hb6 : b ≤ 6 := by omega
  -- the common bound of the hypothesis
  set X : ℝ := 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg zero_le_one (Work.Spaces.HkNorm_nonneg α 4 f))
      (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ## integrability of the individual leaf slots in `θ`
  have hleaf_int : ∀ k : ℕ, k ≤ b → ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ => ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
        * |Work.Spaces.mixed b a f z θ|) Work.Spaces.Iθ := by
    intro k hk z hz
    refine MeasureTheory.Integrable.mono' (hm6.1 z (le_of_lt hz)) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
        (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
          ((hso.mixed b a).continuousOn).abs) hz
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg
        ((Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h0 h1) (abs_nonneg _))
        (abs_nonneg _))]
      exact leaf_slice_le6 hα0 hleaf hab hz ⟨h0, h1⟩
  -- ## integrability in `z` of the `θ`-slice integral of a leaf slot
  have hleaf_intz : ∀ k : ℕ, k ≤ b →
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iz := by
    intro k hk
    refine MeasureTheory.Integrable.mono' hm6.2 ?_ ?_
    · exact (Work.Spaces.aesm_of_continuousOn_Qd _
        (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
          ((hso.mixed b a).continuousOn).abs)).integral_prod_right'
    · filter_upwards [ae_restrict_Iz_of_pos (fun z hz => hz)] with z hz
      have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
            * |Work.Spaces.mixed b a f z θ|) := by
        refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
        exact mul_nonneg (mul_nonneg
          ((Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h0 h1)
          (abs_nonneg _)) (abs_nonneg _)
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae hnn)]
      refine MeasureTheory.integral_mono_of_nonneg hnn (hm6.1 z (le_of_lt hz)) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
      exact leaf_slice_le6 hα0 hleaf hab hz ⟨h0, h1⟩
  -- ## the `θ`-expansion of the group
  have hthid : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        = ∑ k ∈ Finset.range (b + 1),
            (if 5 ≤ k then (b.choose k : ℝ) *
              (∫ θ in Work.Spaces.Iθ, ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) else 0) := by
    intro z hz
    simp only [B2f]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      by_cases h5 : 5 ≤ k
      · simp only [if_pos h5, MeasureTheory.integral_const_mul]
      · simp only [if_neg h5]; simp
    · intro k hk
      by_cases h5 : 5 ≤ k
      · simp only [if_pos h5]
        exact (hleaf_int k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) z hz).const_mul _
      · simp only [if_neg h5]
        exact MeasureTheory.integrableOn_zero
  -- ## the full double integral expands into the sum of the slot pairings
  have hzid : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
      = ∑ k ∈ Finset.range (b + 1),
          (if 5 ≤ k then (b.choose k : ℝ) *
            (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) else 0) := by
    have hae : (fun z => ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∑ k ∈ Finset.range (b + 1),
            (if 5 ≤ k then (b.choose k : ℝ) *
              (∫ θ in Work.Spaces.Iθ, ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) else 0)) := by
      filter_upwards [ae_restrict_Iz_of_pos (fun z hz => hz)] with z hz
      exact hthid z hz
    rw [MeasureTheory.integral_congr_ae hae]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      by_cases h5 : 5 ≤ k
      · simp only [if_pos h5, MeasureTheory.integral_const_mul]
      · simp only [if_neg h5]; simp
    · intro k hk
      by_cases h5 : 5 ≤ k
      · simp only [if_pos h5]
        exact (hleaf_intz k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul _
      · simp only [if_neg h5]
        exact MeasureTheory.integrableOn_zero
  -- ## the arithmetic: the coefficients of the group sum to at most `7`
  have hsumle7 : (∑ k ∈ Finset.range (b + 1),
      (if 5 ≤ k then (b.choose k : ℝ) else 0)) ≤ 7 := by
    have h1 : ∀ k : ℕ, (if 5 ≤ k then (b.choose k : ℝ) else 0)
        ≤ (if 5 ≤ k then ((6 : ℕ).choose k : ℝ) else 0) := by
      intro k
      by_cases h5 : 5 ≤ k
      · rw [if_pos h5, if_pos h5]
        exact_mod_cast Nat.choose_le_choose k hb6
      · rw [if_neg h5, if_neg h5]
    calc (∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ) else 0))
        ≤ ∑ k ∈ Finset.range (b + 1),
            (if 5 ≤ k then ((6 : ℕ).choose k : ℝ) else 0) :=
          Finset.sum_le_sum fun k _ => h1 k
      _ ≤ ∑ k ∈ Finset.range 7, (if 5 ≤ k then ((6 : ℕ).choose k : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro k hk
            simp only [Finset.mem_range] at hk ⊢
            omega
          · intro k _ _
            by_cases h5 : 5 ≤ k <;> simp [h5]
      _ ≤ 7 := by norm_num [Finset.sum_range_succ]
  have hterm : ∀ k ∈ Finset.range (b + 1),
      (if 5 ≤ k then (b.choose k : ℝ) *
          (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) else 0)
        ≤ (if 5 ≤ k then (b.choose k : ℝ) * X else 0) := by
    intro k hk
    by_cases h5 : 5 ≤ k
    · rw [if_pos h5, if_pos h5]
      exact mul_le_mul_of_nonneg_left
        (hbound k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) (by positivity)
    · rw [if_neg h5, if_neg h5]
  -- ## assembly
  rw [hzid]
  calc ∑ k ∈ Finset.range (b + 1),
        (if 5 ≤ k then (b.choose k : ℝ) *
          (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) else 0)
      ≤ ∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ) * X else 0) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ) else 0)) * X := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by by_cases h5 : 5 ≤ k <;> simp [h5]
    _ ≤ 7 * X := mul_le_mul_of_nonneg_right hsumle7 hXnn

end Work.FTS.StrongPersist.H6Pair6Aux
