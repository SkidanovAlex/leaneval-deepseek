import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

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

/-- `B1f` (the group of slots with at most four `D_z`-derivatives on the radial coefficient) is
continuous on the open quadrant.  Same proof as `B2f_continuousOn`. -/
private theorem B1f_continuousOn {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => B1f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [B1f]
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases h4 : k ≤ 4
  · simp only [if_pos h4]
    exact continuousOn_const.mul
      (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
        ((hso.mixed b a).continuousOn).abs)
  · simp only [if_neg h4]; exact continuousOn_const

/-- **The level-six transport row with the coefficient `L₁₂(f)·f`, pointwise in `z`.**

The radial coefficient `L₁₂(f)` is `C^6` on `(0,∞)`; its `D_z`-jets are bounded by
`C₄|f|_{ℋ⁴}` (order `≤ 4`) and `C₆|f|_{ℋ⁶}` (order `≤ 6`), supplied here as hypotheses.
Leibniz expands the slot `D_z^bD_θ^a(L₁₂(f)·f)`; the `k ≤ 4` slots are absorbed into
`448·∫_θ HkIntegrand α 6 f` by the pointwise AM–GM bound `leaf_slice_le6`/`group_sum_le`,
and the `k ≥ 5` slots are left as the explicit remainder `∫_θ B2f a b ρ f`. -/
theorem T3RowTheta (C4 C6 : ℝ) (hC4 : 0 < C4) (hC6 : 0 < C6) :
    ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          ≤ C4 * Work.Spaces.HkNorm α 4 f) →
      (∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          ≤ C6 * Work.Spaces.HkNorm α 6 f) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |∫ θ in Work.Spaces.Iθ, ρ z θ
            * Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * f z θ) z θ
            * Work.Spaces.mixed b a f z θ|
          ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
  intro α hα f a b ρ hso hm6 hm7 hl12 hab hleaf hs4 hs6
  have hα0 : 0 < α := hα.1
  -- ## the radial coefficient is `C^6` on `(0,∞)`
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  -- ## the uniform bounds on the derivative tower of `L₁₂(f)`
  have hsup : ∀ k : ℕ, k ≤ b → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
            else C6 * Work.Spaces.HkNorm α 6 f) := by
    intro k hk z hz
    by_cases h4 : k ≤ 4
    · rw [if_pos h4]; exact hs4 k h4 z hz
    · rw [if_neg h4]; exact hs6 k (by omega) z hz
  -- ## continuity of the slot factors on the open quadrant
  have hcontPsi : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed (b - k) a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun k => (hso.mixed (b - k) a).continuousOn
  have hcontY : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hso.mixed b a).continuousOn
  have hcontρ : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_leaf hleaf
  have hcontB1 : ContinuousOn (fun p : ℝ × ℝ => B1f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    B1f_continuousOn hso hleaf
  have hcontB2 : ContinuousOn (fun p : ℝ × ℝ => B2f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    B2f_continuousOn hso hleaf
  -- ## the defining equations of the two groups
  have hB1def : ∀ z θ : ℝ, B1f a b ρ f z θ = ∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then
      (b.choose k : ℝ)
      * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
      else 0) := fun z θ => rfl
  have hB2def : ∀ z θ : ℝ, B2f a b ρ f z θ = ∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then
      (b.choose k : ℝ)
      * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
      else 0) := fun z θ => rfl
  -- ## slice integrability of the two groups
  have hB1_slice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => B1f a b ρ f z θ) Work.Spaces.Iθ := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    refine MeasureTheory.Integrable.mono' ((hm6.1 z hzI).const_mul 448) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontB1 hz
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      have hterm : ∀ k ∈ Finset.range (b + 1),
          0 ≤ (if k ≤ 4 then (b.choose k : ℝ)
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
              else 0) := by
        intro k _
        by_cases h4 : k ≤ 4
        · rw [if_pos h4]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h4]
      rw [hB1def, Real.norm_eq_abs, Finset.abs_sum_of_nonneg hterm]
      exact group_sum_le hα0 hleaf hab (fun k => k ≤ 4) hz ⟨h1, h2⟩
  have hB2_slice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => B2f a b ρ f z θ) Work.Spaces.Iθ := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    refine MeasureTheory.Integrable.mono' ((hm6.1 z hzI).const_mul 448) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontB2 hz
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      have hterm : ∀ k ∈ Finset.range (b + 1),
          0 ≤ (if 5 ≤ k then (b.choose k : ℝ)
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
              else 0) := by
        intro k _
        by_cases h5 : 5 ≤ k
        · rw [if_pos h5]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h5]
      rw [hB2def, Real.norm_eq_abs, Finset.abs_sum_of_nonneg hterm]
      exact group_sum_le hα0 hleaf hab (fun k => 5 ≤ k) hz ⟨h1, h2⟩
  -- ## the pointwise (a.e. in `z`) bound for the `θ`-integral
  filter_upwards [ae_restrict_Iz_of_pos (fun z hz => hz)] with z hz
  have hzI : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
        ≤ (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
    -- Leibniz
    have hleibθ : Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.mixed (b - k) a f z θ) :=
      leibniz_radial_mul hXsm hso b a (by omega) z θ hz h1 h2
    have hXp : |Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
        ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Spaces.mixed (b - k) a f z θ| := by
      rw [hleibθ]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun k _ => ?_
      have hc : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      exact le_of_eq (by ring)
    have hYnn : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
    have hstep1 : ρ z θ * |Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
      calc ρ z θ * |Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ ρ z θ * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.mixed (b - k) a f z θ|) * |Work.Spaces.mixed b a f z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXp hρ0) hYnn
        _ = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
    have hstep2 : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|))
        ≤ (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
      have hsplit : ∀ k ∈ Finset.range (b + 1),
          (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|)
          ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0) := by
        intro k hk
        have hk' : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hkK := hsup k hk' z hz
        have hψ : 0 ≤ ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
        have hc : 0 ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
        by_cases h4 : k ≤ 4
        · have h5 : ¬ 5 ≤ k := by omega
          rw [if_pos h4, if_neg h5, mul_zero, add_zero]
          rw [if_pos h4] at hkK
          calc (b.choose k : ℝ)
                * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|)
              ≤ (b.choose k : ℝ) * (C4 * Work.Spaces.HkNorm α 4 f)
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hc) hψ
            _ = (C4 * Work.Spaces.HkNorm α 4 f)
                * ((b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|)) := by ring
        · have h5 : 5 ≤ k := by omega
          rw [if_neg h4, mul_zero, zero_add, if_pos h5]
          rw [if_neg h4] at hkK
          calc (b.choose k : ℝ)
                * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|)
              ≤ (b.choose k : ℝ) * (C6 * Work.Spaces.HkNorm α 6 f)
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hc) hψ
            _ = (C6 * Work.Spaces.HkNorm α 6 f)
                * ((b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|)) := by ring
      calc (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|))
          ≤ ∑ k ∈ Finset.range (b + 1), ((C4 * Work.Spaces.HkNorm α 4 f)
              * (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)) :=
            Finset.sum_le_sum hsplit
        _ = (C4 * Work.Spaces.HkNorm α 4 f)
              * (∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0))
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
            + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
            rw [hB1def, hB2def]
    have habs : |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
          * Work.Spaces.mixed b a f z θ|
        = ρ z θ * |Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact le_trans (le_of_eq habs) (le_trans hstep1 hstep2)
  -- ## integrate the `θ`-bound
  have hDslice : IntegrableOn (fun θ : ℝ => (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
      + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) Work.Spaces.Iθ :=
    ((hB1_slice z hz).const_mul _).add ((hB2_slice z hz).const_mul _)
  have h2 : (∫ θ in Work.Spaces.Iθ, |ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hDslice hpt
  have h3 : (∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ))
      = (C4 * Work.Spaces.HkNorm α 4 f) * (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
        + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
    rw [MeasureTheory.integral_add ((hB1_slice z hz).const_mul _)
      ((hB2_slice z hz).const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have h4 : (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
      ≤ 448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ((hm6.1 z hzI).const_mul 448) ?_
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      rw [hB1def]
      exact Finset.sum_nonneg fun k _ => by
        by_cases h4 : k ≤ 4
        · rw [if_pos h4]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h4]
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      rw [hB1def]
      exact group_sum_le hα0 hleaf hab (fun k => k ≤ 4) hz ⟨h1, h2⟩
  calc |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
          * Work.Spaces.mixed b a f z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) := h2
    _ = (C4 * Work.Spaces.HkNorm α 4 f) * (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
          + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := h3
    _ ≤ (C4 * Work.Spaces.HkNorm α 4 f)
          * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
          + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left h4
          (mul_nonneg hC4.le (Work.Spaces.HkNorm_nonneg α 4 f))

end Work.FTS.StrongPersist.H6Pair6Aux
