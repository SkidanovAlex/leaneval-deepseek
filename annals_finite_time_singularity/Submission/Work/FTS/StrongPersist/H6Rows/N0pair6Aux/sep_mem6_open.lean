import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowGroupParam =====
section

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

/-- Parametric form of `T3RowGroup`: if every one of the (at most two) slots `5 ≤ k ≤ b` of the
level-six Leibniz expansion is priced by the *given* constant `C ≥ 0`, then the group
`B2f a b ρ f` is priced by `7·C`, because the coefficients `C(b,k)` sum to at most
`C(6,5) + C(6,6) = 7` over the group. -/
theorem T3RowGroupParam (C : ℝ) (hC : 0 ≤ C) :
    ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ k : ℕ, 5 ≤ k → k ≤ b → (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ)
        ≤ 7 * (C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by
  intro α hα f a b ρ hso hm6 hab hleaf hbound
  have hα0 : 0 < α := hα.1
  have hb6 : b ≤ 6 := by omega
  -- the common bound of the hypothesis
  set X : ℝ := C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg hC (Work.Spaces.HkNorm_nonneg α 4 f))
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
        (hbound k h5 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) (by positivity)
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
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.sep_mem6_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The angular `×` radial separate product at level six, with a continuity hypothesis in
place of `SmoothOpen`.**

This is `Work.FTS.StrongPersist.H6Pair6Aux.sep_mem6_local` with its `SmoothOpen`-hypothesis
(which is used only to supply the continuity of the `ℋ⁶`-integrand) replaced by that
continuity statement itself: the radial factor of the `N₀`-row is `z ↦ L₁₂(f)(z)`, which at
the bare-`f` interface is only `C⁶` on `(0,∞)` (`EllipticEst.UopHk.contDiffOn_L12_k`), never
`C^∞`, while the continuity hypothesis below is available (from `ContDiffOn ℝ 6` of the two
one-variable factors).

ROUTE: verbatim the tail of `sep_mem6_local`, using `hcont` where that proof uses
`hsm.continuousOn_HkIntegrand α 6`; `L6Aux.HkIntegrandSepLeGen`, `integrableOn_sin_two_rpow`
(of `SepMem6Local`), `RMul6.Rint6` and `Work.FTS.LocData.HkMem_of_majorant`. -/
theorem sep_mem6_open {α κ B0 B1 : ℝ} {a : ℝ → ℝ} {ρ : ℝ → ℝ}
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hκ : -1 < 2 * κ - Work.Spaces.gam α)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      ((Work.Spaces.dthU^[i]) a θ) ^ 2 ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ))
    (hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * ρ z) p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hρint : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j ρ z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α 6 (fun z θ => a θ * ρ z) := by
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hK1
  set K2 : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) with hK2
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.H6Pair6Aux.integrableOn_sin_two_rpow
      (by rw [Work.Spaces.eta]; norm_num)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.H6Pair6Aux.integrableOn_sin_two_rpow hκ
  have hintR : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.RMul6.Rint6 ρ) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.range 7) (fun j hj => by
      refine (hρint j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).congr ?_
      refine Filter.Eventually.of_forall fun z => ?_
      ring)
  set Cc : ℝ := 7 * B1 + B0 ^ 2 + 1 with hCc
  have hCcnn : 0 ≤ Cc := by rw [hCc]; positivity
  have hBrnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact add_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg hs0 _)
  refine Work.FTS.LocData.HkMem_of_majorant α 6 (f := fun z θ => a θ * ρ z)
    (M := fun z θ => Cc *
      ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
      * Work.FTS.StrongPersist.RMul6.Rint6 ρ z)
    hcont ?_ ?_ ?_
  · intro z hz
    have h3 := ((h1.add h2).const_mul Cc).mul_const
      (Work.FTS.StrongPersist.RMul6.Rint6 ρ z)
    refine h3.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Pi.add_apply]
  · have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Cc *
        ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
        * Work.FTS.StrongPersist.RMul6.Rint6 ρ z)
        = fun z => (Cc * (K1 + K2)) * Work.FTS.StrongPersist.RMul6.Rint6 ρ z := by
      funext z
      have hEq : (∫ θ in Work.Spaces.Iθ, Cc *
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)))
          = Cc * (K1 + K2) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2, hK1, hK2]
      rw [show (fun θ : ℝ => Cc * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
            * Work.FTS.StrongPersist.RMul6.Rint6 ρ z)
          = (fun θ : ℝ => (Cc * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)))
            * Work.FTS.StrongPersist.RMul6.Rint6 ρ z) from rfl]
      rw [MeasureTheory.integral_mul_const, hEq]
    rw [hfun]
    exact hintR.const_mul _
  · intro z hz θ hθ
    have hRnn : 0 ≤ Work.FTS.StrongPersist.RMul6.Rint6 ρ z :=
      Work.FTS.StrongPersist.RMul6.Rint6_nonneg ρ z
    have htriv : 0 ≤ Cc * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
        * Work.FTS.StrongPersist.RMul6.Rint6 ρ z :=
      mul_nonneg (mul_nonneg hCcnn (hBrnn θ hθ)) hRnn
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
      rw [← hz0] at htriv
      exact htriv
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs]
        exact htriv
      · have hs0 : 0 ≤ Real.sin (2 * θ) :=
          Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
        have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hs)
        have hsep := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
          (C := a) (B := ρ) (z := z) (θ := θ) hθ
        have hrad : (∑ q ∈ Finset.range (6 + 1),
              (Work.Spaces.DzIter q (fun z' _ => ρ z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
            = Work.FTS.StrongPersist.RMul6.Rint6 ρ z := by
          rw [Work.FTS.StrongPersist.RMul6.Rint6]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Work.FTS.StrongPersist.H6Pair6Aux.DzIter_z_only]
        rw [hrad] at hsep
        have ha2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha0 θ hθ) 2
          rwa [sq_abs] at h
        have hang : (a θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + ∑ i ∈ Finset.range (6 + 1),
                  (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
            ≤ Cc * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) := by
          have hterm : ∀ i ∈ Finset.range (6 + 1),
              (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
              ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
            intro i hi
            have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            by_cases h1i : 1 ≤ i
            · rw [if_pos h1i]
              have hb := ha1 i h1i hi6 θ hθ
              have hrw : (Real.sin (2 * θ)) ^ (2 * κ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
                rw [← Real.rpow_add hspos (2 * κ) (-(Work.Spaces.gam α)),
                  show (2 : ℝ) * κ + -(Work.Spaces.gam α)
                    = 2 * κ - Work.Spaces.gam α from by ring]
              calc ((Work.Spaces.dthU^[i]) a θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ)
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
                    mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hs0 _)
                _ = B1 * ((Real.sin (2 * θ)) ^ (2 * κ)
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
                _ = B1 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by rw [hrw]
            · rw [if_neg h1i]
              exact mul_nonneg hB1 (Real.rpow_nonneg hs0 _)
          have hsum : (∑ i ∈ Finset.range (6 + 1),
                (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
              ≤ 7 * (B1 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) := by
            calc (∑ i ∈ Finset.range (6 + 1),
                  (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
                ≤ ∑ _i ∈ Finset.range (6 + 1),
                    (B1 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) :=
                  Finset.sum_le_sum hterm
              _ = 7 * (B1 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
          have hA : (a θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              ≤ B0 ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right ha2 (Real.rpow_nonneg hs0 _)
          have hK2nn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) :=
            Real.rpow_nonneg hs0 _
          have hK1nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
          have hB0s : B0 ^ 2 ≤ Cc := by rw [hCc]; nlinarith [hB1]
          have hB1s : 7 * B1 ≤ Cc := by rw [hCc]; nlinarith [sq_nonneg B0]
          have hCcx := mul_le_mul_of_nonneg_right hB0s hK1nn
          have hCcy := mul_le_mul_of_nonneg_right hB1s hK2nn
          have hsum7 : (∑ i ∈ Finset.range (6 + 1),
                (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
              ≤ (7 * B1) * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) :=
            hsum.trans (le_of_eq (by ring))
          nlinarith [hA, hCcx, hsum7, hCcy, hK1nn, hK2nn]
        calc Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * ρ z) z θ
            ≤ ((a θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ∑ i ∈ Finset.range (6 + 1),
                    (if 1 ≤ i then ((Work.Spaces.dthU^[i]) a θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
              * Work.FTS.StrongPersist.RMul6.Rint6 ρ z := hsep
          _ ≤ Cc * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
              * Work.FTS.StrongPersist.RMul6.Rint6 ρ z :=
              mul_le_mul_of_nonneg_right hang hRnn

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
