/-
# `Work.FTS.StrongPersist.H6Aux.RadialAux` — the two elementary radial inputs of `Corr_HkSq6`

Insurance module for the radial half of `Corr_HkSq6`: the two *elementary* inputs of the bound

`∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f`

are proved here under `Alt_`-prefixed names (so that they cannot clash with the sibling module
`H6Aux.SlotSum_radA_le`, which develops the same bound directly):

* `Alt_C0_sq_le_HkSq6` — `C₀f² ≤ C·HkSq α 6 f`, from `L3Aux.Transport_L12_zero_le`
  (`|C₀f| ≤ C·HkNorm α 4 f`, no smoothness) and the monotonicity `HkSq α 4 f ≤ HkSq α 6 f`;
* `Alt_slotSum_ampB_div_le` — `∫_z Σ_{q≤6}(D_z^q(ampB α/c α) z·w z)² ≤ C`, uniformly in `α ∈ (0,1]`,
  from `L6Aux.bcoefRad_zop_bound6` (`|Zop^j bcoefRad·w| ≤ K/(1+z)` for `j ≤ 6`) and
  `L6Aux.radSnorm6_int_le` (`∫ Σ_{q<7}(Zop^q bcoefRad·w)² ≤ 14K²`), the factor `c(α)⁻¹ ∈ [1,10]`
  being absorbed in `C`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L6Aux.BcoefMem6
import Submission.Work.FTS.StrongPersist.L6Aux.radSnorm6_int_le
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The projector constant at level six.**  `C₀f = L₁₂(Transport f)(0)` is bounded by
`HkNorm α 4 f` (`L3Aux.Transport_L12_zero_le`, which needs only `HkMem α 4 f`), hence by
`HkSq α 6 f` for `H6Adm` data with order-seven honesty. -/
theorem Alt_C0_sq_le_HkSq6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₀, hC₀, hb⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have habs : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0|
      ≤ C₀ * Work.Spaces.HkNorm α 4 f := hb α f hα hα1 hmem4
  have hmono : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 6 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6
  have h4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      = |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ^ 2 := by rw [sq_abs]
    _ ≤ (C₀ * Work.Spaces.HkNorm α 4 f) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C₀ ^ 2 * Work.Spaces.HkSq α 4 f := by
        rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt h4]
    _ ≤ C₀ ^ 2 * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- **The radial block of the projector correction.**  `ampB α z = 2z²/(1+z)³ = bcoefRad z`, so
`D_z^q(ampB α/c α) = c(α)⁻¹·Zop^q bcoefRad`; the `j ≤ 6` weighted bound of `L6Aux.bcoefRad_zop_bound6`
and the block integral of `L6Aux.radSnorm6_int_le` therefore give a constant bound uniform in
`α ∈ (0,1]`. -/
theorem Alt_slotSum_ampB_div_le : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C := by
  obtain ⟨K, hKpos, hKbd⟩ := Work.FTS.StrongPersist.L6Aux.bcoefRad_zop_bound6
  refine ⟨140000 * K ^ 2, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hα hα1
  have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  -- the pointwise bound in the `Zop`-normalisation
  have hrb : ∀ j ≤ 6, ∀ z ∈ Set.Ici (0 : ℝ),
      |Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z|
        ≤ (10 * K) / (1 + z) := by
    intro j hj z hz
    have h1 := hKbd j hj z hz
    have h2 : 0 < 1 + z := by
      have : (0 : ℝ) ≤ z := hz
      linarith
    refine le_trans h1 (div_le_div_of_nonneg_right (by linarith) h2.le)
  obtain ⟨hInt, hBnd⟩ :=
    Work.FTS.StrongPersist.L6Aux.radSnorm6_int_le (K := 10 * K) (by positivity) hrb
  -- the two functions agree a.e. on `Iz`, with the extra factor `c(α)^{-2}`
  have hae : (fun z : ℝ => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => ((Work.Spaces.c α)⁻¹) ^ 2 *
          (∑ q ∈ Finset.range 7,
            (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
              * Work.Spaces.w z) ^ 2)) := by
    rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    have hpt : ∀ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
            Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = ((Work.Spaces.c α)⁻¹) ^ 2
          * ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
              * Work.Spaces.w z) ^ 2) := by
      intro q _
      have hAB : Work.FTS.CoercivityFix.Transfer.ampB α
          = Work.FTS.StrongPersist.L3Aux.bcoefRad := rfl
      have hfun : (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
          = fun z' => (Work.Spaces.c α)⁻¹ * Work.FTS.StrongPersist.L3Aux.bcoefRad z' := by
        funext z'
        rw [hAB, div_eq_mul_inv, mul_comm]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter, hfun,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
      ring
    change (∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z'
          / Work.Spaces.c α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ((Work.Spaces.c α)⁻¹) ^ 2 *
        (∑ q ∈ Finset.range 7,
          (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
            * Work.Spaces.w z) ^ 2)
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  refine ⟨(hInt.const_mul (((Work.Spaces.c α)⁻¹) ^ 2)).congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
  have hnn : 0 ≤ ∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
      (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z) ^ 2 :=
    integral_nonneg fun z => Finset.sum_nonneg fun q _ => sq_nonneg _
  have h1 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h0 : 0 ≤ (Work.Spaces.c α)⁻¹ := le_of_lt (inv_pos.mpr hcpos)
    nlinarith
  calc ((Work.Spaces.c α)⁻¹) ^ 2
        * (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
          (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
            * Work.Spaces.w z) ^ 2)
      ≤ 100 * (14 * (10 * K) ^ 2) := mul_le_mul h1 hBnd hnn (by norm_num)
    _ = 140000 * K ^ 2 := by ring

end Work.FTS.StrongPersist.H6Aux
