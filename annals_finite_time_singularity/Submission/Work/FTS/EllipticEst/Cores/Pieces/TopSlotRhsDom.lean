import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux.AtopClean
import Submission.Work.FTS.EllipticEst.Mine.SlicePoincare
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.lobAux.HkSqDzTransfer
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux.lowSlots
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The lower angular slots of `HkIntegrand α (k-1) A` dominate the `D_θ`-slots; in
particular the sum over `r ∈ Icc 1 (k-1)` of `(D_θ^r A · Wt)²` is at most the whole integrand. -/
theorem sum_slots_le_HkIntegrand (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (A : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ r ∈ Finset.Icc 1 (k - 1),
        (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkIntegrand α (k - 1) A z θ := by
  -- `Msum` splits into rows in `i`, and the `j = 0` term of the row `i` is the slot at `i`.
  have hrow : ∀ i ∈ Finset.Icc 1 (k - 1),
      (Work.Spaces.DthIter i A z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ ∑ j ∈ Finset.range (k - 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k - 1 then
              (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    intro i hi
    obtain ⟨hi1, hile⟩ := Finset.mem_Icc.mp hi
    have h0mem : 0 ∈ Finset.range (k - 1 + 1) := Finset.mem_range.mpr (by omega)
    have hterm : (if 1 ≤ i ∧ i + 0 ≤ k - 1 then
          (Work.Spaces.mixed 0 i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        = (Work.Spaces.DthIter i A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [if_pos ⟨hi1, by omega⟩, Work.Spaces.mixed_zero_left]
    calc (Work.Spaces.DthIter i A z θ * Work.Spaces.Wt α z θ) ^ 2
        = (if 1 ≤ i ∧ i + 0 ≤ k - 1 then
              (Work.Spaces.mixed 0 i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := hterm.symm
      _ ≤ ∑ j ∈ Finset.range (k - 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k - 1 then
              (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
          Finset.single_le_sum (f := fun j => if 1 ≤ i ∧ i + j ≤ k - 1 then
              (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            (fun j _ => by
              by_cases h : (1 ≤ i ∧ i + j ≤ k - 1)
              · rw [if_pos h]; exact sq_nonneg _
              · rw [if_neg h]) h0mem
  have hMsum : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) A z θ
      = ∑ i ∈ Finset.range ((k - 1) + 1),
          ∑ j ∈ Finset.range ((k - 1) + 1),
            (if 1 ≤ i ∧ i + j ≤ k - 1 then
              (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  have hsub : Finset.Icc 1 (k - 1) ⊆ Finset.range ((k - 1) + 1) := by
    intro i hi
    obtain ⟨hi1, hile⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_range.mpr (by omega)
  calc (∑ r ∈ Finset.Icc 1 (k - 1),
        (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∑ i ∈ Finset.range ((k - 1) + 1),
          (∑ j ∈ Finset.range (k - 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k - 1 then
              (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
        -- pad the index set from `Icc 1 (k-1)` to `range (k+1)`
        have h1 : (∑ r ∈ Finset.Icc 1 (k - 1),
              (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ ∑ i ∈ Finset.Icc 1 (k - 1),
                (∑ j ∈ Finset.range (k - 1 + 1),
                  (if 1 ≤ i ∧ i + j ≤ k - 1 then
                    (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum hrow
        have h2 : (∑ i ∈ Finset.Icc 1 (k - 1),
                (∑ j ∈ Finset.range (k - 1 + 1),
                  (if 1 ≤ i ∧ i + j ≤ k - 1 then
                    (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)))
            ≤ ∑ i ∈ Finset.range ((k - 1) + 1),
                (∑ j ∈ Finset.range (k - 1 + 1),
                  (if 1 ≤ i ∧ i + j ≤ k - 1 then
                    (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => Finset.sum_nonneg fun j _ => by
              by_cases h : (1 ≤ i ∧ i + j ≤ k - 1)
              · rw [if_pos h]; exact sq_nonneg _
              · rw [if_neg h])
        exact le_trans h1 h2
    _ = Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) A z θ := by
        rw [hMsum]
    _ ≤ Work.Spaces.HkIntegrand α (k - 1) A z θ := by
        rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq]
        exact le_add_of_nonneg_left
          (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Pointwise bound for the source slot of `F` (a single plain high slot). -/
theorem srcF_pointwise (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α k F z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand k hk
  exact ⟨C0, hC0pos, fun α F hα hsm => hC0 α F k le_rfl hα hsm⟩

/-- Pointwise bound for the source slot of `A = z²∂_z²Ψ`. -/
theorem srcA_pointwise (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (A : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry A)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.remov.selfdth.dthChain_core k (by omega)
  refine ⟨C0, hC0pos, fun α A hα hsm z hz => ?_⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
  · rw [← h0]
    refine Eventually.of_forall (fun θ => ?_)
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by norm_num [Work.Spaces.w]
    rw [hw0, zero_mul]
    exact mul_nonneg hC0pos.le
      (add_nonneg (Work.Spaces.HkIntegrand_nonneg α (k - 1) A 0 θ) (sq_nonneg _))
  · refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hcd : ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry A) (z, θ) := fun n =>
      (hsm n).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hθ⟩)
    have hchain := hC0 A z θ hθ hcd
    have hsplit : (∑ r ∈ Finset.Icc 1 k,
          (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (∑ r ∈ Finset.Icc 1 (k - 1),
            (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
          + (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      have hpt : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hpt, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
    have hstep : (Real.sin (2 * θ) ^ k * Work.Spaces.pthIter k A z θ) ^ 2
          * (Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) :=
      (Work.FTS.EllipticEst.remov.selfdth.slot_sq_eq_Wt_sq k α z θ A hs).symm
    calc (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = (Real.sin (2 * θ) ^ k * Work.Spaces.pthIter k A z θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 := hstep.symm
      _ ≤ (C0 * ∑ r ∈ Finset.Icc 1 k, (Work.Spaces.DthIter r A z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hchain (sq_nonneg _)
      _ = C0 * (∑ r ∈ Finset.Icc 1 k,
            (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          rw [show (C0 * ∑ r ∈ Finset.Icc 1 k, (Work.Spaces.DthIter r A z θ) ^ 2)
                * (Work.Spaces.Wt α z θ) ^ 2
              = C0 * ((∑ r ∈ Finset.Icc 1 k, (Work.Spaces.DthIter r A z θ) ^ 2)
                * (Work.Spaces.Wt α z θ) ^ 2) from by ring,
            Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = C0 * ((∑ r ∈ Finset.Icc 1 (k - 1),
            (Work.Spaces.DthIter r A z θ * Work.Spaces.Wt α z θ) ^ 2)
          + (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2) := by rw [hsplit]
      _ ≤ C0 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
          + (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (sum_slots_le_HkIntegrand k (by omega) α A z θ) le_rfl) hC0pos.le

/-! ## Measurability of the top angular slot, and a general integration helper -/

/-- The weight `Wt α` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0_local (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hprod : ContinuousOn ((fun p : ℝ × ℝ => Work.Spaces.w p.1)
      * fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      Work.FTS.EllipticEst.Q0 := hw.mul hsin
  have hfun : ((fun p : ℝ × ℝ => Work.Spaces.w p.1)
      * fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      = fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2 := by funext p; rfl
  rwa [hfun] at hprod

/-- The mixed slot `D_θ^k f · Wt` is a.e. strongly measurable, for the product measure and for
every angular slice, whenever `f` is `C^∞` on the open quadrant. -/
theorem aesm_mixed_slot_local {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((hf.mixed 0 k).continuousOn).mul (continuousOn_Wt_Q0_local α)
  refine ⟨Work.Spaces.aesm_of_continuousOn_Qd _ hcont, fun z hz => ?_⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← hz0]
      simp [Work.Spaces.Wt, Work.Spaces.w]
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos

/-- A single mixed slot of the `ℋ^k`-integrand is honest in both variables, given `HkMem`. -/
theorem integrableOn_TkSlot {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) (hk : 1 ≤ k) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2)
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := by
  have haesm := aesm_mixed_slot_local (α := α) (k := k) hf
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := haesm.1.pow 2
  have haesm2s : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz => (haesm.2 z hz).pow 2
  have hslot_le : ∀ z θ, (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ k 0 hk (by omega)
  constructor
  · intro z hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) (haesm2s z hz) ?_
    exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hslot_le z θ
  · have hout : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm2.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hmem.2 hout ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    have hinner : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
        (Filter.Eventually.of_forall fun θ => hslot_le z θ)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    exact hinner

/-- **A general integration helper.**  If a pointwise (a.e. in `θ`, for every `z ∈ Iz`) bound by
a majorant `G` holds, and `G` is honest in both variables, then `∫_z ∫_θ F ≤ ∫_z ∫_θ G`.

`F` is never assumed integrable: in the non-integrable case Lean's totalised integral is `0`
and both sides are nonnegative. -/
theorem int_le_of_majorant {G F' : ℝ → ℝ → ℝ}
    (hGslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => G z θ)
      Work.Spaces.Iθ)
    (hGz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, G z θ)
      Work.Spaces.Iz)
    (hGnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ, G z θ)
    (hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      F' z θ ≤ G z θ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F' z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G z θ := by
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, F' z θ) ≤ ∫ θ in Work.Spaces.Iθ, G z θ := by
    intro z hz
    change (∫ θ in Work.Spaces.Iθ, F' z θ) ≤ ∫ θ in Work.Spaces.Iθ, G z θ
    by_cases h : MeasureTheory.Integrable (fun θ => F' z θ)
        (volume.restrict Work.Spaces.Iθ)
    · exact MeasureTheory.integral_mono_ae h (hGslice z hz) (hae z hz)
    · rw [MeasureTheory.integral_undef h]
      exact hGnn z hz
  by_cases h : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, F' z θ)
      (volume.restrict Work.Spaces.Iz)
  · refine MeasureTheory.integral_mono_ae h hGz ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    change (∫ θ in Work.Spaces.Iθ, F' z θ) ≤ ∫ θ in Work.Spaces.Iθ, G z θ
    exact hslice z hz
  · rw [MeasureTheory.integral_undef h]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici hGnn

/-- `HkMem` transfers across functions that agree on the open quadrant. -/
theorem HkMem_of_EqOn {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hmem : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k g := by
  have hcongr : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ :=
    fun z θ hz hθ hθ' =>
      Work.FTS.EllipticEst.lobAux.HkIntegrand_congr_open α k h hz hθ hθ'
  have hEq : ∀ z, 0 < z → (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α k g z θ) := by
    intro z hz
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    exact hcongr z θ hz hθ.1 hθ.2
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hz : (fun θ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext (Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_z_eq_zero α k g)
      rw [hz]
      simp
    · exact (hmem.1 z hz).congr (hEq z hzpos)
  · refine hmem.2.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hz : (fun θ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext (Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_z_eq_zero α k g)
      have hzf : (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext (Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_z_eq_zero α k f)
      change (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g 0 θ
      rw [hz, hzf]
    · exact MeasureTheory.integral_congr_ae (hEq z hzpos)

/-- A four-term linearity lemma for the Bochner integral. -/
theorem integral_sum4 {μ : Measure ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) :
    (∫ a, c₁ * f₁ a + c₂ * f₂ a + c₃ * f₃ a + c₄ * f₄ a ∂μ)
      = c₁ * (∫ a, f₁ a ∂μ) + c₂ * (∫ a, f₂ a ∂μ) + c₃ * (∫ a, f₃ a ∂μ)
        + c₄ * (∫ a, f₄ a ∂μ) := by
  have hc₁ : Integrable (fun a => c₁ * f₁ a) μ := h₁.const_mul c₁
  have hc₂ : Integrable (fun a => c₂ * f₂ a) μ := h₂.const_mul c₂
  have hc₃ : Integrable (fun a => c₃ * f₃ a) μ := h₃.const_mul c₃
  have hc₄ : Integrable (fun a => c₄ * f₄ a) μ := h₄.const_mul c₄
  have hA : Integrable (fun a => c₁ * f₁ a + c₂ * f₂ a) μ := hc₁.add hc₂
  have hB : Integrable (fun a => c₃ * f₃ a + c₄ * f₄ a) μ := hc₃.add hc₄
  calc (∫ a, c₁ * f₁ a + c₂ * f₂ a + c₃ * f₃ a + c₄ * f₄ a ∂μ)
      = ∫ a, (c₁ * f₁ a + c₂ * f₂ a) + (c₃ * f₃ a + c₄ * f₄ a) ∂μ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun a => by ring))
    _ = (∫ a, (c₁ * f₁ a + c₂ * f₂ a) ∂μ) + ∫ a, (c₃ * f₃ a + c₄ * f₄ a) ∂μ :=
        MeasureTheory.integral_add hA hB
    _ = ((∫ a, c₁ * f₁ a ∂μ) + ∫ a, c₂ * f₂ a ∂μ)
          + ((∫ a, c₃ * f₃ a ∂μ) + ∫ a, c₄ * f₄ a ∂μ) := by
        rw [MeasureTheory.integral_add hc₁ hc₂, MeasureTheory.integral_add hc₃ hc₄]
    _ = c₁ * (∫ a, f₁ a ∂μ) + c₂ * (∫ a, f₂ a ∂μ) + c₃ * (∫ a, f₃ a ∂μ)
          + c₄ * (∫ a, f₄ a ∂μ) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        ring

/-- Pointwise bound for the source slot of `B = D_zΨ`, via its second angular derivative. -/
theorem srcB_pointwise (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (B : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 B))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k B z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.pthIter 2 B) z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand (k - 2) (by omega)
  refine ⟨C0, hC0pos, fun α B hα hsmW z hz => ?_⟩
  have hkB : Work.Spaces.pthIter k B
      = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) := by
    conv_lhs => rw [show k = (k - 2) + 2 from by omega]
    exact Work.FTS.EllipticEst.remov.pthIter_add_local (k - 2) 2 B
  have h2 := hC0 α (Work.Spaces.pthIter 2 B) (k - 1) (by omega) hα hsmW z hz
  have h1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k B z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α)) := by
    refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hexp : 2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α
        ≤ 2 * (k : ℝ) - Work.Spaces.gam α := by
      have hcast : (((k - 2 : ℕ)) : ℝ) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]; push_cast; ring
      rw [hcast]; linarith
    have hwle : (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ (Real.sin (2 * θ)) ^ (2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α) :=
      Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
    rw [hkB]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle (sq_nonneg _)) (sq_nonneg _)
  filter_upwards [h1, h2] with θ h1θ h2θ
  exact le_trans h1θ h2θ

/-- Hypothesis (1) of the target, with parameter `D`. -/
def H1 (D : ℝ) (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
    ≤ D * Work.Spaces.HkNorm α k F

/-- Hypothesis (2) of the target, with parameter `D`. -/
def H2 (D : ℝ) (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
    ≤ D * Work.Spaces.HkNorm α k F

theorem topSrcSlot_dev (D : ℝ) (hD : 0 < D) (k : ℕ) (hk : 3 ≤ k) (CT : ℝ) (hCTpos : 0 < CT)
    (hCT : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ → H1 D α k F Ψ → H2 D α k F Ψ →
      α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ≤ CT * Work.Spaces.HkNorm α k F)
    (hmemW : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ → H1 D α k F Ψ → H2 D α k F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                  (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  obtain ⟨C_F, hCFpos, hCF⟩ := srcF_pointwise k (by omega)
  obtain ⟨C_A, hCApos, hCA⟩ := srcA_pointwise k (by omega)
  obtain ⟨C_B, hCBpos, hCB⟩ := srcB_pointwise k hk
  refine ⟨3 * (C_F + C_A * (D ^ 2 + CT ^ 2) + 2 * C_B * D ^ 2) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.DzIter 1 Ψ with hBdef
  set W : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) with hWdef
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso)
      (fun z θ hz hθ hlt => hwk.eq z hz θ hθ hlt)
  have hFfr : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFso
  have hAso : Work.FTS.EllipticEst.SmoothOpen A := by
    rw [hAdef]
    exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2))
      (fun z θ _ _ _ => rfl)
  have hAfr : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry A)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall A).mp hAso
  have hBso : Work.FTS.EllipticEst.SmoothOpen B := by
    rw [hBdef]
    simpa using Work.FTS.EllipticEst.SmoothOpen.Dz hΨso
  have hWso : Work.FTS.EllipticEst.SmoothOpen W := by
    rw [hWdef]
    exact Work.FTS.EllipticEst.SrcBnd.smoothOpen_pthIter hBso 2
  have hWfr : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 B))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall W).mp hWso
  have hmemF : Work.Spaces.HkMem α k F := hwk.memF
  have hmemA1 : Work.Spaces.HkMem α (k - 1) A :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hAfr hwk.memA
  have hmemW1 : Work.Spaces.HkMem α (k - 1) W := by
    rw [hWdef]
    exact hmemW α F Ψ hα hα4 hwk
  have hTkslot := integrableOn_TkSlot (α := α) (k := k) hAso hwk.memA (by omega)
  set G' : ℝ → ℝ → ℝ := fun z θ => 3 * (C_F * Work.Spaces.HkIntegrand α k F z θ
      + (α ^ 4 * C_A) * Work.Spaces.HkIntegrand α (k - 1) A z θ
      + (α ^ 4 * C_A) * (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2
      + ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkIntegrand α (k - 1) W z θ) with hG'def
  have hGslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => G' z θ) Work.Spaces.Iθ := by
    intro z hz
    rw [hG'def]
    exact ((((hmemF.1 z hz).const_mul C_F).add ((hmemA1.1 z hz).const_mul _)).add
      ((hTkslot.1 z hz).const_mul _)).add ((hmemW1.1 z hz).const_mul _) |>.const_mul 3
  have hGz_ae : (fun z => ∫ θ in Work.Spaces.Iθ, G' z θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      fun z => 3 * (C_F * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        + (α ^ 4 * C_A) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (k - 1) A z θ)
        + (α ^ 4 * C_A) * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
        + ((α * (5 + α)) ^ 2 * C_B) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (k - 1) W z θ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rw [hG'def]
    simp only []
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_sum4 (hmemF.1 z hz) (hmemA1.1 z hz) (hTkslot.1 z hz) (hmemW1.1 z hz)
  have hGz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, G' z θ)
      Work.Spaces.Iz :=
    (((((hmemF.2.const_mul C_F).add (hmemA1.2.const_mul _)).add
      (hTkslot.2.const_mul _)).add (hmemW1.2.const_mul _)).const_mul 3).congr hGz_ae.symm
  have hGnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ, G' z θ := by
    intro z hz
    refine MeasureTheory.integral_nonneg fun θ => ?_
    rw [hG'def]
    simp only []
    have h1n : 0 ≤ C_F * Work.Spaces.HkIntegrand α k F z θ :=
      mul_nonneg hCFpos.le (Work.Spaces.HkIntegrand_nonneg α k F z θ)
    have h2n : 0 ≤ (α ^ 4 * C_A) * Work.Spaces.HkIntegrand α (k - 1) A z θ :=
      mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α (k - 1) A z θ)
    have h3n : 0 ≤ (α ^ 4 * C_A)
        * (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have h4n : 0 ≤ ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkIntegrand α (k - 1) W z θ :=
      mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α (k - 1) W z θ)
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg h1n h2n) h3n) h4n)
  have hGeq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G' z θ)
      = 3 * (C_F * Work.Spaces.HkSq α k F
          + (α ^ 4 * C_A) * Work.Spaces.HkSq α (k - 1) A
          + (α ^ 4 * C_A) * Work.FTS.EllipticEst.remov.Step.Tk α k A
          + ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkSq α (k - 1) W) := by
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G' z θ)
        = ∫ z in Work.Spaces.Iz, 3 * (C_F * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F z θ)
            + (α ^ 4 * C_A) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (α ^ 4 * C_A) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
            + ((α * (5 + α)) ^ 2 * C_B) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) W z θ)) from
      MeasureTheory.integral_congr_ae hGz_ae]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [integral_sum4 hmemF.2 hmemA1.2 hTkslot.2 hmemW1.2]
    simp only [Work.Spaces.HkSq, Work.FTS.EllipticEst.remov.Step.Tk]
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ)
            z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ G' z θ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine Eventually.of_forall (fun θ => ?_)
      have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by norm_num [Work.Spaces.w]
      rw [hw0, zero_mul]
      rw [hG'def]
      simp only []
      have h1n : 0 ≤ C_F * Work.Spaces.HkIntegrand α k F 0 θ :=
        mul_nonneg hCFpos.le (Work.Spaces.HkIntegrand_nonneg α k F 0 θ)
      have h2n : 0 ≤ (α ^ 4 * C_A) * Work.Spaces.HkIntegrand α (k - 1) A 0 θ :=
        mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α (k - 1) A 0 θ)
      have h3n : 0 ≤ (α ^ 4 * C_A)
          * (Work.Spaces.mixed 0 k A 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      have h4n : 0 ≤ ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkIntegrand α (k - 1) W 0 θ :=
        mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α (k - 1) W 0 θ)
      exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg h1n h2n) h3n) h4n)
    · have hGh : Work.FTS.EllipticEst.Mine.Gsrc α F Ψ
          = fun z θ => F z θ + α ^ 2 * A z θ + (α * (5 + α)) * B z θ := by
        funext z θ
        simp [Work.FTS.EllipticEst.Mine.Gsrc, hAdef, hBdef, Work.Spaces.DzIter_succ,
          Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      filter_upwards [Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ,
        hCF α F hα hFfr z hz, hCA α A hα hAfr z hz, hCB α B hα hWfr z hz]
        with θ hθ hFp hAp hBp
      have h3 : Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
          = Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
            + (α * (5 + α)) * Work.Spaces.pthIter k B z θ := by
        rw [hGh]
        exact Work.FTS.EllipticEst.SrcBnd.pthIter_three_lin hFso hAso hBso (α ^ 2)
          (α * (5 + α)) k z θ hzpos hθ
      rw [h3]
      have hsθ : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
        Real.rpow_nonneg hsθ.le _
      have key : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        intro a b c
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
      have hquad := key (Work.Spaces.pthIter k F z θ)
        (α ^ 2 * Work.Spaces.pthIter k A z θ)
        ((α * (5 + α)) * Work.Spaces.pthIter k B z θ)
      have hmul := mul_le_mul_of_nonneg_right hquad
        (mul_nonneg (sq_nonneg (Work.Spaces.w z)) hσ)
      have hL : (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
                + (α * (5 + α)) * Work.Spaces.pthIter k B z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          = (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
                + (α * (5 + α)) * Work.Spaces.pthIter k B z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by ring
      rw [hL]
      refine le_trans hmul ?_
      have heq : 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
              + (α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
              + ((α * (5 + α)) * Work.Spaces.pthIter k B z θ) ^ 2)
            * ((Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          = 3 * ((Work.Spaces.w z) ^ 2
                * ((Work.Spaces.pthIter k F z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
              + (α ^ 2) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Work.Spaces.pthIter k A z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
              + (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Work.Spaces.pthIter k B z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))) := by ring
      rw [heq]
      have hA2 : (α ^ 2) ^ 2 * ((Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter k A z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          ≤ (α ^ 2) ^ 2 * (C_A * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hAp (by positivity)
      have hB2 : (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter k B z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          ≤ (α * (5 + α)) ^ 2 * (C_B
              * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.pthIter 2 B) z θ) :=
        mul_le_mul_of_nonneg_left hBp (by positivity)
      have hsum := add_le_add (add_le_add hFp hA2) hB2
      rw [hG'def]
      simp only []
      ring_nf at hsum ⊢
      linarith [hsum]
  have hG1eq : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ)
            z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  rw [hG1eq]
  refine le_trans (int_le_of_majorant hGslice hGz hGnn hpt) ?_
  rw [hGeq]
  have hα2pos : 0 < α ^ 2 := by positivity
  have hα4pos : 0 < α ^ 4 := by positivity
  have hNFnn : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
  have hSqF : Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hA1 : Work.Spaces.HkNorm α (k - 1) A ≤ D * Work.Spaces.HkNorm α k F / α ^ 2 := by
    have h2nn : 0 ≤ Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkNorm_nonneg α (k - 1) _
    have h1' : α ^ 2 * Work.Spaces.HkNorm α (k - 1) A
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F := by
      simpa only [H1, hAdef] using h1
    rw [le_div_iff₀ hα2pos]
    calc Work.Spaces.HkNorm α (k - 1) A * α ^ 2
        = α ^ 2 * Work.Spaces.HkNorm α (k - 1) A := by ring
      _ ≤ D * Work.Spaces.HkNorm α k F := by linarith [h1', h2nn]
  have hA2 : Work.Spaces.HkSq α (k - 1) A
      ≤ D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 / α ^ 4 := by
    have hsq : Work.Spaces.HkSq α (k - 1) A = (Work.Spaces.HkNorm α (k - 1) A) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) A)]
    rw [hsq]
    have hb := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) A) hA1 2
    have hx : (D * Work.Spaces.HkNorm α k F / α ^ 2) ^ 2
        = D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 / α ^ 4 := by
      rw [div_pow, mul_pow, show (α ^ 2) ^ 2 = α ^ 4 by ring]
    rwa [hx] at hb
  have hA3 : (α ^ 4 * C_A) * Work.Spaces.HkSq α (k - 1) A
      ≤ (C_A * D ^ 2) * Work.Spaces.HkSq α k F := by
    have h := mul_le_mul_of_nonneg_left hA2
      (show (0:ℝ) ≤ α ^ 4 * C_A by positivity)
    have hx : α ^ 4 * C_A * (D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 / α ^ 4)
        = C_A * D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by
      field_simp
    rw [hx] at h
    rw [hSqF]
    exact h
  have hT1 : Work.FTS.EllipticEst.remov.Step.Tk α k A
      ≤ CT ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 / α ^ 4 := by
    have ht := hCT α F Ψ hα hα4 hwk h1 h2
    have ht' : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)
        ≤ CT * Work.Spaces.HkNorm α k F := by simpa only [hAdef] using ht
    have hTknn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k A :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg α k A
    have hb : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k A
        ≤ (CT * Work.Spaces.HkNorm α k F) ^ 2 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ α ^ 2 * Real.sqrt
        (Work.FTS.EllipticEst.remov.Step.Tk α k A) by positivity) ht' 2
      have hsq : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)) ^ 2
          = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k A := by
        rw [mul_pow, Real.sq_sqrt hTknn]
        ring
      linarith [h, hsq.le, hsq.ge]
    rw [le_div_iff₀ hα4pos]
    nlinarith [hb]
  have hT2 : (α ^ 4 * C_A) * Work.FTS.EllipticEst.remov.Step.Tk α k A
      ≤ (C_A * CT ^ 2) * Work.Spaces.HkSq α k F := by
    have h := mul_le_mul_of_nonneg_left hT1 (show (0:ℝ) ≤ α ^ 4 * C_A by positivity)
    have hx : α ^ 4 * C_A * (CT ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 / α ^ 4)
        = C_A * CT ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by
      field_simp
    rw [hx] at h
    rw [hSqF]
    exact h
  have hW1 : Work.Spaces.HkNorm α (k - 1) W ≤ D * Work.Spaces.HkNorm α k F := by
    have h1nn : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
    have h2' : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F := by
      simpa only [H2] using h2
    have hW : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F := by linarith [h2', h1nn]
    simpa only [hWdef] using hW
  have hW2 : Work.Spaces.HkSq α (k - 1) W
      ≤ D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by
    have hsq : Work.Spaces.HkSq α (k - 1) W = (Work.Spaces.HkNorm α (k - 1) W) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) W)]
    rw [hsq]
    have hb := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) W) hW1 2
    rwa [mul_pow] at hb
  have hW3 : ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkSq α (k - 1) W
      ≤ (2 * C_B * D ^ 2) * Work.Spaces.HkSq α k F := by
    rw [hSqF]
    have hfac : (α * (5 + α)) ^ 2 ≤ 2 := by nlinarith [hα, hα4]
    have hCBnn : (0:ℝ) ≤ (α * (5 + α)) ^ 2 * C_B := mul_nonneg (sq_nonneg _) hCBpos.le
    have h1' : ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkSq α (k - 1) W
        ≤ ((α * (5 + α)) ^ 2 * C_B) * (D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2) :=
      mul_le_mul_of_nonneg_left hW2 hCBnn
    have h2' : ((α * (5 + α)) ^ 2 * C_B) * (D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2)
        ≤ (2 * C_B * D ^ 2) * (Work.Spaces.HkNorm α k F) ^ 2 := by
      have hD2 : 0 ≤ D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 :=
        mul_nonneg (sq_nonneg D) (sq_nonneg _)
      have hstep : (α * (5 + α)) ^ 2 * C_B ≤ 2 * C_B :=
        mul_le_mul_of_nonneg_right hfac hCBpos.le
      calc ((α * (5 + α)) ^ 2 * C_B) * (D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2)
          ≤ (2 * C_B) * (D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2) :=
            mul_le_mul_of_nonneg_right hstep hD2
        _ = (2 * C_B * D ^ 2) * (Work.Spaces.HkNorm α k F) ^ 2 := by ring
    linarith [h1', h2']
  have hbig : 3 * (C_F * Work.Spaces.HkSq α k F
        + (α ^ 4 * C_A) * Work.Spaces.HkSq α (k - 1) A
        + (α ^ 4 * C_A) * Work.FTS.EllipticEst.remov.Step.Tk α k A
        + ((α * (5 + α)) ^ 2 * C_B) * Work.Spaces.HkSq α (k - 1) W)
      ≤ (3 * (C_F + C_A * (D ^ 2 + CT ^ 2) + 2 * C_B * D ^ 2) + 1) * Work.Spaces.HkSq α k F := by
    have hCFnn : 0 ≤ C_F * Work.Spaces.HkSq α k F :=
      mul_nonneg hCFpos.le (Work.Spaces.HkSq_nonneg α k F)
    have hSqAnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
    nlinarith [hA3, hT2, hW3, hCFnn, hSqAnn, sq_nonneg D, sq_nonneg CT, hCApos, hCBpos,
      hCFpos, mul_nonneg hCFpos.le hSqAnn]
  exact hbig



/-- **The top source slot.**  The plain `∂_θ^k` of `Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)D_zΨ`
is split into the three summands and bounded by a majorant built from the `ℋ^k`-integrand of
`F`, the `ℋ^{k-1}`-integrand of `z²∂_z²Ψ` plus the top `D_θ^k`-slot of `z²∂_z²Ψ` (which is the
`Tk`-slot controlled by `A_top_slot_bound`), and the `ℋ^{k-1}`-integrand of `∂_θθ(D_zΨ)`. -/
theorem topSrcSlot (D : ℝ) (hD : 0 < D) : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      H1 D α k F Ψ → H2 D α k F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                  (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.EllipticEst.remov.A_top_slot_bound_clean D hD k hk
  refine topSrcSlot_dev D hD k hk CT hCTpos hCT ?_
  intro α F Ψ hα hα4 hwk
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hV : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.remov.HkMem_Dz_shift_clean (by omega)
      (Work.FTS.EllipticEst.SrcBnd.smoothOpen_pthIter hΨso 2) hwk.memB
  refine HkMem_of_EqOn ?_ hV
  intro z θ hz hθ hθ'
  exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨso 1
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)).symm

/- **Domination of the right-hand side of `TopSlotTwoD` by `C·|F|²_{ℋ^k}`.**
Intended namespace: `Work.FTS.EllipticEst.Cores.Pieces`.

Hypotheses (1) and (2) are the two level-`(k-1)` norm bounds of the target, with the *parameter* `D`:

(1) `α²|z²∂_z²Ψ|_{k-1} + |∂_θθΨ|_{k-1} ≤ D|F|_k`,
(2) `α²|z²∂_z²(D_zΨ)|_{k-1} + |∂_θθ(D_zΨ)|_{k-1} ≤ D|F|_k`,

where `|f|_m = Work.Spaces.HkNorm α m f` and `D_z = z∂_z`.

The five groups to bound, with `γ = gam α`, `σ = sin(2θ)`, `sEta θ = σ^{-η}`:

* the top source slot `∫∫ (∂_θ^k(Gsrc α F Ψ))²σ^{2k-γ}w²`, `Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)D_zΨ`:
  convert the plain slot into `D_θ`-slots of `F`, of `z²∂_z²Ψ` and of `D_zΨ`; the first are slots of
  `HkSq α k F`, the second come from (1) for levels `≤ k-1` and from the PROVED
  `Work.FTS.EllipticEst.remov.A_top_slot_bound` at level `k`, and the third from (2) (the plain
  `∂_θ^k` of `D_zΨ` is `∂_θ^{k-2}` of `∂_θθ(D_zΨ)`, a level `≤ k-1` slot, its weight `σ^{2k-γ}` being
  dominated by `σ^{2(k-2)-γ}`);
* the `u`-family `Σ_{i∈Icc 3 (k+1)} ∫∫(∂_θ^iΨ)²σ^{2i-4-γ}w²`: each is a plain level-`(i-2)` slot of
  `∂_θθΨ`, i.e. a slot of `HkSq α (k-1)(∂_θθΨ) ≤ D²|F|_k²` by (1);
* the `η`-term `∫∫(∂_θθΨ)²sEta w²`: the pure level-`0` slot of `HkSq α (k-1)(∂_θθΨ) ≤ D²|F|_k²`;
* `∫∫(∂_θΨ)²w²` and `∫∫Ψ²w²`: for a.e. `z` the slice `θ ↦ Ψ z θ` is continuous on `[0, π/2]`
  (the proved `Work.FTS.EllipticEst.remov.weakSliceRegular`) and vanishes at both endpoints, so the
  proved `Work.FTS.EllipticEst.Mine.SlicePoincare.SlicePoincare` gives
  `∫(∂_θΨ)² ≤ K∫(∂_θθΨ)²sEta` and `∫Ψ² ≤ K∫(∂_θθΨ)²sEta`; then `∫(∂_θθΨ)² ≤ ∫(∂_θθΨ)²sEta` because
  `sEta ≥ 1`.  (No smoothness beyond continuity at the endpoints is needed.)

The conversion "plain slot ↦ `D_θ`-slots" is the sharp forward expansion
`σ^{2m}(∂_θ^m f)² ≤ C Σ_{q∈Icc 1 m}(D_θ^q f)²`, in which the `q = 0` term is *absent* (the
coefficient of `∂_θ^0` in `D_θ^m` vanishes because `D_θ(const) = 0`).  The existing
`Work.FTS.EllipticEst.Cores.Pieces.pthIter_sq_mul_sin_pow_le` is the weaker version of this with a
`q = 0` term, hence not sufficient; `Work.FTS.EllipticEst.remov.sliceTopCore.sin_pow_le_dth1Iter`
and `Work.FTS.EllipticEst.dthCoef_self`/`DthCoef_sin_pow_bound` are the available ingredients. -/
theorem TopSlotRhsDom (D : ℝ) (hD : 0 < D) : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                  (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ i ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter i Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        ≤ C * Work.Spaces.HkNorm α k F ^ 2 := by
  intro k hk
  obtain ⟨C1, hC1pos, hC1⟩ := topSrcSlot D hD k hk
  obtain ⟨C2, hC2pos, hC2⟩ :=
    Work.FTS.EllipticEst.remov.high_slice_chain_slots D hD k (by omega)
  obtain ⟨C3, hC3pos, hC3⟩ :=
    Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux.lowSlots D hD k hk
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have h1' : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D * Work.Spaces.HkNorm α k F := by
    have hnn : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
    linarith [h1, hnn]
  have hA := hC1 α F Ψ hα hα4 hwk h1 h2
  have hB := hC2 α F Ψ hα hα4 hwk h1' h2
  have hC := hC3 α F Ψ hα hα4 hwk h1
  have hB' : (∑ i ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter i Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α))
      ≤ C2 * Work.Spaces.HkSq α k F := hB
  have hSqF : Work.Spaces.HkSq α k F = Work.Spaces.HkNorm α k F ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  rw [hSqF] at hA hB' hC
  linarith [hA, hB', hC]

end Work.FTS.EllipticEst.Cores.Pieces
