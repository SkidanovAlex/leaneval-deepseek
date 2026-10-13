/-
# `Work.FTS.Apriori.Limit.SlotCalc` — the slot decomposition of the `ℋ⁴`-integrand

The `ℋ⁴`-integrand of the paper is a sum of squares of weighted slot derivatives.  This module
identifies it with the sum over the finite index set `activeSlots` used by the lower
semicontinuity proof of `HkNorm_le_of_tendstoLocUnif`, and collects the elementary smoothness
and integrability facts about the slots.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary facts about the open quadrant -/

theorem mem_Qd_iff {p : ℝ × ℝ} :
    p ∈ Qd ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 := by
  simp [Qd, Set.mem_Ioi, Set.mem_Ioo, and_assoc]

theorem Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_Qd_iff.mp hp
  show -1 < p.1 ∧ (0 < p.2 ∧ p.2 < π / 2)
  exact ⟨by linarith, h2⟩

theorem sin_two_pos_of_mem_Qd {p : ℝ × ℝ} (hp : p ∈ Qd) : 0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := mem_Qd_iff.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-! ## The slot weights -/

@[simp] theorem slotWeight_zero (α : ℝ) (j : ℕ) (z θ : ℝ) :
    slotWeight α (j, 0) z θ
      = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  simp [slotWeight]

@[simp] theorem slotWeight_succ (α : ℝ) (j i : ℕ) (z θ : ℝ) :
    slotWeight α (j, i + 1) z θ = Work.Spaces.Wt α z θ := by
  simp [slotWeight]

/-! ## Membership in `activeSlots` -/

theorem mem_activeSlots_iff {ji : ℕ × ℕ} :
    ji ∈ activeSlots ↔ (ji.2 = 0 ∧ ji.1 ≤ 4) ∨ (1 ≤ ji.2 ∧ ji.1 + ji.2 ≤ 4) := by
  rw [activeSlots, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h | h⟩
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h.1, h.2⟩
  · rintro (⟨h, h1⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1, by omega⟩, Or.inl h⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inr ⟨h1, h2⟩⟩

/-! ## The slot decomposition of `HkIntegrand` -/

/-- The `ℋ⁴`-integrand is the sum of the squares of the weighted slots. -/
theorem HkIntegrand_eq_sum_slot (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 4 f z θ = ∑ ji ∈ activeSlots, (slot α ji f z θ) ^ 2 := by
  classical
  set D : ℕ → ℕ → ℝ := fun j i => if 1 ≤ i ∧ i + j ≤ 4
      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 with hD
  set E : ℕ → ℕ → ℝ := fun j i => if (i = 0 ∨ (1 ≤ i ∧ i + j ≤ 4))
      then (Work.Spaces.mixed j i f z θ * slotWeight α (j, i) z θ) ^ 2 else 0 with hE
  have hmain : Work.Spaces.HkIntegrand α 4 f z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, D j i := by
    simp only [Work.Spaces.HkIntegrand, hD, Nat.reduceAdd]
  have hiff : ∀ j i : ℕ, (i = 0 ∨ (1 ≤ i ∧ j + i ≤ 4)) ↔ (i = 0 ∨ (1 ≤ i ∧ i + j ≤ 4)) := by
    intro j i
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
  have hslots : (∑ ji ∈ activeSlots, (slot α ji f z θ) ^ 2)
      = ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, E j i := by
    rw [activeSlots, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [hE]
    simp only [slot]
    exact if_congr (hiff j i) rfl rfl
  have hPsum : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∑ j ∈ Finset.range 5, E j 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE]
    simp only [Work.Spaces.mixed_zero_right, slotWeight_zero]
    simp
  have hD0 : ∑ j ∈ Finset.range 5, D j 0 = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp only [hD]
    simp
  have hED : ∀ j i : ℕ, E j (i + 1) = D j (i + 1) := by
    intro j i
    simp only [hE, hD]
    rw [slotWeight_succ]
    simp
  have hDsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, D j i)
      = (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 5, D j (i + 1))
        + ∑ j ∈ Finset.range 5, D j 0 := by
    rw [Finset.sum_range_succ']
  have hEsum : (∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, E j i)
      = ∑ j ∈ Finset.range 5, ((∑ i ∈ Finset.range 4, E j (i + 1)) + E j 0) :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_range_succ' (fun i => E j i) 4)
  have hED' : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 5, E j (i + 1))
      = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 5, D j (i + 1) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hED j i))
  rw [hmain, hslots, hPsum, hDsum, hD0, add_zero, hEsum, Finset.sum_add_distrib,
    Finset.sum_comm (s := Finset.range 5) (t := Finset.range 4) (f := fun j i => E j (i + 1)),
    hED', add_comm]

/-! ## Smoothness of the slot weights on the open quadrant -/

theorem contDiffOn_w_Qd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact ContDiffOn.div ((contDiffOn_const.add contDiffOn_fst).pow 2) (contDiffOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Qd_iff.mp hp).1))

theorem contDiffOn_sin_rpow_Qd (c : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.rpow_const_of_ne (fun p hp => ne_of_gt (sin_two_pos_of_mem_Qd hp))

/-- The square of a slot weight is `C^∞` on the open quadrant. -/
theorem contDiffOn_slotWeight_sq (α : ℝ) (j i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (slotWeight α (j, i) z θ) ^ 2)) Qd := by
  by_cases hi : i = 0
  · subst hi
    have hfun : Function.uncurry (fun z θ => (slotWeight α (j, 0) z θ) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.w p.1
            / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      funext p
      show (slotWeight α (j, 0) p.1 p.2) ^ 2 = _
      rw [slotWeight_zero]
    rw [hfun]
    refine (contDiffOn_w_Qd.div (contDiffOn_sin_rpow_Qd _) (fun p hp => ?_)).pow 2
    exact ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Qd hp) _)
  · have hfun : Function.uncurry (fun z θ => (slotWeight α (j, i) z θ) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
      funext p
      show (slotWeight α (j, i) p.1 p.2) ^ 2 = _
      rw [show slotWeight α (j, i) p.1 p.2
          = Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) by
        simp [slotWeight, hi, Work.Spaces.Wt, Work.Spaces.wTheta]]
    rw [hfun]
    exact (contDiffOn_w_Qd.mul (contDiffOn_sin_rpow_Qd _)).pow 2

/-! ## Integrability helpers -/

/-- The product measure is the restriction of the planar Lebesgue measure to the closed
quadrant. -/
theorem Qμ_eq_restrict :
    Qμ = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [Qμ, Measure.prod_restrict]

/-- A function which is continuous on the open quadrant and vanishes outside a compact subset
of it is integrable with respect to `Qμ`. -/
theorem integrable_of_continuousOn_of_support {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Qd) (hsupp : Function.support F ⊆ K) :
    Integrable F Qμ := by
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
  have hfin : Qμ K < ∞ := by
    rw [Qμ_eq_restrict, Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hK.measure_lt_top
  have haesm : AEStronglyMeasurable F (Qμ.restrict K) :=
    (hF.mono hKQ).aestronglyMeasurable hK.measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF.mono hKQ)
  refine IntegrableOn.of_bound hfin haesm C ?_
  exact ae_restrict_of_forall_mem hK.measurableSet (fun x hx => hC x hx)

/-- The weighted slot `slot α ji f` is continuous on the open quadrant whenever `f` is smooth
there. -/
theorem continuousOn_slot {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (α : ℝ) (ji : ℕ × ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => slot α ji f p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf ji.1 ji.2).continuousOn).mono
      Qd_subset_quadU
  have h2 : ContinuousOn (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2) Qd := by
    by_cases hi : ji.2 = 0
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
        funext p; simp [slotWeight, hi]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.div (contDiffOn_sin_rpow_Qd _).continuousOn
        (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Qd hp) _))
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
        funext p; simp [slotWeight, hi, Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.mul (contDiffOn_sin_rpow_Qd _).continuousOn
  have h3 : (fun p : ℝ × ℝ => slot α ji f p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2 * slotWeight α ji p.1 p.2 := by
    funext p; rfl
  rw [h3]
  exact h1.mul h2

/-- The cut-off `ℋ⁴`-energy is the sum of the cut-off energies of the individual slots. -/
theorem HksqCut_eq_sum_slot {α : ℝ} {f η : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hη : TestQ η) :
    HksqCut α f η
      = ∑ ji ∈ activeSlots, ∫ p, (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2 ∂Qμ := by
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2
      = ∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2 := by
    intro p
    rw [HkIntegrand_eq_sum_slot, Finset.sum_mul]
  have hint : ∀ ji ∈ activeSlots,
      Integrable (fun p : ℝ × ℝ => (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2) Qμ := by
    intro ji _
    refine integrable_of_continuousOn_of_support
      (((continuousOn_slot hf α ji).pow 2).mul hη.1.continuousOn) hη.2.1 hη.2.2 ?_
    exact (Function.support_mul_subset_right _ _).trans (subset_tsupport _)
  rw [HksqCut]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact MeasureTheory.integral_finsetSum _ (fun ji hji => hint ji hji)

end Work.FTS.Apriori.Limit
