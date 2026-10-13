import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G5

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `HkIntegrand` versus the interval integral in `s`, for arbitrary `k`

This is the general-`k` version of
`Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le` (which is the case `k = 4`).
If every slot `D_z^j D_θ^i (H s) z θ` of the family `s ↦ H s` is measurable and bounded
by `C` on `uIoc a b`, and if the slots of the primitive `∫_s H s` are the integrals of the
slots (the exchange identity `hid`), then

`HkIntegrand α k (∫_s H s) z θ ≤ (b - a) · ∫_s HkIntegrand α k (H s) z θ`.

The proof is slotwise Cauchy–Schwarz in `s`: each slot of `HkIntegrand α k (∫_s H s)` is
`W · ∫_s (slot of H s)`, and `(∫_s φ)² ≤ (b - a) ∫_s φ²`; summing over the finitely many
slots (the ranges `Finset.range (k+1)`) and using that the sum over the slots of `H s` is
exactly `HkIntegrand α k (H s) z θ` gives the claim.  Nothing depends on `k = 4` beyond
the index range, so the argument transcribes verbatim.
-/

/-- The main estimate, for arbitrary `k`. -/
theorem HkIntegrand_intervalIntegral_le_gen {α a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {H : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {k : ℕ}
    (hmeas : ∀ (j i : ℕ), j + i ≤ k →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ (j i : ℕ), j + i ≤ k → ∀ s ∈ Set.uIoc a b,
      |Work.Spaces.mixed j i (H s) z θ| ≤ C)
    (hid : ∀ j i : ℕ, j + i ≤ k →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hvol : volume (Set.uIoc a b) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  -- slot integrability, from measurability and the uniform bound on `uIoc a b`
  have hslot : ∀ (j i : ℕ), j + i ≤ k →
      IntervalIntegrable (fun s => Work.Spaces.mixed j i (H s) z θ) volume a b := by
    intro j i hji
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol (hmeas j i hji) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    simpa [Real.norm_eq_abs] using hbdd j i hji s hs
  have hslot2 : ∀ (j i : ℕ), j + i ≤ k → ∀ c : ℝ,
      IntervalIntegrable (fun s => (Work.Spaces.mixed j i (H s) z θ * c) ^ 2) volume a b := by
    intro j i hji c
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol
      (((hmeas j i hji).mul_const c).pow 2) ((C * |c|) ^ 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    have hb1 := hbdd j i hji s hs
    have hb2 : |Work.Spaces.mixed j i (H s) z θ * c| ≤ C * |c| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg c)
    rw [Real.norm_eq_abs, abs_sq]
    calc (Work.Spaces.mixed j i (H s) z θ * c) ^ 2
        = |Work.Spaces.mixed j i (H s) z θ * c| ^ 2 := (sq_abs _).symm
      _ ≤ (C * |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
  -- unfolding `HkIntegrand α k G z θ` into its two blocks
  have hId : Work.Spaces.HkIntegrand α k G z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i G z θ * W) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Work.Spaces.HkIntegrand, hW]
  -- the `D_z`-block
  have hPart1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i G z θ * W) ^ 2)
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2 := by
    refine le_of_eq_of_le ?_ (Work.FTS.StrongEps.E5G.finset_sum_sq_intervalIntegral_le
      (Finset.range (k + 1)) (fun i s => Work.Spaces.mixed i 0 (H s) z θ * W) hab ?_ ?_)
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      rw [show Work.Spaces.DzIter i G z θ = ∫ s in a..b, Work.Spaces.mixed i 0 (H s) z θ
        from hid i 0 hik]
      rw [intervalIntegral.integral_mul_const]
    · intro i hi
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      exact (hslot i 0 hik).mul_const W
    · intro i hi
      have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
      exact hslot2 i 0 hik W
  -- integrability of the mixed slots, in the "`if` inside the square" form
  have hF5 : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      IntervalIntegrable (fun s => if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0)
          = fun s => Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ :=
        funext fun s => ite_eq_left h
      rw [hfe]
      have hij : j + i ≤ k := by omega
      exact (hslot j i hij).mul_const _
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) = fun _ => 0 :=
        funext fun s => ite_eq_right h
      rw [hfe]; exact intervalIntegrable_const
  have hF5sq : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      IntervalIntegrable (fun s => (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
          = fun s => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun s => by rw [ite_eq_left h]
      rw [hfe]
      have hij : j + i ≤ k := by omega
      exact hslot2 j i hij _
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) = fun _ => 0 :=
        funext fun s => by rw [ite_eq_right h]; ring
      rw [hfe]; exact intervalIntegrable_const
  -- the mixed block
  have hPart2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
    have hmain := Work.FTS.StrongEps.E5G.double_sum_sq_intervalIntegral_le
      (Finset.range (k + 1)) (Finset.range (k + 1))
      (fun i j s => if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) hab hF5 hF5sq
    have hL : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (∫ s in a..b, if 1 ≤ i ∧ i + j ≤ k then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · have hij : j + i ≤ k := by omega
        simp only [ite_eq_left h]
        rw [intervalIntegral.integral_mul_const, ← hid j i hij]
      · simp only [ite_eq_right h]
        simp
    rw [hL]
    exact hmain
  -- the slots of the family `H s` recombine into `HkIntegrand α k (H s) z θ`
  have hT : ∀ s : ℝ,
      (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2
      = Work.Spaces.HkIntegrand α k (H s) z θ := by
    intro s
    have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (H s) z θ * W) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by simp only [Work.Spaces.mixed_zero_right]
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1, h2, Work.Spaces.HkIntegrand, hW]
  have hT1int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2) volume a b :=
    Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
      (fun i s => (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      (fun i hi => by
        have hik : i + 0 ≤ k := by have := Finset.mem_range.mp hi; omega
        exact hslot2 i 0 hik W)
  have hT2int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b :=
    Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
      (fun i s => ∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      (fun i hi => Work.FTS.StrongEps.E5G.intervalIntegrable_finsetSum (Finset.range (k + 1))
        (fun j s => (if 1 ≤ i ∧ i + j ≤ k then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        (fun j hj => hF5sq i hi j hj))
  have hTint : (∫ s in a..b, ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      + (∫ s in a..b, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      = ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
    rw [← intervalIntegral.integral_add hT1int hT2int]
    exact intervalIntegral.integral_congr (fun s _ => hT s)
  rw [hId]
  refine le_trans (add_le_add hPart1 hPart2) ?_
  rw [← hTint]
  exact le_of_eq (by ring)

end

end Work.FTS.StrongEps.E5G5
