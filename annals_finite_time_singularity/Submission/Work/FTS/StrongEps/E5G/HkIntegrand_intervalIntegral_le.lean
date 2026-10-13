import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `HkIntegrand` versus the interval integral in the parameter `s`

`Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le` is the pointwise-in-`(z,θ)`
Cauchy–Schwarz ("Jensen") step of the `slice_lip_HkSq` route: if every slot
`D_z^j D_θ^i (H s) z θ` of the family `s ↦ H s` is measurable and bounded by `C` on
`uIoc a b`, and if the slots of the primitive `∫_s H s` are the integrals of the slots
(the exchange identity `hid`), then

`HkIntegrand α 4 (∫_s H s) z θ ≤ (b - a) · ∫_s HkIntegrand α 4 (H s) z θ`.

The proof is Cauchy–Schwarz in `s` slot by slot: each slot of `HkIntegrand α 4 (∫_s H s)`
is `W · ∫_s (slot of H s)`, whose square is `(∫_s φ)^2 ≤ (b - a) ∫_s φ^2`; summing over the
finitely many slots and using that the sum of the squares of the slots of `H s` is exactly
`HkIntegrand α 4 (H s) z θ` gives the claim.

Everything here is `sorry`-free.
-/

/-! ## Cauchy–Schwarz for the interval integral -/

/-- **Jensen/Cauchy–Schwarz for the interval integral.**
For `a ≤ b` and `f` with `f` and `f²` interval integrable on `[a,b]`,
`(∫_a^b f)² ≤ (b-a) · ∫_a^b f²`. -/
theorem intervalIntegral_sq_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume a b) :
    (∫ s in a..b, f s) ^ 2 ≤ (b - a) * ∫ s in a..b, (f s) ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  have hba : 0 < b - a := sub_pos.mpr h
  set M : ℝ := ∫ s in a..b, f s with hM
  have hint : IntervalIntegrable (fun s => (f s - M / (b - a)) ^ 2) volume a b := by
    have h1 : IntervalIntegrable
        (fun s => f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2) volume a b :=
      (hf2.sub (hf.const_mul (2 * (M / (b - a))))).add intervalIntegrable_const
    refine h1.congr_ae (Filter.Eventually.of_forall fun s => ?_)
    ring
  have hnn : 0 ≤ ∫ s in a..b, (f s - M / (b - a)) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  have hcongr : (∫ s in a..b, (f s - M / (b - a)) ^ 2)
      = ∫ s in a..b, (f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2) :=
    intervalIntegral.integral_congr (fun s _ => by ring)
  have hcalc : (∫ s in a..b, (f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2))
      = (∫ s in a..b, f s ^ 2) - M ^ 2 / (b - a) := by
    rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul (2 * (M / (b - a)))))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hf2 (hf.const_mul (2 * (M / (b - a)))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hM]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hcongr, hcalc] at hnn
  have h3 : M ^ 2 / (b - a) ≤ ∫ s in a..b, f s ^ 2 := by linarith
  have h4 : M ^ 2 ≤ (∫ s in a..b, f s ^ 2) * (b - a) := (div_le_iff₀ hba).mp h3
  rw [hM]
  calc (∫ s in a..b, f s) ^ 2 ≤ (∫ s in a..b, f s ^ 2) * (b - a) := h4
    _ = (b - a) * ∫ s in a..b, f s ^ 2 := by ring

/-- **Cauchy–Schwarz for a finite sum of slots.** -/
theorem finset_sum_sq_intervalIntegral_le {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ i ∈ S, IntervalIntegrable (F i) volume a b)
    (hF2 : ∀ i ∈ S, IntervalIntegrable (fun s => F i s ^ 2) volume a b) :
    ∑ i ∈ S, (∫ s in a..b, F i s) ^ 2 ≤ (b - a) * ∫ s in a..b, ∑ i ∈ S, (F i s) ^ 2 := by
  calc ∑ i ∈ S, (∫ s in a..b, F i s) ^ 2
      ≤ ∑ i ∈ S, (b - a) * ∫ s in a..b, (F i s) ^ 2 :=
        Finset.sum_le_sum fun i hi => intervalIntegral_sq_le hab (hF i hi) (hF2 i hi)
    _ = (b - a) * ∑ i ∈ S, ∫ s in a..b, (F i s) ^ 2 := by rw [Finset.mul_sum]
    _ = (b - a) * ∫ s in a..b, ∑ i ∈ S, (F i s) ^ 2 := by
        rw [intervalIntegral.integral_finsetSum (fun i hi => hF2 i hi)]

/-- **Cauchy–Schwarz for a doubly indexed finite family of slots.** -/
theorem double_sum_sq_intervalIntegral_le (S T : Finset ℕ) (F : ℕ → ℕ → ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ i ∈ S, ∀ j ∈ T, IntervalIntegrable (F i j) volume a b)
    (hF2 : ∀ i ∈ S, ∀ j ∈ T, IntervalIntegrable (fun s => F i j s ^ 2) volume a b) :
    ∑ i ∈ S, ∑ j ∈ T, (∫ s in a..b, F i j s) ^ 2
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ S, ∑ j ∈ T, (F i j s) ^ 2 := by
  have hstep : ∀ i ∈ S, IntervalIntegrable (fun s => ∑ j ∈ T, (F i j s) ^ 2) volume a b :=
    fun i hi => by
      have h1 := IntervalIntegrable.sum T (f := fun j s => (F i j s) ^ 2)
        (fun j hj => hF2 i hi j hj)
      rwa [show (∑ j ∈ T, fun s => (F i j s) ^ 2) = fun s => ∑ j ∈ T, (F i j s) ^ 2 from
        funext fun s => Finset.sum_apply s T (fun j s => (F i j s) ^ 2)] at h1
  calc ∑ i ∈ S, ∑ j ∈ T, (∫ s in a..b, F i j s) ^ 2
      ≤ ∑ i ∈ S, (b - a) * ∫ s in a..b, ∑ j ∈ T, (F i j s) ^ 2 :=
        Finset.sum_le_sum fun i hi => finset_sum_sq_intervalIntegral_le T (F i) hab
          (fun j hj => hF i hi j hj) (fun j hj => hF2 i hi j hj)
    _ = (b - a) * ∑ i ∈ S, ∫ s in a..b, ∑ j ∈ T, (F i j s) ^ 2 := by rw [Finset.mul_sum]
    _ = (b - a) * ∫ s in a..b, ∑ i ∈ S, ∑ j ∈ T, (F i j s) ^ 2 := by
        rw [intervalIntegral.integral_finsetSum (f := fun i s => ∑ j ∈ T, (F i j s) ^ 2) hstep]

/-- A finite sum of interval-integrable functions is interval-integrable (uncurried form). -/
theorem intervalIntegrable_finsetSum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ) {a b : ℝ}
    (h : ∀ i ∈ S, IntervalIntegrable (F i) volume a b) :
    IntervalIntegrable (fun s => ∑ i ∈ S, F i s) volume a b := by
  have h1 := IntervalIntegrable.sum S (f := F) h
  rwa [show (∑ i ∈ S, F i) = fun s => ∑ i ∈ S, F i s from
    funext fun s => Finset.sum_apply s S F] at h1

/-- The main estimate. -/
theorem HkIntegrand_intervalIntegral_le {α a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {H : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmeas : ∀ (j i : ℕ), j + i ≤ 4 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.uIoc a b,
      |Work.Spaces.mixed j i (H s) z θ| ≤ C)
    (hid : ∀ j i : ℕ, j + i ≤ 4 →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α 4 (H s) z θ := by
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hvol : volume (Set.uIoc a b) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  -- slot integrability, from measurability and the uniform bound on `uIoc a b`
  have hslot : ∀ (j i : ℕ), j + i ≤ 4 →
      IntervalIntegrable (fun s => Work.Spaces.mixed j i (H s) z θ) volume a b := by
    intro j i hji
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol (hmeas j i hji) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    simpa [Real.norm_eq_abs] using hbdd j i hji s hs
  have hslot2 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ c : ℝ,
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
  -- unfolding `HkIntegrand α 4 G z θ` into its two blocks
  have hId : Work.Spaces.HkIntegrand α 4 G z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i G z θ * W) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Work.Spaces.HkIntegrand, hW]
  -- the `D_z`-block
  have hPart1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i G z θ * W) ^ 2)
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range 5,
          (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2 := by
    refine le_of_eq_of_le ?_ (finset_sum_sq_intervalIntegral_le (Finset.range 5)
      (fun i s => Work.Spaces.mixed i 0 (H s) z θ * W) hab ?_ ?_)
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      rw [show Work.Spaces.DzIter i G z θ = ∫ s in a..b, Work.Spaces.mixed i 0 (H s) z θ
        from hid i 0 hi4]
      rw [intervalIntegral.integral_mul_const]
    · intro i hi
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      exact (hslot i 0 hi4).mul_const W
    · intro i hi
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      exact hslot2 i 0 hi4 W
  -- integrability of the mixed slots, in the "`if` inside the square" form
  have hF5 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntervalIntegrable (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ 4
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0)
          = fun s => Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ :=
        funext fun s => ite_eq_left h
      rw [hfe]
      have hij : j + i ≤ 4 := by omega
      exact (hslot j i hij).mul_const _
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) = fun _ => 0 :=
        funext fun s => ite_eq_right h
      rw [hfe]; exact intervalIntegrable_const
  have hF5sq : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntervalIntegrable (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ 4
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
          = fun s => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun s => by rw [ite_eq_left h]
      rw [hfe]
      have hij : j + i ≤ 4 := by omega
      exact hslot2 j i hij _
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) = fun _ => 0 :=
        funext fun s => by rw [ite_eq_right h]; ring
      rw [hfe]; exact intervalIntegrable_const
  -- the mixed block
  have hPart2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
    have hmain := double_sum_sq_intervalIntegral_le (Finset.range 5) (Finset.range 5)
      (fun i j s => if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) hab hF5 hF5sq
    have hL : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (∫ s in a..b, if 1 ≤ i ∧ i + j ≤ 4 then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · have hij : j + i ≤ 4 := by omega
        simp only [ite_eq_left h]
        rw [intervalIntegral.integral_mul_const, ← hid j i hij]
      · simp only [ite_eq_right h]
        simp
    rw [hL]
    exact hmain
  -- the slots of the family `H s` recombine into `HkIntegrand α 4 (H s) z θ`
  have hT : ∀ s : ℝ,
      (∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2
      = Work.Spaces.HkIntegrand α 4 (H s) z θ := by
    intro s
    have h1 : (∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        = ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (H s) z θ * W) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by simp only [Work.Spaces.mixed_zero_right]
    have h2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1, h2, Work.Spaces.HkIntegrand, hW]
  have hT1int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range 5,
      (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2) volume a b :=
    intervalIntegrable_finsetSum (Finset.range 5)
      (fun i s => (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      (fun i hi => by
        have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
        exact hslot2 i 0 hi4 W)
  have hT2int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b :=
    intervalIntegrable_finsetSum (Finset.range 5)
      (fun i s => ∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      (fun i hi => intervalIntegrable_finsetSum (Finset.range 5)
        (fun j s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        (fun j hj => hF5sq i hi j hj))
  have hTint : (∫ s in a..b, ∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      + (∫ s in a..b, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      = ∫ s in a..b, Work.Spaces.HkIntegrand α 4 (H s) z θ := by
    rw [← intervalIntegral.integral_add hT1int hT2int]
    exact intervalIntegral.integral_congr (fun s _ => hT s)
  rw [hId]
  refine le_trans (add_le_add hPart1 hPart2) ?_
  rw [← hTint]
  exact le_of_eq (by ring)

end Work.FTS.StrongEps.E5G
