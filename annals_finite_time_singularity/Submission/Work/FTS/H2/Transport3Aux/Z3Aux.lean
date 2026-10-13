/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for `good_pointwise_z3`: sum bookkeeping

This file develops the bookkeeping lemmas for
`Work.FTS.H2.Transport3Aux.good_pointwise_z3`:
the splitting of a double `range`-sum with an indicator at a single index, and the
identification `easyM - Mismatchz = Msurv` (the cancellation of the "mismatch" family
`a = i` of the mixed slots against `Mismatchz`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Defs
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.FTS.H2.Transport3Aux.mx_monomial_bound
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux
namespace Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Peeling a single index out of a double `range`-sum -/

/-- `∑_{i<5} ∑_{k≤i} (if (i,k) = (4,0) then X i k else 0) = X 4 0`. -/
theorem sum_pair_peel (X : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
        (if i = 4 ∧ k = 0 then X i k else 0)) = X 4 0 := by
  have h4 : (4 : ℕ) ∈ Finset.range 5 := Finset.mem_range.mpr (by norm_num)
  have h0 : (0 : ℕ) ∈ Finset.range (4 + 1) := Finset.mem_range.mpr (by norm_num)
  rw [Finset.sum_eq_single 4]
  · rw [Finset.sum_congr rfl (fun k hk => ?_), Finset.sum_ite_eq' (Finset.range (4 + 1)) 0
      (fun k => X 4 k), if_pos h0]
    by_cases h : k = 0
    · rw [if_pos (by simp [h]), if_pos h]
    · rw [if_neg (by simp [h]), if_neg h]
  · intro i hi hi4
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    exact fun h => hi4 h.1
  · intro h
    exact absurd h4 h

/-- Splitting off the `(4,0)` summand of the `D_z`-slot double sum. -/
theorem z_split (X : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), X i k)
      = X 4 0 + ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
          (if i = 4 ∧ k = 0 then 0 else X i k) := by
  have hpt : ∀ i k, X i k
      = (if i = 4 ∧ k = 0 then X i k else 0) + (if i = 4 ∧ k = 0 then 0 else X i k) := by
    intro i k
    by_cases h : i = 4 ∧ k = 0 <;> simp [h]
  calc (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), X i k)
      = ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
          ((if i = 4 ∧ k = 0 then X i k else 0) + (if i = 4 ∧ k = 0 then 0 else X i k)) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
        exact hpt i k
    _ = (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), (if i = 4 ∧ k = 0 then X i k else 0))
          + ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
              (if i = 4 ∧ k = 0 then 0 else X i k) := by
        simp only [Finset.sum_add_distrib]
    _ = X 4 0 + ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
          (if i = 4 ∧ k = 0 then 0 else X i k) := by
        rw [sum_pair_peel]

/-- Peeling the `(0,0)` summand out of a double `range`-sum. -/
theorem sum_zero_zero_peel (i j : ℕ) (X : ℕ → ℕ → ℝ) :
    (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if a = 0 ∧ b = 0 then X a b else 0)) = X 0 0 := by
  have h0i : (0 : ℕ) ∈ Finset.range (i + 1) := Finset.mem_range.mpr (Nat.succ_pos i)
  have h0j : (0 : ℕ) ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.succ_pos j)
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_congr rfl (fun b hb => ?_),
      Finset.sum_ite_eq' (Finset.range (j + 1)) 0 (fun b => X 0 b), if_pos h0j]
    by_cases h : b = 0
    · rw [if_pos (by simp [h]), if_pos h]
    · rw [if_neg (by simp [h]), if_neg h]
  · intro a ha ha0
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg]
    exact fun h => ha0 h.1
  · intro h
    exact absurd h0i h

/-- Splitting the `(0,0)` summand out of the mixed double sum of a slot. -/
theorem mx_split (i j : ℕ) (X : ℕ → ℕ → ℝ) :
    (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), X a b)
      - (if i + j = 4 then X 0 0 else 0)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else X a b) := by
  by_cases h4 : i + j = 4
  · rw [if_pos h4]
    have hpt : ∀ a b, X a b
        = (if a = 0 ∧ b = 0 ∧ i + j = 4 then X a b else 0)
          + (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else X a b) := by
      intro a b
      by_cases h : a = 0 ∧ b = 0 <;> simp [h, h4]
    have hsum : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), X a b)
        = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then X a b else 0))
          + ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else X a b) := by
      calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), X a b)
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((if a = 0 ∧ b = 0 ∧ i + j = 4 then X a b else 0)
                + (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else X a b)) := by
            refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
            exact hpt a b
        _ = _ := by
            simp only [Finset.sum_add_distrib]
    have hpeel : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then X a b else 0)) = X 0 0 := by
      rw [Finset.sum_congr rfl (fun a ha => ?_), sum_zero_zero_peel i j X]
      refine Finset.sum_congr rfl fun b hb => ?_
      by_cases h : a = 0 ∧ b = 0
      · rw [if_pos ⟨h.1, h.2, h4⟩, if_pos h]
      · rw [if_neg (fun hh => h ⟨hh.1, hh.2.1⟩), if_neg h]
    rw [hsum, hpeel]
    ring
  · rw [if_neg h4]
    refine Eq.trans (sub_zero _) ?_
    refine (Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_).symm
    rw [if_neg (fun h => h4 h.1)]

/-! ## The slot cancellation of the mismatch family -/

/-- Subtracting the mismatch part of the slot `(i,j)` from the mixed Leibniz sum of the
slot (`a` over `range (i+1)`, the order-five `(0,0)` summand removed when `i + j = 4`)
leaves the surviving sum over `a ∈ range i`. -/
theorem easyM_sub_Mismatchz_slot (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j : ℕ) (hi : 1 ≤ i)
    (z θ : ℝ) :
    (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ))
      - MismatchPart α f g i j z θ
    = ∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
        (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ) := by
  rw [Finset.sum_range_succ (fun a => ∑ b ∈ Finset.range (j + 1),
    (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) i]
  have hai : (∑ b ∈ Finset.range (j + 1),
      (if i + j = 4 ∧ i = 0 ∧ b = 0 then 0 else TM α f g i j i b z θ))
      = MismatchPart α f g i j z θ := by
    rw [MismatchPart]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_neg (by omega : ¬ (i + j = 4 ∧ i = 0 ∧ b = 0)), TM_mismatch]
  rw [hai]
  ring


/-! ## The order bound of the surviving mixed blocks -/

/-- The surviving mixed summands (`a < i`, no order-five case) have `1 ≤ i - a` and total
`g`-block order `(i - a) + (j - b + 1) ≤ 4`. -/
theorem mx_index_le (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a < i) (hb : b ≤ j)
    (hfive : ¬ (i + j = 4 ∧ a = 0 ∧ b = 0)) :
    1 ≤ i - a ∧ (i - a) + (j - b + 1) ≤ 4 := by
  constructor
  · omega
  · by_cases hab : a + b = 0
    · obtain ⟨ha0, hb0⟩ := Nat.add_eq_zero.mp hab
      have hfive' : ¬ (i + j = 4) := fun h => hfive ⟨h, ha0, hb0⟩
      have hij3 : i + j ≤ 3 := by omega
      omega
    · have h1 : 1 ≤ a + b := by omega
      omega

/-! ## The pointwise bounds of the Leibniz summands -/

/-- A `D_z`-slot Leibniz summand is bounded pointwise by
`300 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`. -/
theorem TZ_abs_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.Spaces.SmoothNbhd f) (hwf : Work.Spaces.WlInfMem α 4 f)
    (i k : ℕ) (hi : i ≤ 4) (hd : i + 1 - k ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |TZ α f g i k z θ| ≤ 300 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  have hI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  rcases Nat.lt_or_ge i k with hlt | hge
  · have hch : i.choose k = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [TZ, hch]
    simp only [Nat.cast_zero, zero_mul, abs_zero]
    positivity
  have hk4 : k ≤ 4 := by omega
  have hf1 : |Work.Spaces.DzIter k f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
    Work.Spaces.DzIter_le_WlInf hα (Work.Spaces.SmoothInt.of_SmoothNbhd hsf) hwf hk4 hz hθ
  have hb1 : |Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    abs_dzIter_mul_Whz_le_sqrt α g hd z θ
  have hb2 : |Work.Spaces.DzIter i g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    abs_dzIter_mul_Whz_le_sqrt α g hi z θ
  have hgm : |(Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ)
      * (Work.Spaces.DzIter i g z θ * Whz z θ)| ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    abs_mul_le_of_abs_le_sqrt hI hb1 hb2
  have hcast : (i.choose k : ℝ) ≤ 16 := by
    have h1 : (i.choose k : ℝ) ≤ ((2:ℕ)^i : ℝ) := by
      exact_mod_cast (Nat.choose_le_two_pow i k)
    have h2 : ((2:ℕ)^i : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hi)
    have h3 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
    linarith
  have hcast0 : (0:ℝ) ≤ (i.choose k : ℝ) := Nat.cast_nonneg _
  have habs : |TZ α f g i k z θ|
      = (i.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
        * |(Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ)
            * (Work.Spaces.DzIter i g z θ * Whz z θ)| := by
    rw [TZ]
    simp only [abs_mul, abs_of_nonneg hcast0]
    ring
  rw [habs]
  have hstep : (i.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
        * |(Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ)
            * (Work.Spaces.DzIter i g z θ * Whz z θ)|
      ≤ 16 * (15 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ :=
    mul_le_mul (mul_le_mul hcast hf1 (abs_nonneg _) (by positivity)) hgm (abs_nonneg _)
      (by positivity)
  refine le_trans hstep ?_
  nlinarith [hW, hI]

/-- A surviving mixed-slot Leibniz summand is bounded pointwise by
`9000 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`. -/
theorem TM_abs_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.Spaces.SmoothNbhd f) (hwf : Work.Spaces.WlInfMem α 4 f)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a < i) (hb : b ≤ j)
    (hfive : ¬ (i + j = 4 ∧ a = 0 ∧ b = 0)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |TM α f g i j a b z θ| ≤ 9000 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  have hI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  obtain ⟨hr, hrp⟩ := mx_index_le i j a b hi hij ha hb hfive
  have hab : a + b ≤ 4 := by omega
  have hf1 : |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f :=
    abs_mixed_le_WlInf hα hα1 hsf hwf hab hz hθ
  have hgm : |Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    abs_mixed_pair_mul_weight_le_HkIntegrand α hα g hr hrp hi hij hθ
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθ
  have hi4 : i ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hcast : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 := by
    have h1 : (i.choose a : ℝ) ≤ 16 := by
      have h := Nat.choose_le_two_pow i a
      have h2 : ((2:ℕ)^i : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hi4)
      have h3 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
      have h4 : (i.choose a : ℝ) ≤ ((2:ℕ)^i : ℝ) := by exact_mod_cast h
      linarith
    have h2 : (j.choose b : ℝ) ≤ 16 := by
      have h := Nat.choose_le_two_pow j b
      have h3 : ((2:ℕ)^j : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hj4)
      have h4 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
      have h5 : (j.choose b : ℝ) ≤ ((2:ℕ)^j : ℝ) := by exact_mod_cast h
      linarith
    nlinarith [h1, h2, Nat.cast_nonneg (α := ℝ) (i.choose a),
      Nat.cast_nonneg (α := ℝ) (j.choose b)]
  have hsq : Wm α z θ * Wm α z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← sq]
    exact (Whz_Wm_sq α hα z θ hθ).2
  have hG : |Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
      * (Wm α z θ * Wm α z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [hsq]
    exact hgm
  have habs : |TM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ)) := by
    rw [TM]
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.choose a)),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (j.choose b)), abs_of_nonneg hWmnn]
    ring
  rw [habs]
  have hstep : ((i.choose a : ℝ) * (j.choose b : ℝ)) * |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ))
      ≤ 256 * (30 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ :=
    mul_le_mul (mul_le_mul hcast hf1 (abs_nonneg _) (by positivity)) hG (by positivity)
      (by positivity)
  refine le_trans hstep ?_
  nlinarith [hW, hI]

/-! ## The expansion of the `D_z`-pairing, and the cancellation of `Mismatchz` -/

/-- `H4PairInt α (f D_z g) g - Badz = easyZ + easyM`. -/
theorem H4PairInt_sub_Badz_eq (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
          - Work.FTS.H2.Badz α f g z θ
        = easyZ α f g z θ + easyM α f g z θ := by
  intro z hz θ hθ
  have hZ : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ * Whz z θ)
          * (Work.Spaces.DzIter i g z θ * Whz z θ))
      = ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [DzIter_mul_Dz_eq i f g hf hg z hz θ hθ]
    simp only [Finset.sum_mul, TZ]
  have hM : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ * Wm α z θ)
            * (Work.Spaces.mixed j i g z θ * Wm α z θ)
        else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), TM α f g i j a b z θ
          else 0) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc, mixed_mul_Dz_eq j i f g hf hg z hz θ hθ]
      simp only [Finset.sum_mul, TM]
    · rw [if_neg hc, if_neg hc]
  have hBsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * Work.Spaces.Dz (Work.Spaces.mixed j i g) z θ
            * Work.Spaces.mixed j i g z θ * Wm α z θ ^ 2
        else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j = 4
    · rw [if_pos hc, if_pos hc, TM_zero_zero]
    · rw [if_neg hc, if_neg hc]
  have hZsplit : (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ)
      = TZ α f g 4 0 z θ + easyZ α f g z θ := by
    rw [z_split, easyZ]
  have hMsp : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), TM α f g i j a b z θ)
        else 0))
      - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0))
      = easyM α f g z θ := by
    rw [easyM, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · have hx : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              TM α f g i j a b z θ) else 0) = _ := if_pos hc
      have hy0 : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0) = _ :=
        if_pos hc
      rw [hx, hy0]
      by_cases h4 : i + j = 4
      · rw [if_pos ⟨hc.1, h4⟩]
        have h := mx_split i j (fun a b => TM α f g i j a b z θ)
        rw [if_pos h4] at h
        exact h
      · rw [if_neg (fun hh => h4 hh.2), sub_zero]
        refine (Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_).symm
        rw [if_neg (by omega : ¬ (i + j = 4 ∧ a = 0 ∧ b = 0))]
    · have hx : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              TM α f g i j a b z θ) else 0) = 0 := if_neg hc
      have hy0 : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0) = 0 :=
        if_neg hc
      have hy : (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0) = 0 :=
        if_neg (fun hh => hc ⟨hh.1, by omega⟩)
      rw [hx, hy0, hy, sub_zero]
  rw [Work.FTS.H2.H4PairInt, Work.FTS.H2.Badz, ← TZ_four_zero α f g z θ, hBsum, hZ, hM]
  exact (show (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ)
      + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), TM α f g i j a b z θ else 0))
      - (TZ α f g 4 0 z θ
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0))
      = easyZ α f g z θ + easyM α f g z θ from by
    linear_combination hZsplit + hMsp)

/-- `easyM - Mismatchz = Msurv`. -/
theorem easyM_sub_Mismatchz (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    easyM α f g z θ - Mismatchz α f g z θ = Msurv α f g z θ := by
  rw [easyM, Mismatchz_eq, Msurv, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hc : 1 ≤ i ∧ i + j ≤ 4
  · rw [if_pos hc, if_pos hc, if_pos hc]
    exact easyM_sub_Mismatchz_slot α f g i j hc.1 z θ
  · rw [if_neg hc, if_neg hc, if_neg hc, sub_zero]

/-! ## The aggregate bounds for `easyZ` and `Msurv` -/

/-- The `D_z`-slot part `easyZ` of the good expansion is bounded by
`7500 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`. -/
theorem easyZ_abs_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.Spaces.SmoothNbhd f) (hwf : Work.Spaces.WlInfMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |easyZ α f g z θ| ≤ 7500 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  set K : ℝ := Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (Work.Spaces.WlInf_nonneg α 4 f hwf)
      (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hinner : ∀ i ∈ Finset.range 5,
      |∑ k ∈ Finset.range (i + 1), (if i = 4 ∧ k = 0 then 0 else TZ α f g i k z θ)|
        ≤ 5 * (300 * K) := by
    intro i hi
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ k ∈ Finset.range (i + 1), |(if i = 4 ∧ k = 0 then 0 else TZ α f g i k z θ)|
        ≤ ∑ k ∈ Finset.range (i + 1), (300 * K) := by
          refine Finset.sum_le_sum fun k hk => ?_
          by_cases h : i = 4 ∧ k = 0
          · rw [if_pos h, abs_zero]
            exact mul_nonneg (by norm_num) hK0
          · rw [if_neg h]
            have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hd : i + 1 - k ≤ 4 := by
              rcases Nat.lt_or_ge i 4 with hlt | hge
              · omega
              · have hi4' : i = 4 := by omega
                have hk0 : k ≠ 0 := fun hk0 => h ⟨hi4', hk0⟩
                omega
            have hb := TZ_abs_le α f g hα hα1 hsf hwf i k hi4 hd z hz θ hθ
            calc |TZ α f g i k z θ|
                ≤ 300 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := hb
              _ = 300 * K := by rw [hK]; ring
      _ = ((i : ℝ) + 1) * (300 * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 5 * (300 * K) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact_mod_cast (by omega : i + 1 ≤ 5)
  rw [easyZ]
  calc |∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
        (if i = 4 ∧ k = 0 then 0 else TZ α f g i k z θ)|
      ≤ ∑ i ∈ Finset.range 5, (5 * (300 * K)) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hinner)
    _ = 25 * (300 * K) := by
        rw [Finset.sum_const]
        simp only [Finset.card_range, nsmul_eq_mul]
        ring
    _ = 7500 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [hK]; ring

/-- The surviving mixed part `Msurv` of the good expansion is bounded by
`4500000 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`. -/
theorem Msurv_abs_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.Spaces.SmoothNbhd f) (hwf : Work.Spaces.WlInfMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Msurv α f g z θ| ≤ 4500000 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  set K : ℝ := Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (Work.Spaces.WlInf_nonneg α 4 f hwf)
      (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hslot : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      |(if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0)|
        ≤ 180000 * K := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ a ∈ Finset.range i,
            |∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)|
          ≤ ∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1), (9000 * K) := by
            refine Finset.sum_le_sum fun a ha => ?_
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum fun b hb => ?_
            by_cases h5 : i + j = 4 ∧ a = 0 ∧ b = 0
            · rw [if_pos h5, abs_zero]
              exact mul_nonneg (by norm_num) hK0
            · rw [if_neg h5]
              have ha' : a < i := Finset.mem_range.mp ha
              have hb' : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
              have h := TM_abs_le α f g hα hα1 hsf hwf i j a b hc.1 hc.2 ha' hb' h5 z hz θ hθ
              calc |TM α f g i j a b z θ|
                  ≤ 9000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := h
                _ = 9000 * K := by rw [hK]; ring
        _ = ((i : ℝ) * ((j : ℝ) + 1)) * (9000 * K) := by
            rw [Finset.sum_const, Finset.sum_const]
            simp only [Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ 180000 * K := by
            have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hj4 : j ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have h1 : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
            have h2 : ((j : ℝ) + 1) ≤ 5 := by exact_mod_cast (by omega : j + 1 ≤ 5)
            have h3 : (i : ℝ) * ((j : ℝ) + 1) ≤ 20 :=
              by nlinarith [Nat.cast_nonneg (α := ℝ) i]
            nlinarith [hK0, h3]
    · rw [if_neg hc, abs_zero]
      exact mul_nonneg (by norm_num) hK0
  rw [Msurv]
  calc |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0)|
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (180000 * K) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun j hj => hslot i hi j hj
    _ = 25 * (180000 * K) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_range, nsmul_eq_mul]
        ring
    _ = 4500000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [hK]; ring
