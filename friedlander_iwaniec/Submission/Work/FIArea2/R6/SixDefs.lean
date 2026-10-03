/-
# `FIArea2/R6/SixDefs.lean` — the §9 pair sums at the *sector-scale* axis threshold

The frozen `Defs6.IsAxisFree Pa z` is `Pa.ϑ·√(Pa.N) < |Re z| ∧ Pa.ϑ·√(Pa.N) < |Im z|` — the
paper's §5 sector-scale exclusion `|φ mod π/2| > πϑ` (a point of a remaining polar box has
`|Re z|, |Im z| ≳ ϑ√N`).  The §9 chain of `Submission/Work/FIArea2/` (`Sec9AggDefs.sec9Core`,
`Count.sec9_Z_bound`, `R6.Aggregate6`) was wired at the *stronger* threshold `√(ϑN)` (the paper's
sloppily-written "`√ϑ√N < |r|, |s|`"), so it does not cover the pairs with
`ϑ√N < |Re z| ≤ √(ϑN)` that the round-6 coefficient family `IsBetaCoeff6` is allowed to carry.

This module mirrors the §9 objects at the sector-scale threshold `Work.FITop4.IsAxisFree`, so that
the §9 aggregate (`(9.10)`, error `≍ ϑ⁻¹τ²N²(log N)^b`) can be proved for the coefficients the
round-6 contract actually uses.  The mirror of the *per-frequency* bound `Z(h₁,h₂) ≲
ϑ^{-1}(log N)^8 U` at this threshold is `Work.FIArea2.Count.sec9_Z_bound_six`; the arithmetic of
the §9 count is unchanged, only the conversion `(2R+1)/|r₁| ≤ 8√N/thr` changes from
`8ϑ^{-1/2}` (at `thr = √(ϑN)`) to `8ϑ^{-1}` (at `thr = ϑ√N`), which is exactly the `ϑ^{-1}` of the
paper's (9.10).
-/
import Mathlib
import Submission.Work.FIArea2.Sec9AggDefs
import Submission.Work.FIArea2.Sec9SwapDefs
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea2.summable_uniform_weight

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §9 pair weight `τ(Δ)³|Δ|^{-1}` at the **sector-scale** axis threshold
`Work.FITop4.IsAxisFree` (the predicate carried by `Defs6.IsBetaCoeff6`). -/
def sec9Core6 (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FITop4.IsAxisFree Pa z1
      ∧ Work.FITop4.IsAxisFree Pa z2 then
    (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
      / (Work.FIPlan.absDelta z1 z2 : ℝ))
  else 0

/-- The per-frequency sum (9.5) at the sector-scale threshold. -/
def sec9Zsum6 (Pa : Work.FITop.Params) (h1 h2 : ℤ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FITop4.IsAxisFree Pa z1
        ∧ Work.FITop4.IsAxisFree Pa z2 then
      (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
        / (Work.FIPlan.absDelta z1 z2 : ℝ)) * (gcdDelta z1 z2 h1 h2 : ℝ)
    else 0)

/-- The coefficient-free §9 pair sum (9.5), sector-scale threshold. -/
def sec9Psum06 (Pa : Work.FITop.Params) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    sec9Core6 Pa z1 z2 * sec9Usum Pa z1 z2

/-- The §9 pair sum (9.5) with coefficients, sector-scale threshold. -/
def sec9Psum6 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    ‖β z1‖ * ‖β z2‖ * sec9Core6 Pa z1 z2 * sec9Usum Pa z1 z2

/-! ## Elementary API -/

lemma sec9Core6_nonneg (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) :
    0 ≤ sec9Core6 Pa z1 z2 := by
  unfold sec9Core6
  split_ifs with h
  · positivity
  · exact le_refl 0

lemma sec9Zsum6_eq (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    sec9Zsum6 Pa h1 h2
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          sec9Core6 Pa z1 z2 * (gcdDelta z1 z2 h1 h2 : ℝ) := by
  unfold sec9Zsum6 sec9Core6
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  by_cases h : Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FITop4.IsAxisFree Pa z1
      ∧ Work.FITop4.IsAxisFree Pa z2 <;> simp [h]

lemma sec9Zsum6_nonneg (Pa : Work.FITop.Params) (h1 h2 : ℤ) : 0 ≤ sec9Zsum6 Pa h1 h2 := by
  rw [sec9Zsum6_eq]
  refine Finset.sum_nonneg fun z1 _ => Finset.sum_nonneg fun z2 _ => ?_
  exact mul_nonneg (sec9Core6_nonneg Pa z1 z2) (Nat.cast_nonneg _)

/-- The §9 pair sum is at most `τ²` times its coefficient-free version. -/
lemma sec9Psum6_le_of_beta_bound (Pa : Work.FITop.Params) (β : GaussianInt → ℂ)
    (hβ : ∀ z : GaussianInt, ‖β z‖ ≤ Pa.τ) :
    sec9Psum6 Pa β ≤ Pa.τ ^ (2 : ℕ) * sec9Psum06 Pa := by
  unfold sec9Psum6 sec9Psum06
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun z1 _ => ?_
  refine Finset.sum_le_sum fun z2 _ => ?_
  have hb1 := hβ z1
  have hb2 := hβ z2
  have hτ : 0 ≤ Pa.τ := le_trans (norm_nonneg _) (hβ 0)
  have hb12 : ‖β z1‖ * ‖β z2‖ ≤ Pa.τ ^ (2 : ℕ) := by
    calc ‖β z1‖ * ‖β z2‖ ≤ Pa.τ * Pa.τ := mul_le_mul hb1 hb2 (norm_nonneg _) hτ
      _ = Pa.τ ^ (2 : ℕ) := by ring
  have hu := Work.FIArea2.sec9Usum_nonneg Pa z1 z2
  calc ‖β z1‖ * ‖β z2‖ * sec9Core6 Pa z1 z2 * sec9Usum Pa z1 z2
      = (‖β z1‖ * ‖β z2‖) * (sec9Core6 Pa z1 z2 * sec9Usum Pa z1 z2) := by ring
    _ ≤ (Pa.τ ^ (2 : ℕ)) * (sec9Core6 Pa z1 z2 * sec9Usum Pa z1 z2) :=
        mul_le_mul_of_nonneg_right hb12 (mul_nonneg (sec9Core6_nonneg Pa z1 z2) hu)

/-! ## The interchange of the `h`-sum with the pair sum, sector-scale threshold -/

/-- The integrand of the §9 swap at the sector-scale threshold. -/
def sec9Swap6 (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) (h : ℤ × ℤ) : ℝ :=
  sec9Core6 Pa z1 z2 *
    (if h = (0, 0) then 0 else (gcdDelta z1 z2 h.1 h.2 : ℝ) * sec9Uwt Pa h.1 h.2)

lemma sec9Core6_eq_zero_of_absDelta_eq_zero (Pa : Work.FITop.Params) {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) : sec9Core6 Pa z1 z2 = 0 := by
  unfold sec9Core6
  rw [h]
  simp

lemma summable_sec9Swap6 (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) :
    Summable (fun h : ℤ × ℤ => sec9Swap6 Pa z1 z2 h) := by
  by_cases hD : Work.FIPlan.Delta z1 z2 = 0
  · have h0 : Work.FIPlan.absDelta z1 z2 = 0 := by
      unfold Work.FIPlan.absDelta; rw [hD]; simp
    have hc0 : sec9Core6 Pa z1 z2 = 0 := sec9Core6_eq_zero_of_absDelta_eq_zero Pa h0
    refine (summable_zero).congr fun h => ?_
    simp [sec9Swap6, hc0]
  · have hsum := Work.FIArea2.summable_uniform_weight z1 z2 hD
      (Work.FIPlan.Hscale Pa.M Pa.N) (Work.FIArea2.Hscale_pos Pa)
    refine (hsum.mul_left (sec9Core6 Pa z1 z2)).congr fun h => ?_
    by_cases hh : h = (0, 0)
    · simp [sec9Swap6, hh]
    · simp only [sec9Swap6, sec9Uwt, if_neg hh]
      ring

theorem sec9Sum_product6 (Pa : Work.FITop.Params) (h : ℤ × ℤ) :
    (∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa), sec9Swap6 Pa p.1 p.2 h)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, sec9Swap6 Pa z1 z2 h :=
  Finset.sum_product _ _ (fun p : GaussianInt × GaussianInt => sec9Swap6 Pa p.1 p.2 h)

theorem sec9_tsum_swap6 (Pa : Work.FITop.Params) :
    (∑' h : ℤ × ℤ, ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
        sec9Swap6 Pa p.1 p.2 h)
      = ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          ∑' h : ℤ × ℤ, sec9Swap6 Pa p.1 p.2 h := by
  refine Summable.tsum_finsetSum (L := SummationFilter.unconditional (ℤ × ℤ))
    (s := (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa))
    (f := fun p (h : ℤ × ℤ) => sec9Swap6 Pa p.1 p.2 h) ?_
  intro p _
  exact summable_sec9Swap6 Pa p.1 p.2

/-! ## The coprimality and `τ₃` weights of the (10.6)/(10.7) pair sum -/

/-- The coprimality indicator of `ℤ[i]` as a real number (so that pair sums can be written without
a `Decidable` instance for the classical predicate). -/
def copInd (z1 z2 : GaussianInt) : ℝ := if Work.FIPlan.GaussCoprime z1 z2 then 1 else 0

/-- The 3-fold divisor function `τ₃(n) = Σ_{d | n} τ(n/d)`, with the convention `τ₃ 0 = 1`
(the paper's (10.6) weight; the convention makes the (10.7) statement unconditional). -/
def tau3 (n : ℕ) : ℕ := if n = 0 then 1 else ∑ d ∈ n.divisors, (n / d).divisors.card

lemma copInd_nonneg (z1 z2 : GaussianInt) : 0 ≤ copInd z1 z2 := by
  unfold copInd; split <;> norm_num

lemma copInd_le_one (z1 z2 : GaussianInt) : copInd z1 z2 ≤ 1 := by
  unfold copInd; split <;> norm_num

lemma one_le_tau3 (n : ℕ) : 1 ≤ tau3 n := by
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [tau3]
  · rw [tau3, if_neg h]
    have hmem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr h
    have := Finset.single_le_sum (f := fun d => (n / d).divisors.card)
        (fun d _ => Nat.zero_le _) hmem
    rw [Nat.div_one] at this
    exact le_trans (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr h⟩) this

end

end Work.FIArea2.R6
