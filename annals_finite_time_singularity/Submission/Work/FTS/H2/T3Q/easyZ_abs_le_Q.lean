import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Transport3Aux.Z3Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.FTS.H2.Transport3Aux.mx_monomial_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise bound of a `D_z`-slot Leibniz summand, in the interior class

This is the verbatim port of `Work.FTS.H2.Transport3Aux.Z3.TZ_abs_le` from the analytic class
`Work.Spaces.SmoothNbhd` (with `θ` in the closed quadrant `Iθ`) to the interior class
`Work.FTS.LocData.SmoothQuad` (with `θ` in the open quadrant `(0,π/2)`): the only change is
the multiplier bound `Work.Spaces.DzIter_le_WlInf` (whose hypothesis is `SmoothInt`, i.e.
smoothness of the `z`-slices at *every* `θ ∈ Iθ`) replaced by its interior counterpart
`Work.FTS.H2.WPQ.DzIter_le_WlInf` (which needs `θ ∈ (0,π/2)`).  Everything else -- the
`g`-side AM–GM lemmas `abs_dzIter_mul_Whz_le_sqrt`, `abs_mul_le_of_abs_le_sqrt` and the
nonnegativity of `WlInf`, `HkIntegrand` -- is unconditional in `g`. -/

/-- A `D_z`-slot Leibniz summand is bounded pointwise on the open quadrant by
`300 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, for `f` of class `SmoothQuad` with `WlInfMem α 4 f`. -/
theorem TZ_abs_le_Q (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.FTS.LocData.SmoothQuad f) (hwf : Work.Spaces.WlInfMem α 4 f)
    (i k : ℕ) (hi : i ≤ 4) (hd : i + 1 - k ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ| ≤ 300 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  have hI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  rcases Nat.lt_or_ge i k with hlt | hge
  · have hch : i.choose k = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [Work.FTS.H2.Transport3Aux.Z3.TZ, hch]
    simp only [Nat.cast_zero, zero_mul, abs_zero]
    positivity
  have hk4 : k ≤ 4 := by omega
  have hf1 : |Work.Spaces.DzIter k f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
    Work.FTS.H2.WPQ.DzIter_le_WlInf hsf hwf hk4 hz hθ
  have hb1 : |Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    Work.FTS.H2.Transport3Aux.abs_dzIter_mul_Whz_le_sqrt α g hd z θ
  have hb2 : |Work.Spaces.DzIter i g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    Work.FTS.H2.Transport3Aux.abs_dzIter_mul_Whz_le_sqrt α g hi z θ
  have hgm : |(Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ)
      * (Work.Spaces.DzIter i g z θ * Whz z θ)| ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.FTS.H2.Transport3Aux.abs_mul_le_of_abs_le_sqrt hI hb1 hb2
  have hcast : (i.choose k : ℝ) ≤ 16 := by
    have h1 : (i.choose k : ℝ) ≤ ((2:ℕ)^i : ℝ) := by
      exact_mod_cast (Nat.choose_le_two_pow i k)
    have h2 : ((2:ℕ)^i : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hi)
    have h3 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
    linarith
  have hcast0 : (0:ℝ) ≤ (i.choose k : ℝ) := Nat.cast_nonneg _
  have habs : |Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ|
      = (i.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
        * |(Work.Spaces.DzIter (i + 1 - k) g z θ * Whz z θ)
            * (Work.Spaces.DzIter i g z θ * Whz z θ)| := by
    rw [Work.FTS.H2.Transport3Aux.Z3.TZ]
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

/-- `Z3.easyZ α f g` (the `D_z`-slot Leibniz sum of `H4PairInt α (fun z θ => f z θ * D_z g z θ) g`
with the order-five summand `(i,k) = (4,0)` removed) is bounded on the open quadrant by
`7500 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, for `f` of class `SmoothQuad` with `WlInfMem α 4 f`.

The proof is a verbatim port of `Work.FTS.H2.Transport3Aux.Z3Aux.easyZ_abs_le` (with its
per-term helper `TZ_abs_le`), which proves the same statement in the stronger class
`Work.Spaces.SmoothNbhd f` and on the closed quadrant `θ ∈ Iθ`: replace the multiplier bounds
`Work.Spaces.DzIter_le_WlInf (SmoothInt.of_SmoothNbhd hsf)` by
`Work.FTS.H2.WPQ.DzIter_le_WlInf` (interior class), keep the class-free `g`-lemmas
`Work.FTS.H2.Transport3Aux.abs_dzIter_mul_Whz_le_sqrt`, `...abs_mul_le_of_abs_le_sqrt`,
`Work.FTS.H2.Whz_nonneg`, `Work.Spaces.HkIntegrand_nonneg`, and restrict `θ` to
`Set.Ioo 0 (π/2)`.  No knowledge of `g` (beyond `HkIntegrand`) is needed. -/
theorem easyZ_abs_le_Q (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.FTS.LocData.SmoothQuad f) (hwf : Work.Spaces.WlInfMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.H2.Transport3Aux.Z3.easyZ α f g z θ| ≤ 7500 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  set K : ℝ := Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (Work.Spaces.WlInf_nonneg α 4 f hwf)
      (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hinner : ∀ i ∈ Finset.range 5,
      |∑ k ∈ Finset.range (i + 1),
          (if i = 4 ∧ k = 0 then 0 else Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ)|
        ≤ 5 * (300 * K) := by
    intro i hi
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ k ∈ Finset.range (i + 1),
          |(if i = 4 ∧ k = 0 then 0 else Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ)|
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
            have hb := TZ_abs_le_Q α f g hα hα1 hsf hwf i k hi4 hd z hz θ hθ
            calc |Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ|
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
  rw [Work.FTS.H2.Transport3Aux.Z3.easyZ]
  calc |∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
        (if i = 4 ∧ k = 0 then 0 else Work.FTS.H2.Transport3Aux.Z3.TZ α f g i k z θ)|
      ≤ ∑ i ∈ Finset.range 5, (5 * (300 * K)) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hinner)
    _ = 25 * (300 * K) := by
        rw [Finset.sum_const]
        simp only [Finset.card_range, nsmul_eq_mul]
        ring
    _ = 7500 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [hK]; ring

end Work.FTS.H2.T3Q
