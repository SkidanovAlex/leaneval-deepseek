/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "good" part of the `D_θ`-pairing, and its Leibniz summands

This file fixes the vocabulary used by the proof of
`Work.FTS.H2.Transport3Aux.good_contribution_theta`.

The object of study is the *good* part of the integrand of the flat `ℋ⁴`-pairing
`H4PairInt α (fun z θ => f z θ * D_θ g z θ) g`, i.e. the pairing integrand with the
exceptional part `Badθ α f g` -- the summands of the Leibniz expansion in which all
four derivatives fall on `g` -- removed:

  `GoodInt α f g z θ = H4PairInt α (fun z θ => f z θ * D_θ g z θ) g z θ - Badθ α f g z θ`.

Expanding `H4PairInt` by the Leibniz rules `Spaces.DzIter_mul` (the `D_z`-slots) and
`Spaces.mixed_mul_eq` (the mixed slots) shows that `GoodInt` is the finite sum
`EasySum` of the terms

* `xD f g i b`  (`0 ≤ i ≤ 4`, `0 ≤ b ≤ i`), the `(i,b)`-th `D_z`-slot Leibniz summand,
* `yM α f g i j a b` (`1 ≤ i`, `i + j ≤ 4`, `a ≤ i`, `b ≤ j`), the mixed-slot summand,

with the five terms in which all four derivatives fall on `g` removed: the `(i,b) = (4,0)`
`D_z`-slot term (resp. the `(a,b) = (0,0)` mixed-slot term when `i + j = 4`).  In each of the
remaining terms either a derivative falls on `f` (bounded by `|f|_{𝒲^{4,∞}}`) or the two
`g`-blocks have total order `≤ 4`, so that the term is bounded pointwise by
`C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false

/-- The "good" part of the `D_θ`-pairing integrand: the flat `ℋ⁴`-pairing of
`u = f · D_θ g` with `g`, with the exceptional part `Badθ` (the summands in which all
derivatives fall on `g`) removed. -/
def GoodInt (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ - Badθ α f g z θ

/-- The `(i,b)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`:
`binom(i,b) · D_z^b f · D_z^{i-b}(D_θ g) · D_z^i g · Whz²`. -/
def xD (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) : ℝ :=
  (i.choose b : ℝ) * (Work.Spaces.DzIter b f z θ * Work.Spaces.mixed (i - b) 1 g z θ
    * Work.Spaces.DzIter i g z θ * (Whz z θ) ^ 2)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`:
`binom(i,a) binom(j,b) · D_z^b D_θ^a f · D_z^{j-b} D_θ^{i-a+1} g · D_z^j D_θ^i g · Wm²`. -/
def yM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((i.choose a : ℝ) * (j.choose b : ℝ)) *
    (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a + 1) g z θ
      * Work.Spaces.mixed j i g z θ * (Wm α z θ) ^ 2)

/-- The explicit finite sum form of the good part: all the Leibniz summands of
`H4PairInt α (f · D_θ g) g` except the five in which all four derivatives fall on `g`. -/
def EasySum (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
      if i = 4 ∧ b = 0 then 0 else xD f g i b z θ)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else yM α f g i j a b z θ)
          else 0)

/-- The pointwise majorant of `GoodInt`: the sum of the absolute values of the Leibniz
summands appearing in `EasySum`. -/
def EasyMajor (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
      if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
          else 0)

/-! ## Elementary rewriting and comparison lemmas

The lemmas below are the small facts that the expansion of `GoodInt` (in which the
`D_θ`-derivative hidden in `xD`, `yM` has to commute with the `D_z`-iterates) and the
term-by-term bound of `EasySum` (in which the `η`-weight `Whz` has to be compared with
the `γ`-weight `Wm`) repeatedly need. -/

/-- The `D_θ`-iterate of `D_θ g` is the next iterate of `g`: `D_z^jD_θ^i(D_θ g) =
D_z^jD_θ^{i+1} g`. -/
theorem mixed_Dth (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth g) = Work.Spaces.mixed j (i + 1) g := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dth g))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g)
  rw [show Work.Spaces.Dth g = Work.Spaces.DthIter 1 g from rfl,
    Work.Spaces.DthIter_add_right i 1 g]

/-- A single `D_θ` may be moved across any iterate of `D_z`: `D_z^jD_θ(D_θ^ig)` is
`D_θ(D_z^jD_θ^ig)`. -/
theorem Dth_mixed_eq_mixed {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) (j i : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (Work.Spaces.mixed j i g) z θ
      = Work.Spaces.mixed j (i + 1) g z θ := by
  have h := Work.Spaces.Dth_DzIter_comm_eqOn (Work.Spaces.SmoothNbhd.DthIter hg i) j
    (Work.Spaces.mem_nbhU hz hθ)
  simpa only [Function.uncurry, Work.Spaces.mixed, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero] using h

/-- A single `D_θ` may be moved across any iterate of `D_z`:
`D_θ(D_z^j g) = D_z^j(D_θ g)`. -/
theorem Dth_DzIter_eq_mixed {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) (j : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (Work.Spaces.DzIter j g) z θ = Work.Spaces.mixed j 1 g z θ := by
  have h := Work.Spaces.Dth_DzIter_comm_eqOn hg j (Work.Spaces.mem_nbhU hz hθ)
  simpa only [Function.uncurry, Work.Spaces.mixed, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero] using h

/-- On the closed quadrant the `η`-weight is dominated by the `γ`-weight:
`Whz z θ ≤ Wm α z θ`. -/
theorem Whz_le_Wm {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Whz z θ ≤ Wm α z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hγη : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    have h2 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    linarith
  have hw : 0 ≤ Work.Spaces.w z := by simp only [Work.Spaces.w]; positivity
  have hWhz : Whz z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Whz, div_eq_mul_inv, Real.rpow_neg hs0]
  have hWm : Wm α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Wm, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hWhz, hWm]
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta / 2) ≠ 0),
      Real.zero_rpow (by
        intro hh
        have := Work.Spaces.gam_pos hα
        linarith)]
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)) hw

/-- Every mixed derivative `D_z^bD_θ^a f` of total order at most `4` of a `𝒲^{4,∞}`-function
is bounded by `30 |f|_{𝒲^{4,∞}}`. -/
theorem abs_mixed_le_WlInf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (hab : a + b ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hmem
  have hI : Work.Spaces.SmoothInt f := Work.Spaces.SmoothInt.of_SmoothNbhd hf
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
          Work.Spaces.DzIter_le_WlInf hα hI hmem (by omega) hz hθ
      _ ≤ 30 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b a f z θ|
        ≤ 15 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.Spaces.mixed_le_WlInf hα hI hmem ha hab hz hθ
      _ ≤ 15 * (Work.Spaces.WlInf α 4 f * 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 30 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The `g`-slot bounds -/


/-- The weighted pure `D_z`-block is bounded by the square root of the `ℋ⁴`-integrand. -/
theorem abs_dzIter_mul_Whz_le_sqrt (α : ℝ) (g : ℝ → ℝ → ℝ)
    {i : ℕ} (hi : i ≤ 4) (z θ : ℝ) :
    |Work.Spaces.DzIter i g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
  Real.abs_le_sqrt (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)

/-- The weighted mixed block (`i ≥ 1`) is bounded by the square root of the
`ℋ⁴`-integrand. -/
theorem abs_mixed_mul_Wm_le_sqrt (α : ℝ) (g : ℝ → ℝ → ℝ)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) (z θ : ℝ) :
    |Work.Spaces.mixed j i g z θ * Wm α z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
  Real.abs_le_sqrt (Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)

/-- The mixed block (`i ≥ 1`) with the `η`-weight instead of the `γ`-weight is still bounded
by the square root of the `ℋ⁴`-integrand. -/
theorem abs_mixed_mul_Whz_le_sqrt {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i g z θ * Whz z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
  have hle : |Work.Spaces.mixed j i g z θ * Whz z θ|
      ≤ |Work.Spaces.mixed j i g z θ * Wm α z θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Whz_nonneg hθ), abs_of_nonneg (Wm_nonneg α hθ)]
    exact mul_le_mul_of_nonneg_left (Whz_le_Wm hα hθ) (abs_nonneg _)
  exact le_trans hle (abs_mixed_mul_Wm_le_sqrt α g hi hij z θ)

/-- The product of two quantities whose squares are bounded by `H` (`H ≥ 0`) is bounded
by `H`: the elementary AM–GM step of the term estimates. -/
theorem abs_mul_le_of_sq_le {a b H : ℝ} (ha : a ^ 2 ≤ H) (hb : b ^ 2 ≤ H) :
    |a * b| ≤ H := by
  have hH : 0 ≤ H := le_trans (sq_nonneg a) ha
  have h1 : |a| ≤ Real.sqrt H := Real.abs_le_sqrt ha
  have h2 : |b| ≤ Real.sqrt H := Real.abs_le_sqrt hb
  rw [abs_mul]
  calc |a| * |b| ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = H := Real.mul_self_sqrt hH

/-- The product of two quantities bounded by `√H` is bounded by `H` (AM–GM). -/
theorem abs_mul_le_of_abs_le_sqrt {a b H : ℝ} (hH : 0 ≤ H) (ha : |a| ≤ Real.sqrt H)
    (hb : |b| ≤ Real.sqrt H) : |a * b| ≤ H := by
  rw [abs_mul]
  calc |a| * |b| ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul ha hb (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = H := Real.mul_self_sqrt hH

end Work.FTS.H2.Transport3Aux
