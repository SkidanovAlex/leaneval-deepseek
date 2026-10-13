/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary facts for the interior (`SmoothQuad`) form of the `D_z`-pairing

This module collects the small, shared ingredients of the proof of
`Work.FTS.H2.T3Q.GoodZPt` (the pointwise bound of the "good" part of the `D_z`-pairing
`H4PairInt α (fun z θ => f z θ * D_z g z θ) g - Badz2 α f g` in the interior class
`Work.FTS.LocData.SmoothQuad`):

* `abs_mixed_le_WlInf_Q`: the multiplier bound `|D_z^bD_θ^a f| ≤ 30 |f|_{𝒲^{4,∞}}` on the
  *open* quadrant (where the `SmoothQuad` Leibniz rules are available), obtained from
  `Work.FTS.H2.WPQ.Mixed_le_WlInf` and the elementary estimate
  `(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2` for `0 < α ≤ 1`;
* the vanishing of the two pairing weights — and hence of `HkIntegrand`, `H4PairInt` and
  `Badz2` — at the angular boundary `θ = 0, π/2` (where `sin(2θ) = 0`), which is what makes
  the closed-interval statement `θ ∈ Iθ` follow from the open-quadrant one.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The multiplier bound on the open quadrant -/

/-- **The `f`-side bound for mixed derivatives in the interior class `SmoothQuad`.**

Every mixed derivative `D_z^bD_θ^a f` of total order at most `4` of a `SmoothQuad` function
`f` of class `𝒲^{4,∞}` is bounded on the open quadrant by `30 |f|_{𝒲^{4,∞}}`.

This is the interior replacement of `Work.FTS.H2.Transport3Aux.abs_mixed_le_WlInf`
(which is stated for `Work.Spaces.SmoothNbhd f` on the closed quadrant).  The two
ingredients are `Work.FTS.H2.WPQ.DzIter_le_WlInf` / `Work.FTS.H2.WPQ.Mixed_le_WlInf`
(the honest `SmoothQuad` bounds `15|f|_𝒲` resp. `15|f|_𝒲·(α + sin 2θ)sin(2θ)^{α/5}`) and
the elementary `(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2` for `0 < α ≤ 1`, `0 ≤ θ ≤ π/2`. -/
theorem abs_mixed_le_WlInf_Q {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (hab : a + b ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hmem
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
          Work.FTS.H2.WPQ.DzIter_le_WlInf hf hmem (by omega) hz hθ
      _ ≤ 30 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b a f z θ|
        ≤ 15 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.FTS.H2.WPQ.Mixed_le_WlInf hα hf hmem ha (by omega) hz hθ
      _ ≤ 15 * (Work.Spaces.WlInf α 4 f * 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 30 * Work.Spaces.WlInf α 4 f := by ring

/-! ## Vanishing of the pairing at the angular boundary -/

/-- The `η`-weight vanishes when `sin(2θ) = 0`: `w z / sin(2θ)^{η/2} = w z / 0 = 0`. -/
theorem Whz_eq_zero_of_sin_two_eq_zero {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.FTS.H2.Whz z θ = 0 := by
  rw [Work.FTS.H2.Whz, h,
    Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)]
  simp

/-- The `γ`-weight vanishes when `sin(2θ) = 0`, for `α ≠ 0`. -/
theorem Wm_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) :
    Work.FTS.H2.Wm α z θ = 0 := by
  have hγ : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc
    have h1 : Work.Spaces.gam α = 0 := by linarith [neg_eq_zero.mp hc]
    have h2 : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
    linarith
  rw [Work.FTS.H2.Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta, h, Real.zero_rpow hγ]
  simp

/-- The `ℋ⁴`-integrand vanishes at the angular boundary: both weights carry a positive
power of `sin(2θ)`. -/
theorem HkIntegrand_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α 4 F z θ = 0 := by
  have hη : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)]
  have hγ : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [h, Real.zero_rpow (by
      intro hc
      have h1 : Work.Spaces.gam α = 0 := by linarith [neg_eq_zero.mp hc]
      have h2 : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
      linarith)]
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, hη, hγ]
  simp

/-- The flat pairing integrand vanishes at the angular boundary (both weights vanish). -/
theorem H4PairInt_eq_zero_of_sin_two_eq_zero (α : ℝ) (hα : 0 < α) {u v : ℝ → ℝ → ℝ}
    {z θ : ℝ} (h : Real.sin (2 * θ) = 0) : Work.FTS.H2.H4PairInt α u v z θ = 0 := by
  rw [Work.FTS.H2.H4PairInt, Whz_eq_zero_of_sin_two_eq_zero h,
    Wm_eq_zero_of_sin_two_eq_zero hα h]
  simp

/-- `Badz2 = Badz + Mismatchz` vanishes at the angular boundary: every summand carries one
of the two weights as a factor. -/
theorem Badz2_eq_zero_of_sin_two_eq_zero (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.FTS.H2.Badz2 α f g z θ = 0 := by
  have hWhz : Work.FTS.H2.Whz z θ = 0 := Whz_eq_zero_of_sin_two_eq_zero h
  have hWm : Work.FTS.H2.Wm α z θ = 0 := Wm_eq_zero_of_sin_two_eq_zero hα h
  rw [Work.FTS.H2.Badz2, Work.FTS.H2.Badz, Work.FTS.H2.Mismatchz, hWhz, hWm]
  simp

end Work.FTS.H2.T3Q
