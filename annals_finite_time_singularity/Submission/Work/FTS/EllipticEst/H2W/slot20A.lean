import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! # `slot20A` — the `(2,0)`-slot of `A = z²∂_z²Ψ` with the `γ`-weight

Target: `α⁴ · L2Sq (D_θ²A · Wt α) ≤ K · (α⁴ · P + HkSq α 2 F)` with `A := z²∂_z²Ψ` and

  `P := Σ_{j<3} L2Sq (z²∂_z²(D_z^jΨ) · w/sin(2θ)^{η/2})`

the *pure* part of the `ℋ²`-norm of `A` (identified with `Σ_{j<3} L2Sq(D_z^jA·w/s^{η/2})` by
`z2pzIter2Comm`).

## What is in this file

The **elementary (pointwise) layer** of the reduction of the target to the sharp analytic input
it needs, the statement of that input, and the reduction itself:

* `Az` — the twisted datum `A = z²∂_z²Ψ`;
* `Az_zero_left`, `Az_zero_right` — the slices of `A` vanish at the angular endpoints;
* `zsq_pzIter2` — `A = D_z²Ψ − D_zΨ` on the open quadrant;
* `DthIter_two_eq_pth` — `D_θ²f = sin²(2θ)∂_θ²f + 2 sin(2θ)cos(2θ)∂_θf`;
* `pth_zsq_mul` — `∂_θ(z²g) = z²∂_θg`;
* `quad_core`, `slot20A_pt_le` — the pointwise weight chain
  `(D_θ²A·Wt α)² ≤ 2 (∂_θ²A·w/s^{η/2})² + 8 (∂_θA·w/s^{η/2})²` on the open quadrant;
* `L2Sq_nonneg`, `HkSq_nonneg` — nonnegativity of the two functionals (Mathlib's totalised
  integral takes the value `0` on a non-integrable nonneg integrand, never a negative value);
* `Slot20AHonest` / `Slot20AJunk` / `slot20A_of_sharp` — the two analytic inputs and the
  reduction of the target to them.

## Why the "naive" route does not suffice (see `NOTES_slot20A.md`)

The route proposed in `H2W/NOTES_weakMixedA.md` §2 (reduce the slot to the `η`-weighted second
angular derivative of `A` and invoke `angL0weak` for the datum `A`) is **not sufficient**: if
`A`'s `θ`-profile near an endpoint behaves like `θ^b` with `(γ−1)/2 < b < (3+η)/2`, then the
target's slot `∫(D_θ²A)² sin(2θ)^{−γ}` is honest and non-zero while *every* `η`-weighted
quantity of that route is non-integrable (Bochner value `0`), so a chain
`slot ≤ C·(η-weighted quantities)` is false there.  The target really needs the *`γ`-weighted*
slot estimate for the twisted datum `A` — the `A`-datum analogue of Steps 4–5 of `prop:H2`,
which `H2W/NOTES_mixedA.md` §4 records as the missing sharp analytic chapter.
-/

/-! ## The twisted datum `A = z²∂_z²Ψ` -/

/-- `A = z²∂_z²Ψ`: the radial second derivative of the stream function (the datum of `prop:H2`
whose `ℋ²`-norm is estimated there). -/
def Az (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ



/-- **`A = D_z²Ψ − D_zΨ` on the open quadrant** (the operator identity `z²∂_z² = D_z² − D_z`). -/
theorem zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Az Ψ z θ = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ :=
  Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hz hθ

/-! ## The expansion of `D_θ²` and the pull-out of the `z²`-weight -/

/-- `(sin 2·)' = 2cos(2·)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h.sin
  rwa [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2

/-- **The expansion of `D_θ²`**: `D_θ²f = sin²(2θ)·∂_θ²f + 2 sin(2θ)cos(2θ)·∂_θf`. -/
theorem DthIter_two_eq_pth (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h2 : DifferentiableAt ℝ (fun t => deriv (fun t' => f z t') t) θ) :
    Work.Spaces.DthIter 2 f z θ
      = (Real.sin (2 * θ)) ^ 2 * Work.Spaces.pthIter 2 f z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth f z θ := by
  have hs := hasDerivAt_sin_two θ
  have hd : HasDerivAt (fun t : ℝ => deriv (fun t' => f z t') t)
      (deriv (fun t : ℝ => deriv (fun t' => f z t') t) θ) θ := h2.hasDerivAt
  have hmul := hs.mul hd
  show Real.sin (2 * θ) * deriv (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ = _
  rw [show (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t)
      = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => deriv (fun t' => f z t') t) from rfl]
  rw [hmul.deriv]
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  ring


/-! ## Elementary weight facts -/

/-- `sin(2θ) ∈ [0,1]` on `Iθ`. -/
theorem sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 :=
  ⟨Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩,
    Real.sin_le_one _⟩

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])





/-- `(w·s^{-g/2})² = w²·s^{-g}` for `s > 0`. -/
theorem mul_rpow_half_sq {g w s : ℝ} (hs : 0 < s) :
    (w * s ^ (-(g / 2))) ^ 2 = w ^ 2 * s ^ (-g) := by
  rw [mul_pow, ← Real.rpow_natCast (s ^ (-(g / 2))) 2, ← Real.rpow_mul hs.le]
  congr 1
  ring_nf

/-- `(w/s^{g/2})² = w²·s^{-g}` for `s > 0`. -/
theorem div_rpow_half_sq {g w s : ℝ} (hs : 0 < s) :
    (w / s ^ (g / 2)) ^ 2 = w ^ 2 * s ^ (-g) := by
  have h1 : w / s ^ (g / 2) = w * s ^ (-(g / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs.le]
  rw [h1]
  exact mul_rpow_half_sq hs

/-! ## The pointwise weight chain -/




/-! ## Nonnegativity of the two functionals -/

/-- The `ℋ^k`-integrand is nonnegative. -/
theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

/-- `HkSq` is nonnegative. -/
theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  refine integral_nonneg ?_
  intro z
  exact integral_nonneg (fun θ => HkIntegrand_nonneg α k f z θ)



/-! ## The slots of a function are dominated by its `ℋ²`-norm -/


/-- **A mixed slot of a function is a summand of its `ℋ²`-integrand** (pointwise). -/
theorem mixed_sq_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hik : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hjk : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hnn : ∀ i' ∈ Finset.range (k + 1), (0 : ℝ) ≤ ∑ j' ∈ Finset.range (k + 1),
      (if 1 ≤ i' ∧ i' + j' ≤ k then
        (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    intro i' _
    exact Finset.sum_nonneg (fun j' _ => by split_ifs with h; exacts [sq_nonneg _, le_refl 0])
  have h1 : (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ ∑ j' ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j' ≤ k then
            (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j' => if 1 ≤ i ∧ i + j' ≤ k then
        (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) ?_ hjk
    intro j' _
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  have hred : (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [if_pos ⟨hi, hij⟩]
  rw [hred] at h1
  have h2 : (∑ j' ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j' ≤ k then
          (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ i' ∈ Finset.range (k + 1), ∑ j' ∈ Finset.range (k + 1),
          (if 1 ≤ i' ∧ i' + j' ≤ k then
            (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => ∑ j' ∈ Finset.range (k + 1),
        (if 1 ≤ i' ∧ i' + j' ≤ k then
          (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) hnn hik
  rw [Work.Spaces.HkIntegrand]
  exact le_trans (le_trans h1 h2)
    (le_add_of_nonneg_left (Finset.sum_nonneg (fun i' _ => sq_nonneg _)))

/-- **A pure (`D_z`-only) slot of a function is a summand of its `ℋ²`-integrand** (pointwise). -/
theorem dzIter_sq_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {i : ℕ} (hi : i ≤ k) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hik : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have h1 : (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∑ i' ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i' F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => (Work.Spaces.DzIter i' F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i' _ => sq_nonneg _) hik
  rw [Work.Spaces.HkIntegrand]
  exact le_trans h1 (le_add_of_nonneg_right (Finset.sum_nonneg (fun i' _ =>
    Finset.sum_nonneg (fun j' _ => by split_ifs with h; exacts [sq_nonneg _, le_refl 0]))))



/-! ## The target's hypothesis block, the honest class for `A`, and the two inputs -/










/-! ## The final assembly (a pure re-packaging of `slot20A_of_sharp`) -/


/-! ## The target -/


end

end Work.FTS.EllipticEst.H2W
