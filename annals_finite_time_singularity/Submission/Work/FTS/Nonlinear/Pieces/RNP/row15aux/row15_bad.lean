import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.pth_Fstar_lower
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.notIntegrableOn_Itheta_of_rpow_lower
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `row15_bad`: the "bad" angular endpoint for the `N₂^{ss}` row

Row 15 of the nonlinear estimates is about `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.  The whole row is
an `ℋ⁴`-estimate, and the bookkeeping of `row15_bookkeeping` needs to know that the angular
integral of `HkIntegrand α 4 (N₂^{ss})` at a fixed `z > 0` converges; the "bad" branch is
ruled out by the present lemma:

> if `θ ↦ U(Φ̃_*)(z,θ)` is *bounded away from zero* on a right neighbourhood of `θ = 0`, then
> `θ ↦ HkIntegrand α 4 (N₂^{ss}) z θ` is **not** integrable on `Iθ = [0,π/2]`.

The mathematics is a one-sided blow-up test.  `F_*(z,θ) = α (Γ(θ)/c)·F̲(z)` factorizes with
`Γ(θ) = (sin θ cos²θ)^{α/3}`, so for `0 < α ≤ 1` the angular derivative
`∂_θ F_*(z,θ) = cst(z)·Γ'(θ)` blows up like `θ^{α/3-1}` as `θ → 0⁺`.  Hence with
`|U(Φ̃_*)| ≥ δ`,

  `|N₂^{ss}(z,θ)| = 2|U(Φ̃_*)(z,θ)|·|∂_θF_*(z,θ)| ≳ δ·c·θ^{α/3-1}`,

and the `i = 0` term of the pure-`D_z` part of `HkIntegrand` carries the weight
`sin(2θ)^{-η}`, so on a right neighbourhood of `0`,

  `HkIntegrand α 4 (N₂^{ss}) z θ ≳ θ^{2α/3-2-η}`.

Since `2α/3 - 2 - η ≤ -7/3 < -1`, this power is not integrable at `0`, so the whole
integrand is not integrable on `Iθ`.

Two ingredients are imported from sibling modules of this directory:

* `pth_Fstar_lower` — the quantitative lower bound `|∂_θF_*(z,θ)| ≥ c θ^{α/3-1}` near `0`;
* `notIntegrableOn_Itheta_of_rpow_lower` — the measure-theoretic divergence test for a
  `C·θ^p` lower bound with `p ≤ -1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option maxHeartbeats 1600000

/-! ## Two elementary auxiliary lemmas -/

/-- `sin(2θ)^{-η} ≥ (2θ)^{-η}` for `θ ∈ (0,π/2)`: the `rpow` is decreasing in the base on
positive bases with a negative exponent, and `sin(2θ) ≤ 2θ`. -/
private lemma sin_two_rpow_neg_eta_le {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    (2 * θ) ^ (-Work.Spaces.eta) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hs2θ0 : 0 ≤ 2 * θ := by linarith
  have hsinle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le hs2θ0
  have hsinpos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [hθπ, Real.pi_pos]
  have hη : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  exact Real.rpow_le_rpow_of_nonpos hsinpos hsinle (by linarith)

/-- Splitting the `i = 0` slot of the pure-`D_z` part of `HkIntegrand`: the weight
`(w(z)/sin(2θ)^{η/2})²` equals `w(z)²·sin(2θ)^{-η}`. -/
private lemma div_sin_rpow_sq {z θ : ℝ} (hsinpos : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2,
      ← Real.rpow_mul hsinpos.le (Work.Spaces.eta / 2) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring_nf
  rw [div_pow, h1, div_eq_mul_inv, ← Real.rpow_neg hsinpos.le Work.Spaces.eta]

/-! ## The pointwise lower bound for `HkIntegrand` -/

/-- The `i = 0` slot of the pure-`D_z` block of `HkIntegrand α 4 (N₂^{ss}) z θ` dominates
`C·θ^{2α/3-2-η}` on `Ioo 0 (min ε₁ (π/6))`: the two lower bounds for `|U(Φ̃_*)|` (given on
`Ioo 0 ε₁`) and `|∂_θF_*|` (given on `Ioo 0 (π/6)`) combine, and the angular weight is
compared with the power `(2θ)^{-η}`. -/
private lemma hk_lower_pointwise {α z : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {δ c ε₁ : ℝ} (hz : 0 < z) (hδ : 0 < δ) (hc : 0 < c)
    (hU : ∀ θ ∈ Set.Ioo (0 : ℝ) ε₁,
      δ ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 6),
      c * θ ^ (α / 3 - 1) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ|) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (min ε₁ (Real.pi / 6)),
      C * θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        ≤ Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ := by
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    positivity
  refine ⟨(2 * δ * c) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta), ?_, ?_⟩
  · exact mul_pos (mul_pos (pow_pos (by positivity) 2) (pow_pos hwpos 2))
      (Real.rpow_pos_of_pos (by norm_num) _)
  intro θ hθ
  have hθ1 : θ ∈ Set.Ioo (0 : ℝ) ε₁ := ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_left _ _)⟩
  have hθ2 : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 6) :=
    ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩
  have hθπ2 : θ < Real.pi / 2 := by linarith [hθ2.2, Real.pi_pos]
  have hθpos : 0 < θ := hθ.1
  have hUθ : δ ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := hU θ hθ1
  have hPθ : c * θ ^ (α / 3 - 1) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ| :=
    hP θ hθ2
  have hsinpos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [hθπ2, Real.pi_pos]
  -- ### step 1: the `i = 0` slot is a summand of `HkIntegrand`
  have hstep1 : (Work.FTS.Nonlin.N2ss α Φs z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ := by
    rw [Work.Spaces.HkIntegrand]
    have h1 : (Work.Spaces.DzIter 0 (Work.FTS.Nonlin.N2ss α Φs) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i (Work.FTS.Nonlin.N2ss α Φs) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine Finset.single_le_sum
        (f := fun i => (Work.Spaces.DzIter i (Work.FTS.Nonlin.N2ss α Φs) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (fun i _ => sq_nonneg _) ?_
      exact Finset.mem_range.mpr (by norm_num)
    have h2 : 0 ≤ ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4
          then (Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    simpa only [Work.Spaces.DzIter_zero] using le_trans h1 (le_add_of_nonneg_right h2)
  -- ### step 2: `|N₂^{ss}| ≥ 2δc·θ^{α/3-1}`
  have hN : 2 * δ * c * θ ^ (α / 3 - 1)
      ≤ |Work.FTS.Nonlin.N2ss α Φs z θ| := by
    have hdef : Work.FTS.Nonlin.N2ss α Φs z θ
        = -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
    rw [hdef, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrpow0 : 0 ≤ θ ^ (α / 3 - 1) := Real.rpow_nonneg hθpos.le _
    have h1 : δ * (c * θ ^ (α / 3 - 1))
        ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          * |Work.Spaces.pth (Work.Construction.Fstar α) z θ| :=
      mul_le_mul hUθ hPθ (mul_nonneg hc.le hrpow0) (abs_nonneg _)
    calc 2 * δ * c * θ ^ (α / 3 - 1) = 2 * (δ * (c * θ ^ (α / 3 - 1))) := by ring
      _ ≤ 2 * (|Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            * |Work.Spaces.pth (Work.Construction.Fstar α) z θ|) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            * |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by ring
  -- ### step 3: square it and put the angular weight back in
  have hsq2 : (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
      ≤ (Work.FTS.Nonlin.N2ss α Φs z θ) ^ 2 := by
    have ha : 0 ≤ 2 * δ * c * θ ^ (α / 3 - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ.le) hc.le)
        (Real.rpow_nonneg hθpos.le _)
    have h1 := pow_le_pow_left₀ ha hN 2
    simpa [sq_abs] using h1
  have hsq : (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ (Work.FTS.Nonlin.N2ss α Φs z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinpos.le _)
    calc (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ (Work.FTS.Nonlin.N2ss α Φs z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hsq2 h1
      _ = (Work.FTS.Nonlin.N2ss α Φs z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [mul_pow, div_sin_rpow_sq hsinpos]
  -- ### step 4: the power comparison
  have hrpow2 : (θ ^ (α / 3 - 1)) ^ 2 = θ ^ (2 * α / 3 - 2) := by
    rw [← Real.rpow_natCast (θ ^ (α / 3 - 1)) 2,
      ← Real.rpow_mul hθpos.le (α / 3 - 1) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  have hsinlow : (2 * θ) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
    sin_two_rpow_neg_eta_le hθpos hθπ2
  have hfinal : ((2 * δ * c) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta))
        * θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
      ≤ (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    have hexp1 : θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        = θ ^ (2 * α / 3 - 2) * θ ^ (-Work.Spaces.eta) := by
      rw [← Real.rpow_add hθpos]
      rw [show 2 * α / 3 - 2 + -Work.Spaces.eta = 2 * α / 3 - 2 - Work.Spaces.eta by ring]
    calc ((2 * δ * c) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta))
          * θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        = (2 * δ * c) ^ 2 * (Work.Spaces.w z) ^ 2
            * (2 ^ (-Work.Spaces.eta) * θ ^ (-Work.Spaces.eta)) * θ ^ (2 * α / 3 - 2) := by
          rw [hexp1]; ring
      _ ≤ (2 * δ * c) ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) * θ ^ (2 * α / 3 - 2) := by
          have h2θ : 2 ^ (-Work.Spaces.eta) * θ ^ (-Work.Spaces.eta)
              = (2 * θ) ^ (-Work.Spaces.eta) :=
            (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθpos.le).symm
          rw [h2θ]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsinlow (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
            (Real.rpow_nonneg hθpos.le _)
      _ = (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
          have hkey : (2 * δ * c * θ ^ (α / 3 - 1)) ^ 2
              = (2 * δ * c) ^ 2 * θ ^ (2 * α / 3 - 2) := by
            rw [mul_pow, hrpow2]
          rw [hkey]; ring
  exact hfinal.trans (hsq.trans hstep1)

/-! ## The target -/

theorem row15_bad {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) (hz : 0 < z)
    (hbad : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|) :
    ¬MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ)
      Work.Spaces.Iθ := by
  obtain ⟨δ, hδpos, hδ⟩ := hbad
  -- extract the right neighbourhood on which `|U(Φ̃_*)| ≥ δ`
  obtain ⟨ε₁, hε₁pos, hU₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) ε₁,
      δ ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := by
    rw [eventually_nhdsWithin_iff] at hδ
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp hδ
    refine ⟨ε₁, hε₁pos, fun θ hθ => hε₁ (y := θ) ?_ hθ.1⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact hθ.2
  -- the lower bound for `∂_θF_*` near `0`
  obtain ⟨c, hcpos, hP⟩ := pth_Fstar_lower (z := z) hα hα1 hz
  -- the pointwise lower bound for the integrand
  obtain ⟨C, hCpos, hpoint⟩ := hk_lower_pointwise (z := z) hz hδpos hcpos hU₁ hP
  -- it is a power strictly beyond the integrability threshold
  have hp : 2 * α / 3 - 2 - Work.Spaces.eta ≤ -1 := by
    have h1 : 2 * α / 3 ≤ 2 / 3 := by linarith
    have he : Work.Spaces.eta = 99 / 100 := rfl
    rw [he]
    linarith
  have hnonneg : ∀ θ, 0 ≤ Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ := by
    intro θ
    rw [Work.Spaces.HkIntegrand]
    refine add_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) ?_
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  exact notIntegrableOn_Itheta_of_rpow_lower hCpos hp hnonneg
    ⟨min ε₁ (Real.pi / 6), lt_min hε₁pos (by positivity),
      le_trans (min_le_right _ _) (by linarith [Real.pi_pos]), hpoint⟩

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
