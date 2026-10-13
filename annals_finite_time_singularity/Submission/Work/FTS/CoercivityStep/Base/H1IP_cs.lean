/-
# Cauchy–Schwarz for the `ℋ¹` inner product `H1IP`

`Work.FTS.CoercivityStep.IsHkIP_fts` (the repaired specification of the paper's
`(·,·)_{ℋ^k}`, §"Higher order derivatives and the inner product on `ℋ^k`") contains a
clause `cs`: the pairing is bounded by the honest `ℋ^k`-norm of its two arguments.
This file proves that clause for the base case `k = 1` and the paper's concrete first
inner product

  `H1IP α f g = 10 (D_z f, D_z g)_{w²/sin^η} + 10¹⁰ (f,g)_{w²/sin^η}
                 + 10¹⁷ (f,g)_{w²} + 10²¹ (D_θ f, D_θ g)_{w²/sin^γ}`,

on the regularity class `HkReg α 1 f = SmoothNbhd f ∧ HkMem α 1 f`.

## The argument

Write `Xeta f = f·w/√(sin 2θ^η)`, `XetaDz f = D_z f·w/√(sin 2θ^η)`,
`XgamDth α f = D_θ f·W` and `Xw f = f·w` for the four weighted blocks.  On the angular
domain each of the four pairing integrands is the *product* of the two corresponding
blocks (`Xeta_mul_eq`, `XetaDz_mul_eq`, `XgamDth_mul_eq`, and `Xw` by `ring`), and each
block is `L²` (`L2Mem_DzIter_Hwt`, `L2Mem_mixed_Wt_gen`, `L2Mem_Xw`) as well as
a.e.-strongly measurable (it is continuous on the open quadrant and on every open
angular slice, `aesm_blocks`).  The two-dimensional Cauchy–Schwarz lemma
`iterated_L2Sq_cs` therefore bounds each pairing by the product of the square roots of
the two block `L²`-norms, and each of those is dominated by the `ℋ¹`-norm square:
the three blocks `Xeta`, `XetaDz`, `XgamDth` are literally the first-order summands of
`HkIntegrand α 1 f` (`L2Sq_DzIter_le_HkSq`, `L2Sq_mixed_le_HkSq`), and the remaining
block `Xw f = f·w` is dominated by the `η`-weighted one off the two null endpoints of
`Iθ` (`L2Sq_Xw_le_HkSq` below).

The only remaining ingredient is the triangle inequality for the four terms of `H1IP`,
with the coefficients `10 + 10¹⁰ + 10¹⁷ + 10²¹ ≤ 10²²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.aesm_blocks
import Submission.Work.Coercivity.L2Mem_Xw
import Submission.Work.Coercivity.Xeta_mul_eq
import Submission.Work.Coercivity.XetaDz_mul_eq
import Submission.Work.Coercivity.XgamDth_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Base

set_option autoImplicit false

/-! ## Slice measurability from continuity on the open interval -/

/-- A function continuous on the open interval `(0,π/2)` is a.e. strongly measurable for
the measure `volume.restrict Iθ`; the two endpoints `0`, `π/2` are null. -/
private theorem aesm_slice_of_contOn_Ioo {F : ℝ → ℝ}
    (h : ContinuousOn F (Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable F (volume.restrict Spaces.Iθ) := by
  rw [← Coercivity.restrict_Ioo_eq_restrict_Iθ]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-! ## The four weighted blocks are `L²` -/

/-- `Xeta f = f·w/√(sin 2θ^η)` is square integrable in the iterated sense. -/
private theorem L2Mem_Xeta (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hmem : Spaces.HkMem α 1 f) : Spaces.L2Mem (Coercivity.Xeta f) :=
  Coercivity.L2Mem_DzIter_Hwt α 1 f hsm hmem 0 (by norm_num)

/-- `XetaDz f = D_z f·w/√(sin 2θ^η)` is square integrable in the iterated sense. -/
private theorem L2Mem_XetaDz (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hmem : Spaces.HkMem α 1 f) : Spaces.L2Mem (Coercivity.XetaDz f) :=
  Coercivity.L2Mem_DzIter_Hwt α 1 f hsm hmem 1 (by norm_num)

/-- `XgamDth α f = D_θ f·W` is square integrable in the iterated sense. -/
private theorem L2Mem_XgamDth (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hmem : Spaces.HkMem α 1 f) : Spaces.L2Mem (Coercivity.XgamDth α f) :=
  Coercivity.L2Mem_mixed_Wt_gen α 1 f hsm hmem 1 0 (by norm_num) (by norm_num)

/-! ## The three `L²`-norm identifications with the paper's energies -/

private theorem L2Sq_Xeta (f : ℝ → ℝ → ℝ) :
    Spaces.L2Sq (Coercivity.Xeta f) = Coercivity.EfEta f :=
  Coercivity.L2Sq_U0_eq_EfEta f

private theorem L2Sq_XetaDz (f : ℝ → ℝ → ℝ) :
    Spaces.L2Sq (Coercivity.XetaDz f) = Coercivity.EDz f :=
  Coercivity.L2Sq_U1_eq_EDz f

private theorem L2Sq_XgamDth (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Spaces.L2Sq (Coercivity.XgamDth α f) = Coercivity.EDth α f :=
  Coercivity.L2Sq_U2_eq_EDth α f

/-! ## Each block `L²`-norm is dominated by the `ℋ¹`-norm square -/

private theorem L2Sq_Xeta_le_HkSq (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.HkMem α 1 f) :
    Spaces.L2Sq (Coercivity.Xeta f) ≤ Spaces.HkSq α 1 f :=
  Spaces.L2Sq_DzIter_le_HkSq α 1 f hmem 0 (by norm_num)

private theorem L2Sq_XetaDz_le_HkSq (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.HkMem α 1 f) :
    Spaces.L2Sq (Coercivity.XetaDz f) ≤ Spaces.HkSq α 1 f :=
  Spaces.L2Sq_DzIter_le_HkSq α 1 f hmem 1 (by norm_num)

private theorem L2Sq_XgamDth_le_HkSq (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.HkMem α 1 f) :
    Spaces.L2Sq (Coercivity.XgamDth α f) ≤ Spaces.HkSq α 1 f :=
  Spaces.L2Sq_mixed_le_HkSq α 1 f hmem 1 0 (by norm_num) (by norm_num)

/-- Off the two null endpoints of `Iθ`, the plain block `Xw f = f·w` is dominated by the
`H¹`-integrand, because the `D_z⁰`-summand of the latter is `(f·w/√(sin 2θ^η))²`. -/
private theorem sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (Coercivity.Xw f z θ) ^ 2 ≤ Spaces.HkIntegrand α 1 f z θ := by
  rw [← Coercivity.restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Spaces.eta / 2) :=
          Real.rpow_le_rpow (le_of_lt hs0) hs1
            (div_nonneg (le_of_lt Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Spaces.w z) ^ 2
      ≤ ((f z θ * Spaces.w z) / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos ht0 2)]
    have ht2 : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 ≤ 1 := by
      nlinarith [ht0, ht1]
    simpa using mul_le_mul_of_nonneg_left ht2 (sq_nonneg (f z θ * Spaces.w z))
  have hterm : (Coercivity.Xw f z θ) ^ 2
      ≤ (Spaces.DzIter 0 f z θ
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2 := by
    simp only [Coercivity.Xw, Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-- `|f·w|²_{L²} ≤ |f|²_{ℋ¹}`. -/
private theorem L2Sq_Xw_le_HkSq (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.HkMem α 1 f) :
    Spaces.L2Sq (Coercivity.Xw f) ≤ Spaces.HkSq α 1 f := by
  rw [Spaces.L2Sq, Spaces.HkSq]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z hz) (sq_Xw_le_HkIntegrand_ae α f z)

/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The two-dimensional Cauchy–Schwarz lemma

For `L²`-functions `X`, `Y` (a.e. strongly measurable on the quadrant and on every
angular slice) the iterated integral of the product is bounded by the product of the
square roots of the two iterated `L²`-norms.  The proof is Cauchy–Schwarz twice: on
each angular slice (`holder_two_mul` with the functions `X z`, `Y z`), and then in the
radial variable applied to the two square-root functions
`z ↦ √(∫_θ X(z,θ)²)` and `z ↦ √(∫_θ Y(z,θ)²)`, which are integrable by
`integrable_sqrt_mul_sqrt`. -/
private theorem cs_place (X Y : ℝ → ℝ → ℝ)
    (hX : Spaces.L2Mem X) (hY : Spaces.L2Mem Y)
    (hXs : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => X z θ) (volume.restrict Spaces.Iθ))
    (hYs : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => Y z θ) (volume.restrict Spaces.Iθ))
    (hXp : AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)))
    (hYp : AEStronglyMeasurable (fun p : ℝ × ℝ => Y p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))) :
    |∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, X z θ * Y z θ|
      ≤ Real.sqrt (Spaces.L2Sq X) * Real.sqrt (Spaces.L2Sq Y) := by
  set A : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (X z θ) ^ 2 with hAdef
  set B : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (Y z θ) ^ 2 with hBdef
  have hAint : Integrable A (volume.restrict Spaces.Iz) := by
    rw [hAdef]; exact hX.2
  have hBint : Integrable B (volume.restrict Spaces.Iz) := by
    rw [hBdef]; exact hY.2
  have hAnonneg : ∀ z, 0 ≤ A z := by
    intro z; rw [hAdef]; exact integral_nonneg fun θ => sq_nonneg _
  have hBnonneg : ∀ z, 0 ≤ B z := by
    intro z; rw [hBdef]; exact integral_nonneg fun θ => sq_nonneg _
  -- Cauchy–Schwarz on every angular slice.
  have hslice : ∀ z ∈ Spaces.Iz,
      |∫ θ in Spaces.Iθ, X z θ * Y z θ| ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have h := Coercivity.holder_two_mul (volume.restrict Spaces.Iθ) (X z) (Y z)
      (hXs z hz) (hYs z hz) (hX.1 z hz) (hY.1 z hz)
    simpa only [hAdef, hBdef] using h.2
  -- The dominating function is integrable.
  have hGint : Integrable (fun z => Real.sqrt (A z) * Real.sqrt (B z))
      (volume.restrict Spaces.Iz) :=
    Coercivity.integrable_sqrt_mul_sqrt _ A B hAint hBint hAnonneg hBnonneg
  -- The outer integrand is a.e. strongly measurable.
  have hFmeas : AEStronglyMeasurable (fun z => ∫ θ in Spaces.Iθ, X z θ * Y z θ)
      (volume.restrict Spaces.Iz) := by
    have h : AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2 * Y p.1 p.2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hXp.mul hYp
    have := h.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hFint : Integrable (fun z => ∫ θ in Spaces.Iθ, X z θ * Y z θ)
      (volume.restrict Spaces.Iz) := by
    refine hGint.mono' hFmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    simpa only [Real.norm_eq_abs] using hslice z hz
  -- Measurability and integrability of the two square-root functions in `z`.
  have hAmeas : AEStronglyMeasurable A (volume.restrict Spaces.Iz) := by
    rw [hAdef]
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (X p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hXp.pow 2
    have := h2.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hBmeas : AEStronglyMeasurable B (volume.restrict Spaces.Iz) := by
    rw [hBdef]
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Y p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hYp.pow 2
    have := h2.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hAsq : Integrable (fun z => (Real.sqrt (A z)) ^ 2) (volume.restrict Spaces.Iz) :=
    hAint.congr (Eventually.of_forall fun z => (Real.sq_sqrt (hAnonneg z)).symm)
  have hBsq : Integrable (fun z => (Real.sqrt (B z)) ^ 2) (volume.restrict Spaces.Iz) :=
    hBint.congr (Eventually.of_forall fun z => (Real.sq_sqrt (hBnonneg z)).symm)
  have hcs2 := Coercivity.holder_two_mul (volume.restrict Spaces.Iz)
    (fun z => Real.sqrt (A z)) (fun z => Real.sqrt (B z))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAmeas)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hBmeas) hAsq hBsq
  have hfA : (∫ z in Spaces.Iz, (Real.sqrt (A z)) ^ 2) = ∫ z in Spaces.Iz, A z :=
    integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hAnonneg z))
  have hfB : (∫ z in Spaces.Iz, (Real.sqrt (B z)) ^ 2) = ∫ z in Spaces.Iz, B z :=
    integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hBnonneg z))
  calc |∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, X z θ * Y z θ|
      ≤ ∫ z in Spaces.Iz, |∫ θ in Spaces.Iθ, X z θ * Y z θ| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z in Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hGint
          (ae_restrict_of_forall_mem measurableSet_Ici hslice)
    _ = |∫ z in Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)| :=
        (abs_of_nonneg (integral_nonneg fun z =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ Real.sqrt (∫ z in Spaces.Iz, (Real.sqrt (A z)) ^ 2)
          * Real.sqrt (∫ z in Spaces.Iz, (Real.sqrt (B z)) ^ 2) := hcs2.2
    _ = Real.sqrt (Spaces.L2Sq X) * Real.sqrt (Spaces.L2Sq Y) := by
        rw [hfA, hfB, hAdef, hBdef]
        rfl

/-! ## The main theorem -/

theorem H1IP_cs (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ,
      Work.FTS.CoercivityStep.HkReg α 1 f → Work.FTS.CoercivityStep.HkReg α 1 g →
      |Work.Coercivity.H1IP α f g| ≤ C * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro f g hf hg
  obtain ⟨hsmf, hmemf⟩ := hf
  obtain ⟨hsmg, hmemg⟩ := hg
  set Y : ℝ := Real.sqrt (Spaces.HkSq α 1 f) * Real.sqrt (Spaces.HkSq α 1 g) with hYdef
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 1: the `D_z`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT1 : |Coercivity.wip Coercivity.lamEta (Spaces.Dz f) (Spaces.Dz g)| ≤ Y := by
    rw [hYdef]
    have hwip : Coercivity.wip Coercivity.lamEta (Spaces.Dz f) (Spaces.Dz g)
        = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
            Coercivity.XetaDz f z θ * Coercivity.XetaDz g z θ := by
      simp only [Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Coercivity.XetaDz_mul_eq f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place (Coercivity.XetaDz f) (Coercivity.XetaDz g)
      (L2Mem_XetaDz α f hsmf hmemf) (L2Mem_XetaDz α g hsmg hmemg)
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_XetaDz hsmf hz))
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_XetaDz hsmg hz))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_XetaDz hsmf))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_XetaDz hsmg))) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (L2Sq_XetaDz_le_HkSq α f hmemf))
      (Real.sqrt_le_sqrt (L2Sq_XetaDz_le_HkSq α g hmemg))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 2: the `L²`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT2 : |Coercivity.wip Coercivity.lamEta f g| ≤ Y := by
    rw [hYdef]
    have hwip : Coercivity.wip Coercivity.lamEta f g
        = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
            Coercivity.Xeta f z θ * Coercivity.Xeta g z θ := by
      simp only [Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Coercivity.Xeta_mul_eq f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place (Coercivity.Xeta f) (Coercivity.Xeta g)
      (L2Mem_Xeta α f hsmf hmemf) (L2Mem_Xeta α g hsmg hmemg)
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_Xeta hsmf hz))
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_Xeta hsmg hz))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_Xeta hsmf))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_Xeta hsmg))) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (L2Sq_Xeta_le_HkSq α f hmemf))
      (Real.sqrt_le_sqrt (L2Sq_Xeta_le_HkSq α g hmemg))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 3: the plain `w²`-pairing
  have hT3 : |Coercivity.wip Coercivity.lamW f g| ≤ Y := by
    rw [hYdef]
    have hwip : Coercivity.wip Coercivity.lamW f g
        = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
            Coercivity.Xw f z θ * Coercivity.Xw g z θ := by
      simp only [Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      simp only [Coercivity.Xw, Coercivity.lamW]
      ring
    rw [hwip]
    refine le_trans (cs_place (Coercivity.Xw f) (Coercivity.Xw g)
      (Coercivity.L2Mem_Xw α f hsmf hmemf) (Coercivity.L2Mem_Xw α g hsmg hmemg)
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_Xw hsmf hz))
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_Xw hsmg hz))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_Xw hsmf))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_Xw hsmg))) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (L2Sq_Xw_le_HkSq α f hmemf))
      (Real.sqrt_le_sqrt (L2Sq_Xw_le_HkSq α g hmemg))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 4: the `D_θ`-pairing with weight `w²·sin(2θ)^{-γ}`
  have hT4 : |Coercivity.wip (Coercivity.lamGam α) (Spaces.Dth f) (Spaces.Dth g)| ≤ Y := by
    rw [hYdef]
    have hwip : Coercivity.wip (Coercivity.lamGam α) (Spaces.Dth f) (Spaces.Dth g)
        = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
            Coercivity.XgamDth α f z θ * Coercivity.XgamDth α g z θ := by
      simp only [Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Coercivity.XgamDth_mul_eq α f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place (Coercivity.XgamDth α f) (Coercivity.XgamDth α g)
      (L2Mem_XgamDth α f hsmf hmemf) (L2Mem_XgamDth α g hsmg hmemg)
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_XgamDth α hsmf hz))
      (fun z hz => aesm_slice_of_contOn_Ioo (Coercivity.contOn_slice_XgamDth α hsmg hz))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_XgamDth α hsmf))
      (Spaces.aesm_of_continuousOn_Qd _ (Coercivity.contOn_Qd_XgamDth α hsmg))) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (L2Sq_XgamDth_le_HkSq α f hmemf))
      (Real.sqrt_le_sqrt (L2Sq_XgamDth_le_HkSq α g hmemg))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## The triangle inequality for the four terms of `H1IP`
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have habs : |Work.Coercivity.H1IP α f g|
      ≤ 10 * |Coercivity.wip Coercivity.lamEta (Spaces.Dz f) (Spaces.Dz g)|
        + 10 ^ 10 * |Coercivity.wip Coercivity.lamEta f g|
        + 10 ^ 17 * |Coercivity.wip Coercivity.lamW f g|
        + 10 ^ 21 * |Coercivity.wip (Coercivity.lamGam α) (Spaces.Dth f) (Spaces.Dth g)| := by
    have h := abs_add_four
      ((10 : ℝ) * Coercivity.wip Coercivity.lamEta (Spaces.Dz f) (Spaces.Dz g))
      ((10 : ℝ) ^ 10 * Coercivity.wip Coercivity.lamEta f g)
      ((10 : ℝ) ^ 17 * Coercivity.wip Coercivity.lamW f g)
      ((10 : ℝ) ^ 21 * Coercivity.wip (Coercivity.lamGam α) (Spaces.Dth f) (Spaces.Dth g))
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h10,
      abs_of_nonneg (pow_nonneg h10 10), abs_of_nonneg (pow_nonneg h10 17),
      abs_of_nonneg (pow_nonneg h10 21)] at h
    exact h
  have hT1' : 10 * |Coercivity.wip Coercivity.lamEta (Spaces.Dz f) (Spaces.Dz g)|
      ≤ 10 * Y := mul_le_mul_of_nonneg_left hT1 h10
  have hT2' : 10 ^ 10 * |Coercivity.wip Coercivity.lamEta f g| ≤ 10 ^ 10 * Y :=
    mul_le_mul_of_nonneg_left hT2 (pow_nonneg h10 10)
  have hT3' : 10 ^ 17 * |Coercivity.wip Coercivity.lamW f g| ≤ 10 ^ 17 * Y :=
    mul_le_mul_of_nonneg_left hT3 (pow_nonneg h10 17)
  have hT4' : 10 ^ 21 * |Coercivity.wip (Coercivity.lamGam α) (Spaces.Dth f) (Spaces.Dth g)|
      ≤ 10 ^ 21 * Y := mul_le_mul_of_nonneg_left hT4 (pow_nonneg h10 21)
  have hsum : |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y :=
    le_trans habs (add_le_add (add_le_add (add_le_add hT1' hT2') hT3') hT4')
  calc |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y := hsum
    _ = ((10 : ℝ) + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Y := by ring
    _ ≤ (10 : ℝ) ^ 22 * Y :=
        mul_le_mul_of_nonneg_right (by norm_num) hYnn
    _ = (10 : ℝ) ^ 22 * (Real.sqrt (Spaces.HkSq α 1 f) * Real.sqrt (Spaces.HkSq α 1 g)) := by
        rw [hYdef]
    _ = (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
        simp only [Spaces.HkNorm]
        ring

end Work.FTS.CoercivityStep.Base
