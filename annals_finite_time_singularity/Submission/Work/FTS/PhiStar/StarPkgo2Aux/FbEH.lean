/-
# `FTS/PhiStar/StarPkgo2Aux/FbEH.lean` — the flat bound for the transport coefficient `EH`

`Work.FTS.PhiStar.EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + D_zY) + D_θY` (with `D_zY = z∂_zY`,
`D_θY = sin(2θ)∂_θY`) is the `Ŷ`-expression of `((z+1)/z)·ℛ(Φ̃_*)`, one of the fields of the
`StarPkgo2` bundle (see `CoreAux/FieldsDefs.lean`).

This file proves the flat bound

`Fb 6 (A·K) Y  →  Fb 4 (C·A⁴·K·(α+1)) (EH α Y)`

from the flat bounds `F0 6 A` of the six coefficient functions and `SmoothOpen Y`.

**The proof.**

* `EH α Y` is written as `EH1 + EH2 + EH3` with `EH1 = 2Y`,
  `EH2 = (2α)·(sin²θ·(Y·ρ + D_zY))` (`ρ = (z+1)⁻¹`), `EH3 = sin(2θ)·∂_θY`; the first half
  `F0 4 … (EH α Y)` is the sum of the three bounds obtained from `F0_mul`, `F0_add` and
  `F0_zpz`/`Fb_zpz`.
* The second half is `F0 4 … (∂_θ(EH α Y))`: `∂_θ` is expanded on the open quadrant by the
  product rule `Fbq_pth_mul` (`∂_θ(fg) = ∂_θf·g + f·∂_θg`), the derivative identities
  `∂_θ(sin²θ) = sin 2θ`, `∂_θ(sin 2θ) = 2cos 2θ`, `∂_θ(z+1)⁻¹ = 0` and the two structural
  identities `∂_θ(z∂_zY) = z∂_z(∂_θY)` (`pth_zpz_smoothOpen`) and
  `sin(2θ)·∂_θ(∂_θY) = D_θ(∂_θY)`; the resulting sum is bounded term by term, the
  `D_θ(∂_θY)`-term by `F0_Dth` applied to `F0 5 (A·K) (∂_θY)`.

All constants are traced explicitly and absorbed into `C·A⁴·K·(α+1)` using `A ≥ 1`, `K ≥ 0`,
`α ≥ 0` (the comparison lemmas `absorb_le`, `absorb_le_alpha`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Work.FTS.PhiStar.CoreAux

/-! ## Local vocabulary

The coefficient functions and the `Y`-blocks occurring in `EH`, together with the three
summands `EH1`, `EH2`, `EH3` of `EH α Y` and the terms of `∂_θ(EH α Y)`. -/

/-- The angular coefficient `sin²θ`. -/
private def Sqs : ℝ → ℝ → ℝ := fun _ θ => Real.sin θ ^ 2

/-- The angular coefficient `sin 2θ`. -/
private def Sin2 : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The radial coefficient `(z+1)⁻¹`. -/
private def Rho : ℝ → ℝ → ℝ := fun z _ => (z + 1)⁻¹

/-- `∂_θ(sin²θ) = 2 sinθ cosθ`. -/
private def DSq : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.sin θ * Real.cos θ

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
private def DCos2 : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.cos (2 * θ)

/-- `Y·(z+1)⁻¹`. -/
private def Yrho (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Y z θ * Rho z θ

/-- `Y/(z+1) + D_zY`. -/
private def Zfun (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Yrho Y z θ + Yblk Y z θ

/-- `sin²θ·(Y/(z+1) + D_zY)`. -/
private def Gfun (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Sqs z θ * Zfun Y z θ

/-- The first summand `2Y` of `EH`. -/
private def EH1 (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 2 * Y z θ

/-- The second summand `2α sin²θ (Y/(z+1) + D_zY)` of `EH`. -/
private def EH2 (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (2 * α) * Gfun Y z θ

/-- The third summand `D_θY = sin(2θ)∂_θY` of `EH`. -/
private def EH3 (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Sin2 z θ * Work.Spaces.pth Y z θ

/-- `EH1 + EH2`. -/
private def EH12 (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => EH1 Y z θ + EH2 α Y z θ

/-- The `∂_θ`-expansion of the middle summand of `EH α Y` (after the product rules). -/
private def Inner (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    DSq z θ * Zfun Y z θ
      + (Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
          + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ)

/-- The explicit expression for `∂_θ(EH α Y)` on the open quadrant. -/
private def Dsum (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    2 * Work.Spaces.pth Y z θ + (2 * α) * Inner Y z θ
      + (DCos2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)

/-! ## Smoothness of the coefficient functions -/

private theorem smooth_Sqs : EllipticEst.SmoothOpen Sqs := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Sqs = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 := rfl
  rw [h]
  fun_prop

private theorem smooth_Sin2 : EllipticEst.SmoothOpen Sin2 := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Sin2 = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [h]
  fun_prop

private theorem smooth_Rho : EllipticEst.SmoothOpen Rho := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Rho = fun p : ℝ × ℝ => (p.1 + 1)⁻¹ := rfl
  rw [h]
  exact ContDiffOn.inv (contDiffOn_fst.add contDiffOn_const) (fun p hp => by
    have h1 : (0 : ℝ) < p.1 := (EllipticEst.mem_Q0.mp hp).1
    positivity)

private theorem smooth_DSq : EllipticEst.SmoothOpen DSq := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry DSq = fun p : ℝ × ℝ => 2 * Real.sin p.2 * Real.cos p.2 := rfl
  rw [h]
  fun_prop

private theorem smooth_DCos2 : EllipticEst.SmoothOpen DCos2 := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry DCos2 = fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2) := rfl
  rw [h]
  fun_prop

/-! ## The three `θ`-derivative identities -/

private theorem pth_Sqs : ∀ z θ : ℝ, Work.Spaces.pth Sqs z θ = DSq z θ := by
  intro z θ
  have h := (Real.hasDerivAt_sin θ).pow 2
  show deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ
  rw [show (fun θ' : ℝ => Real.sin θ' ^ 2) = Real.sin ^ 2 from rfl, h.deriv]
  norm_num

private theorem pth_Rho : ∀ z θ : ℝ, Work.Spaces.pth Rho z θ = 0 := by
  intro z θ
  show deriv (fun _ : ℝ => (z + 1)⁻¹) θ = 0
  exact deriv_const θ _

private theorem pth_Sin2 : ∀ z θ : ℝ, Work.Spaces.pth Sin2 z θ = DCos2 z θ := by
  intro z θ
  have hinner : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    have h := (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa only [id_eq, mul_one] using h
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  rw [show (fun θ' : ℝ => Real.sin (2 * θ')) = (Real.sin ∘ fun θ' : ℝ => 2 * θ') from rfl,
    h.deriv]
  ring

/-! ## Absorption of the constants

Every piece of the computation has a constant of the form `c·A^p·K` (or `c·α·A^p·K`) with
`p ≤ 4`; these lemmas show that such a piece is dominated by `c·A⁴K(α+1)`, using `A ≥ 1`,
`K ≥ 0`, `α ≥ 0`. -/

private theorem absorb_le {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) (hc : 0 ≤ c)
    {p : ℕ} (hp : p ≤ 4) : c * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have hA4K : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg (pow_nonneg hA0 4) hK
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) := mul_nonneg hA4K (by linarith)
  have h1 : c * A ^ p * K ≤ c * A ^ 4 * K := by
    refine mul_le_mul_of_nonneg_right ?_ hK
    exact mul_le_mul_of_nonneg_left hp4 hc
  have h2 : c * (A ^ 4 * K) ≤ c * (A ^ 4 * K * (α + 1)) := by
    have hα1 : (1 : ℝ) ≤ α + 1 := by linarith
    calc c * (A ^ 4 * K) = c * (A ^ 4 * K) * 1 := by ring
      _ ≤ c * (A ^ 4 * K) * (α + 1) := mul_le_mul_of_nonneg_left hα1 (mul_nonneg hc hA4K)
      _ = c * (A ^ 4 * K * (α + 1)) := by ring
  linarith

private theorem absorb_le_alpha {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) :
    c * α * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have hA4K : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg (pow_nonneg hA0 4) hK
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) := mul_nonneg hA4K hα1
  have hstep1 : c * α * A ^ p * K ≤ c * A ^ p * K * (α + 1) := by
    have hle : α ≤ α + 1 := by linarith
    have h0 : (0 : ℝ) ≤ c * A ^ p * K := mul_nonneg (mul_nonneg hc (pow_nonneg hA0 p)) hK
    calc c * α * A ^ p * K = (c * A ^ p * K) * α := by ring
      _ ≤ (c * A ^ p * K) * (α + 1) := mul_le_mul_of_nonneg_left hle h0
      _ = c * A ^ p * K * (α + 1) := by ring
  have hstep2 : c * A ^ p * K * (α + 1) ≤ c * (A ^ 4 * K * (α + 1)) := by
    have h : A ^ p * K * (α + 1) ≤ A ^ 4 * K * (α + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp4 hK) hα1
    calc c * A ^ p * K * (α + 1) = c * (A ^ p * K * (α + 1)) := by ring
      _ ≤ c * (A ^ 4 * K * (α + 1)) := mul_le_mul_of_nonneg_left h hc
  linarith

/-- `2α·(256 A³K + 80 A²K) ≤ 1000·A⁴K(α+1)`. -/
private theorem alpha_one {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) :
    2 * α * (256 * A ^ 3 * K + 80 * A ^ 2 * K) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have h1 : 512 * α * A ^ 3 * K ≤ 512 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 512) (by norm_num) (p := 3) (by norm_num)
  have h2 : 160 * α * A ^ 3 * K ≤ 160 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 160) (by norm_num) (p := 3) (by norm_num)
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
  have hstep : 80 * (α * K) * A ^ 2 ≤ 80 * (α * K) * A ^ 3 :=
    mul_le_mul_of_nonneg_left hA23 (mul_nonneg (by norm_num) (mul_nonneg hα hK))
  nlinarith [h1, h2, hstep, hM]

/-- `2α·((256 A³K + 80 A²K) + (256 A³K + 80 A²K)) ≤ 2000·A⁴K(α+1)`. -/
private theorem alpha_pair {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) :
    2 * α * ((256 * A ^ 3 * K + 80 * A ^ 2 * K) + (256 * A ^ 3 * K + 80 * A ^ 2 * K))
      ≤ 2000 * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have h1 : 1024 * α * A ^ 3 * K ≤ 1024 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 1024) (by norm_num) (p := 3) (by norm_num)
  have h2 : 320 * α * A ^ 3 * K ≤ 320 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 320) (by norm_num) (p := 3) (by norm_num)
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
  have hstep : 160 * (α * K) * A ^ 2 ≤ 160 * (α * K) * A ^ 3 :=
    mul_le_mul_of_nonneg_left hA23 (mul_nonneg (by norm_num) (mul_nonneg hα hK))
  nlinarith [h1, h2, hstep, hM]

/-! ## The sum decomposition of `EH α Y` -/

private theorem EH_split {α : ℝ} {Y : ℝ → ℝ → ℝ} (z θ : ℝ) :
    EH α Y z θ = EH12 α Y z θ + EH3 Y z θ := by
  simp only [EH, EH12, EH1, EH2, EH3, Gfun, Zfun, Yrho, Sqs, Rho, Sin2, Tblk,
    Work.Construction.s2]
  ring

/-! ## The `∂_θ`-identity -/

/-- **The explicit form of `∂_θ(EH α Y)` on the open quadrant.**  The right-hand side `Dsum`
is the sum that the product rules produce: the `∂_θ` of `2Y`, of `2α sin²θ(Y/(z+1)+D_zY)`
(four terms) and of `sin(2θ)∂_θY` (two terms). -/
private theorem pth_EH_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hYs : EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EH α Y) z θ = Dsum α Y z θ := by
  intro z θ hz hθ hθ'
  have sSqs : EllipticEst.SmoothOpen Sqs := smooth_Sqs
  have sSin : EllipticEst.SmoothOpen Sin2 := smooth_Sin2
  have sRho : EllipticEst.SmoothOpen Rho := smooth_Rho
  have sYrho : EllipticEst.SmoothOpen (Yrho Y) := Fbq_smoothOpen_mul hYs sRho
  have sYblk : EllipticEst.SmoothOpen (Yblk Y) := hYs.Dz
  have sZ : EllipticEst.SmoothOpen (Zfun Y) := SmoothOpen.add sYrho sYblk
  have sG : EllipticEst.SmoothOpen (Gfun Y) := Fbq_smoothOpen_mul sSqs sZ
  have sPY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sEH1 : EllipticEst.SmoothOpen (EH1 Y) := SmoothOpen.const_mul hYs 2
  have sEH2 : EllipticEst.SmoothOpen (EH2 α Y) := SmoothOpen.const_mul sG (2 * α)
  have sEH3 : EllipticEst.SmoothOpen (EH3 Y) := Fbq_smoothOpen_mul sSin sPY
  have sEH12 : EllipticEst.SmoothOpen (EH12 α Y) := SmoothOpen.add sEH1 sEH2
  have hsplit : EH α Y = fun z θ => EH12 α Y z θ + EH3 Y z θ := by
    funext a b
    exact EH_split a b
  rw [hsplit]
  rw [show Work.Spaces.pth (fun z θ => EH12 α Y z θ + EH3 Y z θ) z θ
        = Work.Spaces.pth (EH12 α Y) z θ + Work.Spaces.pth (EH3 Y) z θ from
      pth_add_Q0 (f := EH12 α Y) (g := EH3 Y) sEH12 sEH3 z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH12 α Y) z θ
        = Work.Spaces.pth (EH1 Y) z θ + Work.Spaces.pth (EH2 α Y) z θ from
      pth_add_Q0 (f := EH1 Y) (g := EH2 α Y) sEH1 sEH2 z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH1 Y) z θ = 2 * Work.Spaces.pth Y z θ from
      congrFun (congrFun (pth_const_mul (2 : ℝ) Y) z) θ]
  rw [show Work.Spaces.pth (EH2 α Y) z θ = (2 * α) * Work.Spaces.pth (Gfun Y) z θ from
      congrFun (congrFun (pth_const_mul (2 * α) (Gfun Y)) z) θ]
  rw [show Work.Spaces.pth (Gfun Y) z θ
        = Work.Spaces.pth Sqs z θ * Zfun Y z θ
          + Sqs z θ * Work.Spaces.pth (Zfun Y) z θ from
      Fbq_pth_mul (f := Sqs) (g := Zfun Y) sSqs sZ z θ hz hθ hθ']
  rw [show Work.Spaces.pth (Zfun Y) z θ
        = Work.Spaces.pth (Yrho Y) z θ + Work.Spaces.pth (Yblk Y) z θ from
      pth_add_Q0 (f := Yrho Y) (g := Yblk Y) sYrho sYblk z θ hz hθ hθ']
  rw [show Work.Spaces.pth (Yrho Y) z θ = Work.Spaces.pth Y z θ * Rho z θ from by
    show Work.Spaces.pth (fun z θ => Y z θ * Rho z θ) z θ
        = Work.Spaces.pth Y z θ * Rho z θ
    rw [Fbq_pth_mul (f := Y) (g := Rho) hYs sRho z θ hz hθ hθ', pth_Rho z θ,
      mul_zero, add_zero]]
  rw [show Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ from
      pth_zpz_smoothOpen hYs z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH3 Y) z θ
        = Work.Spaces.pth Sin2 z θ * Work.Spaces.pth Y z θ
          + Sin2 z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ from
      Fbq_pth_mul (f := Sin2) (g := Work.Spaces.pth Y) sSin sPY z θ hz hθ hθ']
  rw [pth_Sqs z θ, pth_Sin2 z θ]
  simp only [Dsum, Inner, Zfun, Yrho, Sqs, Sin2, DSq, DCos2, Rho, Work.Spaces.Dth]
  ring

/-! ## The main bound -/

private theorem FbEH_aux {α K A : ℝ} {Y : ℝ → ℝ → ℝ}
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hA : 1 ≤ A) (hYs : EllipticEst.SmoothOpen Y)
    (hsq : F0 6 A Sqs) (hc2 : F0 6 A (fun _ θ => Real.cos (2 * θ)))
    (hsi : F0 6 A Sin2) (hci : F0 6 A (fun z _ => (1 + z)⁻¹)) (hY : Fb 6 (A * K) Y) :
    Fb 4 (10 ^ 7 * A ^ 4 * K * (α + 1)) (EH α Y) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hAK : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hM00 : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  set M : ℝ := A ^ 4 * K * (α + 1) with hM
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; exact hM00
  -- ## the coefficient data
  have hRho6 : F0 6 A Rho := F0_congr (fun z θ _ _ _ => by
    show (z + 1)⁻¹ = (1 + z)⁻¹
    rw [add_comm 1 z]) hci
  have hRho4 : F0 4 A Rho := hRho6.mono (by norm_num) le_rfl
  have hSqs4 : F0 4 A Sqs := hsq.mono (by norm_num) le_rfl
  have hSin4 : F0 4 A Sin2 := hsi.mono (by norm_num) le_rfl
  have hCos24 : F0 4 A (fun _ θ => Real.cos (2 * θ)) := hc2.mono (by norm_num) le_rfl
  have hDSq6 : F0 6 A DSq := F0_congr (fun z θ _ _ _ => by
    show 2 * Real.sin θ * Real.cos θ = Real.sin (2 * θ)
    rw [Real.sin_two_mul]) hsi
  have hDSq4 : F0 4 A DSq := hDSq6.mono (by norm_num) le_rfl
  have hDCos2 : F0 4 (2 * A) DCos2 := by
    have h := F0_const_mul (2 : ℝ) hCos24
    have hc : |(2 : ℝ)| * A = 2 * A := by norm_num
    rw [hc] at h
    exact h
  have hY4 : Fb 4 (A * K) Y := hY.mono (by norm_num) le_rfl
  have hY5f0 : F0 5 (A * K) Y := hY.f0.mono (by norm_num) le_rfl
  have hPY4 : F0 4 (A * K) (Work.Spaces.pth Y) := hY4.fd
  have hPY5 : F0 5 (A * K) (Work.Spaces.pth Y) := hY.fd.mono (by norm_num) le_rfl
  -- ## smoothness
  have sRho : EllipticEst.SmoothOpen Rho := smooth_Rho
  have sSqs : EllipticEst.SmoothOpen Sqs := smooth_Sqs
  have sSin : EllipticEst.SmoothOpen Sin2 := smooth_Sin2
  have sDSq : EllipticEst.SmoothOpen DSq := smooth_DSq
  have sDCos2 : EllipticEst.SmoothOpen DCos2 := smooth_DCos2
  have sYrho : EllipticEst.SmoothOpen (Yrho Y) := Fbq_smoothOpen_mul hYs sRho
  have sYblk : EllipticEst.SmoothOpen (Yblk Y) := hYs.Dz
  have sZ : EllipticEst.SmoothOpen (Zfun Y) := SmoothOpen.add sYrho sYblk
  have sG : EllipticEst.SmoothOpen (Gfun Y) := Fbq_smoothOpen_mul sSqs sZ
  have sPY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sPYRho : EllipticEst.SmoothOpen (fun z θ => Work.Spaces.pth Y z θ * Rho z θ) :=
    Fbq_smoothOpen_mul sPY sRho
  have sYblkP : EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) := sPY.Dz
  have sSqsYrhoP : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)) :=
    Fbq_smoothOpen_mul sSqs sPYRho
  have sSqsYblkP : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    Fbq_smoothOpen_mul sSqs sYblkP
  have sIn34 : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.add sSqsYrhoP sSqsYblkP
  have sQ2 : EllipticEst.SmoothOpen (fun z θ => DSq z θ * Zfun Y z θ) :=
    Fbq_smoothOpen_mul sDSq sZ
  have sInner : EllipticEst.SmoothOpen (Inner Y) := by
    show EllipticEst.SmoothOpen (fun z θ => DSq z θ * Zfun Y z θ
      + (Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ))
    exact SmoothOpen.add sQ2 sIn34
  have sQ56 : EllipticEst.SmoothOpen
      (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.add (Fbq_smoothOpen_mul sDCos2 sPY) sPY.Dth
  have sEH1 : EllipticEst.SmoothOpen (EH1 Y) := SmoothOpen.const_mul hYs 2
  have sEH2 : EllipticEst.SmoothOpen (EH2 α Y) := SmoothOpen.const_mul sG (2 * α)
  have sEH3 : EllipticEst.SmoothOpen (EH3 Y) := Fbq_smoothOpen_mul sSin sPY
  have sEH12 : EllipticEst.SmoothOpen (EH12 α Y) := SmoothOpen.add sEH1 sEH2
  -- ## auxiliary flat bounds
  have hYblk4 : F0 4 (5 * (A * K)) (Yblk Y) := by
    have hc : ((↑(4 : ℕ) : ℝ) + 1) * (A * K) = 5 * (A * K) := by norm_num
    exact (F0_zpz (n := 4) hAK hYs hY5f0).mono le_rfl (le_of_eq hc)
  have hYrho4 : F0 4 (16 * A ^ 2 * K) (Yrho Y) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hY4.f0) (Fbq_nonneg_of_F0 hRho4) hYs sRho hY4.f0 hRho4
    have hc : (2 : ℝ) ^ 4 * (A * K) * A = 16 * A ^ 2 * K := by ring
    rw [hc] at h
    exact h
  have hZ4 : F0 4 (16 * A ^ 2 * K + 5 * (A * K)) (Zfun Y) := by
    have h := F0_add sYrho sYblk hYrho4 hYblk4
    exact h
  have hG4 : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K) (Gfun Y) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hZ4) sSqs sZ hSqs4 hZ4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K + 5 * (A * K))
        = 256 * A ^ 3 * K + 80 * A ^ 2 * K := by ring
    rw [hc] at h
    exact h
  have hPYrho4 : F0 4 (16 * A ^ 2 * K)
      (fun z θ => Work.Spaces.pth Y z θ * Rho z θ) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hPY4) (Fbq_nonneg_of_F0 hRho4) sPY sRho hPY4 hRho4
    have hc : (2 : ℝ) ^ 4 * (A * K) * A = 16 * A ^ 2 * K := by ring
    rwa [hc] at h
  have hYblkP4 : F0 4 (5 * (A * K)) (Yblk (Work.Spaces.pth Y)) := by
    have hc : ((↑(4 : ℕ) : ℝ) + 1) * (A * K) = 5 * (A * K) := by norm_num
    exact (F0_zpz (n := 4) hAK sPY hPY5).mono le_rfl (le_of_eq hc)
  -- ## the first half: `F0 4 (EH α Y)`
  have hEH1 : F0 4 (1000 * M) (EH1 Y) := by
    have h : F0 4 (2 * A * K) (EH1 Y) := by
      have h0 := F0_const_mul (2 : ℝ) hY4.f0
      have hc : |(2 : ℝ)| * (A * K) = 2 * A * K := by ring
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 2) (by norm_num) (p := 1) (by norm_num)
    have hlt : (2 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [pow_one] using hb) hlt
  have hEH2 : F0 4 (1000 * M) (EH2 α Y) := by
    have h : F0 4 (2 * α * (256 * A ^ 3 * K + 80 * A ^ 2 * K)) (EH2 α Y) := by
      have h0 := F0_const_mul (2 * α) hG4
      have hc : |2 * α| = 2 * α := abs_of_nonneg (by linarith)
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    exact alpha_one hA hK hα
  have hEH3 : F0 4 (1000 * M) (EH3 Y) := by
    have h : F0 4 (16 * A ^ 2 * K) (EH3 Y) := by
      have h0 := F0_mul (Fbq_nonneg_of_F0 hSin4) (Fbq_nonneg_of_F0 hPY4) sSin sPY hSin4 hPY4
      have hc : (2 : ℝ) ^ 4 * A * (A * K) = 16 * A ^ 2 * K := by ring
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 16) (by norm_num) (p := 2) (by norm_num)
    linarith [hb, hM00]
  have hF0EH : F0 4 ((1000 * M + 1000 * M) + 1000 * M) (EH α Y) := by
    have h12 : F0 4 (1000 * M + 1000 * M) (EH12 α Y) := by
      have h := F0_add sEH1 sEH2 hEH1 hEH2
      exact h
    have h123 : F0 4 ((1000 * M + 1000 * M) + 1000 * M)
        (fun z θ => EH12 α Y z θ + EH3 Y z θ) := F0_add sEH12 sEH3 h12 hEH3
    exact F0_congr (fun z θ _ _ _ => EH_split z θ) h123
  -- ## the second half: `F0 4 (∂_θ(EH α Y))`
  have q1 : F0 4 (1000 * M) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
    have h : F0 4 (2 * A * K) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
      have h0 := F0_const_mul (2 : ℝ) hPY4
      have hc : |(2 : ℝ)| * (A * K) = 2 * A * K := by ring
      rwa [hc] at h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 2) (by norm_num) (p := 1) (by norm_num)
    have hlt : (2 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [pow_one] using hb) hlt
  have q2n : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K)
      (fun z θ => DSq z θ * Zfun Y z θ) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hDSq4) (Fbq_nonneg_of_F0 hZ4) sDSq sZ hDSq4 hZ4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K + 5 * (A * K))
        = 256 * A ^ 3 * K + 80 * A ^ 2 * K := by ring
    rwa [hc] at h0
  have q3n : F0 4 (256 * A ^ 3 * K)
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hPYrho4)
      sSqs sPYRho hSqs4 hPYrho4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K) = 256 * A ^ 3 * K := by ring
    rwa [hc] at h0
  have q4n : F0 4 (80 * A ^ 2 * K)
      (fun z θ => Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hYblkP4)
      sSqs sYblkP hSqs4 hYblkP4
    have hc : (2 : ℝ) ^ 4 * A * (5 * (A * K)) = 80 * A ^ 2 * K := by ring
    rwa [hc] at h0
  have h34n : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K)
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_add sSqsYrhoP sSqsYblkP q3n q4n
  have hInnerNat : F0 4 ((256 * A ^ 3 * K + 80 * A ^ 2 * K)
      + (256 * A ^ 3 * K + 80 * A ^ 2 * K)) (Inner Y) := by
    have h := F0_add sQ2 sIn34 q2n h34n
    exact h
  have hB : F0 4 (2000 * M) (fun z θ => (2 * α) * Inner Y z θ) := by
    have h0 : F0 4 (|2 * α| * ((256 * A ^ 3 * K + 80 * A ^ 2 * K)
        + (256 * A ^ 3 * K + 80 * A ^ 2 * K)))
        (fun z θ => (2 * α) * Inner Y z θ) := F0_const_mul (2 * α) hInnerNat
    have h2 : |2 * α| = 2 * α := abs_of_nonneg (by linarith)
    rw [h2] at h0
    refine h0.mono le_rfl ?_
    rw [hM]
    exact alpha_pair hA hK hα
  have q5 : F0 4 (1000 * M) (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ) := by
    have h : F0 4 (32 * A ^ 2 * K) (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ) := by
      have h0 := F0_mul (Fbq_nonneg_of_F0 hDCos2) (Fbq_nonneg_of_F0 hPY4)
        sDCos2 sPY hDCos2 hPY4
      have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * K) = 32 * A ^ 2 * K := by ring
      rwa [hc] at h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 32) (by norm_num) (p := 2) (by norm_num)
    linarith [hb, hM00]
  have q6 : F0 4 (1000 * M) (Work.Spaces.Dth (Work.Spaces.pth Y)) := by
    have h : F0 4 (A * K) (Work.Spaces.Dth (Work.Spaces.pth Y)) := F0_Dth hPY5
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 1) (by norm_num) (p := 1) (by norm_num)
    have hlt : (1 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [one_mul, pow_one] using hb) hlt
  have h56 : F0 4 (1000 * M + 1000 * M)
      (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) := F0_add (Fbq_smoothOpen_mul sDCos2 sPY) sPY.Dth q5 q6
  have hDsum : F0 4 ((1000 * M + 2000 * M) + (1000 * M + 1000 * M)) (Dsum α Y) := by
    have hAB : F0 4 (1000 * M + 2000 * M)
        (fun z θ => 2 * Work.Spaces.pth Y z θ + (2 * α) * Inner Y z θ) :=
      F0_add (SmoothOpen.const_mul sPY 2) (SmoothOpen.const_mul sInner (2 * α)) q1 hB
    have h := F0_add (SmoothOpen.add (SmoothOpen.const_mul sPY 2)
        (SmoothOpen.const_mul sInner (2 * α))) sQ56 hAB h56
    exact h
  have hF0D : F0 4 ((1000 * M + 2000 * M) + (1000 * M + 1000 * M))
      (Work.Spaces.pth (EH α Y)) :=
    F0_congr (fun z θ hz hθ hθ' => pth_EH_eq hYs z θ hz hθ hθ') hDsum
  -- ## absorption of the total constants
  have hb1 : ((1000 * M + 1000 * M) + 1000 * M) ≤ 10 ^ 7 * A ^ 4 * K * (α + 1) := by
    rw [hM]
    nlinarith [hM00]
  have hb2 : ((1000 * M + 2000 * M) + (1000 * M + 1000 * M))
      ≤ 10 ^ 7 * A ^ 4 * K * (α + 1) := by
    rw [hM]
    nlinarith [hM00]
  exact ⟨hF0EH.mono le_rfl hb1, hF0D.mono le_rfl hb2⟩

/-- **The flat bound for `EH`.**  There is a universal constant `C` with: whenever `Y` is
`C^∞` on the open quadrant, `A ≥ 1`, `K ≥ 0`, `α ≥ 0`, the six coefficient functions are
`F0 6 A` and `Fb 6 (A·K) Y`, then `Fb 4 (C·A⁴·K·(α+1)) (EH α Y)`. -/
theorem FbEH : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EH α Y) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α K A Y hα hK hA hYs hsq _hccs hc2 hsi _hcz hci hY
  exact FbEH_aux hα hK hA hYs hsq hc2 hsi hci hY

end Work.FTS.PhiStar.StarPkgo2Aux
