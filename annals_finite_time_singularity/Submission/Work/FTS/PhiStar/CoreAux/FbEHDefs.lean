/-
# `FTS/PhiStar/CoreAux/FbEHDefs.lean` — the vocabulary of the `EH`-bound

`Work.FTS.PhiStar.EH α Y` is the flat expression

`EH α Y = 2·Y + 2α·sin²θ·(Y/(z+1) + z∂_zY) + sin(2θ)·∂_θY`

(the `((z+1)/z)·ℛ(Φ̃_*)`-field of `FieldsDefs.lean`).  The task `Fb_EH_bound` asks for the flat
bound `Fb 4 (C·A⁴(K+1)(α+1)) (EH α Y)` from `Fb 6 (A(K+1)) Y` and the flat bounds of the six
coefficient functions.

This file fixes the vocabulary used to make that statement manageable, and proves the two
elementary layers: the smoothness of the coefficients and their `θ`-derivatives.

* the coefficients `EhPhi1` (sin²θ), `EhSin2` (sin 2θ), `EhCos2` (cos 2θ), `EhRho` (z/(1+z)),
  `EhRhoInv` ((1+z)⁻¹), `EhZ` (z), and the two angular derivatives
  `EhDSinSq = ∂_θ(sin²θ) = sin 2θ`, `EhDSin2 = ∂_θ(sin 2θ) = 2 cos 2θ`;
* the body `EhX Y = Y/(z+1) + z∂_zY` and its `θ`-derivative `EhDX Y = ∂_θY/(z+1) + z∂_z(∂_θY)`;
* the two canonical forms `EhC α Y` (equal to `EH α Y` pointwise on the quadrant) and
  `EhD α Y` (equal to `∂_θ(EH α Y)` pointwise on the quadrant), written as sums of products of
  the coefficients with the blocks `Y`, `∂_θY`, `z∂_zY`, `z∂_z(∂_θY)` — the shape which the
  bilinear product calculus `F0_mul`/`F0_add`/`F0_zpz` can bound with a constant of the order
  `A^j·(K+1)·(α+1)` (the squared constants of `Fb_basic` would be far too large);
* `SmoothOpen` for every one of these pieces;
* the pointwise `θ`-derivative identities for the coefficients;
* `Fb_const_mul`, the `Fb`-analogue of `F0_const_mul`.

Nothing here is a `sorry` or an axiom.
-/
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
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficients and their `θ`-derivatives -/

/-- `sin²θ` as a function on the quadrant. -/
def EhPhi1 : ℝ → ℝ → ℝ := fun _ θ => Real.sin θ ^ 2

/-- `sin(2θ)` as a function on the quadrant. -/
def EhSin2 : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- `cos(2θ)` as a function on the quadrant. -/
def EhCos2 : ℝ → ℝ → ℝ := fun _ θ => Real.cos (2 * θ)

/-- `z/(1+z)` as a function on the quadrant. -/
def EhRho : ℝ → ℝ → ℝ := fun z _ => z / (1 + z)

/-- `(1+z)⁻¹` as a function on the quadrant. -/
def EhRhoInv : ℝ → ℝ → ℝ := fun z _ => (1 + z)⁻¹

/-- `z` as a function on the quadrant. -/
def EhZ : ℝ → ℝ → ℝ := fun z _ => z

/-- `∂_θ(sin²θ) = 2 sinθ cosθ = sin 2θ`. -/
def EhDSinSq : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.sin θ * Real.cos θ

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
def EhDSin2 : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.cos (2 * θ)

/-- `EhSin2 = EhDSinSq`, i.e. `sin 2θ = 2 sinθ cosθ`. -/
theorem eh_sin2_eq_dsinsq (z θ : ℝ) : EhSin2 z θ = EhDSinSq z θ := by
  simp only [EhSin2, EhDSinSq, Real.sin_two_mul]

/-- `EhDSin2 = 2·EhCos2`. -/
theorem eh_dsin2_eq (z θ : ℝ) : EhDSin2 z θ = 2 * EhCos2 z θ := rfl

/-! ## Smoothness of the coefficients -/

theorem eh_smooth_ph1 : Work.FTS.EllipticEst.SmoothOpen EhPhi1 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
    (Real.contDiff_sin.comp contDiff_snd).pow 2
  exact h.contDiffOn

theorem eh_smooth_sin2 : Work.FTS.EllipticEst.SmoothOpen EhSin2 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) := contDiff_const.mul contDiff_snd
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := Real.contDiff_sin.comp h1
  exact h.contDiffOn

theorem eh_smooth_cos2 : Work.FTS.EllipticEst.SmoothOpen EhCos2 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) := contDiff_const.mul contDiff_snd
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.cos (2 * p.2)) := Real.contDiff_cos.comp h1
  exact h.contDiffOn

theorem eh_smooth_z : Work.FTS.EllipticEst.SmoothOpen EhZ := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  exact h.contDiffOn

theorem eh_smooth_dsinsq : Work.FTS.EllipticEst.SmoothOpen EhDSinSq :=
  Work.FTS.PhiStar.CoreAux.SmoothOpen.congr eh_smooth_sin2
    (fun z θ _ _ _ => eh_sin2_eq_dsinsq z θ)

theorem eh_smooth_dsin2 : Work.FTS.EllipticEst.SmoothOpen EhDSin2 :=
  Work.FTS.PhiStar.CoreAux.SmoothOpen.congr
    (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul (f := EhCos2) eh_smooth_cos2 2)
    (fun z θ _ _ _ => rfl)

theorem eh_smooth_rhoinv : Work.FTS.EllipticEst.SmoothOpen EhRhoInv := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have hfull : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) (Work.FTS.EllipticEst.Q0) :=
      (contDiff_const.add contDiff_fst).contDiffOn
    refine h1.inv fun p hp => ?_
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    intro h
    linarith
  refine hfull.congr fun p hp => ?_
  show ((1 : ℝ) + p.1)⁻¹ = Function.uncurry EhRhoInv p
  simp only [EhRhoInv, Function.uncurry]

theorem eh_smooth_rho : Work.FTS.EllipticEst.SmoothOpen EhRho := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have hfull : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * ((1 : ℝ) + p.1)⁻¹)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) (Work.FTS.EllipticEst.Q0) :=
      (contDiff_const.add contDiff_fst).contDiffOn
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹)
        (Work.FTS.EllipticEst.Q0) := h1.inv fun p hp => by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      intro h
      linarith
    exact contDiffOn_fst.mul h2
  refine hfull.congr fun p hp => ?_
  show p.1 * ((1 : ℝ) + p.1)⁻¹ = Function.uncurry EhRho p
  simp only [EhRho, Function.uncurry]
  rw [div_eq_mul_inv]

/-! ## The `θ`-derivatives of the coefficients -/

theorem eh_pth_ph1 (z θ : ℝ) : Work.Spaces.pth EhPhi1 z θ = EhSin2 z θ := by
  show deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = Real.sin (2 * θ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2)
      (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
  rw [h.deriv, Real.sin_two_mul]
  ring

theorem eh_pth_sin2 (z θ : ℝ) : Work.Spaces.pth EhSin2 z θ = EhDSin2 z θ := by
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]
  ring

theorem eh_pth_rho (z θ : ℝ) : Work.Spaces.pth EhRho z θ = 0 := by
  show deriv (fun _ : ℝ => z / (1 + z)) θ = 0
  rw [deriv_const]

theorem eh_pth_rhoinv (z θ : ℝ) : Work.Spaces.pth EhRhoInv z θ = 0 := by
  show deriv (fun _ : ℝ => (1 + z)⁻¹) θ = 0
  rw [deriv_const]

theorem eh_pth_z (z θ : ℝ) : Work.Spaces.pth EhZ z θ = 0 := by
  show deriv (fun _ : ℝ => z) θ = 0
  rw [deriv_const]

/-! ## `F0`-bounds for the two angular derivatives -/

theorem eh_F0_dsinsq {m : ℕ} {A : ℝ} (h : Work.FTS.PhiStar.F0 m A EhSin2) :
    Work.FTS.PhiStar.F0 m A EhDSinSq :=
  F0_congr (f := EhDSinSq) (g := EhSin2) (fun z θ _ _ _ => (eh_sin2_eq_dsinsq z θ).symm) h

theorem eh_F0_dsin2 {m : ℕ} {A : ℝ} (h : Work.FTS.PhiStar.F0 m A EhCos2) :
    Work.FTS.PhiStar.F0 m (|(2 : ℝ)| * A) EhDSin2 :=
  F0_congr (f := EhDSin2) (g := fun z θ => 2 * EhCos2 z θ)
    (fun z θ _ _ _ => eh_dsin2_eq z θ) (F0_const_mul (2 : ℝ) h)

/-! ## The body, its `θ`-derivative, and the two canonical forms -/

/-- `X = Y/(z+1) + z∂_zY`, the bracket multiplying `2α sin²θ` in `EH`. -/
def EhX (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Y z θ * EhRhoInv z θ + Yblk Y z θ

/-- `∂_θX = ∂_θY/(z+1) + z∂_z(∂_θY)`. -/
def EhDX (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ + Yblk (Work.Spaces.pth Y) z θ

/-- **The canonical form of `EH α Y`**, a sum of products of the bounded coefficients with the
blocks `Y`, `z∂_zY`, `∂_θY`. -/
def EhC (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    2 * Y z θ
      + ((2 * α) * (EhPhi1 z θ * EhX Y z θ)
          + EhSin2 z θ * Work.Spaces.pth Y z θ)

/-- **The canonical form of `∂_θ(EH α Y)`**: the Leibniz expansion, a sum of products of the
coefficients with the blocks `∂_θY`, `z∂_z(∂_θY)`, `D_θ(∂_θY)`. -/
def EhD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    2 * Work.Spaces.pth Y z θ
      + ((2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
          + (EhDSin2 z θ * Work.Spaces.pth Y z θ
              + Work.Spaces.Dth (Work.Spaces.pth Y) z θ))

/-! ## Smoothness of the pieces -/

theorem eh_smooth_yblk {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := by
  have h : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Y z θ) :=
    Fbq_smoothOpen_mul (f := fun z _ : ℝ => z) (g := Work.Spaces.pz Y) eh_smooth_z hY.pz
  exact h

theorem eh_smooth_EhX {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhX Y) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul (f := Y) (g := EhRhoInv) hY eh_smooth_rhoinv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hY
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Y z θ * EhRhoInv z θ + Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add (f := fun z θ => Y z θ * EhRhoInv z θ)
      (g := Yblk Y) h1 h2
  exact h3

theorem eh_smooth_EhDX {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhDX Y) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul (f := Work.Spaces.pth Y) (g := EhRhoInv) hY.pth eh_smooth_rhoinv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) := eh_smooth_yblk hY.pth
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ + Yblk (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (f := fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ)
      (g := Yblk (Work.Spaces.pth Y)) h1 h2
  exact h3

theorem eh_smooth_EhC {α : ℝ} {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhC α Y) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul (f := Y) hY 2
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
      (f := fun z θ => EhPhi1 z θ * EhX Y z θ)
      (Fbq_smoothOpen_mul (f := EhPhi1) (g := EhX Y) eh_smooth_ph1 (eh_smooth_EhX hY)) (2 * α)
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul (f := EhSin2) (g := Work.Spaces.pth Y) eh_smooth_sin2 hY.pth
  have h4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (f := fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ))
      (g := fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) h2 h3
  have h5 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Y z θ
        + ((2 * α) * (EhPhi1 z θ * EhX Y z θ)
            + EhSin2 z θ * Work.Spaces.pth Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add (f := fun z θ => 2 * Y z θ)
      (g := fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) h1 h4
  exact h5

theorem eh_smooth_EhD {α : ℝ} {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhD α Y) := by
  have h0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul (f := Work.Spaces.pth Y) hY.pth 2
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
      (f := fun z θ => EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.add
        (f := fun z θ => EhDSinSq z θ * EhX Y z θ)
        (g := fun z θ => EhPhi1 z θ * EhDX Y z θ)
        (Fbq_smoothOpen_mul (f := EhDSinSq) (g := EhX Y) eh_smooth_dsinsq (eh_smooth_EhX hY))
        (Fbq_smoothOpen_mul (f := EhPhi1) (g := EhDX Y) eh_smooth_ph1 (eh_smooth_EhDX hY))) (2 * α)
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (f := fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ)
      (g := Work.Spaces.Dth (Work.Spaces.pth Y))
      (Fbq_smoothOpen_mul (f := EhDSin2) (g := Work.Spaces.pth Y) eh_smooth_dsin2 hY.pth)
      hY.pth.Dth
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
        + (EhDSin2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (f := fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ))
      (g := fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) h1 h2
  have h4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Spaces.pth Y z θ
        + ((2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
            + (EhDSin2 z θ * Work.Spaces.pth Y z θ
                + Work.Spaces.Dth (Work.Spaces.pth Y) z θ))) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add (f := fun z θ => 2 * Work.Spaces.pth Y z θ)
      (g := fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
        + (EhDSin2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)) h0 h3
  exact h4

/-! ## Scalar multiples in the shifted class -/

theorem Fb_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ)
    (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n (|c| * K) (fun z θ => c * f z θ) := by
  have h2 : Work.FTS.PhiStar.F0 n (|c| * K)
      (Work.Spaces.pth (fun z θ => c * f z θ)) := by
    simpa only [pth_const_mul] using F0_const_mul c hf.fd
  exact ⟨F0_const_mul c hf.f0, h2⟩

end Work.FTS.PhiStar.CoreAux
