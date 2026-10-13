import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS_RegExport.RXT.st1_fb_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux

namespace BslDzAux

/-! ## Smoothness of the partials of a `C^n` function

The two lemmas below make the finite-order regularity of the partial derivatives available:
`∂_z f` (resp. `∂_θ f`) loses exactly one order of differentiability.  The proofs identify the
partial with the evaluation of `fderiv` on a basis vector, use `ContDiffAt.fderiv_right`, and
transfer the resulting `ContDiffAt` statement back along the eventual equality
`pz f =ᶠ fun q => (fderiv ℝ (uncurry f) q) (1,0)` (valid where `f` is differentiable, which is
eventual by `ContDiffAt.eventually`). -/

/-- `∂_z` lowers the order of differentiability by one. -/
theorem contDiffAt_uncurry_pz_succ {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (n : ℕ)
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) p) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz f)) p := by
  have hfd : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry f)) p :=
    h.fderiv_right (by push_cast; rfl)
  have hev : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by
      intro hh
      exact ENat.natCast_ne_top (n + 1) (WithTop.coe_injective hh))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) q) (1, 0)) := by
    filter_upwards [hev] with q hq
    exact Work.Spaces.pz_eq_fderiv hq
  exact (hfd.clm_apply contDiffAt_const).congr_of_eventuallyEq heq

/-- `∂_θ` lowers the order of differentiability by one. -/
theorem contDiffAt_uncurry_pth_succ {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (n : ℕ)
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) p) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth f)) p := by
  have hfd : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry f)) p :=
    h.fderiv_right (by push_cast; rfl)
  have hev : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by
      intro hh
      exact ENat.natCast_ne_top (n + 1) (WithTop.coe_injective hh))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) q) (0, 1)) := by
    filter_upwards [hev] with q hq
    exact Work.Spaces.pth_eq_fderiv hq
  exact (hfd.clm_apply contDiffAt_const).congr_of_eventuallyEq heq

/-! ## The factor `z` is invisible to `∂_θ` -/

/-- Multiplication by the radial variable is constant in `θ`, hence invisible to `∂_θ`. -/
lemma pth_z_mul (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => z' * X z' θ') z θ = z * Work.Spaces.pth X z θ := by
  show deriv (fun θ' => z * X z θ') θ = z * deriv (fun θ' => X z θ') θ
  rw [deriv_const_mul_field]

/-- The same, for two angular derivatives. -/
lemma pthIter_two_z_mul (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z' θ' => z' * X z' θ') z θ
      = z * Work.Spaces.pthIter 2 X z θ := by
  have hfun : Work.Spaces.pth (fun z' θ' => z' * X z' θ')
      = fun z' θ' => z' * Work.Spaces.pth X z' θ' :=
    funext fun z' => funext fun θ' => pth_z_mul X z' θ'
  show Work.Spaces.pth (Work.Spaces.pth (fun z' θ' => z' * X z' θ')) z θ
      = z * Work.Spaces.pth (Work.Spaces.pth X) z θ
  rw [hfun, pth_z_mul]

/-! ## Congruence of the partials along an eventual equality -/

/-- Functions agreeing near `(z,θ)` have the same `∂_θ` there. -/
lemma pth_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually h
  exact hnb.deriv_eq

/-- Functions agreeing near `(z,θ)` have the same `∂_z` there. -/
lemma pz_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually h
  exact hnb.deriv_eq

/-- Functions agreeing near `(z,θ)` have the same `D_z` there. -/
lemma Dz_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz g z θ := by
  show z * Work.Spaces.pz f z θ = z * Work.Spaces.pz g z θ
  rw [pz_congr_of_eventuallyEq h]

/-! ## Clairaut at order two -/

/-- The order-two mixed partials of a `C³` function agree: `∂_z ∂_θ² f = ∂_θ² ∂_z f`. -/
theorem pz_pthIter_two_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (h2p : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth f)) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := by
  have hev : (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2)
      =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2) := by
    filter_upwards [(h2.eventually (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞)))] with y hy
    exact Work.Spaces.pz_pth_comm hy
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ :=
    Work.Spaces.pz_pth_comm h2p
  have h3 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) z θ :=
    pth_congr_of_eventuallyEq hev
  rw [show Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) from rfl,
    show Work.Spaces.pthIter 2 (Work.Spaces.pz f)
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) from rfl, h1, h3]

/-! ## The individual slots of `Lzero` -/

/-- `∂_z` distributes over the three slots of `Lzero`. -/
lemma pz_Lzero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.pthIter 2 f s θ) z)
    (hd2 : DifferentiableAt ℝ
      (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ) z)
    (hd3 : DifferentiableAt ℝ (fun s => f s θ) z) :
    Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
      = -Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := by
  have hmain : deriv ((-(fun s => Work.Spaces.pthIter 2 f s θ))
        + (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ)
        - (fun s => 6 * f s θ)) z
      = -(Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := by
    rw [deriv_sub (hd1.neg.add hd2) (hd3.const_mul 6), deriv_add hd1.neg hd2, deriv.neg,
      deriv_const_mul_field]
    simp only [Work.Spaces.pz]
  show deriv (fun s => Work.Elliptic.Lzero f s θ) z = _
  rw [show (fun s => Work.Elliptic.Lzero f s θ)
      = (-(fun s => Work.Spaces.pthIter 2 f s θ))
        + (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ)
        - (fun s => 6 * f s θ) from rfl]
  exact hmain

/-- `∂_z ∂_θ` of the `tan θ ·` slot equals `∂_θ` of `tan θ · ∂_z` (Clairaut plus the fact
that the `z`-derivative of the coefficient `tan θ` vanishes). -/
lemma pz_pth_tan_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * f z θ')) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
      = Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ := by
  have hfun : Work.Spaces.pz (fun z θ' => Real.tan θ' * f z θ')
      = fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ' := by
    funext z' θ'
    show deriv (fun s => Real.tan θ' * f s θ') z' = Real.tan θ' * deriv (fun s => f s θ') z'
    rw [deriv_const_mul_field]
  rw [Work.Spaces.pz_pth_comm h2T, hfun]

/-- The `tan θ ·` slot of `Lzero (D_z f)`, in terms of `∂_z f`. -/
lemma pth_tan_Dz (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
      = z * Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ := by
  have hfun : (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ')
      = fun z θ' => z * (Real.tan θ' * Work.Spaces.pz f z θ') := by
    funext z' θ'; simp only [Work.Spaces.Dz]; ring
  rw [hfun]
  exact pth_z_mul (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ

/-! ## `Lzero` commutes with `D_z` -/

/-- `Lzero` has `θ`-only coefficients, so it commutes with `D_z = z ∂_z`: at a point where `f`
is `C³` and `cos θ ≠ 0`, `Lzero (D_z f) = D_z (Lzero f)`. -/
theorem Lzero_Dz_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h3 : ContDiffAt ℝ 3 (Function.uncurry f) (z, θ)) (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) := h3.of_le (by norm_num)
  have h1 : ContDiffAt ℝ 1 (Function.uncurry f) (z, θ) := h3.of_le (by norm_num)
  have h2p : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 2 h3
  have h1pp : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 f)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2p
  have h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * f z θ')) (z, θ) := by
    have hproj : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (z, θ) := contDiff_snd.contDiffAt
    have htan : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) (z, θ) :=
      ContDiffAt.comp (z, θ) (g := Real.tan) (f := fun p : ℝ × ℝ => p.2)
        (Real.contDiffAt_tan.mpr hcos) hproj
    exact htan.mul h2
  have h1T : ContDiffAt ℝ 1
      (Function.uncurry (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ'))) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2T
  have hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.pthIter 2 f s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pthIter 2 f) z θ h1pp).differentiableAt
      (by norm_num)
  have hd2 : DifferentiableAt ℝ
      (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst
      (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ h1T).differentiableAt (by norm_num)
  have hd3 : DifferentiableAt ℝ (fun s => f s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst f z θ h1).differentiableAt (by norm_num)
  have e1 : Work.Spaces.pthIter 2 (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := by
    rw [show Work.Spaces.Dz f = fun z θ' => z * Work.Spaces.pz f z θ' from rfl]
    exact pthIter_two_z_mul (Work.Spaces.pz f) z θ
  have e2 : Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
      = z * Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ :=
    pth_tan_Dz f z θ
  have e3 : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  have e4 : Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := pz_pthIter_two_comm h2 h2p
  have e5 : Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
      = Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ :=
    pz_pth_tan_mul h2T
  have e6 : Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
      = -Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := pz_Lzero hd1 hd2 hd3
  show -(Work.Spaces.pthIter 2 (Work.Spaces.Dz f) z θ)
        + Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
        - 6 * (Work.Spaces.Dz f z θ)
      = z * Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
  rw [e6, e4, e5, e1, e2, e3]
  ring

/-! ## `bslOp` in terms of `D_z` -/

/-- `bslOp α f = -α²D_z² f - 5αD_z f + Lzero f` at a point where `f` is `C²`. -/
lemma bslOp_eq_Dz_form {α : ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Elliptic.bslOp α f z θ
      = -(α ^ 2) * Work.Spaces.DzIter 2 f z θ - (5 * α) * Work.Spaces.Dz f z θ
        + Work.Elliptic.Lzero f z θ := by
  have h : Work.Spaces.DzIter 2 f z θ = z * Work.Spaces.pz f z θ
      + z ^ 2 * Work.Spaces.pzIter 2 f z θ := by
    rw [Work.FTS_RegExport.RXT.dziter_two_fb h2]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  have h' : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  rw [Work.Elliptic.bslOp_apply, h, h']
  ring

/-- Multiplication by `z` is `D_z` on the first slot of the `D_z`-expansion of `bslOp`. -/
lemma Dz_lin_expand {α : ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.DzIter 2 f s θ) z)
    (hd2 : DifferentiableAt ℝ (fun s => Work.Spaces.Dz f s θ) z)
    (hd3 : DifferentiableAt ℝ (fun s => Work.Elliptic.Lzero f s θ) z) :
    Work.Spaces.Dz (fun z θ => -(α ^ 2) * Work.Spaces.DzIter 2 f z θ
        - (5 * α) * Work.Spaces.Dz f z θ + Work.Elliptic.Lzero f z θ) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 f z θ - (5 * α) * Work.Spaces.DzIter 2 f z θ
        + Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ := by
  have hderiv : deriv (((fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ)
        - (fun s => (5 * α) * Work.Spaces.Dz f s θ))
        + (fun s => Work.Elliptic.Lzero f s θ)) z
      = -(α ^ 2) * deriv (fun s => Work.Spaces.DzIter 2 f s θ) z
        - (5 * α) * deriv (fun s => Work.Spaces.Dz f s θ) z
        + deriv (fun s => Work.Elliptic.Lzero f s θ) z := by
    rw [deriv_add ((hd1.const_mul _).sub (hd2.const_mul _)) hd3,
      deriv_sub (hd1.const_mul _) (hd2.const_mul _), deriv_const_mul_field, deriv_const_mul_field]
  show z * deriv (fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ
        - (5 * α) * Work.Spaces.Dz f s θ + Work.Elliptic.Lzero f s θ) z = _
  rw [show (fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ
        - (5 * α) * Work.Spaces.Dz f s θ + Work.Elliptic.Lzero f s θ)
      = ((fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ)
        - (fun s => (5 * α) * Work.Spaces.Dz f s θ))
        + (fun s => Work.Elliptic.Lzero f s θ) from rfl,
    hderiv,
    show Work.Spaces.DzIter 3 f z θ = z * deriv (fun s => Work.Spaces.DzIter 2 f s θ) z from rfl,
    show Work.Spaces.DzIter 2 f z θ = z * deriv (fun s => Work.Spaces.Dz f s θ) z from rfl,
    show Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ
      = z * deriv (fun s => Work.Elliptic.Lzero f s θ) z from rfl]
  ring

end BslDzAux

open BslDzAux

/-- `bslOp` commutes with `D_z = z ∂_z`: pointwise on the open quadrant, for a function that is
`C^3` at the point (`bslOp = -α²D_z² - 5αD_z + Lzero`, and `Lzero` has `θ`-only coefficients). -/
theorem bslOp_Dz_comm {α : ℝ} {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd)
    (hQ : ContDiffAt ℝ 3 (Function.uncurry Q) (z, θ)) :
    Work.Elliptic.bslOp α (Work.Spaces.Dz Q) z θ
      = Work.Spaces.Dz (Work.Elliptic.bslOp α Q) z θ := by
  have hθ1 : 0 < θ := hmem.2.1
  have hθ2 : θ < π / 2 := hmem.2.2
  have hcos : Real.cos θ ≠ 0 := by
    have hpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact ne_of_gt hpos
  have h1 : ContDiffAt ℝ 1 (Function.uncurry Q) (z, θ) := hQ.of_le (by norm_num)
  have h2pz : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pz Q)) (z, θ) :=
    contDiffAt_uncurry_pz_succ 2 hQ
  have h1pz : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz Q)) (z, θ) :=
    h2pz.of_le (by norm_num)
  have h1pz2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Q)) (z, θ) :=
    contDiffAt_uncurry_pz_succ 1 h2pz
  have h2pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Q)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 2 hQ
  have h1pth2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 Q)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2pth
  have h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * Q z θ')) (z, θ) := by
    have hproj : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (z, θ) := contDiff_snd.contDiffAt
    have htan : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) (z, θ) :=
      ContDiffAt.comp (z, θ) (g := Real.tan) (f := fun p : ℝ × ℝ => p.2)
        (Real.contDiffAt_tan.mpr hcos) hproj
    exact htan.mul (hQ.of_le (by norm_num))
  have h1T : ContDiffAt ℝ 1
      (Function.uncurry (Work.Spaces.pth (fun z θ' => Real.tan θ' * Q z θ'))) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2T
  -- `C²`-regularity of `D_z Q`
  have h2Dz : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.Dz Q)) (z, θ) := by
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.1) (z, θ) := contDiff_fst.contDiffAt
    exact hfst.mul h2pz
  have h1pzDz : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz Q))) (z, θ) :=
    contDiffAt_uncurry_pz_succ 1 h2Dz
  -- differentiability of the slices appearing in the two expansions
  have hsliceQ : DifferentiableAt ℝ (fun s => Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst Q z θ h1).differentiableAt (by norm_num)
  have hpz1 : DifferentiableAt ℝ (fun s => Work.Spaces.pz Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pz Q) z θ h1pz).differentiableAt
      (by norm_num)
  have hpz2 : DifferentiableAt ℝ (fun s => Work.Spaces.pzIter 2 Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pzIter 2 Q) z θ h1pz2).differentiableAt
      (by norm_num)
  have hpzDz : DifferentiableAt ℝ (fun s => Work.Spaces.pz (Work.Spaces.Dz Q) s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pz (Work.Spaces.Dz Q)) z θ
      h1pzDz).differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.DzIter 2 Q s θ) z := by
    have : (fun s : ℝ => Work.Spaces.DzIter 2 Q s θ)
        = fun s : ℝ => s * Work.Spaces.pz (Work.Spaces.Dz Q) s θ := rfl
    rw [this]
    exact differentiableAt_id.mul hpzDz
  have hd2 : DifferentiableAt ℝ (fun s => Work.Spaces.Dz Q s θ) z := by
    have : (fun s : ℝ => Work.Spaces.Dz Q s θ) = fun s : ℝ => s * Work.Spaces.pz Q s θ := rfl
    rw [this]
    exact differentiableAt_id.mul hpz1
  have hd3 : DifferentiableAt ℝ (fun s => Work.Elliptic.Lzero Q s θ) z :=
    (((Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pthIter 2 Q) z θ
          h1pth2).differentiableAt (by norm_num)).neg.add
      ((Work.Elliptic.contDiffAt_uncurry_slice_fst
          (Work.Spaces.pth (fun z θ' => Real.tan θ' * Q z θ')) z θ h1T).differentiableAt
        (by norm_num))).sub (hsliceQ.const_mul 6)
  -- the `bslOp α Q = -α²D_z²Q - 5αD_zQ + Lzero Q` identity on a neighbourhood
  have hev : (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Q p.1 p.2)
      =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => -(α ^ 2) * Work.Spaces.DzIter 2 Q p.1 p.2
        - (5 * α) * Work.Spaces.Dz Q p.1 p.2 + Work.Elliptic.Lzero Q p.1 p.2) := by
    filter_upwards [(hQ.eventually (by decide : (3 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num))] with p hp
    exact bslOp_eq_Dz_form hp
  have hL : Work.Elliptic.bslOp α (Work.Spaces.Dz Q) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 Q z θ - (5 * α) * Work.Spaces.DzIter 2 Q z θ
        + Work.Elliptic.Lzero (Work.Spaces.Dz Q) z θ := by
    have := bslOp_eq_Dz_form (α := α) h2Dz
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using this
  have hR : Work.Spaces.Dz (Work.Elliptic.bslOp α Q) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 Q z θ - (5 * α) * Work.Spaces.DzIter 2 Q z θ
        + Work.Spaces.Dz (Work.Elliptic.Lzero Q) z θ := by
    rw [Dz_congr_of_eventuallyEq (f := Work.Elliptic.bslOp α Q)
      (g := fun z θ => -(α ^ 2) * Work.Spaces.DzIter 2 Q z θ
        - (5 * α) * Work.Spaces.Dz Q z θ + Work.Elliptic.Lzero Q z θ) hev]
    exact Dz_lin_expand hd1 hd2 hd3
  have hcomm : Work.Elliptic.Lzero (Work.Spaces.Dz Q) z θ
      = Work.Spaces.Dz (Work.Elliptic.Lzero Q) z θ := Lzero_Dz_comm hQ hcos
  rw [hL, hR, hcomm]

end Work.FTS_StreamBdry.SB3.P2Aux
