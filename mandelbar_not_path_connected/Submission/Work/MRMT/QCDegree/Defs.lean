/-
Copyright: Work.MRMT (mandelbar) subproject.

# The maximum principle for Beltrami solutions: shared vocabulary

This file fixes the notions used by `Work.MRMT.QCDegree.max_principle_beltrami` and by the
lemmas proved in parallel for it.

Let `u` have weak Wirtinger derivatives `p = ∂u`, `q = ∂̄u` on the open set `U`
(`Work.MRMT.IsDzDerivOn`, `Work.MRMT.IsDbarDerivOn`).  For real valued `u` the *flux* of the
corresponding divergence form equation `div (A ∇u) = 0` is encoded by the complex valued field

`fluxOf p q = conj p - q`

whose real and imaginary parts are the two components of `A ∇u`.  The equation `div (A ∇u) = 0`
is then equivalent (for real valued `φ`) to

`∫ (w ∂φ + conj w ∂̄φ) = 0`,

which is the content of `IsWeakDivFreeFlux`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Sobolev.dz_convolution_eq_of_isDzDerivOn
import Submission.Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.QCDegree

/-! ## The flux of a plane divergence-form equation -/

/-- Complex encoding of the flux vector field `(Re (p - q), -Im (p + q))` associated with the
weak Wirtinger derivatives `p = ∂u`, `q = ∂̄u` of a solution of `div (A ∇u) = 0`:
`conj p - q`. -/
def fluxOf (p q : ℂ → ℂ) : ℂ → ℂ := fun z => star (p z) - q z

@[simp] theorem fluxOf_apply (p q : ℂ → ℂ) (z : ℂ) : fluxOf p q z = star (p z) - q z := rfl

/-- `w` is a weakly divergence-free flux field on `U`: for every smooth compactly supported
`φ` with `tsupport φ ⊆ U`, `∫ (w ∂φ + conj w ∂̄φ) = 0`. -/
def IsWeakDivFreeFlux (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ z, (w z * Work.MRMT.dz φ z + star (w z) * Work.MRMT.dzbar φ z) = 0

/-! ## Mollification -/

/-- Mollification of a real valued function against a real valued kernel:
`mollR ρ u x = ∫ y, ρ y * u (x - y)`. -/
def mollR (ρ : ℂ → ℝ) (u : ℂ → ℝ) : ℂ → ℝ :=
  MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) (volume : MeasureTheory.Measure ℂ)

theorem mollR_apply (ρ : ℂ → ℝ) (u : ℂ → ℝ) (x : ℂ) :
    mollR ρ u x = ∫ y, ρ y * u (x - y) := by
  rw [mollR, MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  rw [ContinuousLinearMap.lsmul_apply]
  rfl

/-- The complexification of `mollR ρ u` is the complex mollification (in the sense of
`Work.MRMT.Weyl.moll`) of the complexification of `u`. -/
theorem ofReal_mollR (ρ : ℂ → ℝ) (u : ℂ → ℝ) :
    (fun z => ((mollR ρ u z : ℝ) : ℂ)) = Work.MRMT.Weyl.moll ρ (fun z => ((u z : ℝ) : ℂ)) := by
  funext x
  rw [Work.MRMT.Weyl.moll_apply, mollR_apply]
  have h1 : ((∫ y, ρ y * u (x - y) : ℝ) : ℂ)
      = ∫ y, ((ρ y * u (x - y) : ℝ) : ℂ) :=
    (integral_ofReal (μ := volume) (f := fun y : ℂ => ρ y * u (x - y))).symm
  rw [h1]
  apply integral_congr_ae
  filter_upwards with y
  push_cast
  ring

/-- Real valued mollification is smooth. -/
theorem contDiff_mollR {ρ : ℂ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    {u : ℂ → ℝ} (hu : LocallyIntegrable u volume) : ContDiff ℝ (⊤ : ℕ∞) (mollR ρ u) :=
  hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hu

/-- `F ⋆ ρ` in the argument order of the convolution-based weak-derivative lemmas is the same
integral as `Weyl.moll`. -/
theorem convolution_eq_integral (ρ F : ℂ → ℂ) (x : ℂ) :
    MeasureTheory.convolution F ρ (ContinuousLinearMap.mul ℝ ℂ) (volume : MeasureTheory.Measure ℂ) x
      = ∫ y, F (x - y) * ρ y := by
  rw [MeasureTheory.convolution_def]
  rw [show (∫ (t : ℂ), (ContinuousLinearMap.mul ℝ ℂ (F t)) (ρ (x - t)))
      = ∫ (t : ℂ), F t * ρ (x - t) from by
        apply integral_congr_ae
        filter_upwards with t
        rw [ContinuousLinearMap.mul_apply']]
  have hsub : (∫ t, F t * ρ (x - t)) = ∫ t, F (x - t) * ρ t := by
    rw [← integral_sub_left_eq_self (f := fun t : ℂ => F (x - t) * ρ t) (μ := volume) x]
    apply integral_congr_ae
    filter_upwards with t
    simp [sub_sub_cancel]
  exact hsub

/-- `Weyl.moll` written in the convolution order used by the weak-derivative lemmas. -/
theorem moll_eq_convolution (ρ : ℂ → ℝ) (F : ℂ → ℂ) :
    Work.MRMT.Weyl.moll ρ F
      = MeasureTheory.convolution F (fun z => (ρ z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ)
          (volume : MeasureTheory.Measure ℂ) := by
  funext x
  rw [convolution_eq_integral, Work.MRMT.Weyl.moll_apply]
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_comm]

/-- Support of the complexification of a real valued kernel. -/
theorem tsupport_coe {ρ : ℂ → ℝ} : tsupport (fun z => (ρ z : ℂ)) = tsupport ρ := by
  rw [tsupport, tsupport]
  congr 1
  ext z
  simp only [Function.mem_support, ne_eq]
  exact ⟨fun h hz => h (by simp [hz]), fun h => by simp [h]⟩

/-- **Weak `∂`-derivative of a mollification** (in the order `Weyl.moll ρ F`). -/
theorem dz_moll {U : Set ℂ} {F G : ℂ → ℂ} (hFG : Work.MRMT.IsDzDerivOn F G U)
    (hF : LocallyIntegrable F) {ρ : ℂ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) {z : ℂ} (hz : ∀ t ∈ tsupport ρ, z - t ∈ U) :
    Work.MRMT.dz (Work.MRMT.Weyl.moll ρ F) z = Work.MRMT.Weyl.moll ρ G z := by
  have hρ' : ContDiff ℝ (⊤ : ℕ∞) (fun z => (ρ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hρ
  have hρc' : HasCompactSupport (fun z => (ρ z : ℂ)) :=
    hρc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  rw [moll_eq_convolution, moll_eq_convolution]
  exact Work.MRMT.Sobolev.dz_convolution_eq_of_isDzDerivOn hFG hF hρ' hρc'
    (fun t ht => hz t (by simpa [tsupport_coe] using ht))

/-- **Weak `∂̄`-derivative of a mollification** (in the order `Weyl.moll ρ F`). -/
theorem dzbar_moll {U : Set ℂ} {F G : ℂ → ℂ} (hFG : Work.MRMT.IsDbarDerivOn F G U)
    (hF : LocallyIntegrable F) {ρ : ℂ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) {z : ℂ} (hz : ∀ t ∈ tsupport ρ, z - t ∈ U) :
    Work.MRMT.dzbar (Work.MRMT.Weyl.moll ρ F) z = Work.MRMT.Weyl.moll ρ G z := by
  have hρ' : ContDiff ℝ (⊤ : ℕ∞) (fun z => (ρ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hρ
  have hρc' : HasCompactSupport (fun z => (ρ z : ℂ)) :=
    hρc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  rw [moll_eq_convolution, moll_eq_convolution]
  exact Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn hFG hF hρ' hρc'
    (fun t ht => hz t (by simpa [tsupport_coe] using ht))

end Work.MRMT.QCDegree

namespace Work.MRMT.QCDegree

/-! ## A smooth cut-off in the level variable -/

/-- A smooth cut-off in the level variable: it vanishes on `(-∞,0]`, takes values in `[0,1]`, and
has strictly positive derivative on `(0,∞)`. -/
def lvlCutoff (x : ℝ) : ℝ := x.smoothTransition * (1 - Real.exp (-x))

/-- The level cut-off shifted by `t`: `x ↦ lvlCutoff (x - t)`. -/
def lvlCutoffS (t x : ℝ) : ℝ := lvlCutoff (x - t)

theorem contDiff_lvlCutoff : ContDiff ℝ (⊤ : ℕ∞) lvlCutoff :=
  Real.smoothTransition.contDiff.mul (contDiff_const.sub (Real.contDiff_exp.comp contDiff_neg))

theorem one_sub_exp_neg_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) :=
  sub_nonneg.2 (Real.exp_le_one_iff.mpr (by linarith))

theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) :=
  sub_pos.2 (Real.exp_lt_one_iff.mpr (by linarith))

theorem one_sub_exp_neg_le_one (x : ℝ) : 1 - Real.exp (-x) ≤ 1 := by
  linarith [Real.exp_pos (-x)]

theorem lvlCutoff_nonneg (x : ℝ) : 0 ≤ lvlCutoff x := by
  by_cases hx : 0 ≤ x
  · exact mul_nonneg (Real.smoothTransition.nonneg x) (one_sub_exp_neg_nonneg_of_nonneg hx)
  · push_neg at hx
    show x.smoothTransition * (1 - Real.exp (-x)) ≥ 0
    rw [Real.smoothTransition.zero_of_nonpos hx.le, zero_mul]

theorem lvlCutoff_le_one (x : ℝ) : lvlCutoff x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · have h1 : x.smoothTransition ≤ 1 := Real.smoothTransition.le_one x
    have h2 : 1 - Real.exp (-x) ≤ 1 := one_sub_exp_neg_le_one x
    have h0 : 0 ≤ 1 - Real.exp (-x) := one_sub_exp_neg_nonneg_of_nonneg hx
    calc lvlCutoff x ≤ 1 * 1 := mul_le_mul h1 h2 h0 (by norm_num)
      _ = 1 := mul_one 1
  · push_neg at hx
    show x.smoothTransition * (1 - Real.exp (-x)) ≤ 1
    rw [Real.smoothTransition.zero_of_nonpos hx.le, zero_mul]
    norm_num

theorem lvlCutoff_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : lvlCutoff x = 0 := by
  show x.smoothTransition * (1 - Real.exp (-x)) = 0
  rw [Real.smoothTransition.zero_of_nonpos hx, zero_mul]

theorem deriv_lvlCutoff_pos {x : ℝ} (hx : 0 < x) : 0 < deriv lvlCutoff x := by
  have hfun : lvlCutoff = fun y : ℝ => y.smoothTransition * (1 - Real.exp (-y)) := rfl
  have hSTd : DifferentiableAt ℝ Real.smoothTransition x :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x
  have h2 : DifferentiableAt ℝ (fun y : ℝ => 1 - Real.exp (-y)) x :=
    (differentiableAt_const (c := (1 : ℝ))).sub
      (show DifferentiableAt ℝ (fun y : ℝ => Real.exp (-y)) x from
        (Real.differentiableAt_exp (x := -x)).comp x differentiableAt_id.neg)
  rw [hfun]
  change 0 < deriv ((fun y : ℝ => y.smoothTransition) * (fun y : ℝ => 1 - Real.exp (-y))) x
  rw [deriv_mul hSTd h2]
  have hderiv2 : deriv (fun y : ℝ => 1 - Real.exp (-y)) x = Real.exp (-x) := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := hasDerivAt_neg x
    have h2' : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x h1
    have h3' : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (-(Real.exp (-x) * (-1))) x :=
      h2'.const_sub 1
    rw [h3'.deriv]; ring
  rw [hderiv2]
  have h1 : 0 ≤ deriv Real.smoothTransition x := Real.smoothTransition.monotone.deriv_nonneg
  have h4 : 0 < Real.smoothTransition x := Real.smoothTransition.pos_of_pos hx
  have h5 : 0 < Real.exp (-x) := Real.exp_pos _
  have h6 : 0 ≤ deriv Real.smoothTransition x * (1 - Real.exp (-x)) :=
    mul_nonneg h1 (one_sub_exp_neg_nonneg_of_nonneg hx.le)
  nlinarith [mul_pos h4 h5]

theorem contDiff_lvlCutoffS (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lvlCutoffS t) :=
  contDiff_lvlCutoff.comp (contDiff_id.sub contDiff_const)

theorem lvlCutoffS_eq_zero_of_le {t x : ℝ} (hx : x ≤ t) : lvlCutoffS t x = 0 :=
  lvlCutoff_eq_zero_of_nonpos (sub_nonpos.2 hx)

theorem deriv_lvlCutoffS_pos {t x : ℝ} (hx : t < x) : 0 < deriv (lvlCutoffS t) x := by
  have hfun : lvlCutoffS t = fun y : ℝ => lvlCutoff (y - t) := rfl
  have hcomp : deriv (fun y : ℝ => lvlCutoff (y - t)) x = deriv lvlCutoff (x - t) := by
    change deriv (lvlCutoff ∘ fun y : ℝ => y - t) x = deriv lvlCutoff (x - t)
    rw [deriv_comp (x := x) (h := fun y : ℝ => y - t) (h₂ := lvlCutoff)
      ((contDiff_lvlCutoff.differentiable (by norm_num)) (x - t))
      (differentiableAt_id.sub (differentiableAt_const (c := t)))]
    have hd : deriv (fun y : ℝ => y - t) x = 1 := by
      simpa using ((hasDerivAt_id x).sub_const t).deriv
    rw [hd, mul_one]
  rw [hfun, hcomp]
  exact deriv_lvlCutoff_pos (by linarith)

theorem lvlCutoffS_nonneg (t x : ℝ) : 0 ≤ lvlCutoffS t x := lvlCutoff_nonneg _
theorem lvlCutoffS_le_one (t x : ℝ) : lvlCutoffS t x ≤ 1 := lvlCutoff_le_one _

end Work.MRMT.QCDegree
