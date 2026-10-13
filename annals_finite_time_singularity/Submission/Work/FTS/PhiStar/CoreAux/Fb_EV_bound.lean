/-
# `FTS/PhiStar/CoreAux/Fb_EV_bound.lean` — the flat bounds for the `𝒱`-field of `StarPkgo2`

`Work.FTS.PhiStar.EVz Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` and
`Work.FTS.PhiStar.EV Y = (z/(z+1))·EVz Y` are two of the eleven fields of `StarPkgo2`
(`Work.FTS.VocabO2`), written in terms of the flat datum `Ŷ = Ycheck α Φs` and its two blocks
`Yblk`, `Tblk`.  This file proves the flat bounds

`Fb 4 (C A⁴(K+1)) (EVz Y)`,  `Fb 4 (C A⁴(K+1)) (EV Y)`

from `Fb 6 (A(K+1)) Y`, `SmoothOpen Y` and the flat bounds `F0 6 A` of the three coefficient
functions `cos²θ − 2 sin²θ`, `sin 2θ` and `z/(1+z)`; `C = EVC = 4096`.

**The proof.**  `Fb n K f` is the pair of flat bounds `F0 n K f` and `F0 n K (∂_θ f)`, so both
halves of both functions are bounded by writing everything as a sum of products of a
*coefficient factor* (a function of `θ` alone, or of `z` alone, whose flat bounds come from the
hypotheses, with constants independent of `K`) and a *`Y`-block* (`Y`, `∂_θY`, or `D_θ(∂_θY)`,
all with constant `A(K+1)`).  The products are bounded by the Leibniz estimate `F0_mul`
(constant `2^n K K'`, and no factor of `K` is ever squared because only one factor of each
product carries `K`), the sums by `F0_add`, and the congruence of `∂_θ f` with the explicit
expanded expression by `F0_congr` plus the product rule `Fbq_pth_mul` on the open quadrant.

Concretely:

* `cos 2θ` is bounded with the constant `A` from the `cos²θ − 2 sin²θ`-hypothesis through the
  identity `cos 2θ = (2·EVphi + 1)/3` and `(2A+1)/3 ≤ A ⟺ 1 ≤ A` (this is the coefficient
  package `EVCoef A`, proved here as the private `EVCoef_local`);
* `∂_θ(cos²θ − 2 sin²θ) = −3 sin 2θ` and `∂_θ(sin 2θ) = 2 cos 2θ` are the two angular
  derivatives that occur when the product rule is applied; `∂_θ(z/(1+z)) = 0`;
* the `∂_θ`-half of `EVz Y` is the sum of the four products
  `−6 sin 2θ·Y`, `2 cos²·Y`-type terms and `sin 2θ·∂_θ²Y`, the last of which is *one more*
  angular derivative `D_θ(∂_θY)` of the `Fb`-block `∂_θY` (this is `F0_Dth`);
* the final multiplication by `z/(1+z)` only needs `∂_θ(z/(1+z)) = 0`, i.e.
  `∂_θ(EV Y) = (z/(1+z))·∂_θ(EVz Y)`.

The elementary flat-calculus tools used (`F0_const_mul`, `F0_Dth`, `pth_add_Q0`,
`pth_congr_Q0`, `SmoothOpen.const_mul/add/congr`) are in `CoreAux/EVDefs.lean`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.FTS.PhiStar.CoreAux


/-! ## The coefficient package -/

private theorem EVCoef_local {A : ℝ} (hA : 1 ≤ A) (hphi : F0 6 A EVphi)
    (hsin : F0 6 A EVsin) (hrho : F0 6 A EVrho) : EVCoef A := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have sPhi : EllipticEst.SmoothOpen EVphi := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVphi
        = fun p : ℝ × ℝ => Real.cos p.2 ^ 2 - 2 * Real.sin p.2 ^ 2 := rfl
    rw [h]
    fun_prop
  have sSin : EllipticEst.SmoothOpen EVsin := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVsin = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
    rw [h]
    fun_prop
  have sCos2 : EllipticEst.SmoothOpen (fun _ θ => Real.cos (2 * θ)) := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ))
        = fun p : ℝ × ℝ => Real.cos (2 * p.2) := rfl
    rw [h]
    fun_prop
  have sRho : EllipticEst.SmoothOpen EVrho := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVrho = fun p : ℝ × ℝ => p.1 / (1 + p.1) := rfl
    rw [h]
    exact ContDiffOn.div contDiffOn_fst (contDiffOn_const.add contDiffOn_fst)
      (fun p hp => by have h1 := (EllipticEst.mem_Q0.mp hp).1; positivity)
  have hdPhi : ∀ z θ : ℝ, Work.Spaces.pth EVphi z θ = -3 * Real.sin (2 * θ) := by
    intro z θ
    show deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = -3 * Real.sin (2 * θ)
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2)
        (2 * Real.cos θ * (-Real.sin θ)) θ := by
      refine ((Real.hasDerivAt_cos θ).pow 2).congr_deriv ?_
      norm_num
    have h2 : HasDerivAt (fun θ' : ℝ => 2 * Real.sin θ' ^ 2)
        (2 * (2 * Real.sin θ * Real.cos θ)) θ := by
      refine (((Real.hasDerivAt_sin θ).pow 2).const_mul (2 : ℝ)).congr_deriv ?_
      norm_num
    have h3 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
        (2 * Real.cos θ * (-Real.sin θ) - 2 * (2 * Real.sin θ * Real.cos θ)) θ :=
      h1.sub h2
    rw [h3.deriv, Real.sin_two_mul]
    ring
  have hdSin : ∀ z θ : ℝ, Work.Spaces.pth EVsin z θ = 2 * Real.cos (2 * θ) := by
    intro z θ
    show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
    have hinner : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
    rw [h.deriv]
    ring
  have hdRho : ∀ z θ : ℝ, Work.Spaces.pth EVrho z θ = 0 := by
    intro z θ
    show deriv (fun _ : ℝ => z / (1 + z)) θ = 0
    exact deriv_const θ (z / (1 + z))
  have sdPhi : EllipticEst.SmoothOpen (Work.Spaces.pth EVphi) := by
    refine SmoothOpen.congr (f := fun _ θ : ℝ => -3 * Real.sin (2 * θ)) ?_ ?_
    · refine EllipticEst.smoothOpen_of_forall fun n => ?_
      have h : Function.uncurry (fun _ θ : ℝ => -3 * Real.sin (2 * θ))
          = fun p : ℝ × ℝ => -3 * Real.sin (2 * p.2) := rfl
      rw [h]
      fun_prop
    · intro z θ _ _ _
      exact (hdPhi z θ).symm
  have sdSin : EllipticEst.SmoothOpen (Work.Spaces.pth EVsin) := by
    refine SmoothOpen.congr (f := fun _ θ : ℝ => 2 * Real.cos (2 * θ)) ?_ ?_
    · exact SmoothOpen.const_mul sCos2 2
    · intro z θ _ _ _
      exact (hdSin z θ).symm
  have h2phi : F0 6 (2 * A) (fun z θ => 2 * EVphi z θ) := by
    have h := F0_const_mul (2 : ℝ) hphi
    simpa using h
  have h3 : F0 6 (2 * A + 1) (fun z θ => 2 * EVphi z θ + 1) := by
    have h := F0_add (SmoothOpen.const_mul sPhi 2) (SmoothOpen.const 1) h2phi (F0.const 6 1)
    simpa using h
  have h4 : F0 6 ((1 / 3) * (2 * A + 1)) (fun z θ => (1 / 3) * (2 * EVphi z θ + 1)) := by
    have h := F0_const_mul ((1 / 3 : ℝ)) h3
    simpa using h
  have hCos2 : F0 6 A (fun _ θ => Real.cos (2 * θ)) := by
    refine (F0_congr (fun z θ _ _ _ => ?_) h4).mono le_rfl ?_
    · simp only [EVphi]
      rw [Real.cos_two_mul]
      have hs := Real.sin_sq_add_cos_sq θ
      nlinarith [hs]
    · linarith
  exact ⟨sPhi, sSin, sRho, sCos2, sdPhi, sdSin, hphi, hsin, hrho, hCos2, hdPhi, hdSin,
    hdRho⟩

/-! ## The assembly -/

private theorem absorb {A K c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) {p : ℕ} (hp : p ≤ 4)
    (hc : c ≤ EVC) : c * A ^ p * (K + 1) ≤ EVC * A ^ 4 * (K + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have h1 : c * A ^ p ≤ EVC * A ^ 4 :=
    calc c * A ^ p ≤ EVC * A ^ p := mul_le_mul_of_nonneg_right hc (pow_nonneg hA0 p)
      _ ≤ EVC * A ^ 4 := mul_le_mul_of_nonneg_left hp4 (by norm_num [EVC])
  exact mul_le_mul_of_nonneg_right h1 hK1

theorem Fb_EV_bound_aux {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hC : EVCoef A) (hY : Fb 6 (A * (K + 1)) Y) :
    Fb 4 (EVC * A ^ 4 * (K + 1)) (EVz Y) ∧ Fb 4 (EVC * A ^ 4 * (K + 1)) (EV Y) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A * (K + 1) := mul_nonneg hA0 (by linarith)
  have hY4 : Fb 4 (A * (K + 1)) Y := hY.mono (by norm_num) le_rfl
  have hphi4 : F0 4 A EVphi := hC.f0Phi.mono (by norm_num) le_rfl
  have hsin4 : F0 4 A EVsin := hC.f0Sin.mono (by norm_num) le_rfl
  have hrho4 : F0 4 A EVrho := hC.f0Rho.mono (by norm_num) le_rfl
  have hcos4 : F0 4 A (fun _ θ => Real.cos (2 * θ)) := hC.f0Cos2.mono (by norm_num) le_rfl
  have h2phi : F0 4 (2 * A) (fun z θ => 2 * EVphi z θ) := by
    have h := F0_const_mul (2 : ℝ) hphi4
    simpa using h
  have h6sin : F0 4 (6 * A) (fun z θ => -6 * EVsin z θ) := by
    have h := F0_const_mul (-6 : ℝ) hsin4
    simpa using h
  have h2cos : F0 4 (2 * A) (fun z θ => 2 * Real.cos (2 * θ)) := by
    have h := F0_const_mul (2 : ℝ) hcos4
    simpa using h
  have h2A : (0 : ℝ) ≤ 2 * A := by linarith
  have h6A : (0 : ℝ) ≤ 6 * A := by linarith
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have h200 : (0 : ℝ) ≤ 200 * A ^ 2 * (K + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) hK1
  have s2phi : EllipticEst.SmoothOpen (fun z θ => 2 * EVphi z θ) :=
    SmoothOpen.const_mul hC.smoothPhi 2
  have s6sin : EllipticEst.SmoothOpen (fun z θ => -6 * EVsin z θ) :=
    SmoothOpen.const_mul hC.smoothSin (-6)
  have s2cos : EllipticEst.SmoothOpen (fun z θ => 2 * Real.cos (2 * θ)) :=
    SmoothOpen.const_mul hC.smoothCos2 2
  have spY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sppY : EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Spaces.pth Y)) :=
    EllipticEst.SmoothOpen.pth spY
  have s2phiY : EllipticEst.SmoothOpen ((fun z θ => 2 * EVphi z θ) * Y) :=
    Fbq_smoothOpen_mul s2phi hYs
  have ssinpY : EllipticEst.SmoothOpen (EVsin * Work.Spaces.pth Y) :=
    Fbq_smoothOpen_mul hC.smoothSin spY
  have hsplit : EVz Y = (fun z θ => 2 * EVphi z θ) * Y + EVsin * Work.Spaces.pth Y := by
    funext a b
    simp only [EVz, Tblk, EVsin, EVphi, Work.Construction.s2, Pi.add_apply, Pi.mul_apply]
  have sEvz : EllipticEst.SmoothOpen (EVz Y) := by
    rw [hsplit]
    exact SmoothOpen.add s2phiY ssinpY
  -- ## the `F0`-half for `EVz`
  have t1 : F0 4 (32 * A ^ 2 * (K + 1)) ((fun z θ => 2 * EVphi z θ) * Y) := by
    have h := F0_mul h2A hM s2phi hYs h2phi hY4.f0
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have t2 : F0 4 (16 * A ^ 2 * (K + 1)) (EVsin * Work.Spaces.pth Y) := by
    have h := F0_mul hA0 hM hC.smoothSin spY hsin4 hY4.fd
    have hc : (2 : ℝ) ^ 4 * A * (A * (K + 1)) = 16 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have hsumz : F0 4 (48 * A ^ 2 * (K + 1))
      ((fun z θ => 2 * EVphi z θ) * Y + EVsin * Work.Spaces.pth Y) := by
    have h := F0_add s2phiY ssinpY t1 t2
    have hc : 32 * A ^ 2 * (K + 1) + 16 * A ^ 2 * (K + 1) = 48 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have hF0z : F0 4 (48 * A ^ 2 * (K + 1)) (EVz Y) := by
    refine F0_congr (fun z θ _ _ _ => ?_) hsumz
    rw [hsplit]
  -- ## the `∂_θ`-half for `EVz`
  let A1 : ℝ → ℝ → ℝ := fun z θ => 2 * EVphi z θ * Y z θ
  let A2 : ℝ → ℝ → ℝ := fun z θ => EVsin z θ * Work.Spaces.pth Y z θ
  let T1 : ℝ → ℝ → ℝ := fun z θ => -6 * EVsin z θ * Y z θ
  let T2 : ℝ → ℝ → ℝ := fun z θ => 2 * EVphi z θ * Work.Spaces.pth Y z θ
  let T3 : ℝ → ℝ → ℝ := fun z θ => 2 * Real.cos (2 * θ) * Work.Spaces.pth Y z θ
  let T4 : ℝ → ℝ → ℝ := fun z θ => EVsin z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ
  have hT1 : F0 4 (96 * A ^ 2 * (K + 1)) T1 := by
    have h := F0_mul h6A hM s6sin hYs h6sin hY4.f0
    have hc : (2 : ℝ) ^ 4 * (6 * A) * (A * (K + 1)) = 96 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T1, Pi.mul_apply] using h
  have hT2 : F0 4 (32 * A ^ 2 * (K + 1)) T2 := by
    have h := F0_mul h2A hM s2phi spY h2phi hY4.fd
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T2, Pi.mul_apply] using h
  have hT3 : F0 4 (32 * A ^ 2 * (K + 1)) T3 := by
    have h := F0_mul h2A hM s2cos spY h2cos hY4.fd
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T3, Pi.mul_apply] using h
  have hT4 : F0 4 (A * (K + 1)) T4 := by
    have hpm : F0 5 (A * (K + 1)) (Work.Spaces.pth Y) := hY.fd.mono (by norm_num) le_rfl
    refine F0_congr (f := T4) (g := Work.Spaces.Dth (Work.Spaces.pth Y)) (fun z θ _ _ _ => ?_)
      (F0_Dth hpm)
    simp only [T4, Work.Spaces.Dth, EVsin]
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVz Y) z θ = ((T1 + T2) + (T3 + T4)) z θ := by
    intro z θ hz hθ hθ'
    have h4 : Work.Spaces.pth (fun z θ => 2 * EVphi z θ) z θ = -6 * EVsin z θ := by
      have h2 := congrFun (congrFun (pth_const_mul (2 : ℝ) EVphi) z) θ
      rw [h2, hC.dPhi z θ]
      simp only [EVsin]
      ring
    have h5 : Work.Spaces.pth (fun z θ => EVsin z θ) z θ = 2 * Real.cos (2 * θ) := by
      simpa only [] using hC.dSin z θ
    have hA1 : Work.Spaces.pth A1 z θ = -6 * EVsin z θ * Y z θ
        + 2 * EVphi z θ * Work.Spaces.pth Y z θ := by
      have h := Fbq_pth_mul (f := fun z θ => 2 * EVphi z θ) (g := Y) s2phi hYs z θ hz hθ hθ'
      simp only [A1] at h ⊢
      simpa only [Pi.mul_apply, h4] using h
    have hA2 : Work.Spaces.pth A2 z θ = 2 * Real.cos (2 * θ) * Work.Spaces.pth Y z θ
        + EVsin z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ := by
      have h := Fbq_pth_mul (f := fun z θ => EVsin z θ) (g := Work.Spaces.pth Y)
        hC.smoothSin spY z θ hz hθ hθ'
      simp only [A2] at h ⊢
      simpa only [Pi.mul_apply, h5] using h
    have hEq : EVz Y = fun z θ => A1 z θ + A2 z θ := by
      funext a b
      simp only [EVz, Tblk, A1, A2, EVsin, EVphi, Work.Construction.s2]
    have hsum : Work.Spaces.pth (EVz Y) z θ = Work.Spaces.pth A1 z θ + Work.Spaces.pth A2 z θ := by
      have h := pth_add_Q0 (f := A1) (g := A2)
        (SmoothOpen.congr s2phiY (fun a b _ _ _ => by simp only [A1, Pi.mul_apply]))
        (SmoothOpen.congr ssinpY (fun a b _ _ _ => by simp only [A2, Pi.mul_apply]))
        z θ hz hθ hθ'
      simpa only [hEq] using h
    rw [hsum, hA1, hA2]
    simp only [T1, T2, T3, T4, Pi.add_apply, EVsin]
  have hsumd : F0 4 ((96 * A ^ 2 * (K + 1) + 32 * A ^ 2 * (K + 1))
      + (32 * A ^ 2 * (K + 1) + A * (K + 1))) ((T1 + T2) + (T3 + T4)) :=
    F0_add (SmoothOpen.add (Fbq_smoothOpen_mul s6sin hYs) (Fbq_smoothOpen_mul s2phi spY))
      (SmoothOpen.add (Fbq_smoothOpen_mul s2cos spY) (Fbq_smoothOpen_mul hC.smoothSin sppY))
      (F0_add (Fbq_smoothOpen_mul s6sin hYs) (Fbq_smoothOpen_mul s2phi spY) hT1 hT2)
      (F0_add (Fbq_smoothOpen_mul s2cos spY) (Fbq_smoothOpen_mul hC.smoothSin sppY) hT3 hT4)
  have hF0d : F0 4 (200 * A ^ 2 * (K + 1)) (Work.Spaces.pth (EVz Y)) := by
    refine (F0_congr hid hsumd).mono le_rfl ?_
    have hx : (0 : ℝ) ≤ A ^ 2 * (K + 1) := mul_nonneg (pow_nonneg hA0 2) hK1
    have hy : A * (K + 1) ≤ A ^ 2 * (K + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ hK1
      nlinarith [hA]
    linarith
  have hEVz : Fb 4 (200 * A ^ 2 * (K + 1)) (EVz Y) :=
    ⟨hF0z.mono le_rfl (by
        have hx : (0 : ℝ) ≤ A ^ 2 * (K + 1) := mul_nonneg (pow_nonneg hA0 2) hK1
        linarith), hF0d⟩
  -- ## the two halves for `EV`
  have hEVfun : ∀ z θ : ℝ, EV Y z θ = (EVrho * EVz Y) z θ := by
    intro z θ
    simp only [EV, EVrho, Pi.mul_apply]
    rw [add_comm 1 z]
  have hF0ev : F0 4 (3200 * A ^ 3 * (K + 1)) (EV Y) := by
    have h := F0_mul hA0 h200 hC.smoothRho sEvz hrho4 hEVz.f0
    have hc : (2 : ℝ) ^ 4 * A * (200 * A ^ 2 * (K + 1)) = 3200 * A ^ 3 * (K + 1) := by ring
    rw [hc] at h
    exact F0_congr (fun z θ _ _ _ => hEVfun z θ) h
  have hpthEV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EV Y) z θ = (EVrho * Work.Spaces.pth (EVz Y)) z θ := by
    intro z θ hz hθ hθ'
    have h1 : Work.Spaces.pth (EV Y) z θ
        = Work.Spaces.pth (fun z θ => EVrho z θ * EVz Y z θ) z θ :=
      pth_congr_Q0 (fun a b _ _ _ => hEVfun a b) z θ hz hθ hθ'
    rw [h1, Fbq_pth_mul (f := EVrho) (g := EVz Y) hC.smoothRho sEvz z θ hz hθ hθ',
      hC.dRho z θ]
    simp only [Pi.mul_apply, zero_mul, zero_add]
  have hFdev : F0 4 (3200 * A ^ 3 * (K + 1)) (Work.Spaces.pth (EV Y)) := by
    have h := F0_mul hA0 h200 hC.smoothRho sEvz.pth hrho4 hEVz.fd
    have hc : (2 : ℝ) ^ 4 * A * (200 * A ^ 2 * (K + 1)) = 3200 * A ^ 3 * (K + 1) := by ring
    rw [hc] at h
    exact F0_congr (fun z θ hz hθ hθ' => hpthEV z θ hz hθ hθ') h
  refine ⟨hEVz.mono le_rfl (absorb hA hK (p := 2) (by norm_num) (by norm_num [EVC])),
    hF0ev.mono le_rfl (absorb hA hK (p := 3) (by norm_num) (by norm_num [EVC])),
    hFdev.mono le_rfl (absorb hA hK (p := 3) (by norm_num) (by norm_num [EVC]))⟩

theorem Fb_EV_bound : ∃ C : ℝ, 0 < C ∧ ∀ (K A : ℝ) (Y : ℝ → ℝ → ℝ), 0 ≤ K → 1 ≤ A → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) → Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) → Work.FTS.PhiStar.Fb 6 (A * (K + 1)) Y → Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1)) (Work.FTS.PhiStar.EVz Y) ∧ Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1)) (Work.FTS.PhiStar.EV Y) := by
  refine ⟨EVC, by norm_num [EVC], ?_⟩
  intro K A Y hK hA hYs hphi hsin hrho hY
  exact Fb_EV_bound_aux hA hK hYs (EVCoef_local hA hphi hsin hrho) hY

end Work.FTS.PhiStar.CoreAux
