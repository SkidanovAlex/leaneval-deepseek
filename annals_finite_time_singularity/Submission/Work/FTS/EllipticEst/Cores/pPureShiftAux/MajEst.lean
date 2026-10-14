import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkMem_dq_le
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DilMoments =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The moment of a second difference quotient -/

theorem Fstar_dqq_eq {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (dq c (dq c f)) z
      = (Work.Elliptic.Fstar f (c ^ 2 * z) - 2 * Work.Elliptic.Fstar f (c * z)
          + Work.Elliptic.Fstar f z) / (c - 1) ^ 2 := by
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => 2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ := h2.const_mul 2
  have hsplit : (fun θ => dq c (dq c f) z θ * Work.Elliptic.sinCos2 θ)
      = fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2
          - (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2
          + (f z θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2 := by
    funext θ
    by_cases hc1 : c - 1 = 0
    · have hc : c = 1 := sub_eq_zero.mp hc1
      subst hc
      simp [dq_apply]
    · simp only [dq_apply]
      field_simp
      ring
  have hA : MeasureTheory.IntegrableOn
      (fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2)
      Work.Spaces.Iθ := h1.div_const _
  have hB : MeasureTheory.IntegrableOn
      (fun θ => (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2)
      Work.Spaces.Iθ := hI2.div_const _
  have hC : MeasureTheory.IntegrableOn
      (fun θ => (f z θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2) Work.Spaces.Iθ :=
    h3.div_const _
  have hAB : MeasureTheory.IntegrableOn
      (fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2
        - (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2) Work.Spaces.Iθ :=
    hA.sub hB
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar, hsplit,
    MeasureTheory.integral_add hAB hC, MeasureTheory.integral_sub hA hB]
  simp only [MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
  ring

/-- If moreover the three moments vanish, so does the moment of the second difference quotient. -/
theorem Fstar_dqq_eq_zero {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h4 : Work.Elliptic.Fstar f (c ^ 2 * z) = 0) (h5 : Work.Elliptic.Fstar f (c * z) = 0)
    (h6 : Work.Elliptic.Fstar f z = 0) :
    Work.Elliptic.Fstar (dq c (dq c f)) z = 0 := by
  rw [Fstar_dqq_eq h1 h2 h3, h4, h5, h6]
  simp

/-! ## The two instantiations -/

theorem Fstar_dqq_F_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {c : ℝ} (hc : 1 < c) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (dq c (dq c F)) z = 0 := by
  intro z hz
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    smoothOpen_of_bslOp_eq (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  have hmF : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 2) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hSF) h.memF
  have hint : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => F y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun y hy => integrableOn_sinCos2_of_HkMem hSF hmF hy
  refine Fstar_dqq_eq_zero (hint (c ^ 2 * z) ?_) (hint (c * z) ?_) (hint z hz) ?_ ?_ ?_
  · positivity
  · positivity
  · exact h.orthF (c ^ 2 * z) (by positivity)
  · exact h.orthF (c * z) (by positivity)
  · exact h.orthF z hz

theorem Fstar_dqq_Ψ_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {c : ℝ} (hc : 1 < c) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (dq c (dq c Ψ)) z = 0 := by
  intro z hz
  have hint : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun y hy => integrableOn_sinCos2_of_weak (k := 2) (by norm_num) h hy
  refine Fstar_dqq_eq_zero (hint (c ^ 2 * z) ?_) (hint (c * z) ?_) (hint z hz) ?_ ?_ ?_
  · positivity
  · positivity
  · exact h.orthPsi (c ^ 2 * z) (by positivity)
  · exact h.orthPsi (c * z) (by positivity)
  · exact h.orthPsi z hz

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.TL2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `TL2/shiftZeroSlots` — the level-`0` slots of the radially shifted datum

## The statement and the route

For a datum `(F, Ψ)` of the weak elliptic class `EllWeakPos α k F Ψ` (`α ∈ (0,1/4]`) and every
`j ≤ k`, the two *level-`0` slots* of the `j`-times radially shifted solution

  `α⁴ |z²∂_z²(D_z^jΨ)|²_{ℋ⁰} + |∂_θ²(D_z^jΨ)|²_{ℋ⁰}`

are bounded by `C |F|²_{ℋ^k}`, with a universal (`α`-independent) constant `C`, **given** the
level-`0` estimate `EllWeak0` as a hypothesis.

The route is the *dilation difference quotient*.  `bslOp α` is homogeneous under the dilations
`z ↦ c z` (`Dil.bslOp_dil`), and the class `EllWeakPos` is defined by *linear* conditions
(equation, Dirichlet data, the two angular moments, smoothness, the three `HkMem` fields), so for
every `c > 1` the `j`-th difference-quotient datum

  `((dq c)^j F, (dq c)^j Ψ)`,   `dq c g = (g(c·) - g)/(c-1)`,

is again a datum of the *pointwise* class at level `0` (`ellWeakPos_dqIter` below).  In
particular the angular moments of `(dq c)^j F` and `(dq c)^j Ψ` vanish **pointwise** — they are
the difference quotients of the moments of `F`, `Ψ`, which vanish by the hypothesis class; no
moment condition of the *shifted* datum is needed.  The level-`0` estimate therefore applies:

  `α⁴ |z²∂_z²((dq c)^jΨ)|²_{ℋ⁰} + |∂_θ²((dq c)^jΨ)|²_{ℋ⁰} ≤ C₀ |(dq c)^j F|²_{ℋ⁰}`.

Letting `c → 1⁺` along `cₙ = 1 + 1/(n+1)`, using that `(dq c)^j g → D_z^j g`
(`Dil.dqIterTendsto`), the slot identities `z²∂_z²((dq c)^jΨ) = (dq c)^j(z²∂_z²Ψ)` and
`∂_θ²((dq c)^jΨ) = (dq c)^j(∂_θ²Ψ)` (`Dil.zsq_pzIter_two_dq`, `Dil.pthIter_two_dq`), and Fatou's
lemma for the `ℋ⁰`-functional (`Dil.HkSq_zero_le_of_eventually_le`), gives the conclusion.  The
right-hand side is controlled by the *dilation* estimate `|(dq c)^j F|_{ℋ⁰} ≤ c^{3j}|D_z^jF|_{ℋ⁰}`
(`Dil.HkMem_dq_le`) together with the `D_z`-shift inequality `|D_z^jF|_{ℋ⁰} ≤ C|F|_{ℋ^k}`
(`hkSq_dzIter_le`).
-/

/-! ## The iterated difference quotient: smoothness, and commutation with `D_z` -/

/-- `dq c` preserves smoothness on the open quadrant, iterated. -/
theorem smoothOpen_dqIter {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen ((Dil.dq c)^[j] g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact Dil.smoothOpen_dq ih (lt_trans zero_lt_one hc)

/-- **`D_z` commutes with the difference quotient** on the open quadrant. -/
theorem dz_dq_agree {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Dil.dq c g))
      (Dil.dq c (Work.Spaces.Dz g)) := by
  intro z θ hz hθ hlt
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  have h := Dil.pz_dq hg hc z θ hz hθ'
  have h1 : Work.Spaces.Dz (Dil.dq c g) z θ
      = z * ((c * Work.Spaces.pz g (c * z) θ - Work.Spaces.pz g z θ) / (c - 1)) := by
    rw [Work.Spaces.Dz, h]
  have h2 : Dil.dq c (Work.Spaces.Dz g) z θ
      = (c * z * Work.Spaces.pz g (c * z) θ - z * Work.Spaces.pz g z θ) / (c - 1) := by
    simp only [Dil.dq_apply, Work.Spaces.Dz]
  rw [h1, h2]
  ring

/-- `D_z` commutes with the iterates of `D_z` (purely algebraic). -/
theorem dz_dzIter_comm (g : ℝ → ℝ → ℝ) : ∀ m : ℕ,
    Work.Spaces.Dz (Work.Spaces.DzIter m g) = Work.Spaces.DzIter m (Work.Spaces.Dz g) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]

/-- **`D_z` commutes with the iterated difference quotient** on the open quadrant. -/
theorem dz_dqIter_agree {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) (j : ℕ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz ((Dil.dq c)^[j] g))
      ((Dil.dq c)^[j] (Work.Spaces.Dz g)) := by
  induction j with
  | zero => intro z θ hz hθ hlt; rfl
  | succ j ih =>
    intro z θ hz hθ hlt
    have hstep := dz_dq_agree (smoothOpen_dqIter hg hc j) hc z θ hz hθ hlt
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hcz : 0 < c * z := mul_pos (lt_trans zero_lt_one hc) hz
    have h3 : Dil.dq c (Work.Spaces.Dz ((Dil.dq c)^[j] g)) z θ
        = Dil.dq c ((Dil.dq c)^[j] (Work.Spaces.Dz g)) z θ := by
      simp only [Dil.dq_apply]
      rw [ih z θ hz hθ hlt, ih (c * z) θ hcz hθ hlt]
    exact hstep.trans h3

/-- Congruence of `D_z` under agreement on the open quadrant (the derivative needs a
*neighbourhood*, which the open quadrant provides). -/
theorem dz_congr_Q0 {u v : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.AgreeOnQ u v) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
  intro z θ hz hθ hlt
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have heq : Set.EqOn (Function.uncurry u) (Function.uncurry v) Work.FTS.EllipticEst.Q0 :=
    fun p hp' => h p.1 p.2 hp'.1 hp'.2.1 hp'.2.2
  show z * Work.Spaces.pz u z θ = z * Work.Spaces.pz v z θ
  rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 heq hp]

/-! ## Linearity of the angular moment for difference quotients -/

/-- **Linearity of the angular moment** for a difference quotient.  If the two slices of `f` at
`c z` and at `z` are integrable against `sinθcos²θ`, the moment of `dq c f` is the difference
quotient of the moments. -/
theorem Fstar_dq_eq {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Dil.dq c f) z
      = (Work.Elliptic.Fstar f (c * z) - Work.Elliptic.Fstar f z) / (c - 1) := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  have hfun : (fun θ => Dil.dq c f z θ * Work.Elliptic.sinCos2 θ)
      = fun θ => ((f (c * z) θ * Work.Elliptic.sinCos2 θ
          - f z θ * Work.Elliptic.sinCos2 θ) / (c - 1)) := by
    funext θ
    rw [Dil.dq_apply]
    ring
  rw [hfun, MeasureTheory.integral_div, MeasureTheory.integral_sub h1 h2]

/-- The moment of a difference quotient vanishes if the moment of `f` does. -/
theorem Fstar_dq_eq_zero {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h3 : Work.Elliptic.Fstar f (c * z) = 0) (h4 : Work.Elliptic.Fstar f z = 0) :
    Work.Elliptic.Fstar (Dil.dq c f) z = 0 := by
  rw [Fstar_dq_eq h1 h2, h3, h4, sub_zero, zero_div]

/-- A function whose weighted `ℋ⁰`-integrand is integrable on a slice has that slice integrable
against `sinθcos²θ` (pointwise absorption `|a sinθcos²θ| ≤ a²w²sin(2θ)^{-η} + 1`). -/
theorem integrableOn_sinCos2_of_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {y : ℝ} (hy : 0 < y)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f y θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => f y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (f y θ * (Work.Spaces.w y / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Dil.HkIntegrand_zero_apply] using h
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine hf.continuousOn.mul ?_
    have hc : Continuous fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2 := by
      show Continuous fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2
      fun_prop
    exact hc.continuousOn
  refine MeasureTheory.Integrable.mono' (hsq.add hone)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hy) ?_
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun θ hθ => ?_
  rw [Real.norm_eq_abs]
  exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hy hθ

/-! ## Descending the level of the class, and the `D_z`-shifts of an `ℋ^k`-function -/

/-- The weak class at level `k` is a class at every lower level `l ≤ k` (only the three `HkMem`
fields change). -/
theorem ellWeakPos_descend {α : ℝ} {k l : ℕ} (hkl : l ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ :=
  ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp
        (AeMom.Repair.SmoothOpen_of_bslOp_eq h.smoothOpen
          (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt))) h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (AeMom.Repair.SmoothOpen.zsq_mul (h.smoothOpen.pzIter 2))) h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((h.smoothOpen.pth).pth)) h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      (Work.FTS.EllipticEst.TT.smoothOpen_diagHon
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((h.smoothOpen.pth).pth)))
      h.memZPth2⟩

/-- **The `m`-fold radial derivative of an `ℋ^k`-function is in `ℋ^{k-m}`** (for `m ≤ k`). -/
theorem hkMem_dzIter_le {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    ∀ m ≤ k, Work.Spaces.HkMem α (k - m) (Work.Spaces.DzIter m g) := by
  intro m hm
  induction m with
  | zero => simpa using hmem
  | succ m ih =>
    have hmk : m ≤ k := by omega
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter m g) := hg.DzIter m
    have hprev : Work.Spaces.HkMem α (k - m) (Work.Spaces.DzIter m g) := ih hmk
    have hshift := AeMom.Repair.HkMem_Dz_shift (α := α) (k := k - m) (by omega : 1 ≤ k - m)
      hsm hprev
    rw [Work.Spaces.DzIter_succ]
    have heq : k - m - 1 = k - (m + 1) := by omega
    rwa [heq] at hshift

/-- **The `ℋ`-level of the `m`-fold radial derivative** (for `m ≤ k`): iterating the `D_z`-shift
inequality.  The constant is universal in `α`. -/
theorem hkSq_dzIter_level (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α k g → ∀ m ≤ k,
        Work.Spaces.HkSq α (k - m) (Work.Spaces.DzIter m g)
          ≤ C * Work.Spaces.HkSq α k g := by
  induction k with
  | zero =>
    refine ⟨1, one_pos, fun α g hg hmem m hm => ?_⟩
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    simp
  | succ k ih =>
    obtain ⟨C, hCpos, hCb⟩ := ih
    refine ⟨max 1 (C * ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 1))), ?_,
      fun α g hg hmem m hm => ?_⟩
    · exact lt_max_of_lt_left one_pos
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        simp only [Nat.sub_zero, Work.Spaces.DzIter_zero]
        have hle : (1 : ℝ) ≤ max 1 (C * ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 1))) :=
          le_max_left _ _
        calc Work.Spaces.HkSq α (k + 1) g
            = 1 * Work.Spaces.HkSq α (k + 1) g := (one_mul _).symm
          _ ≤ max 1 (C * ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 1)))
                * Work.Spaces.HkSq α (k + 1) g :=
              mul_le_mul_of_nonneg_right hle (Work.Spaces.HkSq_nonneg α (k + 1) g)
      · have hmk : m - 1 ≤ k := by omega
        have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hg.Dz
        have hmemDz : Work.Spaces.HkMem α k (Work.Spaces.Dz g) := by
          have h := AeMom.Repair.HkMem_Dz_shift (α := α) (k := k + 1) (by omega) hg hmem
          rwa [show (k + 1) - 1 = k from rfl] at h
        have hstep := hCb α (Work.Spaces.Dz g) hsm hmemDz (m - 1) hmk
        have hbase := Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le (k := k + 1) (by omega) α g
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg) hmem
        rw [show (k + 1) - 1 = k from rfl] at hbase
        have hcast : ((↑(k + 1) : ℝ) + ↑(k + 1) * ↑(k + 1))
            = ((k : ℝ) + 1) + ((k : ℝ) + 1) * ((k : ℝ) + 1) := by push_cast; ring
        rw [hcast] at hbase
        have hDzIter : Work.Spaces.DzIter m g = Work.Spaces.DzIter (m - 1) (Work.Spaces.Dz g) := by
          rw [show m = (m - 1) + 1 from by omega, Work.Spaces.DzIter_succ, dz_dzIter_comm,
            show m - 1 + 1 - 1 = m - 1 from by omega]
        rw [hDzIter]
        calc Work.Spaces.HkSq α (k + 1 - m) (Work.Spaces.DzIter (m - 1) (Work.Spaces.Dz g))
            = Work.Spaces.HkSq α (k - (m - 1)) (Work.Spaces.DzIter (m - 1) (Work.Spaces.Dz g)) := by
              rw [show k + 1 - m = k - (m - 1) from by omega]
          _ ≤ C * Work.Spaces.HkSq α k (Work.Spaces.Dz g) := hstep
          _ ≤ C * (((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 1)) * Work.Spaces.HkSq α (k + 1) g) :=
              mul_le_mul_of_nonneg_left hbase hCpos.le
          _ ≤ max 1 (C * ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 1)))
                * Work.Spaces.HkSq α (k + 1) g := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_right _ _)
                (Work.Spaces.HkSq_nonneg α (k + 1) g)

/-- **The `ℋ⁰`-norm of the `m`-fold radial derivative of an `ℋ^k`-function** is bounded by the
`ℋ^k`-norm (for `m ≤ k`), with a constant universal in `α`. -/
theorem hkSq_dzIter_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α k g → ∀ m ≤ k,
        Work.Spaces.HkSq α 0 (Work.Spaces.DzIter m g) ≤ C * Work.Spaces.HkSq α k g := by
  obtain ⟨C, hCpos, hCb⟩ := hkSq_dzIter_level k
  refine ⟨C, hCpos, fun α g hg hmem m hm => ?_⟩
  have hlvl := hCb α g hg hmem m hm
  have hmem' : Work.Spaces.HkMem α (k - m) (Work.Spaces.DzIter m g) := hkMem_dzIter_le hg hmem m hm
  have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le (k - m)) hmem'
  exact le_trans hmono hlvl

/-! ## The difference-quotient datum

The `ℋ⁰`-membership and the `ℋ⁰`-norm bound of `dq c g` (from `Dil`, proved by the *dilation*
formula `dq c g = (log c/(c-1))∫₀¹ D_zg(z e^{t log c})·dt`), together with the whole bookkeeping
that shows that the *iterated* difference-quotient datum is again a datum of the class.  The two
facts taken from `Dil` are carried as explicit hypotheses `hA`/`hB` of the lemmas below, so that
the assembly is independent of the exact form in which they are proved. -/

/-- The dilation estimate of `Dil.HkMem_dq_le`, in the shape used by the induction. -/
def DilEstimate : Prop :=
  ∀ {α c : ℝ} {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz g) → 1 < c →
    Work.Spaces.HkMem α 0 (Dil.dq c g) ∧
      Work.Spaces.HkSq α 0 (Dil.dq c g) ≤ c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)

/-- The iterated-difference-quotient limit of `Dil.dqIterTendsto`, in the shape used below. -/
def DqLimit : Prop :=
  ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f → ∀ (j : ℕ) {z θ : ℝ}, 0 < z →
    θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Filter.Tendsto (fun c : ℝ => (Dil.dq c)^[j] f z θ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.DzIter j f z θ))


/-- Slice integrability against `sinθcos²θ` is preserved by the iterated difference quotient. -/
theorem sliceIntegrable_dqIter {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hsl : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => f y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ∀ (m : ℕ) (y : ℝ), 0 < y →
      MeasureTheory.IntegrableOn (fun θ => ((Dil.dq c)^[m] f) y θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
  intro m
  induction m with
  | zero => intro y hy; exact hsl y hy
  | succ m ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    have hcy : 0 < c * y := mul_pos hc hy
    have h1 := ih (c * y) hcy
    have h2 := ih y hy
    have heq : (fun θ => Dil.dq c ((Dil.dq c)^[m] f) y θ * Work.Elliptic.sinCos2 θ)
        = fun θ => ((((Dil.dq c)^[m] f) (c * y) θ * Work.Elliptic.sinCos2 θ
            - ((Dil.dq c)^[m] f) y θ * Work.Elliptic.sinCos2 θ) / (c - 1)) := by
      funext θ
      rw [Dil.dq_apply]
      ring
    rw [heq]
    exact (h1.sub h2).div_const (c - 1)





/-- **The `z`-slot identity for the iterated difference quotient**: on the open quadrant,
`z²∂_z²((dq c)^jΦ) = (dq c)^j(z²∂_z²Φ)`. -/
theorem zsq_pzIter_two_dqIter {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {c : ℝ} (hc : 1 < c) (j : ℕ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 ((Dil.dq c)^[j] Φ) z θ)
      ((Dil.dq c)^[j] (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  induction j with
  | zero => intro z θ hz hθ hlt; rfl
  | succ j ih =>
    intro z θ hz hθ hlt
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
    have hsm := smoothOpen_dqIter hΦ hc j
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show z ^ 2 * Work.Spaces.pzIter 2 (Dil.dq c ((Dil.dq c)^[j] Φ)) z θ
      = Dil.dq c ((Dil.dq c)^[j] (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)) z θ
    rw [Dil.zsq_pzIter_two_dq hsm hc z θ hz hθ']
    have h1 := ih z θ hz hθ hlt
    have h2 := ih (c * z) θ (mul_pos hcpos hz) hθ hlt
    simp only [Dil.dq_apply, h1, h2]

/-- **The `θ`-slot identity for the iterated difference quotient**: on the open quadrant,
`∂_θ²((dq c)^jΦ) = (dq c)^j(∂_θ²Φ)`. -/
theorem pthIter_two_dqIter {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {c : ℝ} (hc : 1 < c) (j : ℕ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pthIter 2 ((Dil.dq c)^[j] Φ))
      ((Dil.dq c)^[j] (Work.Spaces.pthIter 2 Φ)) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  induction j with
  | zero => intro z θ hz hθ hlt; rfl
  | succ j ih =>
    intro z θ hz hθ hlt
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
    have hsm := smoothOpen_dqIter hΦ hc j
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Work.Spaces.pthIter 2 (Dil.dq c ((Dil.dq c)^[j] Φ)) z θ
      = Dil.dq c ((Dil.dq c)^[j] (Work.Spaces.pthIter 2 Φ)) z θ
    rw [Dil.pthIter_two_dq hsm hc z θ hz hθ']
    have h1 := ih z θ hz hθ hlt
    have h2 := ih (c * z) θ (mul_pos hcpos hz) hθ hlt
    simp only [Dil.dq_apply, h1, h2]

/-! ## The iterated difference quotient is honest, with a controlled norm -/

/-- **The iterated difference quotient is in `ℋ⁰` and its `ℋ⁰`-norm is controlled by `c^{3j}` times
the norm of the `j`-th radial derivative.**  This is the induction of `Dil.HkMem_dq_le` (carried
as the hypothesis `hA`), together with the commutation `D_z`/`dq c`. -/
theorem hkMem_dqIter (hA : DilEstimate) (α : ℝ) {c : ℝ} (hc : 1 < c) :
    ∀ (n : ℕ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      (∀ m ≤ n, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m g)) →
      (∀ m ≤ n, Work.Spaces.HkMem α 0 ((Dil.dq c)^[m] g)) ∧
      (∀ m ≤ n, Work.Spaces.HkSq α 0 ((Dil.dq c)^[m] g)
        ≤ (c ^ 3) ^ m * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter m g)) := by
  intro n
  induction n with
  | zero =>
    intro g hg hm
    refine ⟨fun m hm0 => ?_, fun m hm0 => ?_⟩
    · rw [Nat.le_zero.mp hm0]
      simpa using hm 0 (Nat.zero_le 0)
    · rw [Nat.le_zero.mp hm0]
      simp
  | succ n ih =>
    intro g hg hm
    have hgn : ∀ m ≤ n, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m g) :=
      fun m hm' => hm m (by omega)
    have ihg := ih g hg hgn
    have hgDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hg.Dz
    have hmDz : ∀ m ≤ n, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m (Work.Spaces.Dz g)) := by
      intro m hm'
      have h1 : Work.Spaces.DzIter m (Work.Spaces.Dz g) = Work.Spaces.DzIter (m + 1) g := by
        rw [Work.Spaces.DzIter_succ, dz_dzIter_comm]
      rw [h1]
      exact hm (m + 1) (by omega)
    have ihDz := ih (Work.Spaces.Dz g) hgDz hmDz
    have hsmn := smoothOpen_dqIter hg hc n
    have hmDq : Work.Spaces.HkMem α 0 (Work.Spaces.Dz ((Dil.dq c)^[n] g)) := by
      have h2 := ihDz.1 n (le_refl n)
      have hag := dz_dqIter_agree hg hc n
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2
        (fun z hz θ hθ => (hag z θ hz hθ.1 hθ.2).symm)
    refine ⟨fun m hm' => ?_, fun m hm' => ?_⟩
    · rcases Nat.lt_or_eq_of_le hm' with hlt | heq
      · exact ihg.1 m (by omega)
      · subst heq
        rw [Function.iterate_succ_apply']
        exact (hA hsmn hmDq hc).1
    · rcases Nat.lt_or_eq_of_le hm' with hlt | heq
      · exact ihg.2 m (by omega)
      · subst heq
        have hstep := (hA hsmn hmDq hc).2
        have hag := dz_dqIter_agree hg hc n
        have hcongr : Work.Spaces.HkSq α 0 (Work.Spaces.Dz ((Dil.dq c)^[n] g))
            = Work.Spaces.HkSq α 0 ((Dil.dq c)^[n] (Work.Spaces.Dz g)) :=
          Work.FTS.EllipticEst.HkSq_congr_open α 0
            (fun z θ hz hθ hlt => hag z θ hz hθ hlt)
        rw [hcongr] at hstep
        have hidx : Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
          rw [Work.Spaces.DzIter_succ, dz_dzIter_comm]
        calc Work.Spaces.HkSq α 0 ((Dil.dq c)^[n + 1] g)
            = Work.Spaces.HkSq α 0 (Dil.dq c ((Dil.dq c)^[n] g)) := by
              rw [Function.iterate_succ_apply']
          _ ≤ c ^ 3 * Work.Spaces.HkSq α 0 ((Dil.dq c)^[n] (Work.Spaces.Dz g)) := hstep
          _ ≤ c ^ 3 * ((c ^ 3) ^ n * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter n (Work.Spaces.Dz g))) :=
              mul_le_mul_of_nonneg_left (ihDz.2 n (le_refl n)) (by positivity)
          _ = (c ^ 3) ^ (n + 1) * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter (n + 1) g) := by
              rw [hidx, pow_succ]
              ring

/-! ## The iterated difference-quotient datum is again of the weak class -/

/-- **The class is preserved by one difference quotient** (given the shifted honesties needed by
`Dil.HkMem_dq_le`, and the `σ`-integrability of the slices of the solution). -/
theorem ellWeakPos_dq_step (hA : DilEstimate) {α : ℝ} {G Φ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 G Φ) {c : ℝ} (hc : 1 < c)
    (hDzG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz G))
    (hDzA : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)))
    (hDzB : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.pthIter 2 Φ)))
    -- the diagonal second-order honesty of the difference-quotient datum, in the exact form of
    -- the new conjunct of `EllWeakPos` (not derivable from the level-`0` clauses of `h` by a
    -- `Dz`-shift, which needs level `1`; the caller supplies it, cf. `EllWeakPos_dqq`)
    (hZdq : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Dil.dq c Φ)) z θ))
    (hslΦ : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => Φ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 0 (Dil.dq c G) (Dil.dq c Φ) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hΦ : Work.FTS.EllipticEst.SmoothOpen Φ := h.smoothOpen
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    AeMom.Repair.SmoothOpen_of_bslOp_eq hΦ (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt)
  have hDqA := (hA (AeMom.Repair.SmoothOpen.zsq_mul (hΦ.pzIter 2)) hDzA hc).1
  have hDqB := (hA (hΦ.pth.pth) hDzB hc).1
  have hDqG := (hA hG hDzG hc).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ hθ hlt
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
    have hcz : 0 < c * z := mul_pos hcpos hz
    rw [Dil.bslOp_dq α hΦ hc z θ hz hθ']
    rw [h.eq (c * z) hcz θ hθ hlt, h.eq z hz θ hθ hlt, Dil.dq_apply]
  · -- the Dirichlet data at `θ = 0`
    intro z
    rw [Dil.dq_apply, h.zero (c * z), h.zero z, sub_self, zero_div]
  · -- the Dirichlet data at `θ = π/2`
    intro z
    rw [Dil.dq_apply, h.pi_half (c * z), h.pi_half z, sub_self, zero_div]
  · -- the source moment
    intro z hz
    exact Fstar_dq_eq_zero
      (integrableOn_sinCos2_of_HkIntegrand hG (mul_pos hcpos hz)
        (h.memF.1 (c * z) (le_of_lt (mul_pos hcpos hz))))
      (integrableOn_sinCos2_of_HkIntegrand hG hz (h.memF.1 z (le_of_lt hz)))
      (h.orthF (c * z) (mul_pos hcpos hz)) (h.orthF z hz)
  · -- the solution moment
    intro z hz
    exact Fstar_dq_eq_zero (hslΦ (c * z) (mul_pos hcpos hz)) (hslΦ z hz)
      (h.orthPsi (c * z) (mul_pos hcpos hz)) (h.orthPsi z hz)
  · -- smoothness
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Dil.dq c Φ)).mp
      (Dil.smoothOpen_dq hΦ hcpos) n
  · -- `dq c G ∈ ℋ⁰`
    exact hDqG
  · -- `z²∂_z²(dq c Φ) ∈ ℋ⁰`
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hDqA (fun z hz θ hθ => ?_)
    exact (Dil.zsq_pzIter_two_dq hΦ hc z θ hz hθ).symm
  · -- `∂_θ²(dq c Φ) ∈ ℋ⁰`
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hDqB (fun z hz θ hθ => ?_)
    exact (Dil.pthIter_two_dq hΦ hc z θ hz hθ).symm
  · -- `z ∂_z∂_θθ(dq c Φ) ∈ ℋ⁰` (assumed; see `EllWeakPos_dqq`)
    exact hZdq

/-- **The iterated difference-quotient datum is again a datum of the weak class at level `0`.**

The static inputs are the shifted honesties of the three fields of the class (`F`, `z²∂_z²Ψ`,
`∂_θ²Ψ`) up to order `j`, and the `σ`-integrability of the slices of `Ψ` (both come from the
original class at level `k ≥ j` together with `Dil.HkMem_dq_le`). -/
theorem ellWeakPos_dqIter (hA : DilEstimate) {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) {c : ℝ} (hc : 1 < c) (j : ℕ)
    (hDzF : ∀ m ≤ j, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m F))
    (hDzA : ∀ m ≤ j, Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
    (hDzB : ∀ m ≤ j, Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter m (Work.Spaces.pthIter 2 Ψ)))
    (hDzW : ∀ m ≤ j, Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter m (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)))
    (hslΨ : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ∀ m ≤ j, Work.FTS.EllipticEst.TT.EllWeakPos α 0
      ((Dil.dq c)^[m] F) ((Dil.dq c)^[m] Ψ) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ := h.smoothOpen
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    AeMom.Repair.SmoothOpen_of_bslOp_eq hΨsm (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt)
  have hsmA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    AeMom.Repair.SmoothOpen.zsq_mul (hΨsm.pzIter 2)
  have hsmB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hΨsm.pth.pth
  intro m
  induction m with
  | zero => intro _; simpa using h
  | succ m ih =>
    intro hmj
    have hmj' : m ≤ j := by omega
    have hh : Work.FTS.EllipticEst.TT.EllWeakPos α 0
        ((Dil.dq c)^[m] F) ((Dil.dq c)^[m] Ψ) := ih hmj'
    have hj1 : 1 ≤ j := by omega
    -- the shifted honesties of the fields of the *difference-quotient* datum
    have hgdqF : ∀ m' ≤ j - 1, Work.Spaces.HkMem α 0
        ((Dil.dq c)^[m'] (Work.Spaces.Dz F)) :=
      (hkMem_dqIter hA α hc (j - 1) (Work.Spaces.Dz F) hFsm.Dz (fun m' hm' => by
        have h1 := hDzF (m' + 1) (by omega)
        rwa [Work.Spaces.DzIter_succ, dz_dzIter_comm] at h1)).1
    have hgdqA : ∀ m' ≤ j - 1, Work.Spaces.HkMem α 0
        ((Dil.dq c)^[m'] (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) :=
      (hkMem_dqIter hA α hc (j - 1) (Work.Spaces.Dz
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) hsmA.Dz (fun m' hm' => by
        have h1 := hDzA (m' + 1) (by omega)
        rwa [Work.Spaces.DzIter_succ, dz_dzIter_comm] at h1)).1
    have hgdqB : ∀ m' ≤ j - 1, Work.Spaces.HkMem α 0
        ((Dil.dq c)^[m'] (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
      (hkMem_dqIter hA α hc (j - 1) (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) hsmB.Dz
        (fun m' hm' => by
          have h1 := hDzB (m' + 1) (by omega)
          rwa [Work.Spaces.DzIter_succ, dz_dzIter_comm] at h1)).1
    -- the *diagonal* honesty of the `dq`-iterates: `(dq c)^m (z ∂_z∂_θθΨ)`
    have hgdqW : ∀ m' ≤ j, Work.Spaces.HkMem α 0
        ((Dil.dq c)^[m']
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      (hkMem_dqIter hA α hc j
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) hsmB.Dz
        (fun m' hm' => hDzW m' hm')).1
    have hDzG : Work.Spaces.HkMem α 0
        (Work.Spaces.Dz ((Dil.dq c)^[m] F)) := by
      have h2 := hgdqF m (by omega)
      have hag := dz_dqIter_agree hFsm hc m
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2
        (fun z hz θ hθ => (hag z θ hz hθ.1 hθ.2).symm)
    have hDzA' : Work.Spaces.HkMem α 0
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 ((Dil.dq c)^[m] Ψ) z θ)) := by
      have h2 := hgdqA m (by omega)
      have hag1 := dz_dqIter_agree hsmA hc m
      have hag2 := zsq_pzIter_two_dqIter hΨsm hc m
      have h2' : Work.Spaces.HkMem α 0
          (Work.Spaces.Dz ((Dil.dq c)^[m] (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) :=
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2
          (fun z hz θ hθ => (hag1 z θ hz hθ.1 hθ.2).symm)
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2'
        (fun z hz θ hθ => (dz_congr_Q0 hag2 z θ hz hθ.1 hθ.2).symm)
    have hDzB' : Work.Spaces.HkMem α 0
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 ((Dil.dq c)^[m] Ψ))) := by
      have h2 := hgdqB m (by omega)
      have hag1 := dz_dqIter_agree hsmB hc m
      have hag2 := pthIter_two_dqIter hΨsm hc m
      have h2' : Work.Spaces.HkMem α 0
          (Work.Spaces.Dz ((Dil.dq c)^[m] (Work.Spaces.pthIter 2 Ψ))) :=
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2
          (fun z hz θ hθ => (hag1 z θ hz hθ.1 hθ.2).symm)
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2'
        (fun z hz θ hθ => (dz_congr_Q0 hag2 z θ hz hθ.1 hθ.2).symm)
    -- the *diagonal* honesty of the *next* `dq`-iterate, which is the new conjunct of the
    -- conclusion: `z ∂_z∂_θθ((dq c)^(m+1)Ψ) = (dq c)^(m+1)(z ∂_z∂_θθΨ)` on the open quadrant
    have hZdq : Work.Spaces.HkMem α 0
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 ((Dil.dq c)^[m + 1] Ψ)) z θ) := by
      have h2 := hgdqW (m + 1) (by omega)
      have hag1 := dz_dqIter_agree hsmB hc (m + 1)
      have hag2 := pthIter_two_dqIter hΨsm hc (m + 1)
      have h2' : Work.Spaces.HkMem α 0
          (Work.Spaces.Dz ((Dil.dq c)^[m + 1] (Work.Spaces.pthIter 2 Ψ))) :=
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2
          (fun z hz θ hθ => (hag1 z θ hz hθ.1 hθ.2).symm)
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h2'
        (fun z hz θ hθ => (dz_congr_Q0 hag2 z θ hz hθ.1 hθ.2).symm)
    have hsl' : ∀ y : ℝ, 0 < y → MeasureTheory.IntegrableOn
        (fun θ => ((Dil.dq c)^[m] Ψ) y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      sliceIntegrable_dqIter hcpos hslΨ m
    have hstep := ellWeakPos_dq_step hA hh hc hDzG hDzA' hDzB'
      (by simpa only [Function.iterate_succ_apply'] using hZdq) hsl'
    have h1 : ((Dil.dq c)^[m + 1] F) = Dil.dq c ((Dil.dq c)^[m] F) := by
      rw [Function.iterate_succ_apply']
    have h2 : ((Dil.dq c)^[m + 1] Ψ) = Dil.dq c ((Dil.dq c)^[m] Ψ) := by
      rw [Function.iterate_succ_apply']
    rw [h1, h2]
    exact hstep

/-! ## The a.e. structure of the quadrant, and the two slot identities for `D_z`-iterates -/

/-- The quadrant condition holds almost everywhere for the product measure on `Iz ×ˢ Iθ`
(the exceptional set is `{0} × Iθ ∪ Iz × {0} ∪ Iz × {π/2}`). -/
theorem ae_quadMeasure_of_forall_pos {P : ℝ → ℝ → Prop}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → P z θ) :
    ∀ᵐ p ∂Dil.quadMeasure, P p.1 p.2 := by
  rw [Dil.quadMeasure, MeasureTheory.Measure.prod_restrict, Work.Spaces.Iz, Work.Spaces.Iθ,
    MeasureTheory.ae_restrict_iff' (measurableSet_Ici.prod measurableSet_Icc)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null
    (s := {p : ℝ × ℝ | ¬(p ∈ Set.Ici 0 ×ˢ Set.Icc 0 (Real.pi / 2) → P p.1 p.2)})
    (t := ({0} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
      ∪ ((Set.univ : Set ℝ) ×ˢ ({Real.pi / 2} : Set ℝ))) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hp
    obtain ⟨⟨hz, hθ⟩, hpP⟩ := hp
    rw [Set.mem_Ici] at hz
    rw [Set.mem_Icc] at hθ
    by_cases h1 : 0 < p.1
    · by_cases h2 : 0 < p.2
      · by_cases h3 : p.2 < Real.pi / 2
        · exact absurd (h p.1 p.2 h1 h2 h3) hpP
        · exact Or.inr ⟨Set.mem_univ _, le_antisymm hθ.2 (not_lt.mp h3)⟩
      · exact Or.inl (Or.inr ⟨Set.mem_univ _, le_antisymm (not_lt.mp h2) hθ.1⟩)
    · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h1) hz, Set.mem_univ _⟩)
  · rw [MeasureTheory.measure_union_null_iff, MeasureTheory.measure_union_null_iff]
    exact ⟨⟨by rw [MeasureTheory.Measure.prod_prod]; simp,
        by rw [MeasureTheory.Measure.prod_prod]; simp⟩,
      by rw [MeasureTheory.Measure.prod_prod]; simp⟩

/-- **The `z`-slot identity for the `D_z`-iterates**: on the open quadrant,
`z²∂_z²(D_z^jΨ) = D_z^j(z²∂_z²Ψ)`. -/
theorem zsq_pzIter_two_DzIter_agree {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
      (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  intro j
  induction j with
  | zero => intro z θ hz hθ hlt; rfl
  | succ j ih =>
    intro z θ hz hθ hlt
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
    have hfun : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter (j + 1) Ψ) z θ)
        = (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.Spaces.Dz (Work.Spaces.DzIter j Ψ)) z θ) := by
      rw [Work.Spaces.DzIter_succ]
    rw [hfun]
    refine (Dil.zsq_pzIter_two_Dz_AgreeOnQ (hΨ.DzIter j) z θ hz hθ hlt).trans ?_
    refine (dz_congr_Q0 ih z θ hz hθ hlt).trans ?_
    exact congrFun (congrFun
      (Work.Spaces.DzIter_succ j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)).symm z) θ

/-- **The `θ`-slot identity for the `D_z`-iterates**: on the open quadrant,
`∂_θ²(D_z^jΨ) = D_z^j(∂_θ²Ψ)`. -/
theorem pthIter_two_DzIter_agree {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
      (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) := by
  intro j
  induction j with
  | zero => intro z θ hz hθ hlt; rfl
  | succ j ih =>
    intro z θ hz hθ hlt
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
    have hfun : Work.Spaces.pthIter 2 (Work.Spaces.DzIter (j + 1) Ψ)
        = Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.Spaces.DzIter j Ψ)) := by
      rw [Work.Spaces.DzIter_succ]
    rw [hfun]
    refine (Dil.pthIter_two_Dz_AgreeOnQ (hΨ.DzIter j) z θ hz hθ hlt).trans ?_
    refine (dz_congr_Q0 ih z θ hz hθ hlt).trans ?_
    exact congrFun (congrFun
      (Work.Spaces.DzIter_succ j (Work.Spaces.pthIter 2 Ψ)).symm z) θ

/-- The slices of the solution of a datum of the weak class (`k ≥ 1`) are integrable against
`sinθcos²θ`. -/
theorem psiSliceIntegrable {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro y hy
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := h.smoothOpen
  have hsinCos2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rw [Work.Elliptic.sinCos2]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [sq_nonneg (Real.cos θ)]
  have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have h1 : MeasureTheory.Integrable (fun θ : ℝ => |Ψ y θ| * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable hk h y hy).integrable
  refine h1.mono' ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (hΨ.continuousOn.mul hcontσ.continuousOn) hy
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsinCos2_nn θ hθ), mul_comm]

/-- **The main estimate, with the level-`0` estimate fixed at a constant `C₀`.**

This is the mathematical content of `shiftZeroSlots`, phrased with a *fixed* witness `C₀` of the
hypothesis so that the constant produced may depend on it. -/
theorem shiftZeroSlots_bound (hA : DilEstimate) (hB : DqLimit) (k j : ℕ) (hj : j ≤ k)
    (C₀ : ℝ) (hC₀pos : 0 < C₀) (hEW : Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C * Work.Spaces.HkSq α k F := by
  classical
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    refine ⟨max C₀ 1, lt_max_of_lt_left hC₀pos, fun α F Ψ hα hα4 hcl => ?_⟩
    have hcl0 : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ :=
      ellWeakPos_descend (Nat.zero_le k) hcl
    have hest := hEW α F Ψ hα hα4 hcl0
    have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le k) hcl.memF
    have hnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
    calc α ^ 4 * Work.Spaces.HkSq α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 0 Ψ) z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ))
        = α ^ 4 * Work.Spaces.HkSq α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) := by simp
      _ ≤ C₀ * Work.Spaces.HkSq α 0 F := hest
      _ ≤ C₀ * Work.Spaces.HkSq α k F := mul_le_mul_of_nonneg_left hmono hC₀pos.le
      _ ≤ max C₀ 1 * Work.Spaces.HkSq α k F :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  · obtain ⟨C₁, hC₁pos, hC₁⟩ := hkSq_dzIter_le k
    refine ⟨2 * C₀ * 8 ^ j * C₁ + 1, by positivity, fun α F Ψ hα hα4 hcl => ?_⟩
    have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ := hcl.smoothOpen
    have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
      AeMom.Repair.SmoothOpen_of_bslOp_eq hΨsm (fun z θ hz hθ hlt => hcl.eq z hz θ hθ hlt)
    have hsmA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      AeMom.Repair.SmoothOpen.zsq_mul (hΨsm.pzIter 2)
    have hsmB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hΨsm.pth.pth
    have hcl0 : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ :=
      ellWeakPos_descend (Nat.zero_le k) hcl
    -- static honesties, up to the `j`-th radial derivative
    have hstat : ∀ (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
        Work.Spaces.HkMem α k g → ∀ m ≤ j, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m g) :=
      fun g hg hmem m hm => Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.zero_le (k - m))
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hg.DzIter m))
        (hkMem_dzIter_le hg hmem m (le_trans hm hj))
    have hslΨ := psiSliceIntegrable (α := α) (k := k) (by omega) hcl
    -- the sequence `cₙ = 1 + 1/(n+1) ↓ 1`
    set cseq : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hcseqdef
    have hcseq_gt : ∀ n : ℕ, 1 < cseq n := by
      intro n
      rw [hcseqdef]
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hcseq_le : ∀ n : ℕ, cseq n ≤ 2 := by
      intro n
      rw [hcseqdef]
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h1]
        linarith
      linarith
    have htend : Filter.Tendsto cseq Filter.atTop (𝓝[Set.Ioi 1] 1) := by
      rw [nhdsWithin, Filter.tendsto_inf]
      refine ⟨?_, Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hcseq_gt)⟩
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Filter.Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [hcseqdef]
      simpa using h1
    -- the level-`0` estimate applied to the difference-quotient data
    have hseq : ∀ n : ℕ,
        α ^ 4 * Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j] (Work.Spaces.pthIter 2 Ψ))
        ≤ C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)) := by
      intro n
      have hclass := ellWeakPos_dqIter hA hcl0 (hcseq_gt n) j
        (fun m hm => hstat F hFsm hcl.memF m hm)
        (fun m hm => hstat (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hsmA hcl.memA m hm)
        (fun m hm => hstat (Work.Spaces.pthIter 2 Ψ) hsmB hcl.memB m hm)
        (fun m hm => hstat (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
          hsmB.Dz hcl.memZPth2 m hm)
        hslΨ
      have hest := hEW α ((Dil.dq (cseq n))^[j] F) ((Dil.dq (cseq n))^[j] Ψ) hα hα4
        (hclass j le_rfl)
      rw [Work.FTS.EllipticEst.HkSq_congr_open α 0 (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            ((Dil.dq (cseq n))^[j] Ψ) z θ) (g := (Dil.dq (cseq n))^[j]
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          (fun z θ hz hθ hlt => zsq_pzIter_two_dqIter hΨsm (hcseq_gt n) j z θ hz hθ hlt)] at hest
      rw [Work.FTS.EllipticEst.HkSq_congr_open α 0
            (f := Work.Spaces.pthIter 2 ((Dil.dq (cseq n))^[j] Ψ))
            (g := (Dil.dq (cseq n))^[j] (Work.Spaces.pthIter 2 Ψ))
          (fun z θ hz hθ hlt => pthIter_two_dqIter hΨsm (hcseq_gt n) j z θ hz hθ hlt)] at hest
      have hdq := (hkMem_dqIter hA α (hcseq_gt n) j F hFsm
        (fun m hm => hstat F hFsm hcl.memF m hm)).2 j le_rfl
      have h8 : ((cseq n) ^ 3) ^ j ≤ 8 ^ j := by
        have h0 : (0 : ℝ) ≤ cseq n := le_of_lt (lt_trans zero_lt_one (hcseq_gt n))
        have h3 : (cseq n) ^ 3 ≤ 8 := by
          calc (cseq n) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 (hcseq_le n) 3
            _ = 8 := by norm_num
        exact pow_le_pow_left₀ (by positivity) h3 j
      have hR : Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j] F)
          ≤ 8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) :=
        le_trans hdq (mul_le_mul_of_nonneg_right h8
          (Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.DzIter j F)))
      exact le_trans hest (mul_le_mul_of_nonneg_left hR hC₀pos.le)
    -- the two individual bounds for Fatou
    have hbA : ∀ n : ℕ, Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ (α ^ 4)⁻¹ * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F))) := by
      intro n
      have hα4pos : (0 : ℝ) < α ^ 4 := by positivity
      have h1 : α ^ 4 * Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          ≤ C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)) := by
        have h2 : 0 ≤ Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j] (Work.Spaces.pthIter 2 Ψ)) :=
          Work.Spaces.HkSq_nonneg _ _ _
        linarith [hseq n, h2]
      calc Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          = (α ^ 4)⁻¹ * (α ^ 4 * Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hα4pos), one_mul]
        _ ≤ (α ^ 4)⁻¹ * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F))) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hα4pos))
    have hbB : ∀ n : ℕ, Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j] (Work.Spaces.pthIter 2 Ψ))
        ≤ C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)) := by
      intro n
      have h2 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0 ((Dil.dq (cseq n))^[j]
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
      linarith [hseq n, h2]
    -- Fatou
    have hFatouA : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ (α ^ 4)⁻¹ * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F))) :=
      Dil.HkSq_zero_le_of_eventually_le
        (α := α)
        (u := fun n : ℕ => (Dil.dq (cseq n))^[j]
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        (v := Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        (fun n => Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
          ((smoothOpen_dqIter hsmA (hcseq_gt n) j).continuousOn_HkIntegrand α 0))
        (Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
          ((hsmA.DzIter j).continuousOn_HkIntegrand α 0))
        (fun n => (hkMem_dqIter hA α (hcseq_gt n) j _ hsmA
          (fun m hm => hstat _ hsmA hcl.memA m hm)).1 j le_rfl)
        (hstat _ hsmA hcl.memA j le_rfl)
        (ae_quadMeasure_of_forall_pos (fun z θ hz hθ hlt => (hB hsmA j hz ⟨hθ, hlt⟩).comp htend))
        (Filter.Eventually.of_forall hbA)
    have hFatouB : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
        ≤ C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)) :=
      Dil.HkSq_zero_le_of_eventually_le
        (α := α)
        (u := fun n : ℕ => (Dil.dq (cseq n))^[j] (Work.Spaces.pthIter 2 Ψ))
        (v := Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
        (fun n => Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
          ((smoothOpen_dqIter hsmB (hcseq_gt n) j).continuousOn_HkIntegrand α 0))
        (Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
          ((hsmB.DzIter j).continuousOn_HkIntegrand α 0))
        (fun n => (hkMem_dqIter hA α (hcseq_gt n) j _ hsmB
          (fun m hm => hstat _ hsmB hcl.memB m hm)).1 j le_rfl)
        (hstat _ hsmB hcl.memB j le_rfl)
        (ae_quadMeasure_of_forall_pos (fun z θ hz hθ hlt => (hB hsmB j hz ⟨hθ, hlt⟩).comp htend))
        (Filter.Eventually.of_forall hbB)
    -- the two slot identities for the `D_z`-iterates, and the assembly
    have hLHS : α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        = α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) := by
      rw [Work.FTS.EllipticEst.HkSq_congr_open α 0
            (fun z θ hz hθ hlt => zsq_pzIter_two_DzIter_agree hΨsm j z θ hz hθ hlt),
          Work.FTS.EllipticEst.HkSq_congr_open α 0
            (fun z θ hz hθ hlt => pthIter_two_DzIter_agree hΨsm j z θ hz hθ hlt)]
    rw [hLHS]
    have hSq := hC₁ α F hFsm hcl.memF j hj
    have hnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
    have hY : (0 : ℝ) < 8 ^ j := by positivity
    have hα4pos : (0 : ℝ) < α ^ 4 := by positivity
    calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
        ≤ α ^ 4 * ((α ^ 4)⁻¹ * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0
              (Work.Spaces.DzIter j F))))
          + C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)) := by
          have h2 := mul_le_mul_of_nonneg_left hFatouA (le_of_lt hα4pos)
          linarith [h2, hFatouB]
      _ = 2 * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F))) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hα4pos), one_mul]
          ring
      _ ≤ 2 * C₀ * 8 ^ j * C₁ * Work.Spaces.HkSq α k F := by
          have h2 : 8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)
              ≤ 8 ^ j * (C₁ * Work.Spaces.HkSq α k F) :=
            mul_le_mul_of_nonneg_left hSq (le_of_lt hY)
          have h3 : C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F))
              ≤ C₀ * (8 ^ j * (C₁ * Work.Spaces.HkSq α k F)) :=
            mul_le_mul_of_nonneg_left h2 hC₀pos.le
          have h4 : 2 * (C₀ * (8 ^ j * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F)))
              ≤ 2 * (C₀ * (8 ^ j * (C₁ * Work.Spaces.HkSq α k F))) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
          have heq : 2 * (C₀ * (8 ^ j * (C₁ * Work.Spaces.HkSq α k F)))
              = 2 * C₀ * 8 ^ j * C₁ * Work.Spaces.HkSq α k F := by ring
          rw [← heq]
          exact h4
      _ ≤ (2 * C₀ * 8 ^ j * C₁ + 1) * Work.Spaces.HkSq α k F := by
          nlinarith [hnn]

/-- **`shiftZeroSlots`, from the two dilation inputs.**  The hypothesis `∃C₀, EllWeak0 C₀` is a
*closed* proposition (it does not involve `α`, `F`, `Ψ`), so a witness `C₀` of it may be chosen
before the universally quantified data, and the constant of the estimate is allowed to depend on
it. -/
theorem shiftZeroSlots_aux (hA : DilEstimate) (hB : DqLimit) (k j : ℕ) (hj : j ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) →
      α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C * Work.Spaces.HkSq α k F := by
  by_cases hex : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀
  · obtain ⟨C₀, hC₀pos, hEW⟩ := hex
    obtain ⟨C, hCpos, hCb⟩ := shiftZeroSlots_bound hA hB k j hj C₀ hC₀pos hEW
    exact ⟨C, hCpos, fun α F Ψ hα hα4 hcl _ => hCb α F Ψ hα hα4 hcl⟩
  · refine ⟨1, one_pos, fun α F Ψ hα hα4 hcl h0 => ?_⟩
    exact absurd h0 hex


end Work.FTS.EllipticEst.Cores.Pieces.TL2
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.pPureShiftAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The quadrant measure, in this file's namespace. -/
abbrev qM : MeasureTheory.Measure (ℝ × ℝ) := Work.FTS.EllipticEst.Cores.Dil.quadMeasure

/-- The quadrant measure with the radial variable restricted to the *open* half-line; the two
differ only by the null set `{z = 0}`. -/
theorem qM_eq_ioi :
    qM = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  show (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]


/-- `qM` as the restriction of the two-dimensional Lebesgue measure to the closed quadrant. -/
theorem qM_eq_restrict :
    qM = ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.Measure.prod_restrict]

/-- **The `u`-average majorant** of `Φ` over the segment `[z, cz]`: with `Φ` the `ℋ⁰`-integrand
of `D_z g` it dominates the `ℋ⁰`-integrand of the difference quotient `dq c g`. -/
def Maj (c : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (z * u) θ

theorem Maj_nonneg {c : ℝ} {Φ : ℝ → ℝ → ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (z θ : ℝ) : 0 ≤ Maj c Φ z θ := by
  refine mul_nonneg (inv_nonneg.mpr (by linarith)) ?_
  refine intervalIntegral.integral_nonneg (le_of_lt hc) ?_
  intro u _
  exact mul_nonneg (sq_nonneg u) (hnn _ _)

/-! ## Change of variables in the lower Lebesgue integral on an interval -/

/-- **Change of variables** `u ↦ z * u` (`z > 0`) for the lower Lebesgue integral over an open
interval.  No measurability of `F` is required. -/
theorem lintegral_Ioo_comp_mul_pos {a b z : ℝ} (hz : 0 < z) (F : ℝ → ENNReal) :
    (∫⁻ u in Set.Ioo a b, F (z * u))
      = ENNReal.ofReal z⁻¹ * ∫⁻ s in Set.Ioo (z * a) (z * b), F s := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hmem : ∀ u : ℝ, u ∈ Set.Ioo a b ↔ z * u ∈ Set.Ioo (z * a) (z * b) := by
    intro u
    simp only [Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [hz], by nlinarith [hz]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [hz], by nlinarith [hz]⟩
  have hmain : ∀ H : ℝ → ENNReal,
      (∫⁻ u, H (z * u)) = ENNReal.ofReal z⁻¹ * ∫⁻ s, H s := by
    intro H
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ z hz0).toMeasurableEquiv
    have he : ⇑e = (fun u : ℝ => z * u) := rfl
    have hmap : Measure.map (⇑e) MeasureTheory.volume =
        ENNReal.ofReal z⁻¹ • MeasureTheory.volume := by
      rw [he, Real.map_volume_mul_left hz0, abs_of_pos (inv_pos.mpr hz)]
    calc ∫⁻ u, H (z * u)
        = ∫⁻ u, H (e u) := by rw [he]
      _ = ∫⁻ u, H u ∂(Measure.map (⇑e) MeasureTheory.volume) :=
            (lintegral_map_equiv H e).symm
      _ = ∫⁻ u, H u ∂(ENNReal.ofReal z⁻¹ • MeasureTheory.volume) := by rw [hmap]
      _ = ENNReal.ofReal z⁻¹ * ∫⁻ u, H u := by
            rw [lintegral_smul_measure, smul_eq_mul]
  calc (∫⁻ u in Set.Ioo a b, F (z * u))
      = ∫⁻ u, (Set.Ioo a b).indicator (fun u => F (z * u)) u :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioo (fun u => F (z * u))).symm
    _ = ∫⁻ u, (Set.Ioo (z * a) (z * b)).indicator F (z * u) := by
        refine lintegral_congr fun u => ?_
        by_cases h : u ∈ Set.Ioo a b
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem u).mp h)]
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (fun hc => h ((hmem u).mpr hc))]
    _ = ENNReal.ofReal z⁻¹ * ∫⁻ s, (Set.Ioo (z * a) (z * b)).indicator F s := hmain _
    _ = ENNReal.ofReal z⁻¹ * ∫⁻ s in Set.Ioo (z * a) (z * b), F s := by
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioo F]

/-! ## Continuity and a.e. measurability of the shifted integrands -/


/-- **A.e. measurability of the pair integrand** `(θ, u) ↦ u² Φ (z u) θ`, on
`Iθ × (1, c)`, from continuity of `Φ` on the open quadrant. -/
theorem aemeasurable_shift_pair {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z c : ℝ} (hz : 0 < z) (hc : 1 < c) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => q.2 ^ 2 * Φ (z * q.2) q.1)
      (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) := by
    refine ContinuousOn.mul ((continuous_snd.pow 2).continuousOn) ?_
    have hmap : ContinuousOn (fun q : ℝ × ℝ => (z * q.2, q.1))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) :=
      ((continuous_const.mul continuous_snd).prodMk continuous_fst).continuousOn
    have hms : Set.MapsTo (fun q : ℝ × ℝ => (z * q.2, q.1))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      intro q hq
      show 0 < z * q.2 ∧ q.1 ∈ Set.Ioo 0 (Real.pi / 2)
      exact ⟨mul_pos hz (lt_trans zero_lt_one hq.2.1), hq.1⟩
    exact hΦ.comp hmap hms
  have hce : ContinuousOn (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hIθ, MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)

/-- **A.e. measurability of the triple integrand** `(p, u) ↦ u² Φ (p.1 u) p.2`, on
`qM ⊗ du|_{(1,c)}`, from continuity of `Φ` on the open quadrant. -/
theorem aemeasurable_shift_triple {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {c : ℝ} (hc : 1 < c) :
    AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      (qM.prod (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) := by
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2)
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) := by
    refine ContinuousOn.mul ((continuous_snd.pow 2).continuousOn) ?_
    have hmap : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) :=
      (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
        (continuous_snd.comp continuous_fst)).continuousOn
    have hms : Set.MapsTo (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      intro q hq
      exact ⟨mul_pos hq.1.1 (lt_trans zero_lt_one hq.2.1), hq.1.2⟩
    exact hΦ.comp hmap hms
  have hce : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [qM_eq_ioi, hIθ, MeasureTheory.Measure.prod_restrict,
    MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioi.prod isOpen_Ioo).prod isOpen_Ioo).measurableSet

/-! ## The pointwise expansion of the majorant -/

/-- `ofReal` of the majorant is the `u`-lintegral of the shifted integrand: for `z > 0` and
`θ ∈ Iθ`,

  `ofReal (Maj c Φ z θ) = ofReal ((c-1)⁻¹) ∫⁻ u ∈ (1,c), ofReal (u² Φ (z u) θ)`. -/
theorem ofReal_Maj_eq {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Maj c Φ z θ)
        = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
            ENNReal.ofReal (u ^ 2 * Φ (z * u) θ) := by
  intro z hz θ hθ
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  have hcnn : (0 : ℝ) ≤ c - 1 := by linarith
  show ENNReal.ofReal ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (z * u) θ) = _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcnn)]
  congr 1
  exact Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral hc1
    (hcontu z (Set.mem_Ici.mpr (le_of_lt hz)) θ hθ)
    (fun u _ => mul_nonneg (sq_nonneg u) (hnn (z * u) θ))

/-! ## A.e. measurability on the quadrant from continuity on the open quadrant -/

/-- If `Φ` is continuous on the open quadrant then `ofReal ∘ Φ` is a.e.-measurable for the
quadrant measure: the open quadrant differs from `Iz × Iθ` by the null set
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`. -/
theorem aemeasurable_ofReal_Q0 {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2)) qM := by
  have hce : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2))
      Work.FTS.EllipticEst.Q0 :=
    ENNReal.continuous_ofReal.comp_continuousOn hΦ
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [qM_eq_ioi, hIθ, MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-- The shift `p ↦ (p.1 * u, p.2)` of a function continuous on the open quadrant is again
continuous on the open quadrant, for `u > 0`. -/
theorem continuousOn_shift_fst {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    {u : ℝ} (hu : 0 < u) :
    ContinuousOn (fun p : ℝ × ℝ => Φ (p.1 * u) p.2) Work.FTS.EllipticEst.Q0 := by
  have hmap : ContinuousOn (fun p : ℝ × ℝ => (p.1 * u, p.2)) Work.FTS.EllipticEst.Q0 :=
    ((continuous_fst.mul continuous_const).prodMk continuous_snd).continuousOn
  have hms : Set.MapsTo (fun p : ℝ × ℝ => (p.1 * u, p.2))
      Work.FTS.EllipticEst.Q0 Work.FTS.EllipticEst.Q0 := by
    intro p hp
    show 0 < p.1 * u ∧ p.2 ∈ Set.Ioo 0 (Real.pi / 2)
    exact ⟨mul_pos hp.1 hu, hp.2⟩
  exact hΦ.comp hmap hms

/-- **The multiplicative substitution in the radial variable** for the quadrant measure:
`∫⁻ p, ofReal (Φ (p.1 u) p.2) = u⁻¹ ∫⁻ p, ofReal (Φ p.1 p.2)` for `u > 0`. -/
theorem lintegral_shift_Phi {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    {u : ℝ} (hu : 0 < u) :
    (∫⁻ p, ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM)
      = ENNReal.ofReal u⁻¹ * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM := by
  have hmeas1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ (p.1 * u) p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← qM_eq_ioi]
    exact aemeasurable_ofReal_Q0 (Φ := fun a b => Φ (a * u) b) (continuousOn_shift_fst hΦ hu)
  have hmeas2 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← qM_eq_ioi]
    exact aemeasurable_ofReal_Q0 hΦ
  rw [qM_eq_ioi, MeasureTheory.lintegral_prod _ hmeas1,
    MeasureTheory.lintegral_prod _ hmeas2]
  have hswap : (∫⁻ z in Set.Ioi 0,
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ (z * u) θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Φ (u * z) θ) := by
    refine lintegral_congr fun z => lintegral_congr fun θ => ?_
    rw [mul_comm]
  rw [hswap]
  exact Work.FTS.EllipticEst.AngSecond.lintegral_Ioi_comp_mul_pos u hu
    (fun s : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ s θ))

/-! ## The `ℋ⁰`-lintegral of the majorant -/

/-- **The majorant estimate**: the `ℋ⁰`-lintegral of `Maj c Φ` is at most `c³` times the
`ℋ⁰`-lintegral of `Φ`. -/
theorem lintegral_Maj_le {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c)) :
    (∫⁻ p, ENNReal.ofReal (Maj c Φ p.1 p.2) ∂qM)
      ≤ ENNReal.ofReal (c ^ 3) * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM := by
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  have hcnn : (0 : ℝ) ≤ c - 1 := by linarith
  set K : ENNReal := ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM with hK
  have hF : AEMeasurable
      (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      (qM.prod (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) :=
    aemeasurable_shift_triple hΦc hc
  -- step 1: expand `ofReal (Maj ·)` a.e.
  have hae1 : ∀ᵐ p ∂qM, ENNReal.ofReal (Maj c Φ p.1 p.2)
      = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) := by
    have hset : Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ
        =ᵐ[((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume)]
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      MeasureTheory.Measure.set_prod_ae_eq
        (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ)) (by simp))
        (Filter.EventuallyEq.rfl)
    rw [qM_eq_restrict, ← MeasureTheory.Measure.restrict_congr_set hset]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (isOpen_Ioi.measurableSet.prod measurableSet_Icc) ?_
    intro p hp
    exact ofReal_Maj_eq hc hnn hcontu p.1 hp.1 p.2 hp.2
  rw [lintegral_congr_ae hae1,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 2: Tonelli, swapping `p` and `u`
  have hswap :
      MeasureTheory.lintegral qM (fun p : ℝ × ℝ =>
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)))
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => MeasureTheory.lintegral qM
              (fun p : ℝ × ℝ => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2))) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun (p : ℝ × ℝ) (u : ℝ) => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)) hF
  rw [hswap]
  -- step 3: the value of the inner integral
  have hpoint : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      (∫⁻ p, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) ∂qM) = ENNReal.ofReal u * K := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    calc (∫⁻ p, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) ∂qM)
        = ∫⁻ p, ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM :=
          lintegral_congr fun p => by rw [ENNReal.ofReal_mul (sq_nonneg u)]
      _ = ENNReal.ofReal (u ^ 2) * (∫⁻ p, ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (u ^ 2) * (ENNReal.ofReal u⁻¹ * K) := by
          rw [lintegral_shift_Phi hΦc hu0]
      _ = ENNReal.ofReal u * K := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg u),
            show u ^ 2 * u⁻¹ = u by field_simp]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hpoint]
  rw [MeasureTheory.lintegral_mul_const K (f := fun u : ℝ => ENNReal.ofReal u)
    (ENNReal.measurable_ofReal.comp measurable_id)]
  -- step 4: the `u`-integral and the arithmetic
  have hvalue : (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal u)
      = ENNReal.ofReal ((c ^ 2 - 1) / 2) := by
    have h1 : (∫ x in (1 : ℝ)..c, x) = (c ^ 2 - 1) / 2 := by
      rw [integral_id]; ring
    rw [← h1]
    exact (Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral
      (a := (1 : ℝ)) (b := c) (f := fun u : ℝ => u) hc1 continuousOn_id
      (fun u hu => by linarith [hu.1])).symm
  have hcc : (c - 1)⁻¹ * ((c ^ 2 - 1) / 2) = (c + 1) / 2 := by
    have hcne : c - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hvalue, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hcnn), hcc]
  gcongr
  have h2 : c ≤ c ^ 3 := by nlinarith [hc]
  linarith

/-! ## The `θ`-slice and `z`-integral integrability of the majorant -/

/-- **The `u`-average bound.**  For `z > 0`,
`∫⁻_{u ∈ (1,c)} ofReal u² · ofReal (∫_θ Φ (z u) θ) ≤ c² · z⁻¹ · ∫⁻ Φ`. -/
theorem lintegral_shift_mul_bound {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    {z : ℝ} (hz : 0 < z) :
    (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2) *
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ))
      ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) := by
  have hbound2 : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      ENNReal.ofReal (u ^ 2) ≤ ENNReal.ofReal (c ^ 2) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hu.1, hu.2]
  calc (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2) *
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ))
      ≤ (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (c ^ 2) *
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ)) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun u hu =>
          mul_le_mul_of_nonneg_right (hbound2 u hu) (by positivity)
    _ = ENNReal.ofReal (c ^ 2) * (∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ)) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          (∫⁻ s in Set.Ioo z (z * c),
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))) := by
        rw [lintegral_Ioo_comp_mul_pos hz
          (fun s => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))]
        simp only [mul_one]
    _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        calc (∫⁻ s in Set.Ioo z (z * c),
              ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))
            = ∫⁻ s in Set.Ioo z (z * c), ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) := by
              refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo ?_
              intro s hs
              have hsIz : s ∈ Work.Spaces.Iz := le_of_lt (lt_trans hz hs.1)
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦint s hsIz)
                (Filter.Eventually.of_forall fun θ => hnn s θ)
          _ ≤ ∫⁻ s in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) :=
              MeasureTheory.lintegral_mono_set (fun s hs => lt_trans hz hs.1)
          _ = ∫⁻ s in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) :=
              MeasureTheory.setLIntegral_congr
                (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ))
                  (by simp))
          _ = ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM :=
              (MeasureTheory.lintegral_prod _ (aemeasurable_ofReal_Q0 hΦc)).symm

/-- **The `θ`-slice bound for the majorant.**  For `z > 0` the `ℋ⁰`-lintegral of `Maj c Φ z ·`
is finite, with an explicit bound in terms of the total `ℋ⁰`-lintegral of `Φ`. -/
theorem lintegral_Maj_theta_le {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    {z : ℝ} (hz : 0 < z) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ))
      ≤ ENNReal.ofReal ((c - 1)⁻¹) * (ENNReal.ofReal (c ^ 2) *
          (ENNReal.ofReal z⁻¹ * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM)) := by
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  -- step 1: expand every `θ`-slice
  have hstep : ∀ θ ∈ Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)
      = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (u ^ 2 * Φ (z * u) θ) :=
    fun θ hθ => ofReal_Maj_eq hc hnn hcontu z (Set.mem_Ioi.mpr hz) θ hθ
  rw [MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) hstep,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 2: Tonelli in `(θ, u)`
  have hF : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) :=
    aemeasurable_shift_pair hΦc hz hc
  have hswap :
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun θ : ℝ => MeasureTheory.lintegral
            (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ)))
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => MeasureTheory.lintegral
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)
              (fun θ : ℝ => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun (θ : ℝ) (u : ℝ) => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ)) hF
  rw [hswap]
  -- step 3: the value of the inner integral
  have hpoint : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
        = ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ) := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    have hzu : z * u ∈ Work.Spaces.Iz := le_of_lt (mul_pos hz hu0)
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (Φ (z * u) θ) :=
          lintegral_congr fun θ => by rw [ENNReal.ofReal_mul (sq_nonneg u)]
      _ = ENNReal.ofReal (u ^ 2) *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ (z * u) θ)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ) := by
          rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦint (z * u) hzu)
            (Filter.Eventually.of_forall (fun θ => hnn (z * u) θ))).symm]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hpoint]
  exact mul_le_mul_of_nonneg_left
    (lintegral_shift_mul_bound hc hnn hΦc hΦint hz) (by positivity)

/-- **The `θ`-slices of the majorant are integrable.** -/
theorem integrableOn_Maj_slice {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    (hΦ0 : ∀ θ, Φ 0 θ = 0)
    (hKfin : (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) ≠ ⊤) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj c Φ z θ) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ θ, Maj c Φ 0 θ = 0 := by
      intro θ
      show (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (0 * u) θ = 0
      simp only [zero_mul, hΦ0, mul_zero, intervalIntegral.integral_zero, mul_zero]
    refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero
      (fun θ _ => (h0 θ).symm) measurableSet_Icc
  · have hA : AEMeasurable (fun θ => ENNReal.ofReal (Maj c Φ z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h1 : AEMeasurable (fun θ : ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
          ∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((aemeasurable_shift_pair hΦc hzpos hc).lintegral_prod_right).const_mul _
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact (ofReal_Maj_eq hc hnn hcontu z (Set.mem_Ioi.mpr hzpos) θ hθ).symm
    have ham : MeasureTheory.AEStronglyMeasurable (fun θ => Maj c Φ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h2 : AEMeasurable (fun θ : ℝ => (ENNReal.ofReal (Maj c Φ z θ)).toReal)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ENNReal.measurable_toReal.comp_aemeasurable hA
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ _
      exact ENNReal.toReal_ofReal (Maj_nonneg hc hnn z θ)
    have hfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_Maj_theta_le hc hnn hΦc hcontu hΦint hzpos) ?_
      exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)))
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ham
      (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)).mp hfin.ne

/-- **The `z`-integral of the majorant's `θ`-slices is integrable.** -/
theorem integrableOn_Maj_z {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    (hΦ0 : ∀ θ, Φ 0 θ = 0)
    (hKfin : (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) ≠ ⊤) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj c Φ z θ) Work.Spaces.Iz := by
  have hslice := integrableOn_Maj_slice hc hnn hΦc hcontu hΦint hΦ0 hKfin
  have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Maj c Φ p.1 p.2)) qM := by
    have hset : Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ
        =ᵐ[((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume)]
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      MeasureTheory.Measure.set_prod_ae_eq
        (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ)) (by simp))
        (Filter.EventuallyEq.rfl)
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
        ∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)) qM :=
      ((aemeasurable_shift_triple hΦc hc).lintegral_prod_right).const_mul _
    refine h1.congr ?_
    rw [qM_eq_restrict, ← MeasureTheory.Measure.restrict_congr_set hset]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (isOpen_Ioi.measurableSet.prod measurableSet_Icc)] with p hp
    exact (ofReal_Maj_eq hc hnn hcontu p.1 hp.1 p.2 hp.2).symm
  have hbridge : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ))
      = ∫⁻ p, ENNReal.ofReal (Maj c Φ p.1 p.2) ∂qM := by
    have hcongr : ∀ z ∈ Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)
          = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ) :=
      fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice z hz)
        (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)
    rw [MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hcongr]
    exact (MeasureTheory.lintegral_prod _ hA).symm
  have hfin : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)) < ⊤ := by
    rw [hbridge]
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)
      (lintegral_Maj_le hc hnn hΦc hcontu))
  have hmes : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h2 : AEMeasurable (fun z : ℝ =>
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)).toReal)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ENNReal.measurable_toReal.comp_aemeasurable hA.lintegral_prod_right
    refine h2.aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice z hz)
      (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)]
    exact ENNReal.toReal_ofReal
      (MeasureTheory.integral_nonneg fun θ => Maj_nonneg hc hnn z θ)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmes
    (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Maj_nonneg hc hnn z θ)).mp hfin.ne

/-- The `ℋ⁰`-lintegral of a smooth honest function is `ofReal` of its `HkSq`. -/
theorem lintegral_ofReal_HkIntegrand_eq' {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 f) :
    (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f p.1 p.2) ∂qM)
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 f) :=
  (Work.FTS.EllipticEst.Cores.Dil.ofReal_HkSq_zero hmem
    (aemeasurable_ofReal_Q0 (hf.continuousOn_HkIntegrand α 0))).symm

/-- **The level-`0` estimate for the radial difference quotient**: the `ℋ⁰`-lintegral of `dq c g`
is at most `c³` times the `ℋ⁰`-squared norm of the radial derivative `D_z g`. -/
theorem lintegral_HkIntegrand_dq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g)) (hc : 1 < c) :
    (∫⁻ p, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2)
        ∂qM)
      ≤ ENNReal.ofReal (c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
  have hΦc : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    hg.Dz.continuousOn_HkIntegrand α 0
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dz g) z θ
  have hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
        (Set.Icc (1 : ℝ) c) :=
    Work.FTS.EllipticEst.Cores.PPureShiftRad.continuousOn_u_majorant (α := α) hg hc
  have hae : ∀ᵐ p ∂qM, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2)
      ≤ ENNReal.ofReal (Maj c (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ)
          p.1 p.2) := by
    rw [qM_eq_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) ?_
    intro p hp
    exact ENNReal.ofReal_le_ofReal
      (Work.FTS.EllipticEst.Cores.PPureShiftRad.HkIntegrand_dq_le hg hc p.1 hp.1 p.2 hp.2)
  calc (∫⁻ p, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2) ∂qM)
      ≤ ∫⁻ p, ENNReal.ofReal (Maj c
          (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ) p.1 p.2) ∂qM :=
        lintegral_mono_ae hae
    _ ≤ ENNReal.ofReal (c ^ 3) * (∫⁻ p, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2) ∂qM) :=
        lintegral_Maj_le hc hnn hΦc hcontu
    _ = ENNReal.ofReal (c ^ 3) *
          ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        rw [lintegral_ofReal_HkIntegrand_eq' hg.Dz hgmem]
    _ = ENNReal.ofReal (c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        rw [ENNReal.ofReal_mul (by positivity)]

end Work.FTS.EllipticEst.Cores.pPureShiftAux
end
end
