import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DqqTendsto =====
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

theorem dq_dq_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    dq c (dq c f) z θ = (f (c ^ 2 * z) θ - 2 * f (c * z) θ + f z θ) / (c - 1) ^ 2 := by
  by_cases hc : c = 1
  · subst hc
    simp [dq_apply]
  · have hne : c - 1 ≠ 0 := sub_ne_zero.mpr hc
    simp only [dq_apply]
    field_simp
    ring

/-- `dq c` only sees the values of its argument on `Ioi 0` (both evaluation points are
positive when `c > 0` and `z > 0`). -/
theorem dq_congr_of_pos {c : ℝ} {f g : ℝ → ℝ → ℝ} (hc : 0 < c) {θ : ℝ}
    (h : ∀ y : ℝ, 0 < y → f y θ = g y θ) {z : ℝ} (hz : 0 < z) :
    dq c f z θ = dq c g z θ := by
  simp only [dq_apply, h (c * z) (by positivity), h z hz]

theorem tendsto_dqq_DzDz {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (fun c : ℝ => dq c (dq c g) z θ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Work.Spaces.Dz (Work.Spaces.Dz g) z θ)) := by
  have hcurry : ContDiffOn ℝ 2 (fun y : ℝ => g y θ) (Set.Ioi 0) :=
    (hg.curry_z hθ).of_le (by norm_num)
  have hmain := SecondDiffQuot hz hcurry
  have hlim : z * deriv (fun y : ℝ => g y θ) z + z ^ 2 * deriv (deriv (fun y : ℝ => g y θ)) z
      = Work.Spaces.Dz (Work.Spaces.Dz g) z θ := by
    have h1 : deriv (fun y : ℝ => g y θ) z = Work.Spaces.pz g z θ := rfl
    have h2 : deriv (deriv (fun y : ℝ => g y θ)) z = Work.Spaces.pzIter 2 g z θ := rfl
    rw [h1, h2, Work.Spaces.Dz]
    rw [pz_Dz_eq hg z θ hz hθ]
    ring
  have hgoal : Filter.Tendsto
      (fun c : ℝ => (g (c ^ 2 * z) θ - 2 * g (c * z) θ + g z θ) / (c - 1) ^ 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.Dz (Work.Spaces.Dz g) z θ)) := by
    rw [← hlim]
    exact hmain
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun c => (dq_dq_apply c g z θ).symm) hgoal

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.Tools =====
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

/-! ## The source of a weak datum is `C^∞` on the open quadrant -/

theorem smoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- `z² · Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Ψ z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h ⊢
  intro n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ)).pow 2
  have h3 := h1.mul (h n)
  have hfun : Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Ψ p.1 p.2 := by
    funext p
    rfl
  rwa [hfun]

/-! ## `ℋ⁰`-honesty of `D_z (D_z f)` -/

/-- The single slot of `HkIntegrand α 0 (D_z (D_z f))` is a slot of `HkIntegrand α 2 f`. -/
theorem HkIntegrand_DzDz_le (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz f)) z θ
      ≤ Work.Spaces.HkIntegrand α 2 f z θ := by
  rw [HkIntegrand_zero_apply]
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
    (Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ 2 (by norm_num))

theorem HkMem_DzDz {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 2 f) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz f)) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := Work.Spaces.Dz (Work.Spaces.Dz f))
    (M := fun z θ => Work.Spaces.HkIntegrand α 2 f z θ) ?_ ?_ ?_ ?_
  · exact (hf.Dz.Dz).continuousOn_HkIntegrand α 0
  · intro z hz
    exact hmem.1 z hz
  · exact hmem.2
  · intro z hz θ hθ
    exact HkIntegrand_DzDz_le α f z θ

/-! ## Slice integrability against `sin θ cos²θ` -/

/-- A function whose level-`0` weighted integrand is honest has its slices integrable against
`sin θ cos²θ` (pointwise absorption `|a sinθcos²θ| ≤ a² w² sin(2θ)^{-η} + 1`). -/
theorem integrableOn_sinCos2_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 f)
    {y : ℝ} (hy : 0 < y) :
    MeasureTheory.IntegrableOn (fun θ => f y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (f y θ * (Work.Spaces.w y / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [HkIntegrand_zero_apply] using hmem.1 y (le_of_lt hy)
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
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hy ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- The `Ψ`-side: the slices of a weak datum are integrable against `sin θ cos²θ`. -/
theorem integrableOn_sinCos2_of_weak {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {y : ℝ} (hy : 0 < y) :
    MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
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
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsinCos2_nn θ hθ)]

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.dqIterTendsto =====
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

variable {f g X Y : ℝ → ℝ → ℝ}

/-! ## The exponential dilation average -/

/-- The exponential dilation average `Bh c X z θ = ∫_0^1 X (z c^t) θ dt`. -/
def Bh (c : ℝ) (X : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∫ t in (0 : ℝ)..1, X (z * c ^ t) θ

@[simp] theorem Bh_apply (c : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Bh c X z θ = ∫ t in (0 : ℝ)..1, X (z * c ^ t) θ := rfl

/-- The normalisation `log c/(c-1)` comparing the difference quotient with the logarithmic
dilation. -/
def lam (c : ℝ) : ℝ := Real.log c / (c - 1)

/-! ## The angular slice of `Bh c X` composed with the exponential dilation -/

theorem continuousOn_rpow_pair {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {z c θ : ℝ} (hz : 0 < z) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun t : ℝ => X (z * c ^ t) θ) (Set.uIcc 0 1) := by
  have hpair : ContinuousOn (fun t : ℝ => (z * c ^ t, θ)) (Set.uIcc 0 1) :=
    ((continuous_const.mul (Real.continuous_const_rpow (ne_of_gt hc))).prodMk
      continuous_const).continuousOn
  have hcomp := hX.comp hpair (fun t ht => Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨mul_pos hz (Real.rpow_pos_of_pos hc t), hθ.1, hθ.2⟩)
  simpa only [Function.comp_def, Function.uncurry] using hcomp

/-! ## The base identity: `dq` is `lam · Bh` applied to the radial derivative -/

theorem dq_eq_lam_Bh {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    dq c g z θ = lam c * Bh c (Work.Spaces.Dz g) z θ := by
  have hcpos : 0 < c := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (z * c ^ s) θ)
        (Real.log c * Work.Spaces.Dz g (z * c ^ t) θ) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => g u θ) (Work.Spaces.pz g (z * c ^ t) θ) (z * c ^ t) :=
      hg.hasDerivAt_slice hθ (mul_pos hz (Real.rpow_pos_of_pos hcpos t))
    have h2 : HasDerivAt (fun s : ℝ => z * c ^ s) (z * (c ^ t * Real.log c)) t :=
      ((Real.hasStrictDerivAt_const_rpow hcpos t).hasDerivAt).const_mul z
    have h3 := h1.comp t h2
    have hdeq : Work.Spaces.pz g (z * c ^ t) θ * (z * (c ^ t * Real.log c))
        = Real.log c * Work.Spaces.Dz g (z * c ^ t) θ := by
      rw [Work.Spaces.Dz]; ring
    simpa only [Function.comp_def, hdeq] using h3
  have hint : IntervalIntegrable
      (fun s : ℝ => Real.log c * Work.Spaces.Dz g (z * c ^ s) θ) volume 0 1 :=
    ContinuousOn.intervalIntegrable
      ((continuousOn_rpow_pair (hg.Dz).continuousOn hz hcpos hθ).const_mul _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlog : Real.log c * Bh c (Work.Spaces.Dz g) z θ = g (c * z) θ - g z θ := by
    rw [Bh, ← intervalIntegral.integral_const_mul]
    simpa only [Real.rpow_one, Real.rpow_zero, mul_one, mul_comm] using hFTC
  rw [show dq c g z θ = (g (c * z) θ - g z θ) / (c - 1) from rfl, lam, div_mul_eq_mul_div, hlog]

/-! ## Congruence and homogeneity of the iterates of `Bh` -/

theorem BhIter_congr {c : ℝ} (hc : 0 < c) {X Y : ℝ → ℝ → ℝ}
    (hXY : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → X z θ = Y z θ) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → (Bh c)^[i] X z θ = (Bh c)^[i] Y z θ := by
  induction i with
  | zero => exact hXY
  | succ i ih =>
    intro z θ hz hθ
    simp only [Function.iterate_succ_apply', Bh]
    apply intervalIntegral.integral_congr
    intro t ht
    exact ih (z * c ^ t) θ (mul_pos hz (Real.rpow_pos_of_pos hc t)) hθ

theorem Bh_const_mul (c μ : ℝ) (X : ℝ → ℝ → ℝ) (i : ℕ) :
    (Bh c)^[i] (fun z θ => μ * X z θ) = fun z θ => μ * (Bh c)^[i] X z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext z θ
    simp only [Bh]
    rw [intervalIntegral.integral_const_mul]

/-! ## The radial derivative of a difference quotient -/

theorem Dz_dq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Dz (dq c g) z θ = dq c (Work.Spaces.Dz g) z θ := by
  intro z θ hz hθ
  have hp := pz_dq hg hc z θ hz hθ
  have hD : Work.Spaces.Dz (dq c g) z θ = z * Work.Spaces.pz (dq c g) z θ := rfl
  rw [hD, hp]
  show z * ((c * Work.Spaces.pz g (c * z) θ - Work.Spaces.pz g z θ) / (c - 1))
      = ((c * z) * Work.Spaces.pz g (c * z) θ - z * Work.Spaces.pz g z θ) / (c - 1)
  ring

theorem DzIter_dq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter i (dq c g) z θ = dq c (Work.Spaces.DzIter i g) z θ := by
  induction i with
  | zero => intro z θ hz hθ; simp
  | succ i ih =>
    intro z θ hz hθ
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
    have hev : (fun z' : ℝ => Work.Spaces.DzIter i (dq c g) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => dq c (Work.Spaces.DzIter i g) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' θ hz' hθ
    have h1 : Work.Spaces.Dz (Work.Spaces.DzIter i (dq c g)) z θ
        = Work.Spaces.Dz (dq c (Work.Spaces.DzIter i g)) z θ := by
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq]
    rw [h1, Dz_dq (hg.DzIter i) hc z θ hz hθ]

/-! ## The iterated identity -/

theorem dqIter_eq (c : ℝ) (hc : 1 < c) (j : ℕ) :
    ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (dq c)^[j] f z θ
        = (lam c) ^ j * (Bh c)^[j] (Work.Spaces.DzIter j f) z θ := by
  induction j with
  | zero => intro f hf z θ hz hθ; simp
  | succ j ih =>
    intro f hf z θ hz hθ
    rw [Function.iterate_succ_apply,
      ih (dq c f) (smoothOpen_dq hf (by linarith : (0 : ℝ) < c)) z θ hz hθ]
    rw [BhIter_congr (by linarith : (0 : ℝ) < c)
      (X := Work.Spaces.DzIter j (dq c f)) (Y := dq c (Work.Spaces.DzIter j f))
      (fun z' θ' hz' hθ' => DzIter_dq hf hc j z' θ' hz' hθ') j z θ hz hθ]
    rw [BhIter_congr (by linarith : (0 : ℝ) < c)
      (X := dq c (Work.Spaces.DzIter j f))
      (Y := fun z θ => lam c * (Bh c) (Work.Spaces.DzIter (j + 1) f) z θ)
      (fun z' θ' hz' hθ' => dq_eq_lam_Bh (hf.DzIter j) hc hz' hθ') j z θ hz hθ]
    rw [Bh_const_mul]
    simp only [Function.iterate_succ_apply]
    rw [pow_succ]
    ring

/-! ## Continuity in the radial variable at a fixed angle -/

theorem continuousOn_comp_rpow {Y : ℝ → ℝ} {z c : ℝ} (hz : 0 < z) (hc : 0 < c)
    (hY : ContinuousOn Y (Set.Ioi 0)) :
    ContinuousOn (fun t : ℝ => Y (z * c ^ t)) (Set.uIcc 0 1) := by
  refine hY.comp (continuous_const.mul (Real.continuous_const_rpow (ne_of_gt hc))).continuousOn
    (fun t ht => mul_pos hz (Real.rpow_pos_of_pos hc t))

theorem Bh_slice_cont {X : ℝ → ℝ → ℝ} {c θ : ℝ} (hc : 1 < c)
    (hX : ContinuousOn (fun z => X z θ) (Set.Ioi 0)) :
    ContinuousOn (fun z => Bh c X z θ) (Set.Ioi 0) := by
  have hcpos : 0 < c := by linarith
  have hlogc_ne : Real.log c ≠ 0 := ne_of_gt (Real.log_pos hc)
  have hYc : Continuous (fun v : ℝ => X (Real.exp v) θ) :=
    hX.comp_continuous Real.continuous_exp (fun v => Real.exp_pos v)
  set Ψ : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..v, X (Real.exp u) θ with hΨdef
  have hΨderiv : ∀ v : ℝ, HasDerivAt Ψ (X (Real.exp v) θ) v := by
    intro v
    have hsm : StronglyMeasurableAtFilter (fun u : ℝ => X (Real.exp u) θ) (𝓝 v) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_univ hYc.continuousOn v trivial
    exact intervalIntegral.integral_hasDerivAt_right
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := v))
      hsm hYc.continuousAt
  have hΨcont : Continuous Ψ :=
    continuous_iff_continuousAt.mpr (fun v => (hΨderiv v).continuousAt)
  have hlogcont : ContinuousOn Real.log (Set.Ioi 0) := fun x hx =>
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  -- the value formula
  have hval : ∀ z ∈ Set.Ioi 0, Bh c X z θ
      = (Real.log c)⁻¹ * (Ψ (Real.log c + Real.log z) - Ψ (Real.log z)) := by
    intro z hz
    show (∫ t in (0 : ℝ)..1, X (z * c ^ t) θ) = _
    have hfun : (fun t : ℝ => X (z * c ^ t) θ)
        = fun t : ℝ => X (Real.exp (Real.log c * t + Real.log z)) θ := by
      funext t
      congr 1
      rw [Real.rpow_def_of_pos hcpos, Real.exp_add, Real.exp_log hz]
      ring
    rw [hfun]
    have hkey : (∫ t in (0 : ℝ)..1, X (Real.exp (Real.log c * t + Real.log z)) θ)
        = (Real.log c)⁻¹ * (∫ u in (Real.log z)..(Real.log c + Real.log z),
            X (Real.exp u) θ) := by
      have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
        (fun u : ℝ => X (Real.exp u) θ) hlogc_ne (Real.log z)
      simpa only [mul_zero, add_zero, zero_add, mul_one, smul_eq_mul] using h
    rw [hkey]
    congr 1
    have h := intervalIntegral.integral_interval_sub_left
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ))
        (b := Real.log c + Real.log z))
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := Real.log z))
    rw [← h]
  have hcont : ContinuousOn
      (fun z => (Real.log c)⁻¹ * (Ψ (Real.log c + Real.log z) - Ψ (Real.log z)))
      (Set.Ioi 0) :=
    continuousOn_const.mul
      ((hΨcont.comp_continuousOn (continuousOn_const.add (hlogcont))).sub
        (hΨcont.comp_continuousOn hlogcont))
  refine hcont.congr (fun z hz => hval z hz)

theorem BhIter_slice_cont {c θ : ℝ} (hc : 1 < c) (i : ℕ) :
    ∀ (X : ℝ → ℝ → ℝ), ContinuousOn (fun z => X z θ) (Set.Ioi 0) →
      ContinuousOn (fun z => (Bh c)^[i] X z θ) (Set.Ioi 0) := by
  induction i with
  | zero => intro X hX; simpa using hX
  | succ i ih =>
    intro X hX
    simpa only [Function.iterate_succ_apply'] using
      Bh_slice_cont (X := (Bh c)^[i] X) hc (ih X hX)

/-! ## `Bh`-iterates are convex averages -/

theorem Bh_bounds {X : ℝ → ℝ → ℝ} {c θ : ℝ} (hc : 1 < c)
    (hX : ContinuousOn (fun z => X z θ) (Set.Ioi 0)) (i : ℕ) :
    ∀ z, 0 < z → ∀ m M,
      (∀ u ∈ Set.Icc z (z * c ^ (i : ℝ)), m ≤ X u θ ∧ X u θ ≤ M) →
      m ≤ (Bh c)^[i] X z θ ∧ (Bh c)^[i] X z θ ≤ M := by
  have hcpos : 0 < c := by linarith
  induction i with
  | zero =>
    intro z hz m M hb
    simpa using hb z (by simp [Real.rpow_zero])
  | succ i ih =>
    intro z hz m M hb
    have hstep : (Bh c)^[i + 1] X z θ = ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ := by
      simp only [Function.iterate_succ_apply', Bh]
    rw [hstep]
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        m ≤ (Bh c)^[i] X (z * c ^ t) θ ∧ (Bh c)^[i] X (z * c ^ t) θ ≤ M := by
      intro t ht
      refine ih (z * c ^ t) (mul_pos hz (Real.rpow_pos_of_pos hcpos t)) m M ?_
      intro u hu
      refine hb u ⟨?_, ?_⟩
      · exact le_trans (le_mul_of_one_le_right (le_of_lt hz)
          (Real.one_le_rpow (le_of_lt hc) ht.1)) hu.1
      · have h2 : (z * c ^ t) * c ^ (i : ℝ) ≤ z * c ^ ((i : ℝ) + 1) := by
          rw [mul_assoc, ← Real.rpow_add hcpos]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (le_of_lt hc) (by linarith [ht.2]))
            (le_of_lt hz)
        calc u ≤ (z * c ^ t) * c ^ (i : ℝ) := hu.2
          _ ≤ z * c ^ ((i : ℝ) + 1) := h2
          _ = z * c ^ ((i + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_one]
    have hint : IntervalIntegrable (fun t : ℝ => (Bh c)^[i] X (z * c ^ t) θ) volume 0 1 :=
      ContinuousOn.intervalIntegrable
        (continuousOn_comp_rpow hz hcpos (BhIter_slice_cont hc i X hX))
    constructor
    · calc m = ∫ t in (0 : ℝ)..1, (m : ℝ) := by simp
        _ ≤ ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ :=
            intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hint
              (fun t ht => (hbd t ht).1)
    · calc ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ
          ≤ ∫ t in (0 : ℝ)..1, (M : ℝ) :=
            intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
              (fun t ht => (hbd t ht).2)
        _ = M := by simp

/-! ## The limit of the iterates -/

theorem lam_tendsto : Filter.Tendsto lam (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hslope : Filter.Tendsto (slope Real.log 1) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  have h1 : ∀ c : ℝ, c ≠ 1 → slope Real.log 1 c = lam c := by
    intro c hc
    rw [slope_def_module, lam]
    simp only [smul_eq_mul, Real.log_one, sub_zero]
    ring
  refine Filter.Tendsto.congr' ?_ (hslope.mono_left (nhdsWithin_mono 1 ?_))
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact h1 c (ne_of_gt hc)
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx

theorem lam_pow_tendsto (j : ℕ) :
    Filter.Tendsto (fun c : ℝ => lam c ^ j) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  simpa using lam_tendsto.pow j

theorem BhIter_tendsto {X : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hX : ContinuousOn (fun u => X u θ) (Set.Ioi 0)) (i : ℕ) :
    Filter.Tendsto (fun c : ℝ => (Bh c)^[i] X z θ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (X z θ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcontz : ContinuousAt (fun u => X u θ) z := hX.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hev : ∀ᶠ u in 𝓝 z, dist (X u θ) (X z θ) < ε / 2 :=
    (Metric.tendsto_nhds.mp hcontz.tendsto) (ε / 2) (by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- the smallness of the interval `[z, z c^i]`
  have hex : ∃ η > 0, z * ((1 + η) ^ (i : ℝ) - 1) < δ := by
    have hcont : ContinuousAt (fun η : ℝ => (1 + η) ^ (i : ℝ)) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
    have hT : Filter.Tendsto (fun η : ℝ => z * ((1 + η) ^ (i : ℝ) - 1)) (𝓝 0) (𝓝 0) := by
      have h2 : Filter.Tendsto (fun η : ℝ => (1 + η) ^ (i : ℝ)) (𝓝 0) (𝓝 1) := by
        simpa using hcont.tendsto
      have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
      simpa using ((h2.sub hone).const_mul z)
    have h3 := (Metric.tendsto_nhds.mp hT) δ hδpos
    rw [Metric.eventually_nhds_iff] at h3
    obtain ⟨r, hrpos, hr⟩ := h3
    refine ⟨min (r / 2) 1, by positivity, ?_⟩
    have hmem : min (r / 2) 1 ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      have := min_le_left (r / 2) 1
      linarith
    have h4 := hr hmem
    rw [Real.dist_eq, sub_zero] at h4
    have hpos : (0 : ℝ) ≤ min (r / 2) 1 := le_of_lt (by positivity)
    have hone : (1 : ℝ) ≤ 1 + min (r / 2) 1 := by linarith
    have hle : (1 : ℝ) ≤ (1 + min (r / 2) 1) ^ (i : ℝ) :=
      Real.one_le_rpow hone (Nat.cast_nonneg i)
    rw [abs_of_nonneg (mul_nonneg (le_of_lt hz) (by linarith))] at h4
    exact h4
  obtain ⟨η, hηpos, hηlt⟩ := hex
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hηpos] with c hc hcI
  have hc1 : 1 < c := hcI
  have hclt : c < 1 + η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
    linarith [hc.2]
  have hbd : ∀ u ∈ Set.Icc z (z * c ^ (i : ℝ)),
      X z θ - ε / 2 ≤ X u θ ∧ X u θ ≤ X z θ + ε / 2 := by
    intro u hu
    have huz : dist u z < δ := by
      rw [Real.dist_eq]
      have h1 : u - z ≤ z * ((1 + η) ^ (i : ℝ) - 1) := by
        have h2 : z * c ^ (i : ℝ) ≤ z * (1 + η) ^ (i : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (le_of_lt (by linarith : (0 : ℝ) < c)) (le_of_lt hclt)
              (Nat.cast_nonneg i))
            (le_of_lt hz)
        have h3 : z * (1 + η) ^ (i : ℝ) = z * (1 + ((1 + η) ^ (i : ℝ) - 1)) := by ring
        linarith [hu.1, hu.2]
      rw [abs_of_nonneg (by linarith [hu.1])]
      linarith [hηlt]
    have hd := hδ huz
    rw [Real.dist_eq, abs_lt] at hd
    exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hb := Bh_bounds hc1 hX i z hz (X z θ - ε / 2) (X z θ + ε / 2) hbd
  rw [Real.dist_eq]
  rw [abs_lt]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-! ## The target -/

theorem dqIterTendsto {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (fun c : ℝ => (Work.FTS.EllipticEst.Cores.Dil.dq c)^[j] f z θ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.DzIter j f z θ)) := by
  have hslice : ContinuousOn (fun u => Work.Spaces.DzIter j f u θ) (Set.Ioi 0) :=
    ((hf.DzIter j).curry_z hθ).continuousOn
  refine Filter.Tendsto.congr' ?_ (by
    simpa using (lam_pow_tendsto j).mul (BhIter_tendsto hz hslice j))
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (dqIter_eq c hc j f hf z θ hz hθ).symm

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.PPureShiftRad

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The level-`0` `ℋ`-integrand -/

/-- The level-`0` `ℋ`-integrand is the single weighted squared slot; writing the angular
weight as `sin(2θ)^{-η}` separates the three factors. -/
theorem hk_zero_eq (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 h z θ
      = (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.EllipticEst.Cores.Dil.HkIntegrand_zero_apply]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, Real.rpow_neg hs]
    ring

/-- The level-`0` `ℋ`-integrand of any function vanishes where `sin(2θ) = 0`. -/
theorem hk_zero_of_sin_eq_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 h z θ = 0 := by
  rw [Work.FTS.EllipticEst.Cores.Dil.HkIntegrand_zero_apply, hs,
    Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
    div_zero, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-! ## The pointwise comparison of the radial weight `w` -/

/-- `w` is nonnegative (it is a quotient of squares). -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- For `z > 0` and `u ≥ 1`, `w z ≤ u² w (z u)`: both sides are `((1+z)/z)²` resp.
`((1+zu)/z)²`, and `1 + z ≤ 1 + z u`. -/
theorem w_le_mul_sq {z u : ℝ} (hz : 0 < z) (hu : 1 ≤ u) :
    Work.Spaces.w z ≤ u ^ 2 * Work.Spaces.w (z * u) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have h1 : (1 + z) ^ 2 ≤ (1 + z * u) ^ 2 := by
    have h : 1 + z ≤ 1 + z * u := by nlinarith [hz, hu]
    exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + z) h 2
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  have hw2 : u ^ 2 * Work.Spaces.w (z * u) = (1 + z * u) ^ 2 / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  rw [hw, hw2]
  exact div_le_div_of_nonneg_right h1 (le_of_lt hz2)

/-- For `z > 0` and `u ≥ 1`, `(w z)² ≤ u⁴ (w (z u))²`. -/
theorem w_sq_le_mul {z u : ℝ} (hz : 0 < z) (hu : 1 ≤ u) :
    (Work.Spaces.w z) ^ 2 ≤ u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by
  have h := w_le_mul_sq hz hu
  have h4 : (u ^ 2 * Work.Spaces.w (z * u)) ^ 2
      = u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by ring
  have hzu : 0 < z * u := mul_pos hz (lt_of_lt_of_le zero_lt_one hu)
  calc (Work.Spaces.w z) ^ 2 ≤ (u ^ 2 * Work.Spaces.w (z * u)) ^ 2 :=
        pow_le_pow_left₀ (w_nonneg z) h 2
    _ = u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := h4

/-! ## The difference quotient as an interval integral -/

/-- **The fundamental theorem of calculus for the difference quotient.**  For `g` of class
`C^∞` on the open quadrant, `c > 1`, `z > 0` and `θ ∈ (0,π/2)`,

  `dq c g z θ = (c-1)⁻¹ ∫_1^c u⁻¹ (D_z g) (z u) θ du`. -/
theorem dq_eq_intervalIntegral {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.EllipticEst.Cores.Dil.dq c g z θ
        = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ := by
  intro z θ hz hθ
  have hderiv : ∀ u ∈ Set.uIcc (1 : ℝ) c,
      HasDerivAt (fun u' : ℝ => g (z * u') θ) (u⁻¹ * Work.Spaces.Dz g (z * u) θ) u := by
    intro u hu
    rw [Set.uIcc_of_le (le_of_lt hc)] at hu
    have hu1 : (1 : ℝ) ≤ u := hu.1
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hzu : 0 < z * u := mul_pos hz hu0
    have hsl := hg.hasDerivAt_slice hθ hzu
    have hlin : HasDerivAt (fun u' : ℝ => z * u') z u := by
      simpa using (hasDerivAt_id u).const_mul z
    have hcomp := hsl.comp u hlin
    have hcoe : Work.Spaces.pz g (z * u) θ * z = u⁻¹ * Work.Spaces.Dz g (z * u) θ := by
      rw [Work.Spaces.Dz]
      field_simp
    rw [hcoe] at hcomp
    simpa only [Function.comp_def] using hcomp
  have hcont : ContinuousOn (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ)
      (Set.uIcc (1 : ℝ) c) := by
    rw [Set.uIcc_of_le (le_of_lt hc)]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.comp continuousOn_id (fun u hu => by
        simp only [Set.mem_Icc] at hu
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
    · exact ((hg.Dz).curry_z hθ).continuousOn.comp (by fun_prop) (fun u hu => by
        simp only [Set.mem_Icc] at hu
        simp only [Set.mem_Ioi]
        nlinarith [hu.1, hz])
  have hint : IntervalIntegrable (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ) volume
      (1 : ℝ) c := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC, Work.FTS.EllipticEst.Cores.Dil.dq_apply, div_eq_inv_mul, mul_one]
  rw [show c * z = z * c by ring]

/-! ## The weighted Cauchy–Schwarz instance -/

/-- Weighted Cauchy–Schwarz with weight `σ ≡ 1` and constant interval: for `f` continuous on
`[a,b]`, `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
theorem interval_sq_le_mul_sub {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * ∫ u in a..b, (f u) ^ 2 := by
  have hf2 : MeasureTheory.IntegrableOn (fun s : ℝ => (f s) ^ 2 * (1 : ℝ)) (Set.Ioc a b) := by
    have h : MeasureTheory.IntegrableOn (f ^ 2) (Set.Ioc a b) :=
      ((hf.pow 2).integrableOn_compact (μ := volume) isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have h2 : (fun s : ℝ => (f s) ^ 2 * (1 : ℝ)) = f ^ 2 := by
      funext s; simp
    rw [h2]
    exact h
  have hσi : MeasureTheory.IntegrableOn (fun s : ℝ => ((fun _ : ℝ => (1 : ℝ)) s)⁻¹)
      (Set.Ioc a b) := by
    have h : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
      MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp)
    have h' : (fun s : ℝ => ((fun _ : ℝ => (1 : ℝ)) s)⁻¹) = fun _ : ℝ => (1 : ℝ) := by
      funext s; simp
    rw [h']
    exact h
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul (f := f)
    (σ := fun _ : ℝ => (1 : ℝ)) hab (fun s _ => one_pos) hf2 hσi
  have h1 : (∫ u in a..b, ((fun _ : ℝ => (1 : ℝ)) u)⁻¹) = b - a := by
    rw [intervalIntegral.integral_const]
    norm_num
  have h2 : (∫ u in a..b, (f u) ^ 2 * (fun _ : ℝ => (1 : ℝ)) u) = ∫ u in a..b, (f u) ^ 2 := by
    simp
  rw [h1, h2] at hcs
  calc (∫ u in a..b, f u) ^ 2 ≤ (∫ u in a..b, (f u) ^ 2) * (b - a) := hcs
    _ = (b - a) * ∫ u in a..b, (f u) ^ 2 := by ring

/-! ## The pointwise domination by the majorant -/

/-- The majorant integrand of the difference quotient: `u² · HkIntegrand α 0 (D_z g) (z u) θ`,
continuous in `u` on `[1,c]` for every point of the closed quadrant. -/
theorem continuousOn_u_majorant {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn
        (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
        (Set.Icc 1 c) := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ u : ℝ,
        u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ = 0 := by
      intro u
      rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
    simp only [h0]
    exact continuousOn_const
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have hs : Real.sin (2 * θ) = 0 := by rw [← hθ0]; simp
      have h0 : ∀ u : ℝ,
          u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
        intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
      simp only [h0]
      exact continuousOn_const
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · -- the interior case: a composition of continuous maps
        have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
        have hmap : Set.MapsTo (fun u : ℝ => (z * u, θ)) (Set.Icc 1 c)
            (Work.FTS.EllipticEst.Q0) := by
          intro u hu
          simp only [Set.mem_Icc] at hu
          exact Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨mul_pos hzpos (lt_of_lt_of_le zero_lt_one hu.1), hθ'⟩
        have hDz : ContinuousOn (fun u : ℝ => Work.Spaces.Dz g (z * u) θ) (Set.Icc 1 c) :=
          (hg.Dz).continuousOn.comp
            ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn hmap
        have hwcont : ContinuousOn (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2) (Set.Icc 1 c) := by
          have hcoe : (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2)
              = fun u : ℝ => ((1 + z * u) ^ 2 / (z * u) ^ 2) ^ 2 := by
            funext u; rw [Work.Spaces.w]
          rw [hcoe]
          refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
          · have h1 : ContinuousOn (fun u : ℝ => 1 + z * u) (Set.Icc 1 c) :=
              continuous_const.continuousOn.add
                ((continuous_const.mul continuous_id).continuousOn)
            exact h1.pow 2
          · exact ((continuous_const.mul continuous_id).continuousOn).pow 2
          · intro u hu
            simp only [Set.mem_Icc] at hu
            exact pow_ne_zero 2 (mul_ne_zero (ne_of_gt hzpos)
              (ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)))
        have hcoe : ∀ u : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ
            = (Work.Spaces.Dz g (z * u) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w (z * u)) ^ 2 :=
          fun u => hk_zero_eq α (Work.Spaces.Dz g) (z * u) θ hθ
        simp only [hcoe]
        exact (continuousOn_id.pow 2).mul (((hDz.pow 2).mul continuousOn_const).mul hwcont)
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [hθpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have h0 : ∀ u : ℝ,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
          intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
        simp only [h0]
        exact continuousOn_const

/-- **The pointwise domination.**  For every `z ∈ Iz`, `θ ∈ Iθ`,

  `HkIntegrand α 0 (dq c g) z θ ≤ (c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du`. -/
theorem HkIntegrand_dq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
        ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
  intro z hz θ hθ
  have hc1 : 1 ≤ c := le_of_lt hc
  -- degenerate cases: everything vanishes
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ u : ℝ,
        u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ = 0 := by
      intro u; rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
    rw [Work.FTS.LocData.HkIntegrand_zero_fst α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) θ]
    refine le_of_eq ?_
    simp only [h0, intervalIntegral.integral_zero, mul_zero]
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have hs : Real.sin (2 * θ) = 0 := by rw [← hθ0]; simp
      have h0 : ∀ u : ℝ,
          u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
        intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
      rw [hk_zero_of_sin_eq_zero α (Work.FTS.EllipticEst.Cores.Dil.dq c g) hs z]
      refine le_of_eq ?_
      simp only [h0, intervalIntegral.integral_zero, mul_zero]
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · -- the interior case
        have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
        have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Real.rpow_nonneg
            (Real.sin_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
        have hwznn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        -- continuity of `u ↦ u⁻¹ D_z g (z u) θ` on `[1,c]`
        have hcont : ContinuousOn (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ)
            (Set.Icc 1 c) := by
          refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_id.inv₀ (fun u hu => by
              simp only [Set.mem_Icc] at hu
              exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
          · exact ((hg.Dz).curry_z hθ').continuousOn.comp (by fun_prop) (fun u hu => by
              simp only [Set.mem_Icc] at hu
              simp only [Set.mem_Ioi]
              nlinarith [hu.1, hzpos])
        -- the fundamental theorem of calculus
        have hftc := dq_eq_intervalIntegral hg hc z θ hzpos hθ'
        -- the Cauchy–Schwarz step
        have hcs := interval_sq_le_mul_sub hc1 hcont
        have hcne : (c - 1) ≠ 0 := by linarith
        have hA : (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
            ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
          rw [hftc]
          calc ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              = (c - 1)⁻¹ ^ 2
                  * (∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by ring
            _ ≤ (c - 1)⁻¹ ^ 2 * ((c - 1) * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
            _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                calc (c - 1)⁻¹ ^ 2 * ((c - 1) * ∫ u in (1 : ℝ)..c,
                      (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2)
                    = (c - 1)⁻¹ * ((c - 1)⁻¹ * (c - 1)) * ∫ u in (1 : ℝ)..c,
                        (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by ring
                  _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                        (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                      rw [inv_mul_cancel₀ hcne, mul_one]
        -- multiply by the angular weight and the radial weight
        have hB : (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
            ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
          have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 :=
            mul_nonneg hsnn hwznn
          calc (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
              ≤ ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2)
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2) :=
                mul_le_mul_of_nonneg_right hA h2
            _ = (c - 1)⁻¹ * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w z) ^ 2)
                  * ∫ u in (1 : ℝ)..c, (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) := by ring
            _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                rw [intervalIntegral.integral_const_mul]
        -- the pointwise comparison of the integrands
        have hpt : ∀ u ∈ Set.Icc (1 : ℝ) c,
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
          intro u hu
          have hu1 : (1 : ℝ) ≤ u := hu.1
          have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          have hw := w_sq_le_mul hzpos hu1
          have hune : u ≠ 0 := ne_of_gt hu0
          have halg : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2))
              = u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w (z * u)) ^ 2) := by
            field_simp
          have hKeq := hk_zero_eq α (Work.Spaces.Dz g) (z * u) θ hθ
          have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2)) := by
            have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
              ring
            rw [h1]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hw (sq_nonneg _)) hsnn
          calc ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2)) := hstep
            _ = u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w (z * u)) ^ 2) := halg
            _ = u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
                rw [hKeq]
        -- assemble
        have hInt1 : IntervalIntegrable (fun u : ℝ =>
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
              * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) volume (1 : ℝ) c := by
          have hc' : ContinuousOn (fun u : ℝ =>
              ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) (Set.uIcc (1 : ℝ) c) := by
            rw [Set.uIcc_of_le hc1]
            exact (hcont.pow 2).const_mul _
          exact hc'.intervalIntegrable
        have hInt2 : IntervalIntegrable (fun u : ℝ => u ^ 2 *
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) volume (1 : ℝ) c := by
          have hc' : ContinuousOn (fun u : ℝ => u ^ 2 *
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) (Set.uIcc (1 : ℝ) c) := by
            rw [Set.uIcc_of_le hc1]
            exact continuousOn_u_majorant hg hc z hz θ hθ
          exact hc'.intervalIntegrable
        have hmono := intervalIntegral.integral_mono_on hc1 hInt1 hInt2 hpt
        have hQQ : Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
            = (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2) := by
          rw [hk_zero_eq α (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ hθ]
          ring
        rw [hQQ]
        exact hB.trans (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (by linarith)))
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [hθpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have h0 : ∀ u : ℝ,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
          intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
        rw [hk_zero_of_sin_eq_zero α (Work.FTS.EllipticEst.Cores.Dil.dq c g) hs z]
        refine le_of_eq ?_
        simp only [h0, intervalIntegral.integral_zero, mul_zero]

end Work.FTS.EllipticEst.Cores.PPureShiftRad
end
end
