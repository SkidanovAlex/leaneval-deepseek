import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_layer
import Submission.Work.FTS.EllipticEst.Cert.GbarSin_layer
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cert.FstarSmoothOfSol
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Smoothness infrastructure for the open quadrant -/

theorem mem_Iθ_iff {θ : ℝ} : θ ∈ Work.Spaces.Iθ ↔ 0 ≤ θ ∧ θ ≤ π / 2 := Set.mem_Icc

theorem mem_Iz_iff {z : ℝ} : z ∈ Work.Spaces.Iz ↔ 0 ≤ z := Set.mem_Ici

/-- `Work.Stability.smoothOrder` is not zero (it is the genuine smooth order `∞`). -/
theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- `SmoothNbhd f` (smooth on a neighbourhood of the closed quadrant) implies `SmoothOpen f`. -/
theorem smoothOpen_of_smoothNbhd {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.FTS.EllipticEst.SmoothOpen f := by
  have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := h
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
  refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
  · exact Set.Ioi_subset_Ioi (by norm_num)
  · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

/-- The raw shape of `SmoothOpen` used by `HkNorm_add_le` and `HkNorm_const_mul`. -/
theorem contDiffOn_uncurry_of_smoothOpen {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  intro n
  simpa only [Work.FTS.EllipticEst.Q0] using hf.forall n

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  have hfun : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact (contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.FTS.EllipticEst.Q0).mul hf

/-- `SmoothOpen` only depends on the values on the open quadrant. -/
theorem smoothOpen_congr {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → g z θ = f z θ) : SmoothOpen g :=
  hf.congr (fun p hp => by
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact h p.1 p.2 hz hθ0 hθ1)

/-- A radial function times `sin 2θ` is smooth on the open quadrant. -/
theorem smoothOpen_radial_sin {R : ℝ → ℝ} (hR : ∀ m : ℕ, ContDiffOn ℝ m R (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => R z * Real.sin (2 * θ)) := by
  have hRsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Ioi 0) := contDiffOn_infty.mpr hR
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => R p.1)
      Work.FTS.EllipticEst.Q0 :=
    hRsm.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact h1.mul h2

/-- `SmoothOpen` is closed under iterated `∂_θ`. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (n : ℕ) :
    SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The derivative of a function which is `C^m` on `(0,∞)` for every `m` is again `C^m`. -/
theorem contDiffOn_deriv_of_smooth (f : ℝ → ℝ)
    (hf : ∀ m : ℕ, ContDiffOn ℝ m f (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (deriv f) (Set.Ioi 0) := by
  intro m
  have h1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f (Set.Ioi 0) := hf (m + 1)
  have h2 := h1.deriv_of_isOpen isOpen_Ioi (m := (m : WithTop ℕ∞)) (by simp)
  simpa using h2

/-- A primitive of a `C^∞` function on `(0,∞)` is `C^∞` there. -/
theorem contDiffOn_of_hasDerivAt_of_smooth {f g : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt f (g z) z)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m f (Set.Ioi 0) := by
  have hgTop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.Ioi 0) := contDiffOn_infty.mpr hg
  have hTop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt,
      hgTop.congr (fun z hz => (hderiv z hz).deriv)⟩
  exact contDiffOn_infty.mp hTop

/-! ## 2. Additivity and separation of the iterated derivatives -/

/-- Pointwise equal functions have equal iterated `∂_θ`. -/
theorem pthIter_congr_pt {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) (n : ℕ) :
    Work.Spaces.pthIter n f = Work.Spaces.pthIter n g := by
  induction n with
  | zero => funext z θ; exact h z θ
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- Pointwise equal functions have equal iterated `∂_z`. -/
theorem pzIter_congr_pt {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) (n : ℕ) :
    Work.Spaces.pzIter n f = Work.Spaces.pzIter n g := by
  induction n with
  | zero => funext z θ; exact h z θ
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-- On the open quadrant the iterated `∂_θ`-operators are additive for `SmoothOpen` data. -/
theorem pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((smoothOpen_pthIter hf n).curry_θ hz).differentiableOn smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((smoothOpen_pthIter hg n).curry_θ hz).differentiableOn smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-- On the open quadrant the iterated `∂_z`-operators are additive for `SmoothOpen` data. -/
theorem pzIter_add_on_Q0 {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pzIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pzIter n f z θ + Work.Spaces.pzIter n g z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun z' => Work.Spaces.pzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter n f z' θ + Work.Spaces.pzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter n f z' θ) z :=
        ((hf.pzIter n).hasDerivAt_slice hθ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter n g z' θ) z :=
        ((hg.pzIter n).hasDerivAt_slice hθ hz).differentiableAt
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-- `∂_θ (R z · sin 2θ) = R z · 2 cos 2θ`. -/
theorem pth_radial_sin (R : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => R z * Real.sin (2 * θ))
      = fun z θ => R z * (2 * Real.cos (2 * θ)) := by
  funext z θ
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ :=
    ((Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).differentiableAt
  have key : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = Real.cos (2 * θ) * (2 * 1) :=
    ((Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).deriv
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul (R z) hd, key]
  ring

/-- `∂_θ² (R z · sin 2θ) = R z · (-4 sin 2θ)`. -/
theorem pthIter_two_radial_sin (R : ℝ → ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => R z * Real.sin (2 * θ))
      = fun z θ => R z * (-4 * Real.sin (2 * θ)) := by
  show Work.Spaces.pth (Work.Spaces.pth (fun z θ => R z * Real.sin (2 * θ)))
      = fun z θ => R z * (-4 * Real.sin (2 * θ))
  rw [pth_radial_sin R]
  funext z θ
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ :=
    (((Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).const_mul
      2).differentiableAt
  have key : deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ
      = 2 * (-Real.sin (2 * θ) * (2 * 1)) :=
    (((Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).const_mul 2).deriv
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul (R z) hd, key]
  ring

/-- `∂_z² (R z · sin 2θ) = (∂_z²R) z · sin 2θ`. -/
theorem pzIter_two_radial_sin (R : ℝ → ℝ)
    (hR : ∀ m : ℕ, ContDiffOn ℝ m R (Set.Ioi 0)) {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.pzIter 2 (fun z θ => R z * Real.sin (2 * θ)) z θ
      = deriv (fun z' => deriv R z') z * Real.sin (2 * θ) := by
  have hd : ∀ w ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ R w :=
    fun w hw => (((hR 1).differentiableOn (by decide)).differentiableAt
      (isOpen_Ioi.mem_nhds hw))
  have hd' : ∀ w ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (deriv R) w :=
    fun w hw => (((contDiffOn_deriv_of_smooth R hR 1).differentiableOn (by decide)).differentiableAt
      (isOpen_Ioi.mem_nhds hw))
  have heq : (fun z' => deriv (fun z'' => R z'' * Real.sin (2 * θ)) z')
      =ᶠ[𝓝 z] (fun z' => deriv R z' * Real.sin (2 * θ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact deriv_mul_const (hd w hw) (Real.sin (2 * θ))
  show deriv (fun z' => deriv (fun z'' => R z'' * Real.sin (2 * θ)) z') z
      = deriv (fun z' => deriv R z') z * Real.sin (2 * θ)
  rw [heq.deriv_eq]
  exact deriv_mul_const (hd' z hz) (Real.sin (2 * θ))

/-! ## 3. `HkMem` is closed under addition on the open quadrant -/

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data. -/
theorem HkMem_add_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hfg : SmoothOpen (fun z θ => f z θ + g z θ) := smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hfg.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have htarget : IntegrableOn (fun z : ℝ => 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) + 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)) Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hf hg z hz θ hθ

/-! ## 4. The analytic facts about `F_*`, `L₁₂`, `Gsing` and `Ḡ` from `EllHyp` -/

/-- **The smoothness and the two ODE relations of the singular term.** -/
theorem gsing_facts_fts (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : EllHyp α k F Ψ) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        = (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z) := by
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarSmoothOfSol α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_of_hasDerivAt_of_smooth hL12 (fun m =>
      ((contDiffOn_const.mul (hFsm m)).div contDiffOn_id (fun z hz => ne_of_gt hz)).neg)
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by decide)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α F hFsm hFint hα hα1
  obtain ⟨hGsm, hode⟩ :=
    Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α F hα hFsm hFint hL12
  have hrel : ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z :=
    Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ
  have hGbarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have hαm : ContDiffOn ℝ m (fun _ : ℝ => α) (Set.Ioi 0) := contDiffOn_const
    have hzid : ContDiffOn ℝ m (fun z : ℝ => z) (Set.Ioi 0) := contDiffOn_id
    have hdm : ContDiffOn ℝ m (fun z : ℝ => deriv (Work.Elliptic.Gsing α F) z) (Set.Ioi 0) :=
      contDiffOn_deriv_of_smooth (Work.Elliptic.Gsing α F) hGsm m
    have hnum : ContDiffOn ℝ m
        (fun z : ℝ => -(α * z * deriv (Work.Elliptic.Gsing α F) z)) (Set.Ioi 0) :=
      ((hαm.mul hzid).mul hdm).neg
    have h5 : ContDiffOn ℝ m (fun _ : ℝ => (5 : ℝ)) (Set.Ioi 0) := contDiffOn_const
    have h1 : ContDiffOn ℝ m
        (fun z : ℝ => -(α * z * deriv (Work.Elliptic.Gsing α F) z) / 5) (Set.Ioi 0) :=
      hnum.div h5 (fun z _ => by norm_num)
    exact h1.congr (fun z hz => by rw [hrel z hz]; ring)
  refine ⟨hGsm, hGbarsm, hL12sm, hrel, ?_⟩
  intro z hz
  have h1 := hode z hz
  have h2 := hrel z hz
  have h3 : α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = -5 * (5 + α) * Work.Elliptic.Gbar α F z := by
    calc α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (5 + α) * (α * z * deriv (Work.Elliptic.Gsing α F) z) := by ring
      _ = (5 + α) * (-5 * Work.Elliptic.Gbar α F z) := by rw [h2]
      _ = -5 * (5 + α) * Work.Elliptic.Gbar α F z := by ring
  linarith

/-! ## 5. The angular moment of the straightened solution, and the orthogonality identity -/

/-- The straightened solution `V = Ψ + Gsing α F · sin 2θ`. -/
def Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- **The angular moment of the straightened solution.** -/
theorem Fstar_Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : -1 < z) :
    Work.Elliptic.Fstar (Vfts α F Ψ) z
      = Work.Elliptic.Fstar Ψ z + Work.Elliptic.Gsing α F z * (4 / 15) := by
  have hslice : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ := by
    have h : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := hsm.continuousOn
    refine h.comp (continuousOn_const.prodMk continuousOn_id) ?_
    intro θ hθ
    obtain ⟨h0, h1⟩ := mem_Iθ_iff.mp hθ
    show (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)
    exact ⟨hz, by linarith, by linarith [Real.pi_pos]⟩
  have hf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (hslice.mul (by unfold Work.Elliptic.sinCos2; fun_prop)).integrableOn_compact isCompact_Icc
  have hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2; fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hsplit : (fun θ : ℝ => (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ
          + Work.Elliptic.Gsing α F z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    funext θ; ring
  simp only [Work.Elliptic.Fstar, Vfts]
  rw [hsplit, MeasureTheory.integral_add hf (hg.const_mul _),
    MeasureTheory.integral_const_mul, Work.Elliptic.integral_sin_two_mul_sinCos2]
  try ring

/-- **The orthogonality condition identifies `L₁₂`.** -/
theorem L12_eq_of_orth (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hα : 0 < α) (hOrth : Work.Elliptic.OrthCond (Vfts α F Ψ)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.L12 F z
        = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z := by
  intro z hz
  have hz0 : 0 < z := hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have h0 : Work.Elliptic.Gsing α F z = -(15 / 4) * Work.Elliptic.Fstar Ψ z := by
    have h := hOrth z
    rw [Fstar_Vfts α F Ψ hsm hz1] at h
    linarith
  have hGstar : Work.Elliptic.Gstar α F z = -(1 / (4 * α)) * Work.Elliptic.L12 F z := rfl
  have hGsing : Work.Elliptic.Gsing α F z
      = Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z := rfl
  rw [hGsing, hGstar] at h0
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hL : -(1 / (4 * α)) * Work.Elliptic.L12 F z
      = -(15 / 4) * Work.Elliptic.Fstar Ψ z - Work.Elliptic.Gbar α F z := by linarith
  have hcancel : -(4 * α) * (-(1 / (4 * α)) * Work.Elliptic.L12 F z)
      = Work.Elliptic.L12 F z := by
    field_simp
  have hmul : Work.Elliptic.L12 F z
      = -(4 * α) * (-(15 / 4) * Work.Elliptic.Fstar Ψ z - Work.Elliptic.Gbar α F z) := by
    rw [← hcancel, hL]
  rw [hmul]; ring


/-! ## 6. The pointwise straightening identities on the open quadrant -/

/-- On the open quadrant, `∂_θ² V = ∂_θ² Ξ - 4 Ḡ sin 2θ`. -/
theorem pthIter_two_Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hGbarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0))
    (hΞsm : SmoothOpen (Work.Elliptic.EllResid α F Ψ)) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter 2 (Vfts α F Ψ) z θ
        = Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
          + (-4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
  intro z θ hz h1 h2
  have hcongr : ∀ z θ, Vfts α F Ψ z θ
      = Work.Elliptic.EllResid α F Ψ z θ + Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
    intro z θ
    simp only [Vfts, Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
    ring
  have hsplit : Work.Spaces.pthIter 2 (fun z θ => Work.Elliptic.EllResid α F Ψ z θ
        + Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
        + Work.Spaces.pthIter 2 (fun z θ => Work.Elliptic.Gbar α F z
            * Real.sin (2 * θ)) z θ :=
    pthIter_add_on_Q0 hΞsm
      (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm) 2 z θ hz h1 h2
  rw [pthIter_congr_pt hcongr 2, hsplit, pthIter_two_radial_sin (Work.Elliptic.Gbar α F)]
  ring

/-- On the open quadrant, `∂_z² V = ∂_z² Ψ + Gsing'' · sin 2θ`. -/
theorem pzIter_two_Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hGsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0))
    (hΨsm : SmoothOpen Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pzIter 2 (Vfts α F Ψ) z θ
        = Work.Spaces.pzIter 2 Ψ z θ
          + deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z * Real.sin (2 * θ) := by
  intro z θ hz h1 h2
  have hV : Vfts α F Ψ = fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ) :=
    rfl
  have hsplit : Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z
        * Real.sin (2 * θ)) z θ
      = Work.Spaces.pzIter 2 Ψ z θ
        + Work.Spaces.pzIter 2 (fun z θ => Work.Elliptic.Gsing α F z
            * Real.sin (2 * θ)) z θ :=
    pzIter_add_on_Q0 hΨsm
      (smoothOpen_radial_sin (R := Work.Elliptic.Gsing α F) hGsm) 2 z θ hz h1 h2
  rw [hV, hsplit, pzIter_two_radial_sin (Work.Elliptic.Gsing α F) hGsm hz]

/-- **The ODE of the singular term in the form needed for `z² ∂_zz`.** -/
theorem zsq_G2_sin_ode (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hode2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        = (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z) :
    ∀ z θ, 0 < z →
      α ^ 2 * ((z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
          * Real.sin (2 * θ))
        = (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
          + 5 * (5 + α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  intro z θ hz
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have h := hode2 z hz'
  calc α ^ 2 * ((z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
        * Real.sin (2 * θ))
      = (α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
          * Real.sin (2 * θ) := by ring
    _ = ((15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z)
          * Real.sin (2 * θ) := by rw [h]
    _ = (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
          + 5 * (5 + α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by ring

/-- **Honesty of `z² Gsing'' · sin 2θ`** from the ODE form and the two layer certificates. -/
theorem HkMem_zsq_G2_sin (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hGbarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0))
    (hode2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        = (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z)
    (hmemFstar : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
    (hmemGbar : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :
    Work.Spaces.HkMem α k (fun z θ => (z ^ 2 * deriv (fun z' =>
      deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)) := by
  have hOdemem : Work.Spaces.HkMem α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
      * Real.sin (2 * θ)) + 5 * (5 + α) * (Work.Elliptic.Gbar α F z
        * Real.sin (2 * θ))) :=
    HkMem_add_open α k
      (smoothOpen_const_mul (15 / 4)
        (smoothOpen_radial_sin (R := Work.Elliptic.Fstar F) hFsm))
      (smoothOpen_const_mul (5 * (5 + α))
        (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm))
      (Work.FTS.LocData.HkMem_const_mul α k (15 / 4) hmemFstar)
      (Work.FTS.LocData.HkMem_const_mul α k (5 * (5 + α)) hmemGbar)
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
    (Work.FTS.LocData.HkMem_const_mul α k (1 / α ^ 2) hOdemem) ?_
  intro z hz θ hθ
  have hz0 : 0 < z := hz
  have h := zsq_G2_sin_ode α F hα hode2 z θ hz0
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hα)
  rw [← h, one_div, inv_mul_cancel_left₀ hα2]

/-- **Honesty of `∂_θ² Ξ`** for the residual of Theorem `RemovingL12`. -/
theorem HkMem_pthIter2_EllResid_fts (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hmemΨ : Work.Spaces.HkMem α k Ψ)
    (hmemDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ))
    (hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0))
    (hL12id : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.L12 F z
        = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z)
    (hGbarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0))
    (hmemGbar : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) := by
  have hΨsm : SmoothOpen Ψ := smoothOpen_of_smoothNbhd hsm
  have hFstarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar Ψ) (Set.Ioi 0) :=
    fun m => (Work.FTS.EllipticEst.Fstar_contDiffOn Ψ hsm m).mono
      (Set.Ioi_subset_Ioi (by norm_num))
  have hGstarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    have hc : ContDiffOn ℝ m (fun _ : ℝ => -(1 / (4 * α))) (Set.Ioi 0) := contDiffOn_const
    refine (hc.mul (hL12sm m)).congr (fun z _ => ?_)
    simp only [Work.Elliptic.Gstar]
  have hmem15 : Work.Spaces.HkMem α k
      (fun z θ => 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k 15
      (Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hΨsm hmemΨ)
  have hP15sm : SmoothOpen (fun z θ => 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    smoothOpen_const_mul 15 (smoothOpen_radial_sin (R := Work.Elliptic.Fstar Ψ) hFstarsm)
  have hP4sm : SmoothOpen (fun z θ => 4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    smoothOpen_const_mul 4 (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm)
  have hmem4 : Work.Spaces.HkMem α k
      (fun z θ => 4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k 4 hmemGbar
  have hsum_mem : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
      + 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    HkMem_add_open α k (smoothOpen_pthIter hΨsm 2) hP15sm hmemDth2 hmem15
  have hsum_mem' : Work.Spaces.HkMem α k (fun z θ => (Work.Spaces.pthIter 2 Ψ z θ
      + 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)))
        + 4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    HkMem_add_open α k (smoothOpen_add (smoothOpen_pthIter hΨsm 2) hP15sm) hP4sm
      hsum_mem hmem4
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hsum_mem' ?_
  intro z hz θ hθ
  have hcongr : ∀ z θ, Work.Elliptic.EllResid α F Ψ z θ
      = Ψ z θ + Work.Elliptic.Gstar α F z * Real.sin (2 * θ) := by
    intro z θ; simp only [Work.Elliptic.EllResid, Work.Elliptic.Gstar]; ring
  have hsplit : Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gstar α F z
        * Real.sin (2 * θ)) z θ
      = Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pthIter 2 (fun z θ =>
          Work.Elliptic.Gstar α F z * Real.sin (2 * θ)) z θ :=
    pthIter_add_on_Q0 hΨsm
      (smoothOpen_radial_sin (R := Work.Elliptic.Gstar α F) hGstarsm) 2 z θ hz hθ.1 hθ.2
  have hG : Work.Elliptic.Gstar α F z * (-4 * Real.sin (2 * θ))
      = 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + 4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
    have h4 : -4 * Work.Elliptic.Gstar α F z
        = 15 * Work.Elliptic.Fstar Ψ z + 4 * Work.Elliptic.Gbar α F z := by
      have h := hL12id z hz
      simp only [Work.Elliptic.Gstar]
      rw [h]
      field_simp
    rw [show Work.Elliptic.Gstar α F z * (-4 * Real.sin (2 * θ))
        = (-4 * Work.Elliptic.Gstar α F z) * Real.sin (2 * θ) from by ring, h4]
    ring
  have hval : Work.Spaces.pthIter 2 (fun z θ => Work.Elliptic.Gstar α F z
        * Real.sin (2 * θ)) z θ
      = Work.Elliptic.Gstar α F z * (-4 * Real.sin (2 * θ)) :=
    congrFun (congrFun (pthIter_two_radial_sin (Work.Elliptic.Gstar α F)) z) θ
  rw [pthIter_congr_pt hcongr 2, hsplit, hval, hG]
  ring

/-! ## 7. The straightening transfers -/

theorem straight_transfers (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + Work.Spaces.HkNorm α k F) ∧
      Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α k F) := by
  obtain ⟨Cf, hCf_pos, hFstar_bd⟩ := Work.FTS.EllipticEst.Cert.FstarSin_layer k
  obtain ⟨Cg, hCg_pos, hGbar_bd⟩ := Work.FTS.EllipticEst.Cert.GbarSin_layer k
  set Cval : ℝ := Real.sqrt 2 * (1 + 4 * Cg) + Real.sqrt 2 * (1 + Real.sqrt 2 *
      ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) with hCval
  have hCg_nn : (0 : ℝ) ≤ Cg := le_of_lt hCg_pos
  have hCval_pos : 0 < Cval := by
    rw [hCval]
    have h1 : (0 : ℝ) < Real.sqrt 2 * (1 + 4 * Cg) := by positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 * (1 + Real.sqrt 2 *
        ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) := by positivity
    linarith
  have hC1 : Real.sqrt 2 ≤ Cval := by
    rw [hCval]
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 * (1 + Real.sqrt 2 *
        ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) := by positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt 2 * (4 * Cg) := by positivity
    nlinarith [Real.sqrt_nonneg 2]
  have hC2 : Real.sqrt 2 * 4 * Cg ≤ Cval := by
    rw [hCval]
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 * (1 + Real.sqrt 2 *
        ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) := by positivity
    nlinarith [Real.sqrt_nonneg 2]
  have hC3 : 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg) ≤ Cval := by
    rw [hCval]
    have h1 : (0 : ℝ) ≤ Real.sqrt 2 * (1 + 4 * Cg) := by positivity
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : (0 : ℝ) ≤ (15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg := by positivity
    nlinarith [Real.sqrt_nonneg 2]
  refine ⟨Cval, hCval_pos, ?_⟩
  intro α F Ψ hα hα4 hHyp hOrth
  have hα1 : α ≤ 1 := by linarith
  -- the analytic facts of the singular term
  obtain ⟨hGsm, hGbarsm, hL12sm, hrel, hode2⟩ := gsing_facts_fts α k F Ψ hα hα1 hHyp
  -- the two layer certificates
  obtain ⟨hmemFstar, hFstar_norm⟩ := hFstar_bd α F Ψ hα hα4 hHyp
  obtain ⟨hmemGbar, hGbar_norm⟩ := hGbar_bd α F Ψ hα hα4 hHyp
  -- the orthogonality identity
  have hL12id : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.L12 F z
        = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z :=
    L12_eq_of_orth α F Ψ hHyp.smoothNbhd hα hOrth
  -- smoothness of the source and of `Ψ`
  have hFsmF : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarSmoothOfSol α F Ψ hHyp.smoothNbhd hHyp.sol
  have hΨsm : SmoothOpen Ψ := smoothOpen_of_smoothNbhd hHyp.smoothNbhd
  have hFstarsmΨ : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar Ψ) (Set.Ioi 0) :=
    fun m => (Work.FTS.EllipticEst.Fstar_contDiffOn Ψ hHyp.smoothNbhd m).mono
      (Set.Ioi_subset_Ioi (by norm_num))
  have hGstarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    have hc : ContDiffOn ℝ m (fun _ : ℝ => -(1 / (4 * α))) (Set.Ioi 0) := contDiffOn_const
    refine (hc.mul (hL12sm m)).congr (fun z _ => ?_)
    simp only [Work.Elliptic.Gstar]
  have hΞsm : SmoothOpen (Work.Elliptic.EllResid α F Ψ) := by
    refine smoothOpen_congr (smoothOpen_add hΨsm
      (smoothOpen_radial_sin (R := Work.Elliptic.Gstar α F) hGstarsm)) ?_
    intro z θ _ _ _
    simp only [Work.Elliptic.EllResid, Work.Elliptic.Gstar]
    ring
  have hVsm : SmoothOpen (Vfts α F Ψ) :=
    smoothOpen_add hΨsm (smoothOpen_radial_sin (R := Work.Elliptic.Gsing α F) hGsm)
  -- ### FIRST CONJUNCT
  have hYsm : SmoothOpen (fun z θ => -4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    smoothOpen_const_mul (-4) (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm)
  have hYmem : Work.Spaces.HkMem α k
      (fun z θ => -4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-4) hmemGbar
  have hXsm : SmoothOpen (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) :=
    smoothOpen_pthIter hΞsm 2
  have hXmem : Work.Spaces.HkMem α k
      (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) :=
    HkMem_pthIter2_EllResid_fts α k F Ψ hα hα1 hHyp.smoothNbhd hHyp.memPsi hHyp.memDth2
      hL12sm hL12id hGbarsm hmemGbar
  have hptV := pthIter_two_Vfts α F Ψ hGbarsm hΞsm
  have hcore1 : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vfts α F Ψ))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + Work.Spaces.HkNorm α k (fun z θ => -4 * (Work.Elliptic.Gbar α F z
              * Real.sin (2 * θ)))) := by
    have hcongr := Work.FTS.EllipticEst.HkSq_congr_open (α := α) (k := k) hptV
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hcongr]
    exact Work.FTS.EllipticEst.HkNorm_add_le α k
      (contDiffOn_uncurry_of_smoothOpen hXsm)
      (contDiffOn_uncurry_of_smoothOpen hYsm) hXmem hYmem
  have hYnorm_eq : Work.Spaces.HkNorm α k
      (fun z θ => -4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
      = 4 * Work.Spaces.HkNorm α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
    have hc := Work.FTS.EllipticEst.HkNorm_const_mul α k (-4)
      (f := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      (contDiffOn_uncurry_of_smoothOpen
        (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm))
    simpa using hc
  have hYbound : Work.Spaces.HkNorm α k (fun z θ => -4 * (Work.Elliptic.Gbar α F z
      * Real.sin (2 * θ))) ≤ 4 * Cg * Work.Spaces.HkNorm α k F := by
    rw [hYnorm_eq]
    nlinarith [hGbar_norm, Work.Spaces.HkNorm_nonneg α k F]
  have hfirst : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vfts α F Ψ))
      ≤ Cval * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + Work.Spaces.HkNorm α k F) := by
    have hA : (0 : ℝ) ≤ Work.Spaces.HkNorm α k
        (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) :=
      Work.Spaces.HkNorm_nonneg α k _
    have hB : (0 : ℝ) ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
    have hr2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vfts α F Ψ))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + Work.Spaces.HkNorm α k (fun z θ => -4 * (Work.Elliptic.Gbar α F z
                * Real.sin (2 * θ)))) := hcore1
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + 4 * Cg * Work.Spaces.HkNorm α k F) := by
          nlinarith [hr2, hYbound]
      _ ≤ Cval * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + Work.Spaces.HkNorm α k F) := by
          nlinarith [hC1, hC2, hA, hB, hr2, hCg_nn]
  refine ⟨hfirst, ?_⟩
  -- ### SECOND CONJUNCT
  have hG2sm : ∀ m : ℕ, ContDiffOn ℝ m
      (fun z => deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z) (Set.Ioi 0) :=
    contDiffOn_deriv_of_smooth _ (contDiffOn_deriv_of_smooth _ hGsm)
  have hptW := pzIter_two_Vfts α F Ψ hGsm hΨsm
  have hPt1sm : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_fst.pow 2).mul (hΨsm.pzIter 2)
    exact h1
  have hPt1mem : Work.Spaces.HkMem α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := hHyp.memZ2
  have hPt2sm : SmoothOpen (fun z θ => (z ^ 2 * deriv (fun z' =>
      deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)) :=
    smoothOpen_radial_sin
      (R := fun z => z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
      (fun m => (contDiffOn_id.pow 2).mul (hG2sm m))
  have hPt2mem : Work.Spaces.HkMem α k (fun z θ => (z ^ 2 * deriv (fun z' =>
      deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)) :=
    HkMem_zsq_G2_sin α k F hα hFsmF hGbarsm hode2 hmemFstar hmemGbar
  have hVzsm : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vfts α F Ψ) z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 (Vfts α F Ψ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_fst.pow 2).mul (hVsm.pzIter 2)
    exact h1
  have hcore2 : Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Vfts α F Ψ) z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α k (fun z θ => (z ^ 2 * deriv (fun z' =>
              deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ))) := by
    have hptW' : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        z ^ 2 * Work.Spaces.pzIter 2 (Vfts α F Ψ) z θ
          = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
            + (z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
              * Real.sin (2 * θ) := by
      intro z θ hz h1 h2
      rw [hptW z θ hz h1 h2]
      ring
    have hcongr := Work.FTS.EllipticEst.HkSq_congr_open (α := α) (k := k)
      (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vfts α F Ψ) z θ)
      (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
          * Real.sin (2 * θ)) hptW'
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hcongr]
    exact Work.FTS.EllipticEst.HkNorm_add_le α k
      (contDiffOn_uncurry_of_smoothOpen hPt1sm)
      (contDiffOn_uncurry_of_smoothOpen hPt2sm) hPt1mem hPt2mem
  have hscale : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
          (Vfts α F Ψ) z θ))
      = α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Vfts α F Ψ) z θ) := by
    have hc := Work.FTS.EllipticEst.HkNorm_const_mul α k (α ^ 2)
      (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vfts α F Ψ) z θ)
      (contDiffOn_uncurry_of_smoothOpen hVzsm)
    rw [hc, abs_of_nonneg (sq_nonneg α)]
  have hPt2scale : α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => (z ^ 2 * deriv (fun z' =>
        deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ))
      = Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * ((z ^ 2 * deriv (fun z' =>
          deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ))) := by
    have hc := Work.FTS.EllipticEst.HkNorm_const_mul α k (α ^ 2)
      (f := fun z θ => (z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
        * Real.sin (2 * θ))
      (contDiffOn_uncurry_of_smoothOpen hPt2sm)
    rw [hc, abs_of_nonneg (sq_nonneg α)]
  have hComb : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * ((z ^ 2 * deriv (fun z' =>
        deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)))
      = Work.Spaces.HkNorm α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
          * Real.sin (2 * θ)) + 5 * (5 + α) * (Work.Elliptic.Gbar α F z
            * Real.sin (2 * θ))) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    congr 1
    exact Work.FTS.EllipticEst.HkSq_congr_open (α := α) (k := k)
      (fun z θ hz _ _ => zsq_G2_sin_ode α F hα hode2 z θ hz)
  have hComb_bound : Work.Spaces.HkNorm α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
        * Real.sin (2 * θ)) + 5 * (5 + α) * (Work.Elliptic.Gbar α F z
          * Real.sin (2 * θ)))
      ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + α) * Cg) * Work.Spaces.HkNorm α k F := by
    have h1 := Work.FTS.EllipticEst.HkNorm_add_le α k
      (contDiffOn_uncurry_of_smoothOpen (smoothOpen_const_mul (15 / 4)
        (smoothOpen_radial_sin (R := Work.Elliptic.Fstar F) hFsmF)))
      (contDiffOn_uncurry_of_smoothOpen (smoothOpen_const_mul (5 * (5 + α))
        (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm)))
      (Work.FTS.LocData.HkMem_const_mul α k (15 / 4) hmemFstar)
      (Work.FTS.LocData.HkMem_const_mul α k (5 * (5 + α)) hmemGbar)
    have h15 : Work.Spaces.HkNorm α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
        * Real.sin (2 * θ))) = (15 / 4) * Work.Spaces.HkNorm α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) := by
      have hc := Work.FTS.EllipticEst.HkNorm_const_mul α k (15 / 4)
        (f := fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        (contDiffOn_uncurry_of_smoothOpen
          (smoothOpen_radial_sin (R := Work.Elliptic.Fstar F) hFsmF))
      rw [hc, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4)]
    have h5 : Work.Spaces.HkNorm α k (fun z θ => 5 * (5 + α) * (Work.Elliptic.Gbar α F z
        * Real.sin (2 * θ))) = 5 * (5 + α) * Work.Spaces.HkNorm α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
      have hc := Work.FTS.EllipticEst.HkNorm_const_mul α k (5 * (5 + α))
        (f := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        (contDiffOn_uncurry_of_smoothOpen
          (smoothOpen_radial_sin (R := Work.Elliptic.Gbar α F) hGbarsm))
      rw [hc, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * (5 + α))]
    rw [h15, h5] at h1
    have hr2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hFnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
    have hcoef : (0 : ℝ) ≤ (15 / 4) * Cf + 5 * (5 + α) * Cg := by positivity
    calc Work.Spaces.HkNorm α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
          * Real.sin (2 * θ)) + 5 * (5 + α) * (Work.Elliptic.Gbar α F z
            * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * ((15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
            + 5 * (5 + α) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := h1
      _ ≤ Real.sqrt 2 * ((15 / 4) * (Cf * Work.Spaces.HkNorm α k F)
            + 5 * (5 + α) * (Cg * Work.Spaces.HkNorm α k F)) := by
          have ha : (15 / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
              ≤ (15 / 4) * (Cf * Work.Spaces.HkNorm α k F) :=
            mul_le_mul_of_nonneg_left hFstar_norm (by norm_num)
          have hb : 5 * (5 + α) * Work.Spaces.HkNorm α k
                (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
              ≤ 5 * (5 + α) * (Cg * Work.Spaces.HkNorm α k F) :=
            mul_le_mul_of_nonneg_left hGbar_norm (by positivity)
          exact mul_le_mul_of_nonneg_left (add_le_add ha hb) hr2
      _ ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + α) * Cg) * Work.Spaces.HkNorm α k F := by
          have heq : (15 / 4) * (Cf * Work.Spaces.HkNorm α k F)
                + 5 * (5 + α) * (Cg * Work.Spaces.HkNorm α k F)
              = ((15 / 4) * Cf + 5 * (5 + α) * Cg) * Work.Spaces.HkNorm α k F := by ring
          rw [heq]
          exact le_of_eq (mul_assoc _ _ _).symm
  have hsecond : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
          (Vfts α F Ψ) z θ))
      ≤ Cval * (α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α k F) := by
    have hA : (0 : ℝ) ≤ Work.Spaces.HkNorm α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := Work.Spaces.HkNorm_nonneg α k _
    have hB : (0 : ℝ) ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
    have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have hr2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hDmax : (0 : ℝ) ≤ (15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg := by positivity
    have hDle : (15 / 4) * Cf + 5 * (5 + α) * Cg
        ≤ (15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg := by
      have hCf_nn : (0 : ℝ) ≤ Cf := le_of_lt hCf_pos
      nlinarith [hα, hα4]
    have hbound : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * ((z ^ 2 * deriv (fun z' =>
          deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
            * Work.Spaces.HkNorm α k F := by
      rw [hComb]
      calc Work.Spaces.HkNorm α k (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z
            * Real.sin (2 * θ)) + 5 * (5 + α) * (Work.Elliptic.Gbar α F z
              * Real.sin (2 * θ)))
          ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + α) * Cg)
              * Work.Spaces.HkNorm α k F := hComb_bound
        _ ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
              * Work.Spaces.HkNorm α k F := by
            have h1 : Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + α) * Cg)
                ≤ Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg) :=
              mul_le_mul_of_nonneg_left hDle hr2
            exact mul_le_mul_of_nonneg_right h1 hB
    calc Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
            (Vfts α F Ψ) z θ))
        = α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Vfts α F Ψ) z θ) := hscale
      _ ≤ α ^ 2 * (Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α k (fun z θ => (z ^ 2 * deriv (fun z' =>
                deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)))) :=
          mul_le_mul_of_nonneg_left hcore2 hα2
      _ = Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => (z ^ 2 * deriv (fun z' =>
                deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ))) := by ring
      _ = Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * ((z ^ 2 * deriv (fun z' =>
                deriv (Work.Elliptic.Gsing α F) z') z) * Real.sin (2 * θ)))) := by
          rw [hPt2scale]
      _ ≤ Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                * Work.Spaces.HkNorm α k F) := by
          nlinarith [hr2, hbound]
      _ ≤ Cval * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α k F) := by
          have h1 : Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
              ≤ Cval * (α ^ 2 * Work.Spaces.HkNorm α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
            mul_le_mul_of_nonneg_right hC1 (mul_nonneg hα2 hA)
          have hs : Real.sqrt 2 * (Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                * Work.Spaces.HkNorm α k F)
              = (2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) * Work.Spaces.HkNorm α k F := by
            calc Real.sqrt 2 * (Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                  * Work.Spaces.HkNorm α k F)
                = (Real.sqrt 2 * Real.sqrt 2)
                    * (((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg) * Work.Spaces.HkNorm α k F) := by
                  ring
              _ = 2 * (((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg) * Work.Spaces.HkNorm α k F) := by
                  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
              _ = (2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)) * Work.Spaces.HkNorm α k F := by
                  ring
          have h2 : Real.sqrt 2 * (Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                * Work.Spaces.HkNorm α k F) ≤ Cval * Work.Spaces.HkNorm α k F := by
            rw [hs]
            exact mul_le_mul_of_nonneg_right hC3 hB
          have hgoal : Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                * Work.Spaces.HkNorm α k F)
              = Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
                + Real.sqrt 2 * (Real.sqrt 2 * ((15 / 4) * Cf + 5 * (5 + 1 / 4) * Cg)
                  * Work.Spaces.HkNorm α k F) := by ring
          have hgoal2 : Cval * (α ^ 2 * Work.Spaces.HkNorm α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + Work.Spaces.HkNorm α k F)
              = Cval * (α ^ 2 * Work.Spaces.HkNorm α k
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
                + Cval * Work.Spaces.HkNorm α k F := by ring
          rw [hgoal, hgoal2]
          exact add_le_add h1 h2
  exact hsecond

end Work.FTS.EllipticEst.RPFresh
