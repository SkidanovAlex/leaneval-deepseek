/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.th2_holder` — the two-point θ-Hölder modulus of `∂_θ²(E g)`

This is the `HolMod` producer of the box-`C²` chapter (`ProducerH/H2/Data.lean`).

## Route

Write `S = E g` and `G = Work.Elliptic.Lzero (E g) z` on a fixed slice `z`.  The slice solves

  `S'' = tan θ · S' + (cos θ)⁻² S − 6 S − G`   on `(0,π/2)`,

and the key object is the combination

  `W := S'' + 4S + G = tan θ · S' + ((cos θ)⁻² − 2) · S`,

which has the closed form (`BoxAux.th2Ident`)  `W(θ) = (cos θ)⁻³ ∫_θ^{π/2} sin t cos²t G(t) dt`.

On the open quadrant `G = g + α²D_z²S + 5α D_zS` (the elliptic law plus
`z²∂_z² = D_z² − D_z`), so `G` inherits the class rate

  `|G| ≤ K·Xn6·min(θ,π/2−θ)^β₀`,   `β₀ = (γ−1)/2 = α/20`     (`BoxAux.lzero_rate`),

and the sibling `wRateModulusUnif` converts the `π/2`-rate of `G` — through the integral formula
above — into the two-point modulus `|W(θ) − W(θ')| ≤ C·Xn6·|θ−θ'|^β₀`.  The two remaining terms of

  `S''(θ) − S''(θ') = (W(θ) − W(θ')) − 4(S(θ) − S(θ')) − (G(θ) − G(θ'))`

are Lipschitz in `θ` with constant `C·Xn6`: `S` by the sibling `sliceDzMod` (`a = 0`), and `G`
once more through `G = g + α²D_z²S + 5α D_zS`, with the source part `g` at its class rate
`α/20` (`BoxAux.classCThetaHolder`) and the radial parts `D_zS`, `D_z²S` by `sliceDzMod`
(`a = 1, 2`).  Since `θ, θ' ∈ (0,π/2)` gives `|θ − θ'| ≤ π/2`, a Lipschitz bound is a
Hölder-`β₀` bound.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Eg_modulus
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.FTS_EllLimOK.ProducerH.H2.sliceDzMod
import Submission.Work.FTS_EllLimOK.ProducerH.H2.wRateModulusUnif

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The angular slice ODE -/

/-- **The angular slice of `E g` at a fixed radius solves the `Lzero`-equation**
(definitional unfolding of `Lzero`). -/
theorem th2Holder_sliceOde {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv (deriv (fun θ' => (E g) z θ')) θ
        = Real.tan θ * deriv (fun θ' => (E g) z θ') θ
          + ((Real.cos θ) ^ 2)⁻¹ * (E g) z θ - 6 * (E g) z θ
          - Work.Elliptic.Lzero (E g) z θ := by
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  have h2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hSsm hz).of_le (by norm_num)
  have hLfun : Work.Elliptic.Lzero (E g) z
      = fun θ => -deriv (deriv (fun θ' => (E g) z θ')) θ
          + deriv (fun θ' => Real.tan θ' * (E g) z θ') θ - 6 * (E g) z θ := by
    funext θ'
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  intro θ hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hSd : HasDerivAt (fun θ'' => (E g) z θ'')
      (deriv (fun θ'' => (E g) z θ'') θ) θ :=
    (((h2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num))).hasDerivAt
  have htan : HasDerivAt Real.tan (((Real.cos θ) ^ 2)⁻¹) θ := by
    simpa only [one_div] using Real.hasDerivAt_tan (ne_of_gt hcos)
  have hprod : deriv (fun θ'' => Real.tan θ'' * (E g) z θ'') θ
      = ((Real.cos θ) ^ 2)⁻¹ * (E g) z θ
        + Real.tan θ * deriv (fun θ'' => (E g) z θ'') θ :=
    (htan.mul hSd).deriv
  have hL := congrFun hLfun θ
  rw [hL, hprod]
  ring

/-! ## Continuity of the source `G = Lzero (E g) z` on the open interval -/

/-- `Lzero (E g) z` is continuous on `(0,π/2)` (it is `−S'' + sec²θ·S + tanθ·S' − 6S` there). -/
theorem th2Holder_continuousOn_lzero {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun t => Work.Elliptic.Lzero (E g) z t) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  have hode := th2Holder_sliceOde hα hα4 hE hg hz
  have hEq : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.Lzero (E g) z t
        = (Real.tan t * Work.Spaces.pth (E g) z t + ((Real.cos t) ^ 2)⁻¹ * (E g) z t
            - 6 * (E g) z t) - Work.Spaces.pthIter 2 (E g) z t := by
    intro t ht
    have h := hode t ht
    have e1 : deriv (fun θ' => (E g) z θ') t = Work.Spaces.pth (E g) z t := rfl
    have e2 : deriv (deriv (fun θ' => (E g) z θ')) t
        = Work.Spaces.pthIter 2 (E g) z t := rfl
    rw [e1, e2] at h
    linarith
  refine ContinuousOn.congr ?_ (fun t ht => hEq t ht)
  have htan : ContinuousOn Real.tan (Set.Ioo (0 : ℝ) (π / 2)) := by
    have h1 : ContinuousOn (fun t : ℝ => Real.sin t / Real.cos t) (Set.Ioo (0 : ℝ) (π / 2)) :=
      ContinuousOn.div Real.continuous_sin.continuousOn Real.continuous_cos.continuousOn
        (fun t ht => ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩))
    exact h1.congr (fun t _ => (Real.tan_eq_sin_div_cos t))
  have hcont_pth : ContinuousOn (fun t : ℝ => Work.Spaces.pth (E g) z t)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ (Work.FTS.EllipticEst.SmoothOpen.pth hsm) hz).continuousOn
  have hcont_psi : ContinuousOn (fun t : ℝ => (E g) z t) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hsm hz).continuousOn
  have hcont_pth2 : ContinuousOn (fun t : ℝ => Work.Spaces.pthIter 2 (E g) z t)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ
      (Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth hsm)) hz).continuousOn
  have hcosne : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), Real.cos t ≠ 0 := fun t ht =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  have hinv : ContinuousOn (fun t : ℝ => ((Real.cos t) ^ 2)⁻¹) (Set.Ioo (0 : ℝ) (π / 2)) :=
    ContinuousOn.inv₀ (Real.continuous_cos.continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hcosne t ht))
  exact ContinuousOn.sub
    (ContinuousOn.sub (ContinuousOn.add (htan.mul hcont_pth) (hinv.mul hcont_psi))
      ((continuousOn_const.mul hcont_psi))) hcont_pth2

/-! ## The closed form of `W = S'' + 4S + G` -/

/-- **The integral representation** `W(θ) = (cos θ)⁻³ ∫_θ^{π/2} sin t cos²t G(t) dt`
of `W = ∂_θ²Ψ + 4Ψ + G`, obtained from `BoxAux.th2Ident` by dividing by `cos³θ ≠ 0`. -/
theorem th2Holder_Wrepr {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z)
    {MW MG : ℝ}
    (hGc : ContinuousOn (fun t => Work.Elliptic.Lzero (E g) z t) (Set.Ioo (0 : ℝ) (π / 2)))
    (hGb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Lzero (E g) z t| ≤ MG)
    (hWb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (deriv (fun θ' => (E g) z θ')) θ + 4 * (E g) z θ
        + Work.Elliptic.Lzero (E g) z θ| ≤ MW) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv (deriv (fun θ' => (E g) z θ')) θ + 4 * (E g) z θ + Work.Elliptic.Lzero (E g) z θ
        = ((Real.cos θ) ^ 3)⁻¹
          * ∫ t in θ..(π / 2), Real.sin t * (Real.cos t) ^ 2 * Work.Elliptic.Lzero (E g) z t := by
  intro θ hθ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hS2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hE g hg).2.2.smooth.curry_θ hz).of_le (by norm_num)
  have h := Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident (S := fun θ' => (E g) z θ')
      (G := fun t => Work.Elliptic.Lzero (E g) z t) (MG := MG) (MW := MW)
      hS2 hGc hGb (th2Holder_sliceOde hα hα4 hE hg hz) hWb θ hθ
  have h3 : (Real.cos θ) ^ 3 ≠ 0 := pow_ne_zero 3 hcos
  have hY : ∀ y : ℝ, ((Real.cos θ) ^ 3)⁻¹ * ((Real.cos θ) ^ 3 * y) = y := by
    intro y
    rw [← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  have h' : ((Real.cos θ) ^ 3)⁻¹ * ((Real.cos θ) ^ 3
        * (deriv (deriv (fun θ' => (E g) z θ')) θ + 4 * (E g) z θ
          + Work.Elliptic.Lzero (E g) z θ))
      = ((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(π / 2),
          Real.sin t * (Real.cos t) ^ 2 * Work.Elliptic.Lzero (E g) z t) := by
    rw [h]
  rw [hY] at h'
  exact h'

/-! ## The elliptic identification of the source -/

/-- **The source in terms of the class datum and the radial derivatives**:
on the open quadrant, `Lzero Ψ = g + α²D_z²Ψ + 5α D_zΨ`. -/
theorem th2Holder_lzero_decomp {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.Lzero (E g) z θ
      = g z θ + α ^ 2 * Work.Spaces.DzIter 2 (E g) z θ
        + 5 * α * Work.Spaces.DzIter 1 (E g) z θ := by
  have hsol : Work.Elliptic.bslOp α (E g) z θ = g z θ := (hE g hg).1.1.1 z hz θ hθ.1 hθ.2
  have hL := Work.FTS_EllLimOK.ProducerH.SecondDeriv.Lzero_eq_bslOp_add α (E g) z θ
  have hslice : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      ContDiffOn ℝ 2 (fun z' => (E g) z' θ') (Set.Ioi 0) :=
    fun θ' hθ' => (((hE g hg).1.2.1).curry_z hθ').of_le (by simp [Work.Stability.smoothOrder])
  have hzsq := Work.FTS_EllLimOK.ProducerH.SecondDeriv.zsq_pzIter_two_eq
    (h := E g) hslice hz hθ
  simp only [Work.Spaces.mixed_zero_right] at hzsq
  have hone : Work.Spaces.DzIter 1 (E g) z θ = z * Work.Spaces.pz (E g) z θ := rfl
  rw [hL, hsol, hzsq, hone]
  ring

/-! ## The Lipschitz-to-Hölder conversion on the angular interval -/

/-- For `0 ≤ h ≤ c` and `0 < β ≤ 1`, `h ≤ c^{1-β} h^β`. -/
theorem th2Holder_le_rpow_of_le {β h c : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hh : 0 ≤ h) (hhc : h ≤ c)
    (hc : 0 ≤ c) : h ≤ c ^ (1 - β) * h ^ β := by
  rcases eq_or_lt_of_le hh with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (ne_of_gt hβ0), mul_zero]
  · have h1 : h ^ (1 - β) ≤ c ^ (1 - β) :=
      Real.rpow_le_rpow hh hhc (by linarith)
    have h2 : h = h ^ β * h ^ (1 - β) := by
      rw [← Real.rpow_add hpos, show β + (1 - β) = 1 by ring, Real.rpow_one]
    calc h = h ^ β * h ^ (1 - β) := h2
      _ ≤ h ^ β * c ^ (1 - β) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hh _)
      _ = c ^ (1 - β) * h ^ β := by ring

/-- `|a - 4*b - c| ≤ |a| + 4|b| + |c|`. -/
theorem th2Holder_abs_sub_four_sub_le (a b c : ℝ) : |a - 4 * b - c| ≤ |a| + 4 * |b| + |c| := by
  have h1 : |a - 4 * b - c| ≤ |a - 4 * b| + |c| := by
    have h := abs_add_le (a - 4 * b) (-c)
    rw [abs_neg] at h
    simpa [sub_eq_add_neg] using h
  have h2 : |a - 4 * b| ≤ |a| + 4 * |b| := by
    have h := abs_add_le a (-(4 * b))
    rw [abs_neg] at h
    have h4 : |4 * b| = 4 * |b| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    simpa [sub_eq_add_neg, h4] using h
  linarith

/-! ## The target -/

theorem th2_holder {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ'' => (E g) z θ'')) θ - deriv (deriv (fun θ'' => (E g) z θ'')) θ'|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β := by
  -- the exponent `β₀ = (γ-1)/2 = α/20` of the class rate
  set β : ℝ := (Work.Spaces.gam α - 1) / 2 with hβdef
  have hβpos : 0 < β := by rw [hβdef, Work.Spaces.gam_sub_one]; linarith
  have hβle : β ≤ 1 := by rw [hβdef, Work.Spaces.gam_sub_one]; linarith
  have hβ20 : β = α / 20 := by rw [hβdef, Work.Spaces.gam_sub_one]; ring
  have hπ2pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set Cπ : ℝ := (Real.pi / 2) ^ (1 - β) with hCπdef
  have hCπnn : 0 ≤ Cπ := by rw [hCπdef]; exact Real.rpow_nonneg hπ2pos.le _
  -- the inputs
  obtain ⟨Mp, hMp0, hMp⟩ := Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds (α := α) (Ce := Ce) hα hα4 hE ha₀ hab
  obtain ⟨Klz, hKlz0, hKlz⟩ := Work.FTS_EllLimOK.ProducerH.BoxAux.lzero_rate (α := α) (Ce := Ce) hα hα4 hE ha₀ hab
  obtain ⟨Mth, hMth0, hMth⟩ := Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6 (α := α) (Ce := Ce) hα hα4 hE ha₀ hab
  obtain ⟨Cg, hCg0, hCg⟩ := Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder (α := α) hα hα4
  obtain ⟨Ka0, hKa00, hKa0b⟩ := sliceDzMod (α := α) (Ce := Ce) hα hα4 hE 0 (by norm_num) ha₀ hab
  obtain ⟨Ka1, hKa10, hKa1b⟩ := sliceDzMod (α := α) (Ce := Ce) hα hα4 hE 1 (by norm_num) ha₀ hab
  obtain ⟨Ka2, hKa20, hKa2b⟩ := sliceDzMod (α := α) (Ce := Ce) hα hα4 hE 2 (by norm_num) ha₀ hab
  obtain ⟨CW, hCW0, hCWb⟩ := wRateModulusUnif (β := β) hβpos hβle
  refine ⟨CW * Klz + 4 * Ka0 * Cπ + (Cg + α ^ 2 * (Ka2 * Cπ) + 5 * α * (Ka1 * Cπ)),
    ?_, β, hβpos, ?_⟩
  · have h1 : 0 < CW * Klz := mul_pos hCW0 hKlz0
    have h2 : 0 ≤ 4 * Ka0 * Cπ := mul_nonneg (mul_nonneg (by norm_num) hKa00.le) hCπnn
    have h3 : 0 ≤ α ^ 2 * (Ka2 * Cπ) :=
      mul_nonneg (sq_nonneg α) (mul_nonneg hKa20.le hCπnn)
    have h4 : 0 ≤ 5 * α * (Ka1 * Cπ) :=
      mul_nonneg (mul_nonneg (by linarith) hα.le) (mul_nonneg hKa10.le hCπnn)
    linarith
  intro g hg z hz θ hθ θ' hθ'
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hz0 : 0 < z := lt_of_lt_of_le ha₀ hz.1
  -- `|θ - θ'| ≤ π/2`
  have hδle : |θ - θ'| ≤ Real.pi / 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hθ.1, hθ.2, hθ'.1, hθ'.2], by linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]⟩
  -- the source and the closed form
  have hGc := th2Holder_continuousOn_lzero (α := α) (Ce := Ce) hα hα4 hE hg hz0
  have hGb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Elliptic.Lzero (E g) z t| ≤ Mp * Work.FTS.StrongGlobal.Xn6 α g :=
    fun t ht => (hMp g hg z hz t ht).2.2
  have hWb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (deriv (fun θ' => (E g) z θ')) t + 4 * (E g) z t
        + Work.Elliptic.Lzero (E g) z t| ≤ (Mth + 5 * Mp) * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    have h1 : |deriv (deriv (fun θ' => (E g) z θ')) t|
        ≤ Mth * Work.FTS.StrongGlobal.Xn6 α g := hMth g hg z hz t ht
    have h2 : |(E g) z t| ≤ Mp * Work.FTS.StrongGlobal.Xn6 α g := (hMp g hg z hz t ht).1
    have h3 : |Work.Elliptic.Lzero (E g) z t| ≤ Mp * Work.FTS.StrongGlobal.Xn6 α g := hGb t ht
    have h4 : |deriv (deriv (fun θ' => (E g) z θ')) t + 4 * (E g) z t|
        ≤ Mth * Work.FTS.StrongGlobal.Xn6 α g + 4 * (Mp * Work.FTS.StrongGlobal.Xn6 α g) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      linarith
    refine le_trans (abs_add_le _ _) ?_
    nlinarith [hX0, hMth0, hMp0, h4, h3]
  have hrepr := fun t ht => th2Holder_Wrepr (α := α) (Ce := Ce) hα hα4 hE hg hz0 hGc hGb hWb t ht
  -- the modulus of `W`
  have hWL : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Elliptic.Lzero (E g) z t - 0| ≤ (Klz * Work.FTS.StrongGlobal.Xn6 α g)
        * (Real.pi / 2 - t) ^ β := by
    intro t ht
    have h := hKlz g hg z hz t ht
    have hβr : (min t (Real.pi / 2 - t)) ^ β ≤ (Real.pi / 2 - t) ^ β :=
      Real.rpow_le_rpow (le_of_lt (lt_min ht.1 (by linarith [ht.2]))) (min_le_right _ _) hβpos.le
    rw [sub_zero]
    calc |Work.Elliptic.Lzero (E g) z t|
        ≤ Klz * Work.FTS.StrongGlobal.Xn6 α g * (min t (Real.pi / 2 - t)) ^ β := h
      _ ≤ Klz * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - t) ^ β :=
          mul_le_mul_of_nonneg_left hβr (mul_nonneg hKlz0.le hX0)
      _ = (Klz * Work.FTS.StrongGlobal.Xn6 α g) * (Real.pi / 2 - t) ^ β := by ring
  have hWmod : |deriv (deriv (fun θ'' => (E g) z θ'')) θ + 4 * (E g) z θ
        + Work.Elliptic.Lzero (E g) z θ
      - (deriv (deriv (fun θ'' => (E g) z θ'')) θ' + 4 * (E g) z θ'
        + Work.Elliptic.Lzero (E g) z θ')|
      ≤ CW * (Klz * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| ^ β := by
    rw [hrepr θ hθ, hrepr θ' hθ']
    exact hCWb (mul_nonneg hKlz0.le hX0) hGc hWL θ hθ θ' hθ'
  -- the Lipschitz moduli of `S` and of `G`
  have hSmod : |(E g) z θ - (E g) z θ'|
      ≤ Ka0 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by
    have h1 := hKa0b g hg z hz θ hθ θ' hθ'
    simp only [Work.Spaces.DzIter_zero] at h1
    have hδ : |θ - θ'| ≤ Cπ * |θ - θ'| ^ β := by
      rw [hCπdef]
      exact th2Holder_le_rpow_of_le (β := β) hβpos hβle (abs_nonneg _) hδle hπ2pos.le
    calc |(E g) z θ - (E g) z θ'|
        ≤ Ka0 * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := h1
      _ ≤ Ka0 * Work.FTS.StrongGlobal.Xn6 α g * (Cπ * |θ - θ'| ^ β) :=
          mul_le_mul_of_nonneg_left hδ (mul_nonneg hKa00.le hX0)
      _ = Ka0 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by ring
  have hGmod : |Work.Elliptic.Lzero (E g) z θ - Work.Elliptic.Lzero (E g) z θ'|
      ≤ (Cg + α ^ 2 * (Ka2 * Cπ) + 5 * α * (Ka1 * Cπ)) * Work.FTS.StrongGlobal.Xn6 α g
        * |θ - θ'| ^ β := by
    rewrite [th2Holder_lzero_decomp (α := α) (Ce := Ce) hα hα4 hE hg hz0 hθ,
      th2Holder_lzero_decomp (α := α) (Ce := Ce) hα hα4 hE hg hz0 hθ']
    have h1 : |g z θ - g z θ'| ≤ Cg * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β := by
      have h := hCg g hg z hz0 θ hθ θ' hθ'
      rwa [← hβ20] at h
    have h2 : |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'|
        ≤ Ka2 * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := hKa2b g hg z hz θ hθ θ' hθ'
    have h3 : |Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'|
        ≤ Ka1 * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := hKa1b g hg z hz θ hθ θ' hθ'
    have hδ : |θ - θ'| ≤ Cπ * |θ - θ'| ^ β := by
      rw [hCπdef]
      exact th2Holder_le_rpow_of_le (β := β) hβpos hβle (abs_nonneg _) hδle hπ2pos.le
    have h2' : |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'|
        ≤ Ka2 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by
      calc |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'|
          ≤ Ka2 * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := h2
        _ ≤ Ka2 * Work.FTS.StrongGlobal.Xn6 α g * (Cπ * |θ - θ'| ^ β) :=
            mul_le_mul_of_nonneg_left hδ (mul_nonneg hKa20.le hX0)
        _ = Ka2 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by ring
    have h3' : |Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'|
        ≤ Ka1 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by
      calc |Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'|
          ≤ Ka1 * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := h3
        _ ≤ Ka1 * Work.FTS.StrongGlobal.Xn6 α g * (Cπ * |θ - θ'| ^ β) :=
            mul_le_mul_of_nonneg_left hδ (mul_nonneg hKa10.le hX0)
        _ = Ka1 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β := by ring
    have heq : g z θ + α ^ 2 * Work.Spaces.DzIter 2 (E g) z θ
          + 5 * α * Work.Spaces.DzIter 1 (E g) z θ
        - (g z θ' + α ^ 2 * Work.Spaces.DzIter 2 (E g) z θ'
          + 5 * α * Work.Spaces.DzIter 1 (E g) z θ')
        = (g z θ - g z θ')
          + α ^ 2 * (Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ')
          + 5 * α * (Work.Spaces.DzIter 1 (E g) z θ
            - Work.Spaces.DzIter 1 (E g) z θ') := by ring
    rw [heq]
    have h1' : |α ^ 2 * (Work.Spaces.DzIter 2 (E g) z θ
          - Work.Spaces.DzIter 2 (E g) z θ')|
        = α ^ 2 * |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg α)]
    have h1'' : |5 * α * (Work.Spaces.DzIter 1 (E g) z θ
          - Work.Spaces.DzIter 1 (E g) z θ')|
        = 5 * α * |Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 5 * α)]
    have htri : |(g z θ - g z θ')
          + α ^ 2 * (Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ')
          + 5 * α * (Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ')|
        ≤ |g z θ - g z θ'|
          + α ^ 2 * |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'|
          + 5 * α * |Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'| := by
      have hA := abs_add_le ((g z θ - g z θ')
          + α ^ 2 * (Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'))
        (5 * α * (Work.Spaces.DzIter 1 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ'))
      have hB := abs_add_le (g z θ - g z θ')
        (α ^ 2 * (Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 2 (E g) z θ'))
      rw [h1'] at hB
      rw [h1''] at hA
      linarith
    refine le_trans htri ?_
    have hXπ : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β :=
      mul_nonneg hX0 (Real.rpow_nonneg (abs_nonneg _) _)
    nlinarith [h1, h2', h3', hX0, hXπ]
  -- the final assembly
  have hsplit : deriv (deriv (fun θ'' => (E g) z θ'')) θ
        - deriv (deriv (fun θ'' => (E g) z θ'')) θ'
      = (deriv (deriv (fun θ'' => (E g) z θ'')) θ + 4 * (E g) z θ
          + Work.Elliptic.Lzero (E g) z θ)
        - (deriv (deriv (fun θ'' => (E g) z θ'')) θ' + 4 * (E g) z θ'
          + Work.Elliptic.Lzero (E g) z θ')
        - 4 * ((E g) z θ - (E g) z θ')
        - (Work.Elliptic.Lzero (E g) z θ - Work.Elliptic.Lzero (E g) z θ') := by ring
  rw [hsplit]
  have htri : |(deriv (deriv (fun θ'' => (E g) z θ'')) θ + 4 * (E g) z θ
          + Work.Elliptic.Lzero (E g) z θ)
        - (deriv (deriv (fun θ'' => (E g) z θ'')) θ' + 4 * (E g) z θ'
          + Work.Elliptic.Lzero (E g) z θ')
        - 4 * ((E g) z θ - (E g) z θ')
        - (Work.Elliptic.Lzero (E g) z θ - Work.Elliptic.Lzero (E g) z θ')|
      ≤ |(deriv (deriv (fun θ'' => (E g) z θ'')) θ + 4 * (E g) z θ
            + Work.Elliptic.Lzero (E g) z θ)
          - (deriv (deriv (fun θ'' => (E g) z θ'')) θ' + 4 * (E g) z θ'
            + Work.Elliptic.Lzero (E g) z θ')|
        + 4 * |(E g) z θ - (E g) z θ'|
        + |Work.Elliptic.Lzero (E g) z θ - Work.Elliptic.Lzero (E g) z θ'| := by
    exact th2Holder_abs_sub_four_sub_le _ _ _
  refine le_trans htri ?_
  have hXπ : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β :=
    mul_nonneg hX0 (Real.rpow_nonneg (abs_nonneg _) _)
  calc |(deriv (deriv (fun θ'' => (E g) z θ'')) θ + 4 * (E g) z θ
          + Work.Elliptic.Lzero (E g) z θ)
        - (deriv (deriv (fun θ'' => (E g) z θ'')) θ' + 4 * (E g) z θ'
          + Work.Elliptic.Lzero (E g) z θ')|
      + 4 * |(E g) z θ - (E g) z θ'|
      + |Work.Elliptic.Lzero (E g) z θ - Work.Elliptic.Lzero (E g) z θ'|
      ≤ CW * (Klz * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| ^ β
        + 4 * (Ka0 * Work.FTS.StrongGlobal.Xn6 α g * Cπ * |θ - θ'| ^ β)
        + (Cg + α ^ 2 * (Ka2 * Cπ) + 5 * α * (Ka1 * Cπ)) * Work.FTS.StrongGlobal.Xn6 α g
          * |θ - θ'| ^ β := by
        linarith [hWmod, hSmod, hGmod]
    _ = (CW * Klz + 4 * Ka0 * Cπ + (Cg + α ^ 2 * (Ka2 * Cπ) + 5 * α * (Ka1 * Cπ)))
          * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β := by ring

end Work.FTS_EllLimOK.ProducerH.H2
