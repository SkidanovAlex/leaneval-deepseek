/-
# The x-seminorm of the spike piece of the tangency layer

`tangSpike l d tau x = int_{1/2}^{3/2} K^{(d)}(tau,it) e^{-pi x t} dt` is the window of the
contour integral that contains the pole `z_1 = poleOne tau` of `z -> K^{(d)}(tau,z)`.  As `tau`
approaches the tangency point `+-1/2 + i/2` the pole `z_1` approaches the contour point `i`
(its real part tends to `0`), so `||K(tau,it)||` is *not* uniformly bounded on
`[1/2,3/2] x ctanRegion` -- the modulus of the integrand has a spike of height
`~ 1/||z_1 - i R||`.  The signed contour integral is nevertheless bounded and decays faster than
any power of `1 + x`: the contour is deformed to the *right* edge `Re z = 1/4` of the rectangle
`[0,1/4] x [1/2,3/2]`, which the pole misses.

## The argument

* **The only pole in the rectangle.**  `tangOrbitRectCl` says that for `tau in ctanCl` the closed
  rectangle `[0,1/4] x [1/2,3/2]` contains exactly one point of the orbit of `tau`, namely
  `z_1 = poleOne tau`; by `tangPoleGeom` its real part is in `(0,1/4)` and its imaginary part in
  `(1/2,3/2)`, so it is an interior point.

* **The residue at `z_1` vanishes.**  `AfunFun_poleOne_eq_zero` says the residue
  `-AfunFun(tau,z_1)/j'(z_1)` of `z -> K^{(d)}(tau,z)` at `z_1` is `0`; consequently `K` is
  *bounded* near `z_1` (`exists_bound_Kaxis_near_pole`, from `localPrincipalPart`), i.e. the
  residue theorem `Work.Asymptotics.residue_rectangle_of_bdd` applies with residue `0` -- no
  residue term survives.

* **The three other edges are uniformly bounded.**  `tangEdgeBound` bounds `||K^{(d)}(tau,z)||`
  for `tau in ctanCl` on `Re z = 1/4`, `Im z = 1/2` and `Im z = 3/2`.

Differentiating the contour integral `m` times under the integral sign multiplies the amplitude
by `(-pi t)^m`; the same contour shift applied to the *holomorphic* weight
`W(z) = (pi i z)^m e^{pi i x z}` (which on the contour is `(-pi t)^m e^{-pi x t}`) gives the
`m`-th derivative as a sum of three edge integrals whose amplitudes are bounded by
`C (7 pi / 4)^m` and whose Gaussian factor is `e^{-pi x Im z} <= e^{-pi x / 2}`; this is
`O((1+x)^{-N})` for every `N`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.HalfFunnel.tangPrincipalPart
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Asymptotics.HalfFunnel.tangEdgeBound
import Submission.Work.Asymptotics.HalfFunnel.residue_rect_bdd
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.HalfFunnel.tangKaxisFlatLow
import Submission.Work.HFN.HalfFunnel.lowBad_Phi12_deriv
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

set_option maxHeartbeats 4000000

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology

noncomputable section

/-! ## The lift of the kernel and the holomorphic weight of the contour shift -/

/-- The lift `z -> K^{(d)}(tau, ofComplex z)` of the CKMRV kernel to the complex plane. -/
def tangKc (l : Work.Kernels.LogLambdaData) (d : Nat) (tau : UpperHalfPlane) (z : Complex) : Complex :=
  Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex z)

/-- The holomorphic weight `z -> (pi i z)^m e^{pi i x z}`.  On the imaginary axis `z = it` it is
`(-pi t)^m e^{-pi x t}`, which is exactly the `m`-th derivative weight of the contour integral. -/
def tangW (m : Nat) (x : Real) (z : Complex) : Complex :=
  ((Real.pi : Complex) * Complex.I * z) ^ m * Complex.exp (Real.pi * Complex.I * (x : Complex) * z)

/-- The shifted integrand `z -> K^{(d)}(tau,z) W(z)` of the contour shift. -/
def tangF (l : Work.Kernels.LogLambdaData) (d : Nat) (tau : UpperHalfPlane) (m : Nat) (x : Real)
    (z : Complex) : Complex :=
  tangKc l d tau z * tangW m x z

/-- Real part of a point of the right edge `Re z = 1/4`. -/
lemma re_const_add_mul_I (a y : Real) : ((((a : Real)) : Complex) + (y : Complex) * Complex.I).re = a := by
  simp

/-- Imaginary part of a point of the right edge. -/
lemma im_const_add_mul_I (a y : Real) : ((((a : Real)) : Complex) + (y : Complex) * Complex.I).im = y := by
  simp

/-- Real part of a point of a horizontal edge. -/
lemma re_add_const_mul_I (u a : Real) : ((u : Complex) + (((a : Real)) : Complex) * Complex.I).re = u := by
  simp

/-- Imaginary part of a point of a horizontal edge. -/
lemma im_add_const_mul_I (u a : Real) : ((u : Complex) + (((a : Real)) : Complex) * Complex.I).im = a := by
  simp

/-! ## Continuity and holomorphy of the lift on the tangency rectangle -/

/-- The lift of the kernel is continuous on the closed tangency rectangle `[0,1/4] x [1/2,3/2]`
away from the pole `poleOne tau`. -/
theorem continuousAt_tangKc_of_mem_rect (l : Work.Kernels.LogLambdaData) (d : Nat)
    (hd : d = 8 ∨ d = 24) {tau : UpperHalfPlane} (htau : tau ∈ ctanCl) {z : Complex}
    (hzre : 0 ≤ z.re) (hzre' : z.re ≤ 1 / 4) (hzim : (1 : Real) / 2 ≤ z.im) (hzim' : z.im ≤ 3 / 2)
    (hne : z ≠ ((poleOne tau : UpperHalfPlane) : Complex)) :
    ContinuousAt (fun w : Complex => Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w)) z := by
  have hzpos : 0 < z.im := by linarith
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : Complex) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzpos]
  have hclean : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
      ≠ Work.Kernels.jInvariantFun tau := by
    intro hjeq
    have hzeta : UpperHalfPlane.ofComplex z = poleOne tau :=
      tangOrbitRectCl tau (UpperHalfPlane.ofComplex z) htau
        (by rw [← UpperHalfPlane.coe_re, hcoe]; exact hzre)
        (by rw [← UpperHalfPlane.coe_re, hcoe]; exact hzre')
        (by rw [← UpperHalfPlane.coe_im, hcoe]; exact hzim)
        (by rw [← UpperHalfPlane.coe_im, hcoe]; exact hzim')
        hjeq
    exact hne (by rw [← hcoe, hzeta])
  have h1 : ContinuousAt (fun q : UpperHalfPlane × UpperHalfPlane => Work.Kernels.Kfun l d q.1 q.2)
      (tau, UpperHalfPlane.ofComplex z) :=
    Work.Asymptotics.continuousAt_Kfun_of_clean hd hclean.symm
  have h2 : ContinuousAt (fun w : Complex => (tau, UpperHalfPlane.ofComplex w)) z :=
    continuousAt_const.prodMk (UpperHalfPlane.mdifferentiableAt_ofComplex hzpos).continuousAt
  exact ContinuousAt.comp (f := fun w : Complex => (tau, UpperHalfPlane.ofComplex w)) h1 h2

/-- The lift of the kernel is complex differentiable on the open tangency rectangle
`(0,1/4) x (1/2,3/2)` away from the pole `poleOne tau`. -/
theorem differentiableAt_tangKc_of_mem_openRect (l : Work.Kernels.LogLambdaData) (d : Nat)
    (hd : d = 8 ∨ d = 24) {tau : UpperHalfPlane} (htau : tau ∈ ctanCl) {z : Complex}
    (hzre : 0 < z.re) (hzre' : z.re < 1 / 4) (hzim : (1 : Real) / 2 < z.im) (hzim' : z.im < 3 / 2)
    (hne : z ≠ ((poleOne tau : UpperHalfPlane) : Complex)) :
    DifferentiableAt Complex (fun w : Complex =>
      Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w)) z := by
  have hzpos : 0 < z.im := by linarith
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : Complex) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzpos]
  have hclean : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
      ≠ Work.Kernels.jInvariantFun tau := by
    intro hjeq
    have hzeta : UpperHalfPlane.ofComplex z = poleOne tau :=
      tangOrbitRectCl tau (UpperHalfPlane.ofComplex z) htau
        (by rw [← UpperHalfPlane.coe_re, hcoe]; linarith)
        (by rw [← UpperHalfPlane.coe_re, hcoe]; linarith)
        (by rw [← UpperHalfPlane.coe_im, hcoe]; linarith)
        (by rw [← UpperHalfPlane.coe_im, hcoe]; linarith)
        hjeq
    exact hne (by rw [← hcoe, hzeta])
  have hmd := Work.Residues.mdifferentiableAt_Kfun_snd l d hd tau (UpperHalfPlane.ofComplex z) hclean
  have h := (UpperHalfPlane.mdifferentiableAt_iff
    (f := fun zeta : UpperHalfPlane => Work.Kernels.Kfun l d tau zeta)
    (τ := UpperHalfPlane.ofComplex z)).mp hmd
  exact hcoe ▸ h

/-! ## The bound near the pole and on the window -/

/-- **The kernel is bounded near the pole.**  The residue of `z -> K^{(d)}(tau,z)` at
`z_1 = poleOne tau` is `-AfunFun(tau,z_1)/j'(z_1) = 0` (`AfunFun_poleOne_eq_zero`), so the local
principal-part expansion of `localPrincipalPart` leaves a bounded remainder. -/
lemma exists_bound_Kaxis_near_pole (l : Work.Kernels.LogLambdaData) (d : Nat)
    (hd : d = 8 ∨ d = 24) (tau : UpperHalfPlane) (htau : tau ∈ ctanRegion) :
    ∃ r : Real, 0 < r ∧ ∃ M : Real, 0 ≤ M ∧ ∀ z : Complex, 0 < z.im →
      z ≠ ((poleOne tau : UpperHalfPlane) : Complex) →
      ‖z - ((poleOne tau : UpperHalfPlane) : Complex)‖ < r →
      ‖Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex z)‖ ≤ M := by
  obtain ⟨r, hr, M, hM, hbound⟩ := localPrincipalPart l d hd tau (poleOne tau)
    (jInvariantFun_poleOne tau) (jprimePoleOneNeZero tau htau)
  refine ⟨r, hr, M, hM, fun z hz hzne hzlt => ?_⟩
  have hzero : -(Work.Asymptotics.AfunFun l d tau (poleOne tau)) / Work.Residues.jprime (poleOne tau)
      = 0 := by
    rw [AfunFun_poleOne_eq_zero l d hd tau htau, neg_zero, zero_div]
  have h := hbound z hz hzne hzlt
  simpa [hzero] using h

/-- **The kernel is bounded on the window `[1/2,3/2]` of the contour**, for `tau` in the tangency
region.  The window is the image of the compact interval `[1/2,3/2]` under `t -> it`, and it meets
the orbit of `tau ∈ ctanRegion` in no point, because such a point would lie in the rectangle
`[0,1/4] x [1/2,3/2]` and hence be `poleOne tau`, whose real part is `> 0`. -/
theorem exists_bound_Kaxis_tang_window (l : Work.Kernels.LogLambdaData) (d : Nat)
    (hd : d = 8 ∨ d = 24) (tau : UpperHalfPlane) (htau : tau ∈ ctanRegion) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t : Real, 1 / 2 ≤ t → t ≤ 3 / 2 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t‖ ≤ B := by
  have htaucl : tau ∈ ctanCl := ctanRegion_subset_ctanCl htau
  have hTcompact : IsCompact (ctFun '' Set.Icc (1 / 2 : Real) (3 / 2)) :=
    isCompact_Icc.image_of_continuousOn
      (continuousOn_ctFun.mono (by intro s hs; exact lt_of_lt_of_le (by norm_num) hs.1))
  have hsep : ∀ (tau' : UpperHalfPlane), tau' ∈ ({tau} : Set UpperHalfPlane) →
      ∀ z : UpperHalfPlane, z ∈ ctFun '' Set.Icc (1 / 2 : Real) (3 / 2) →
      Work.Kernels.jInvariantFun tau' ≠ Work.Kernels.jInvariantFun z := by
    intro tau' htau' z hz
    rw [Set.mem_singleton_iff] at htau'
    obtain ⟨s, hs, hzs⟩ := hz
    rw [htau', ← hzs]
    have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
    rw [ctFun_eq_imagAxis hspos]
    intro hjeq
    have hre0 : (Work.Kernels.imagAxis s hspos).re = 0 := by
      rw [← UpperHalfPlane.coe_re]
      show ((s : Complex) * Complex.I).re = 0
      simp
    have hims : (Work.Kernels.imagAxis s hspos).im = s := by
      rw [← UpperHalfPlane.coe_im]
      show ((s : Complex) * Complex.I).im = s
      simp
    have hzeta : Work.Kernels.imagAxis s hspos = poleOne tau :=
      tangOrbitRectCl tau (Work.Kernels.imagAxis s hspos) htaucl
        (by simp [hre0]) (by simp [hre0]) (by simpa [hims] using hs.1)
        (by simpa [hims] using hs.2) hjeq.symm
    have hpos := (tangPoleGeom tau htau).1
    rw [hzeta] at hre0
    linarith
  obtain ⟨CK, hCKpos, hCK⟩ :=
    exists_bound_Kfun_off_coincidence l d hd isCompact_singleton hTcompact hsep
  refine ⟨max CK 0, le_max_right _ _, fun t ht1 ht2 => ?_⟩
  have htpos : 0 < t := by linarith
  have hz : Work.Kernels.imagAxis t htpos ∈ ctFun '' Set.Icc (1 / 2 : Real) (3 / 2) :=
    ⟨t, ⟨ht1, ht2⟩, ctFun_eq_imagAxis htpos⟩
  have hb : ‖Work.Kernels.Kfun l d tau (Work.Kernels.imagAxis t htpos)‖ ≤ CK :=
    hCK tau (by simp) (Work.Kernels.imagAxis t htpos) hz
  rw [Work.Kernels.Kaxis, dif_pos htpos]
  exact le_trans hb (le_max_left _ _)

/-! ## Elementary facts about the weight -/

/-- The exponential decay `e^{-pi x/2}` is `O((1+x)^{-N})` at infinity. -/
lemma exp_neg_half_le_rpow_neg (N : Real) (hN : 0 ≤ N) :
    ∃ K : Real, 0 ≤ K ∧ ∀ x : Real, 0 ≤ x →
      Real.exp (-(Real.pi * x / 2)) ≤ K * (1 + x) ^ (-N) := by
  obtain ⟨K, hK0, hK⟩ := exists_exp_neg_le_pow (c := Real.pi / 2) (by positivity) (Nat.ceil N)
  refine ⟨K, hK0, fun x hx => ?_⟩
  have hK' : Real.exp (-(Real.pi * x / 2)) ≤ K * (1 + x) ^ (-((Nat.ceil N : Nat) : Real)) := by
    rw [show -(Real.pi * x / 2) = -(Real.pi / 2 * x) by ring]
    exact hK x hx
  refine le_trans hK' (mul_le_mul_of_nonneg_left ?_ hK0)
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  have hceil : N ≤ ((Nat.ceil N : Nat) : Real) := Nat.le_ceil N
  linarith

/-- The contour point `it` is `ofComplex ((t : Complex) * I)`. -/
lemma imagAxis_eq_ofComplex (t : Real) (ht : 0 < t) :
    Work.Kernels.imagAxis t ht = UpperHalfPlane.ofComplex ((t : Complex) * Complex.I) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]
  show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : Complex) = (t : Complex) * Complex.I
  rw [Work.Kernels.imagAxis]

/-- On the contour, the lift of the kernel is the contour integrand. -/
lemma Kaxis_eq_tangKc (l : Work.Kernels.LogLambdaData) (d : Nat) {tau : UpperHalfPlane} {t : Real}
    (ht : 0 < t) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t = tangKc l d tau ((t : Complex) * Complex.I) := by
  rw [Work.Kernels.Kaxis, dif_pos ht, tangKc, imagAxis_eq_ofComplex t ht]

/-- On the contour, the weight `W` is the `m`-th derivative weight `(-pi t)^m e^{-pi x t}`. -/
lemma tangW_apply_imagAxis (m : Nat) (x t : Real) :
    tangW m x ((t : Complex) * Complex.I)
      = (((-(Real.pi * t) : Real)) : Complex) ^ m * (Real.exp (-(Real.pi * x * t)) : Complex) := by
  have h1 : (Real.pi : Complex) * Complex.I * ((t : Complex) * Complex.I)
      = ((-(Real.pi * t) : Real) : Complex) := by
    rw [show (Real.pi : Complex) * Complex.I * ((t : Complex) * Complex.I)
        = ((Real.pi * t : Real) : Complex) * (Complex.I * Complex.I) by push_cast; ring]
    rw [Complex.I_mul_I]
    push_cast
    ring
  have h2 : (Real.pi : Complex) * Complex.I * (x : Complex) * ((t : Complex) * Complex.I)
      = ((-(Real.pi * x * t) : Real) : Complex) := by
    rw [show (Real.pi : Complex) * Complex.I * (x : Complex) * ((t : Complex) * Complex.I)
        = ((Real.pi * x * t : Real) : Complex) * (Complex.I * Complex.I) by push_cast; ring]
    rw [Complex.I_mul_I]
    push_cast
    ring
  rw [tangW, h1, h2, Complex.ofReal_exp]

/-- The modulus of the weight: `‖(pi i z)^m e^{pi i x z}‖ = (pi ‖z‖)^m e^{-pi x Im z}`. -/
lemma norm_tangW (m : Nat) (x : Real) (z : Complex) :
    ‖tangW m x z‖ = (Real.pi * ‖z‖) ^ m * Real.exp (-(Real.pi * x * z.im)) := by
  have hnorm : ‖(Real.pi : Complex) * Complex.I * z‖ = Real.pi * ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, mul_one]
  have hre : ((Real.pi : Complex) * Complex.I * (x : Complex) * z).re = -(Real.pi * x * z.im) := by
    rw [show (Real.pi : Complex) * Complex.I * (x : Complex) * z
        = ((Real.pi * x : Real) : Complex) * (Complex.I * z) by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [tangW, norm_mul, norm_pow, hnorm, Complex.norm_exp, hre]




/-! ## The contour shift for the `m`-th derivative -/

/-- **The `m`-th derivative of the spike integral, after the contour shift.**  Cauchy's residue
theorem on the rectangle `[0,1/4] x [1/2,3/2]` applied to `z -> K^{(d)}(tau,z) W(z)` -- whose only
pole in the rectangle is `z_1 = poleOne tau`, with vanishing residue -- writes the `m`-th
derivative of `tangSpike` as the sum of three integrals over the edges of the rectangle other
than the contour. -/
theorem tangSpike_deriv_shift (l : Work.Kernels.LogLambdaData) (d : Nat) (hd : d = 8 ∨ d = 24)
    (m : Nat) (tau : UpperHalfPlane) (htau : tau ∈ ctanRegion) (x : Real) (hx : 0 ≤ x) :
    iteratedDeriv m (tangSpike l d tau) x
      = (∫ y in (1 / 2 : Real)..(3 / 2),
            tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I))
        - Complex.I * (∫ u in (0 : Real)..(1 / 4),
            tangF l d tau m x ((u : Complex) + (((1 : Real) / 2 : Real) : Complex) * Complex.I))
        + Complex.I * (∫ u in (0 : Real)..(1 / 4),
            tangF l d tau m x ((u : Complex) + (((3 : Real) / 2 : Real) : Complex) * Complex.I)) := by
  have htaucl : tau ∈ ctanCl := ctanRegion_subset_ctanCl htau
  have hp := tangPoleGeom tau htau
  have hz0re : (((poleOne tau : UpperHalfPlane) : Complex)).re = (poleOne tau).re := by
    rw [UpperHalfPlane.coe_re]
  have hz0im : (((poleOne tau : UpperHalfPlane) : Complex)).im = (poleOne tau).im := by
    rw [UpperHalfPlane.coe_im]
  -- ## Step 1: differentiation under the integral sign
  have hdiff : iteratedDeriv m (tangSpike l d tau) x
      = ∫ t in (1 / 2 : Real)..(3 / 2), tangF l d tau m x ((t : Complex) * Complex.I) := by
    obtain ⟨B, hB0, hB⟩ := exists_bound_Kaxis_tang_window l d hd tau htau
    have hmeas : AEStronglyMeasurable
        (fun t : Real => Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t)
        (volume.restrict (Set.Ioc (1 / 2 : Real) (3 / 2))) :=
      (measurable_Kaxis_Kfun l d hd tau).aestronglyMeasurable
    have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : Real) (3 / 2))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t‖ ≤ B := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact hB t (le_of_lt ht.1) ht.2
    have hfuneq : tangSpike l d tau = fun y : Real =>
        ∫ t in (1 / 2 : Real)..(3 / 2),
          Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t
            * (Real.exp (-(Real.pi * y * t)) : Complex) := by
      funext y
      rw [tangSpike]
      refine intervalIntegral.integral_congr fun t _ => ?_
      congr 1
      rw [tangGauss, Complex.ofReal_exp]
      push_cast
      ring
    rw [hfuneq, iteratedDeriv_intervalIntegral_exp_of_bound
      (fun t : Real => Work.Kernels.Kaxis (Work.Kernels.Kfun l d) tau t) (1 / 2) (3 / 2)
      (by norm_num) hmeas hB0 hbd m x]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num : (1 : Real) / 2 ≤ 3 / 2)] at ht
    have htpos : 0 < t := by linarith [ht.1]
    rw [Kaxis_eq_tangKc l d htpos]
    show tangKc l d tau ((t : Complex) * Complex.I) * (((-(Real.pi * t) : Real)) : Complex) ^ m
        * (Real.exp (-(Real.pi * x * t)) : Complex)
      = tangKc l d tau ((t : Complex) * Complex.I) * tangW m x ((t : Complex) * Complex.I)
    rw [tangW_apply_imagAxis m x t]
    ring
  -- ## Step 2: Cauchy's residue theorem on the rectangle
  have hcont : ContinuousOn (tangF l d tau m x)
      ({z : Complex | 0 ≤ z.re ∧ z.re ≤ 1 / 4 ∧ (1 : Real) / 2 ≤ z.im ∧ z.im ≤ 3 / 2} \
        {((poleOne tau : UpperHalfPlane) : Complex)}) := by
    intro z hz
    obtain ⟨hzr, hzne⟩ := hz
    have h1 : ContinuousAt
        (fun w : Complex => Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w)) z :=
      continuousAt_tangKc_of_mem_rect l d hd htaucl hzr.1 hzr.2.1 hzr.2.2.1 hzr.2.2.2 hzne
    have h2 : ContinuousAt
        (fun w : Complex =>
          Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w) * tangW m x w) z := by
      refine h1.mul ?_
      show ContinuousAt (fun w : Complex => ((Real.pi : Complex) * Complex.I * w) ^ m
        * Complex.exp (Real.pi * Complex.I * (x : Complex) * w)) z
      fun_prop
    exact h2.continuousWithinAt
  have hhol : ∀ z : Complex, 0 < z.re → z.re < 1 / 4 → (1 : Real) / 2 < z.im → z.im < 3 / 2 →
      z ≠ ((poleOne tau : UpperHalfPlane) : Complex) →
      DifferentiableAt Complex (tangF l d tau m x) z := by
    intro z h1 h2 h3 h4 hne
    have hd1 : DifferentiableAt Complex
        (fun w : Complex => Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w)) z :=
      differentiableAt_tangKc_of_mem_openRect l d hd htaucl h1 h2 h3 h4 hne
    have hd2 : DifferentiableAt Complex
        (fun w : Complex =>
          Work.Kernels.Kfun l d tau (UpperHalfPlane.ofComplex w) * tangW m x w) z := by
      refine hd1.mul ?_
      show DifferentiableAt Complex (fun w : Complex => ((Real.pi : Complex) * Complex.I * w) ^ m
        * Complex.exp (Real.pi * Complex.I * (x : Complex) * w)) z
      fun_prop
    exact hd2
  have hbdd : ∃ M : Real, 0 ≤ M ∧ ∃ r : Real, 0 < r ∧
      ∀ z : Complex, z ≠ ((poleOne tau : UpperHalfPlane) : Complex) →
        ‖z - ((poleOne tau : UpperHalfPlane) : Complex)‖ < r →
        ‖tangF l d tau m x z - (0 : Complex) / (z - ((poleOne tau : UpperHalfPlane) : Complex))‖
          ≤ M := by
    obtain ⟨r, hr, M, hM, hKbd⟩ := exists_bound_Kaxis_near_pole l d hd tau htau
    refine ⟨M * (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m,
      by positivity, min r (1 / 4), lt_min hr (by norm_num), fun z hzne hzlt => ?_⟩
    have hzlt' : ‖z - ((poleOne tau : UpperHalfPlane) : Complex)‖ < r :=
      lt_of_lt_of_le hzlt (min_le_left _ _)
    have hzlt'' : ‖z - ((poleOne tau : UpperHalfPlane) : Complex)‖ < 1 / 4 :=
      lt_of_lt_of_le hzlt (min_le_right _ _)
    have hzim : 0 < z.im := by
      have h := Complex.abs_im_le_norm (z - ((poleOne tau : UpperHalfPlane) : Complex))
      rw [Complex.sub_im, hz0im] at h
      have h2 := lt_of_le_of_lt h hzlt''
      have h3 := (abs_lt.mp h2).1
      linarith [hp.2.2.1]
    have hK : ‖tangKc l d tau z‖ ≤ M := by
      have := hKbd z hzim hzne hzlt'
      simpa only [tangKc] using this
    have hW : ‖tangW m x z‖
        ≤ (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m := by
      rw [norm_tangW]
      have hnorm : ‖z‖ ≤ ‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4 := by
        have h1 : ‖z‖ ≤ ‖z - ((poleOne tau : UpperHalfPlane) : Complex)‖
            + ‖((poleOne tau : UpperHalfPlane) : Complex)‖ := by
          have := norm_add_le (z - ((poleOne tau : UpperHalfPlane) : Complex))
            ((poleOne tau : UpperHalfPlane) : Complex)
          simpa using this
        linarith
      have h1 : Real.pi * ‖z‖ ≤ Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4) :=
        mul_le_mul_of_nonneg_left hnorm Real.pi_pos.le
      have h2 : (Real.pi * ‖z‖) ^ m
          ≤ (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
      have h3 : Real.exp (-(Real.pi * x * z.im)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h4 : 0 ≤ Real.pi * x * z.im := mul_nonneg (mul_nonneg Real.pi_pos.le hx) hzim.le
        linarith
      calc (Real.pi * ‖z‖) ^ m * Real.exp (-(Real.pi * x * z.im))
          ≤ (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m * 1 :=
            mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
        _ = (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m := mul_one _
    have h2 : ‖tangF l d tau m x z‖
        ≤ M * (Real.pi * (‖((poleOne tau : UpperHalfPlane) : Complex)‖ + 1 / 4)) ^ m := by
      show ‖tangKc l d tau z * tangW m x z‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul hK hW (norm_nonneg _) hM
    simpa using h2
  have hmain := Work.Asymptotics.residue_rectangle_of_bdd (tangF l d tau m x)
    ((poleOne tau : UpperHalfPlane) : Complex) 0 0 (1 / 4) (1 / 2) (3 / 2)
    (by rw [hz0re]; exact hp.1) (by rw [hz0re]; exact hp.2.1)
    (by rw [hz0im]; exact hp.2.2.1) (by rw [hz0im]; exact hp.2.2.2)
    hcont hhol hbdd
  -- ## Step 3: solve the rectangle identity for the contour integral
  have h0 : (2 : Complex) * (Real.pi : Complex) * Complex.I * 0 = 0 := by ring
  rw [h0] at hmain
  have hleft : (∫ y in (1 / 2 : Real)..(3 / 2),
        tangF l d tau m x ((((0 : Real)) : Complex) + (y : Complex) * Complex.I))
      = ∫ y in (1 / 2 : Real)..(3 / 2), tangF l d tau m x ((y : Complex) * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => by simp
  rw [hleft] at hmain
  have hXY : Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
        tangF l d tau m x ((y : Complex) * Complex.I))
      = (∫ u in (0 : Real)..(1 / 4),
            tangF l d tau m x ((u : Complex) + (((1 : Real) / 2 : Real) : Complex) * Complex.I))
        - (∫ u in (0 : Real)..(1 / 4),
            tangF l d tau m x ((u : Complex) + (((3 : Real) / 2 : Real) : Complex) * Complex.I))
        + Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
            tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I)) :=
    (sub_eq_zero.mp hmain).symm
  have hJJ : (∫ y in (1 / 2 : Real)..(3 / 2), tangF l d tau m x ((y : Complex) * Complex.I))
      = (-(Complex.I)) * ((∫ u in (0 : Real)..(1 / 4),
              tangF l d tau m x ((u : Complex) + (((1 : Real) / 2 : Real) : Complex) * Complex.I))
          - (∫ u in (0 : Real)..(1 / 4),
              tangF l d tau m x ((u : Complex) + (((3 : Real) / 2 : Real) : Complex) * Complex.I))
          + Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
              tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I))) := by
    have hstep : (-(Complex.I)) * (Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
          tangF l d tau m x ((y : Complex) * Complex.I)))
        = (-(Complex.I)) * ((∫ u in (0 : Real)..(1 / 4),
              tangF l d tau m x ((u : Complex) + (((1 : Real) / 2 : Real) : Complex) * Complex.I))
          - (∫ u in (0 : Real)..(1 / 4),
              tangF l d tau m x ((u : Complex) + (((3 : Real) / 2 : Real) : Complex) * Complex.I))
          + Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
              tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I))) :=
      congrArg (fun w => (-(Complex.I)) * w) hXY
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] at hstep
    exact hstep
  rw [hdiff, hJJ, mul_add, mul_sub]
  rw [show (-(Complex.I)) * (Complex.I * (∫ y in (1 / 2 : Real)..(3 / 2),
        tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I)))
      = ∫ y in (1 / 2 : Real)..(3 / 2),
          tangF l d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I) by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]]
  ring

/-! ## The seminorm of the spike piece -/

theorem tangSpikeDeriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ m : ℕ, ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (x : ℝ),
      τ ∈ Work.Asymptotics.HalfFunnel.ctanRegion → 0 ≤ x →
      ‖iteratedDeriv m (Work.Asymptotics.HalfFunnel.tangSpike ℓ d τ) x‖
        ≤ C * (1 + x) ^ (-N) := by
  intro m N hN
  obtain ⟨CE, hCEpos, hCE⟩ := tangEdgeBound ℓ d hd
  obtain ⟨Kc, hKc0, hKc⟩ := exp_neg_half_le_rpow_neg N hN
  refine ⟨(3 / 2) * CE * (7 * Real.pi / 4) ^ m * Kc, by positivity, fun tau x htau hx => ?_⟩
  have htaucl : tau ∈ ctanCl := ctanRegion_subset_ctanCl htau
  have hdec : Real.exp (-(Real.pi * x / 2)) ≤ Kc * (1 + x) ^ (-N) := hKc x hx
  set MW : Real := (7 * Real.pi / 4) ^ m * Real.exp (-(Real.pi * x / 2)) with hMW
  have hMW0 : 0 ≤ MW := by rw [hMW]; positivity
  have hedge : ∀ z : Complex,
      (z.re = 1 / 4 ∧ (1 : Real) / 2 ≤ z.im ∧ z.im ≤ 3 / 2) ∨
      (z.im = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4) ∨
      (z.im = 3 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4) →
      ‖tangKc ℓ d tau z * tangW m x z‖ ≤ CE * MW := by
    intro z hz
    have hK : ‖tangKc ℓ d tau z‖ ≤ CE := by
      have hh := hCE tau z htaucl hz
      simpa only [tangKc] using hh
    have hW : ‖tangW m x z‖ ≤ MW := by
      rw [hMW, norm_tangW]
      have hre : |z.re| ≤ 1 / 4 := by
        rcases hz with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [h1] <;> norm_num
        · rw [abs_of_nonneg h2] <;> linarith
        · rw [abs_of_nonneg h2] <;> linarith
      have himge : (1 : Real) / 2 ≤ z.im := by
        rcases hz with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact h2
        · rw [h1] <;> norm_num
        · rw [h1] <;> norm_num
      have himle : z.im ≤ 3 / 2 := by
        rcases hz with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact h3
        · rw [h1] <;> norm_num
        · rw [h1] <;> norm_num
      have hnorm : ‖z‖ ≤ 7 / 4 := by
        have h1 := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos (by linarith : (0 : Real) < z.im)] at h1
        linarith
      have h1 : Real.pi * ‖z‖ ≤ 7 * Real.pi / 4 := by nlinarith [Real.pi_pos, hnorm]
      have h2 : (Real.pi * ‖z‖) ^ m ≤ (7 * Real.pi / 4) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
      have h3 : Real.exp (-(Real.pi * x * z.im)) ≤ Real.exp (-(Real.pi * x / 2)) := by
        apply Real.exp_le_exp.mpr
        have hx2 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx
        nlinarith [hx2, himge]
      exact mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    rw [norm_mul]
    exact mul_le_mul hK hW (norm_nonneg _) hCEpos.le
  rw [tangSpike_deriv_shift ℓ d hd m tau htau x hx]
  set Jr : Complex := ∫ y in (1 / 2 : Real)..(3 / 2),
    tangF ℓ d tau m x ((((1 : Real) / 4 : Real) : Complex) + (y : Complex) * Complex.I) with hJr
  set Ab : Complex := ∫ u in (0 : Real)..(1 / 4),
    tangF ℓ d tau m x ((u : Complex) + (((1 : Real) / 2 : Real) : Complex) * Complex.I) with hAb
  set At : Complex := ∫ u in (0 : Real)..(1 / 4),
    tangF ℓ d tau m x ((u : Complex) + (((3 : Real) / 2 : Real) : Complex) * Complex.I) with hAt
  have hV : ‖Jr‖ ≤ CE * MW := by
    rw [hJr]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := CE * MW)
      (a := 1 / 2) (b := 3 / 2) ?_) ?_
    · intro y hy
      rw [Set.uIoc_of_le (by norm_num : (1 : Real) / 2 ≤ 3 / 2)] at hy
      exact hedge _
        (Or.inl ⟨by rw [re_const_add_mul_I],
          by rw [im_const_add_mul_I]; linarith [hy.1],
          by rw [im_const_add_mul_I]; linarith [hy.2]⟩)
    · rw [show (3 : Real) / 2 - 1 / 2 = 1 by norm_num,
        abs_of_pos (by norm_num : (0 : Real) < 1)] <;> exact le_of_eq (by ring)
  have hB : ‖Ab‖ ≤ CE * MW * (1 / 4) := by
    rw [hAb]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := CE * MW)
      (a := 0) (b := 1 / 4) ?_) ?_
    · intro u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1 / 4)] at hu
      exact hedge _
        (Or.inr (Or.inl ⟨by rw [im_add_const_mul_I],
          by rw [re_add_const_mul_I]; linarith [hu.1],
          by rw [re_add_const_mul_I]; linarith [hu.2]⟩))
    · rw [show (1 : Real) / 4 - 0 = 1 / 4 by norm_num,
        abs_of_pos (by norm_num : (0 : Real) < 1 / 4)] <;> exact le_of_eq (by ring)
  have hC : ‖At‖ ≤ CE * MW * (1 / 4) := by
    rw [hAt]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := CE * MW)
      (a := 0) (b := 1 / 4) ?_) ?_
    · intro u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1 / 4)] at hu
      exact hedge _
        (Or.inr (Or.inr ⟨by rw [im_add_const_mul_I],
          by rw [re_add_const_mul_I]; linarith [hu.1],
          by rw [re_add_const_mul_I]; linarith [hu.2]⟩))
    · rw [show (1 : Real) / 4 - 0 = 1 / 4 by norm_num,
        abs_of_pos (by norm_num : (0 : Real) < 1 / 4)] <;> exact le_of_eq (by ring)
  have htri : ‖Jr - Complex.I * Ab + Complex.I * At‖ ≤ ‖Jr‖ + ‖Ab‖ + ‖At‖ := by
    calc ‖Jr - Complex.I * Ab + Complex.I * At‖
        ≤ ‖Jr - Complex.I * Ab‖ + ‖Complex.I * At‖ := norm_add_le _ _
      _ ≤ (‖Jr‖ + ‖Complex.I * Ab‖) + ‖Complex.I * At‖ :=
          add_le_add (norm_sub_le Jr (Complex.I * Ab)) le_rfl
      _ = ‖Jr‖ + ‖Ab‖ + ‖At‖ := by simp only [norm_mul, Complex.norm_I, one_mul]
  have hsum : ‖Jr‖ + ‖Ab‖ + ‖At‖ ≤ (3 / 2) * (CE * MW) := by
    have h4 : ‖Ab‖ + ‖At‖ ≤ CE * MW * (1 / 4) + CE * MW * (1 / 4) := add_le_add hB hC
    have h5 : ‖Jr‖ + (‖Ab‖ + ‖At‖)
        ≤ CE * MW + (CE * MW * (1 / 4) + CE * MW * (1 / 4)) := add_le_add hV h4
    have h6 : CE * MW + (CE * MW * (1 / 4) + CE * MW * (1 / 4)) = (3 / 2) * (CE * MW) := by
      ring
    calc ‖Jr‖ + ‖Ab‖ + ‖At‖ = ‖Jr‖ + (‖Ab‖ + ‖At‖) := by ring
      _ ≤ CE * MW + (CE * MW * (1 / 4) + CE * MW * (1 / 4)) := h5
      _ = (3 / 2) * (CE * MW) := h6
  calc ‖Jr - Complex.I * Ab + Complex.I * At‖ ≤ ‖Jr‖ + ‖Ab‖ + ‖At‖ := htri
    _ ≤ (3 / 2) * (CE * MW) := hsum
    _ = (3 / 2) * CE * (7 * Real.pi / 4) ^ m * Real.exp (-(Real.pi * x / 2)) := by
        rw [hMW]; ring
    _ ≤ (3 / 2) * CE * (7 * Real.pi / 4) ^ m * (Kc * (1 + x) ^ (-N)) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = ((3 / 2) * CE * (7 * Real.pi / 4) ^ m * Kc) * (1 + x) ^ (-N) := by ring

end

end Work.HFN.HalfFunnel
