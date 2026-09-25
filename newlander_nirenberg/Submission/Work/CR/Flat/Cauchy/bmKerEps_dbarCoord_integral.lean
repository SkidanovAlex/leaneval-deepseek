import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-! ## Elementary support and integrability lemmas

Everything in the present file is an application of the integration-by-parts identity for
`∂̄` (`Work.CR.Flat.integral_mul_dbarCoord_eq_neg`) to the regularised kernel `bmKerEps`.
The hypotheses of that identity, and the exchange of the finite sum with the integral, need
the facts collected here: `bmKerEps k ε` is smooth for `ε > 0`, a continuous function times
a continuous compactly supported one is integrable, and the derivative of a function that
vanishes outside the ball of radius `R` is compactly supported. -/

/-- A function vanishing on `{x | R ≤ ‖x‖}` has compact support (its support is contained
in the closed ball of radius `R`). -/
private lemma hasCompactSupport_of_norm_le {n : ℕ} {f : (Fin n → ℂ) → ℂ} {R : ℝ}
    (h : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  exact hx (h x hcon.le)

/-- A continuous function times a continuous compactly supported one is integrable. -/
private lemma integrable_mul_of_hasCompactSupport {n : ℕ} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x => a x * b x) volume :=
  (ha.mul hb).integrable_of_hasCompactSupport (hbc.mul_left (f := a))

/-- A function vanishing on `{x | R ≤ ‖x‖}` is identically zero *near* every point with
`R < ‖x‖`, hence its Fréchet derivative vanishes there. -/
private lemma fderiv_eq_zero_of_lt {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) {x : Fin n → ℂ} (hx : R < ‖x‖) :
    fderiv ℝ g x = 0 := by
  have hopen : IsOpen {y : Fin n → ℂ | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hg0 : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hsupp y hy.le
  have hfd : HasFDerivAt g (0 : (Fin n → ℂ) →L[ℝ] ℂ) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).congr_of_eventuallyEq hg0
  exact hfd.fderiv

/-- The directional derivative `x ↦ fderiv ℝ g x w` of a function vanishing on
`{x | R ≤ ‖x‖}` has compact support. -/
private lemma hasCompactSupport_fderiv_apply {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (w : Fin n → ℂ) :
    HasCompactSupport (fun x => fderiv ℝ g x w) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  rw [Function.mem_support] at hx
  exact hx (by rw [fderiv_eq_zero_of_lt hsupp hcon]; rfl)

/-- The regularised Bochner–Martinelli kernel is `C¹` for `ε > 0`. -/
private lemma contDiff_one_bmKerEps {n : ℕ} (k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (bmKerEps k ε) := by
  have hnum : ContDiff ℝ 1 (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k)) := by
    have h : (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k))
        = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘
            ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := by
      funext x; simp
    rw [h]
    exact (Complex.conjCLE.contDiff).comp
      (((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))
  have hden : ContDiff ℝ 1 (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n) := by
    have hnrm : ContDiff ℝ 1 (fun x : Fin n → ℂ => nrmSq x) := by
      have h : (fun x : Fin n → ℂ => nrmSq x) = fun x => ∑ i : Fin n, ‖x i‖ ^ 2 := rfl
      rw [h]
      refine ContDiff.sum (s := Finset.univ) ?_
      intro i _
      have h2 : (fun x : Fin n → ℂ => ‖x i‖ ^ 2)
          = (fun y : ℂ => ‖y‖ ^ 2) ∘
            ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := rfl
      rw [h2]
      exact (contDiff_norm_sq ℂ (E := ℂ) (n := 1)).comp
        (((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))
    exact (Complex.ofRealCLM.contDiff.comp (hnrm.add contDiff_const)).pow n
  have hne : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n ≠ 0 := by
    intro x
    have hpos : (0 : ℝ) < nrmSq x + ε ^ 2 := by
      have := nrmSq_nonneg x; positivity
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
  show ContDiff ℝ 1
    (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)
  have hfun : (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)
      = (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k))
        * (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)⁻¹ := by
    funext x; simp [div_eq_mul_inv]
  rw [hfun]
  exact ContDiff.mul hnum (ContDiff.inv hden hne)

/-- `dbarCoord k (bmKerEps k ε)` is continuous for `ε > 0`. -/
private lemma continuous_dbarCoord_bmKerEps {n : ℕ} (k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : Fin n → ℂ => dbarCoord k (bmKerEps k ε) x) := by
  have hfd : Continuous (fderiv ℝ (bmKerEps k ε)) :=
    (contDiff_one_bmKerEps k hε).continuous_fderiv (by norm_num)
  have h1 : Continuous (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single k 1)) :=
    hfd.clm_apply continuous_const
  have hI : Continuous
      (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single k Complex.I)) :=
    hfd.clm_apply continuous_const
  show Continuous (fun x => (1 / 2 : ℂ) * (fderiv ℝ (bmKerEps k ε) x (Pi.single k 1)
    + Complex.I * fderiv ℝ (bmKerEps k ε) x (Pi.single k Complex.I)))
  exact continuous_const.mul (h1.add (continuous_const.mul hI))

namespace BmEpsAux

lemma differentiableAt_normSq (a : ℂ) : DifferentiableAt ℝ Complex.normSq a := by
  have h : Complex.normSq = fun y : ℂ => y.re * y.re + y.im * y.im := by
    funext y; rw [Complex.normSq_apply]
  rw [h]; fun_prop

lemma fderiv_normSq (a : ℂ) :
    fderiv ℝ Complex.normSq a
      = (2 * a.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (2 * a.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ) := by
  have h : Complex.normSq = fun y : ℂ => y.re * y.re + y.im * y.im := by
    funext y; rw [Complex.normSq_apply]
  rw [h]
  have hre : (fun y : ℂ => y.re) = ⇑(Complex.reCLM : ℂ →L[ℝ] ℝ) := by
    funext z; rw [Complex.reCLM_apply]
  have him : (fun y : ℂ => y.im) = ⇑(Complex.imCLM : ℂ →L[ℝ] ℝ) := by
    funext z; rw [Complex.imCLM_apply]
  have hfun : (fun y : ℂ => y.re * y.re + y.im * y.im)
      = (fun y : ℂ => y.re * y.re) + (fun y : ℂ => y.im * y.im) := rfl
  rw [hfun, fderiv_add (by fun_prop) (by fun_prop)]
  rw [show (fun y : ℂ => y.re * y.re) = (fun y : ℂ => y.re) * (fun y : ℂ => y.re) from rfl]
  rw [show (fun y : ℂ => y.im * y.im) = (fun y : ℂ => y.im) * (fun y : ℂ => y.im) from rfl]
  rw [fderiv_mul (by fun_prop) (by fun_prop), fderiv_mul (by fun_prop) (by fun_prop)]
  rw [hre, him, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  module

lemma nrmSq_eq_sum_normSq {n : ℕ} :
    (fun x : Fin n → ℂ => nrmSq x)
      = ∑ i : Fin n, (fun x : Fin n → ℂ => Complex.normSq (x i)) := by
  funext x; rw [nrmSq, Finset.sum_apply]; simp [Complex.normSq_eq_norm_sq]

lemma fderiv_nrmSq_apply {n : ℕ} (z v : Fin n → ℂ) :
    fderiv ℝ (fun x : Fin n → ℂ => nrmSq x) z v
      = 2 * ∑ i : Fin n, ((z i).re * (v i).re + (z i).im * (v i).im) := by
  have hD : fderiv ℝ (fun x : Fin n → ℂ => nrmSq x) z
      = ∑ i : Fin n, fderiv ℝ (fun x : Fin n → ℂ => Complex.normSq (x i)) z := by
    rw [nrmSq_eq_sum_normSq]
    exact fderiv_sum (u := Finset.univ) (A := fun i (x : Fin n → ℂ) => Complex.normSq (x i))
      (fun i _ => (differentiableAt_normSq (z i)).comp z
        ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt)
  have hval : ∀ i : Fin n, fderiv ℝ (fun x : Fin n → ℂ => Complex.normSq (x i)) z v
      = 2 * ((z i).re * (v i).re + (z i).im * (v i).im) := by
    intro i
    have hcomp : fderiv ℝ (fun x : Fin n → ℂ => Complex.normSq (x i)) z
        = (fderiv ℝ Complex.normSq (z i)).comp
            ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := by
      rw [show (fun x : Fin n → ℂ => Complex.normSq (x i))
            = Complex.normSq ∘
              ⇑((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) from rfl]
      rw [fderiv_comp z (differentiableAt_normSq (z i))
        ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt]
      rw [ContinuousLinearMap.fderiv]
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.proj_apply]
    rw [hcomp, fderiv_normSq (z i)]
    simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.proj_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    ring
  rw [hD, sum_apply]
  rw [Finset.sum_congr rfl fun i _ => hval i, Finset.mul_sum]

lemma differentiableAt_nrmSq {n : ℕ} (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun x : Fin n → ℂ => nrmSq x) z := by
  rw [nrmSq_eq_sum_normSq]
  exact DifferentiableAt.sum (u := Finset.univ) (A := fun i (x : Fin n → ℂ) => Complex.normSq (x i))
    (fun i _ => (differentiableAt_normSq (z i)).comp z
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt)

lemma differentiableAt_nrmSq_complex {n : ℕ} (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z :=
  Complex.ofRealCLM.differentiableAt.comp z (differentiableAt_nrmSq z)

lemma dbarCoord_nrmSq {n : ℕ} (j : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z = z j := by
  have hcomp : fderiv ℝ (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z
      = Complex.ofRealCLM.comp (fderiv ℝ (fun x : Fin n → ℂ => nrmSq x) z) := by
    rw [show (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ))
          = Complex.ofRealCLM ∘ (fun x : Fin n → ℂ => nrmSq x) from rfl]
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt (differentiableAt_nrmSq z)]
    rw [ContinuousLinearMap.fderiv]
  have hval : ∀ v : Fin n → ℂ,
      fderiv ℝ (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z v
        = ((fderiv ℝ (fun x : Fin n → ℂ => nrmSq x) z v : ℝ) : ℂ) := by
    intro v
    rw [hcomp]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  rw [dbarCoord]
  obtain ⟨hd1, hdI⟩ :
      fderiv ℝ (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z (Pi.single j 1) = 2 * ((z j).re : ℂ) ∧
      fderiv ℝ (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z (Pi.single j Complex.I)
        = 2 * ((z j).im : ℂ) := by
    constructor
    · rw [hval, fderiv_nrmSq_apply]
      have hs : (∑ i : Fin n, ((z i).re * ((Pi.single j (1 : ℂ) : Fin n → ℂ) i).re
          + (z i).im * ((Pi.single j (1 : ℂ) : Fin n → ℂ) i).im)) = (z j).re := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [hs]; norm_num
    · rw [hval, fderiv_nrmSq_apply]
      have hs : (∑ i : Fin n, ((z i).re * ((Pi.single j Complex.I : Fin n → ℂ) i).re
          + (z i).im * ((Pi.single j Complex.I : Fin n → ℂ) i).im)) = (z j).im := by
        rw [Finset.sum_eq_single j]
        · simp [Complex.I_re, Complex.I_im]
        · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [hs]; norm_num
  rw [hd1, hdI]
  conv_rhs => rw [← Complex.re_add_im (z j)]
  ring

lemma dbarCoord_const {n : ℕ} (k : Fin n) (a : ℂ) (z : Fin n → ℂ) :
    dbarCoord k (fun _ : Fin n → ℂ => a) z = 0 := by
  rw [dbarCoord]; simp

lemma dbarCoord_nrmSq_add {n : ℕ} (k : Fin n) (c : ℝ) (z : Fin n → ℂ) :
    dbarCoord k (fun x : Fin n → ℂ => (((nrmSq x + c : ℝ)) : ℂ)) z = z k := by
  have hsum : (fun x : Fin n → ℂ => (((nrmSq x + c : ℝ)) : ℂ))
      = fun x => ((nrmSq x : ℝ) : ℂ) + ((c : ℝ) : ℂ) := by
    funext x; simp [Complex.ofReal_add]
  rw [hsum, Work.CR.Flat.Polydisc.dbarCoord_add k (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ))
      (fun _ : Fin n → ℂ => ((c : ℝ) : ℂ)) z (differentiableAt_nrmSq_complex z)
      (differentiableAt_const ((c : ℝ) : ℂ)), dbarCoord_nrmSq, dbarCoord_const, add_zero]

lemma dbarCoord_zpow {n : ℕ} (k : Fin n) (m : ℤ) {u : (Fin n → ℂ) → ℂ} (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (huz : u z ≠ 0) :
    dbarCoord k (fun x => (u x) ^ m) z = ((m : ℂ) * (u z) ^ (m - 1)) * dbarCoord k u z := by
  have hΨ : HasFDerivAt (fun y : ℂ => y ^ m)
      ((ContinuousLinearMap.toSpanSingleton ℂ ((m : ℂ) * (u z) ^ (m - 1))).restrictScalars ℝ)
      (u z) :=
    ((hasDerivAt_zpow m (u z) (Or.inl huz)).hasFDerivAt).restrictScalars ℝ
  have hcomp := hΨ.comp z hu.hasFDerivAt
  have hfder : fderiv ℝ (fun x => (u x) ^ m) z
      = ((m : ℂ) * (u z) ^ (m - 1)) • fderiv ℝ u z := by
    have hfun : (fun x => (u x) ^ m) = (fun y : ℂ => y ^ m) ∘ u := rfl
    rw [hfun, hcomp.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_apply]
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  rw [dbarCoord, dbarCoord, hfder]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma dbarCoord_radial {n : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin n) (z : Fin n → ℂ) :
    dbarCoord k (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))) z
      = -((n : ℂ) * (z k)) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1) := by
  have hGdiff : DifferentiableAt ℝ (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z := by
    have hsum : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ)))
        = fun x => ((nrmSq x : ℝ) : ℂ) + ((ε ^ 2 : ℝ) : ℂ) := by
      funext x; simp [Complex.ofReal_add]
    rw [hsum]
    exact (differentiableAt_nrmSq_complex z).add (differentiableAt_const ((ε ^ 2 : ℝ) : ℂ))
  have hGz : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z ≠ 0 := by
    show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
  have hexp : (-(n:ℤ) - 1 : ℤ) = -(((n+1:ℕ):ℤ)) := by omega
  rw [dbarCoord_zpow k (-(n:ℤ)) z hGdiff hGz]
  rw [show dbarCoord k (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z = z k from
    dbarCoord_nrmSq_add k (ε^2) z]
  rw [show ((↑(-(n:ℤ)) : ℂ)) = -(n : ℂ) by push_cast; ring]
  rw [show (((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (-(n:ℤ) - 1))
      = (((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1))⁻¹ by
    rw [hexp, zpow_neg, zpow_natCast]]
  rw [div_eq_mul_inv]
  ring

lemma differentiableAt_zpow_comp {n : ℕ} {u : (Fin n → ℂ) → ℂ} (z : Fin n → ℂ) (m : ℤ)
    (hu : DifferentiableAt ℝ u z) (huz : u z ≠ 0) :
    DifferentiableAt ℝ (fun x => (u x) ^ m) z := by
  have hΨ : DifferentiableAt ℝ (fun y : ℂ => y ^ m) (u z) :=
    ((hasDerivAt_zpow m (u z) (Or.inl huz)).hasFDerivAt.restrictScalars ℝ).differentiableAt
  have hfun : (fun x => (u x) ^ m) = (fun y : ℂ => y ^ m) ∘ u := rfl
  rw [hfun]
  exact hΨ.comp z hu

lemma dbarCoord_bmKerEps {n : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin n) (z : Fin n → ℂ) :
    dbarCoord k (bmKerEps k ε) z
      = 1 / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ n
        + star (z k) * (-((n : ℂ) * (z k)) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1)) := by
  have hfun : bmKerEps k ε = fun x : Fin n → ℂ =>
      star (x k) * ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ))) := by
    funext x
    rw [bmKerEps_apply, div_eq_mul_inv]
    congr 1
    rw [show (-(n:ℤ)) = -((n:ℤ)) from rfl, zpow_neg, zpow_natCast]
  have hu : DifferentiableAt ℝ (fun x : Fin n → ℂ => star (x k)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z
      ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z := by
    have hsum : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ)))
        = fun x => ((nrmSq x : ℝ) : ℂ) + ((ε ^ 2 : ℝ) : ℂ) := by
      funext x; simp [Complex.ofReal_add]
    rw [hsum]
    exact (differentiableAt_nrmSq_complex z).add (differentiableAt_const ((ε ^ 2 : ℝ) : ℂ))
  have hGz : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z ≠ 0 := by
    show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
  have hv := differentiableAt_zpow_comp z (-(n:ℤ)) hGdiff hGz
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_mul k (fun x : Fin n → ℂ => star (x k))
      (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))) z hu hv]
  rw [show dbarCoord k (fun x : Fin n → ℂ => star (x k)) z = 1 from by
    rw [Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord k k z]; simp]
  rw [show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))
      = 1 / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ n from by
    rw [show (-(n:ℤ)) = -((n:ℤ)) from rfl, zpow_neg, zpow_natCast, one_div]]
  rw [dbarCoord_radial hε k z]
  ring

theorem bmKerEpsDivergence {n : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Fin n → ℂ) :
    ∑ k, dbarCoord k (bmKerEps k ε) z
      = (n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1) := by
  rw [Finset.sum_congr rfl (fun k _ => dbarCoord_bmKerEps hε k z)]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ k : Fin n, 1 / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ n)
      = (n : ℂ) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hss : (∑ k : Fin n, star (z k) * z k) = ((nrmSq z : ℝ) : ℂ) := by
    have h : ∀ k : Fin n, star (z k) * z k = ((‖z k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun k _ => h k), ← Complex.ofReal_sum]
    rw [nrmSq]
  have h2 : (∑ k : Fin n, star (z k) *
        (-((n : ℂ) * (z k)) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1)))
      = (-(n : ℂ) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1)) * ((nrmSq z : ℝ) : ℂ) := by
    have hc : ∀ k : Fin n, star (z k) *
        (-((n : ℂ) * (z k)) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1))
        = (-(n : ℂ) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1)) * (star (z k) * z k) := by
      intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => hc k), ← Finset.mul_sum, hss]
  rw [h1, h2]
  have hD : ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
  field_simp
  push_cast
  ring


end BmEpsAux
/-- **The regularised Bochner–Martinelli identity.**  For `ε > 0` the regularised kernel
`bmKerEps k ε x = \bar x_k /(nrmSq x + ε²)^n` (see `Submission/Work/CR/Flat/Cauchy/bmSetup.lean`)
is smooth, and `Σ_k ∂̄_k (bmKerEps k ε) = n ε² /(nrmSq x + ε²)^{n+1}` pointwise.  Integrating by
parts against a compactly supported `C¹` function `g` therefore gives
`Σ_k ∫ x, bmKerEps k ε x * ∂̄_k g x = -∫ x, n ε² /(nrmSq x + ε²)^{n+1} * g x`.
This is the identity that tends to the Bochner–Martinelli formula as `ε → 0⁺`
(see `Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps`). -/
theorem bmKerEps_dbarCoord_integral {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x
      = -∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_norm_le hsupp
  have hg_cont : Continuous g := hg.continuous
  have hfdg_cont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hker_cont : ∀ k : Fin n, Continuous (bmKerEps k ε) :=
    fun k => (contDiff_one_bmKerEps k hε).continuous
  have hkerd_cont : ∀ k : Fin n,
      Continuous (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single k 1)) :=
    fun k => ((contDiff_one_bmKerEps k hε).continuous_fderiv (by norm_num)).clm_apply
      continuous_const
  have hkerdI_cont : ∀ k : Fin n,
      Continuous (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single k Complex.I)) :=
    fun k => ((contDiff_one_bmKerEps k hε).continuous_fderiv (by norm_num)).clm_apply
      continuous_const
  -- integration by parts in each coordinate
  have hstep : ∀ k : Fin n, ∫ x, bmKerEps k ε x * dbarCoord k g x
      = -∫ x, dbarCoord k (bmKerEps k ε) x * g x := by
    intro k
    refine Work.CR.Flat.integral_mul_dbarCoord_eq_neg k (contDiff_one_bmKerEps k hε) hg
      ?_ ?_ ?_ ?_ ?_
    · exact integrable_mul_of_hasCompactSupport (hkerd_cont k) hg_cont hgc
    · exact integrable_mul_of_hasCompactSupport (hkerdI_cont k) hg_cont hgc
    · exact integrable_mul_of_hasCompactSupport (hker_cont k)
        (hfdg_cont.clm_apply continuous_const)
        (hasCompactSupport_fderiv_apply hsupp (Pi.single k 1))
    · exact integrable_mul_of_hasCompactSupport (hker_cont k)
        (hfdg_cont.clm_apply continuous_const)
        (hasCompactSupport_fderiv_apply hsupp (Pi.single k Complex.I))
    · exact integrable_mul_of_hasCompactSupport (hker_cont k) hg_cont hgc
  -- exchange the finite sum with the integral
  have hInt : ∀ k : Fin n, Integrable (fun x => dbarCoord k (bmKerEps k ε) x * g x) volume :=
    fun k => integrable_mul_of_hasCompactSupport (continuous_dbarCoord_bmKerEps k hε) hg_cont hgc
  calc ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x
      = ∑ k, -∫ x, dbarCoord k (bmKerEps k ε) x * g x :=
        Finset.sum_congr rfl fun k _ => hstep k
    _ = -(∑ k, ∫ x, dbarCoord k (bmKerEps k ε) x * g x) := by rw [Finset.sum_neg_distrib]
    _ = -∫ x, (∑ k, dbarCoord k (bmKerEps k ε) x) * g x := by
        congr 1
        rw [show (fun x : Fin n → ℂ => (∑ k, dbarCoord k (bmKerEps k ε) x) * g x)
              = (fun x => ∑ k, dbarCoord k (bmKerEps k ε) x * g x) from by
            funext x; rw [Finset.sum_mul]]
        exact (integral_finsetSum Finset.univ (fun k _ => hInt k)).symm
    _ = -∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x := by
        congr 1
        have hdiv : (fun x : Fin n → ℂ => (∑ k, dbarCoord k (bmKerEps k ε) x) * g x)
            = (fun x : Fin n → ℂ =>
                ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) := by
          funext x; rw [BmEpsAux.bmKerEpsDivergence hε x]
        rw [hdiv]

end Work.CR.Flat.Cauchy
