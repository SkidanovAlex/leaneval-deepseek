import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LocaliseGradWideDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real Topology BigOperators Pointwise
open MeasureTheory


namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma deriv_qsneg {v : ℝ} (hv : v < 0) : deriv Real.smoothTransition v = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hv] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

lemma contDiff_Phi : ContDiff ℝ 2 Phi := by
  have h1 : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have h2 : ContDiff ℝ 2 (fun u : ℝ => (4 - u) / 3) := by fun_prop
  exact h1.comp h2

lemma deriv_Phi_eq (u : ℝ) : deriv Phi u = deriv Real.smoothTransition ((4 - u) / 3) * (-(1/3)) := by
  have hlin : HasDerivAt (fun u : ℝ => (4 - u) / 3) (-(1/3)) u := by
    have h : HasDerivAt (fun u : ℝ => (4 - u) / 3) ((0 - 1) / 3) u :=
      ((hasDerivAt_const (x := u) (c := (4 : ℝ))).sub (hasDerivAt_id u)).div_const 3
    convert h using 1
    ring
  have hST : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((4 - u) / 3))
      ((4 - u) / 3) :=
    ((Real.smoothTransition.contDiff (n := (2 : ℕ∞))).differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact (hST.comp u hlin).deriv

lemma hasDerivAt_Phi (u : ℝ) : HasDerivAt Phi (deriv Phi u) u :=
  hasDerivAt_deriv_iff.mpr (contDiff_Phi.differentiable (by norm_num)).differentiableAt

lemma deriv_Phi_bound (h : ∀ x, |deriv Real.smoothTransition x| ≤ 45 / 16) (u : ℝ) :
    |deriv Phi u| ≤ 15 / 16 := by
  rw [deriv_Phi_eq u, abs_mul]
  have h3 : |(-(1 / 3) : ℝ)| = 1 / 3 := by norm_num
  rw [h3]
  nlinarith [h ((4 - u) / 3), abs_nonneg (deriv Real.smoothTransition ((4 - u) / 3))]

lemma deriv_Phi_eq_zero {u : ℝ} (hu : 4 < u) : deriv Phi u = 0 := by
  rw [deriv_Phi_eq u]
  have hv : (4 - u) / 3 < 0 := by linarith
  rw [deriv_qsneg hv, zero_mul]

lemma contDiff_psiOf (ℓ : ℝ) : ContDiff ℝ 2 (psiOf ℓ) := by
  unfold psiOf
  fun_prop

lemma contDiff_etaOf (ℓ : ℝ) : ContDiff ℝ 2 (etaOf ℓ) := by
  unfold etaOf
  exact contDiff_Phi.comp (contDiff_psiOf ℓ)

lemma etaOf_eq_zero' {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : 2 * ℓ < ‖x‖) :
    etaOf ℓ x = 0 := etaOf_eq_zero hℓ (le_of_lt hx)

lemma hasCompactSupport_etaOf {ℓ : ℝ} (hℓ : 0 < ℓ) : HasCompactSupport (etaOf ℓ) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * ℓ))
    (isCompact_closedBall 0 (2 * ℓ)) ?_
  intro x hx
  simp only [Function.mem_support, Metric.mem_closedBall, dist_zero_right] at hx ⊢
  by_contra hlt
  exact hx (etaOf_eq_zero hℓ (le_of_lt (not_le.mp hlt)))

lemma gradient_psiOf {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : E3) :
    gradient (psiOf ℓ) x = (2 / ℓ ^ 2) • x := by
  have hfun : psiOf ℓ = fun y : E3 => ‖y‖ ^ 2 / ℓ ^ 2 :=
    funext fun y => psiOf_eq_norm_sq hℓ y
  rw [hfun]
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, real_inner_smul_left]
  have hs : (fun y : E3 => ‖y‖ ^ 2 / ℓ ^ 2)
      = (ℓ ^ 2)⁻¹ • (fun y : E3 => ‖y‖ ^ 2) := by
    funext y; simp [div_eq_inv_mul]
  rw [hs, fderiv_const_smul ((hasStrictFDerivAt_norm_sq x).differentiableAt) ((ℓ ^ 2)⁻¹)]
  rw [smul_apply]
  have hfn : fderiv ℝ (fun y : E3 => ‖y‖ ^ 2) x = (2 : ℕ) • innerSL ℝ x := by
    simpa [Pi.smul_apply] using congrFun (fderiv_norm_sq (F := E3)) x
  rw [hfn, smul_apply, innerSL_apply_apply]
  simp only [nsmul_eq_mul]
  ring

lemma norm_gradient_psiOf {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : E3) :
    ‖gradient (psiOf ℓ) x‖ = 2 * ‖x‖ / ℓ ^ 2 := by
  rw [gradient_psiOf hℓ x, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2 / ℓ ^ 2)]
  ring

lemma gradient_etaOf (ℓ : ℝ) (x : E3) :
    gradient (etaOf ℓ) x = deriv Phi (psiOf ℓ x) • gradient (psiOf ℓ) x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, real_inner_smul_left]
  have hcomp : fderiv ℝ (etaOf ℓ) x
      = (fderiv ℝ Phi (psiOf ℓ x)) ∘SL (fderiv ℝ (psiOf ℓ) x) := by
    rw [show (etaOf ℓ) = Phi ∘ psiOf ℓ from rfl]
    exact fderiv_comp x (contDiff_Phi.differentiable (by norm_num)).differentiableAt
      ((contDiff_psiOf ℓ).differentiable (by norm_num)).differentiableAt
  rw [hcomp, ContinuousLinearMap.comp_apply,
    show fderiv ℝ Phi (psiOf ℓ x)
      = ContinuousLinearMap.toSpanSingleton ℝ (deriv Phi (psiOf ℓ x)) from
      (hasDerivAt_Phi (psiOf ℓ x)).hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, ← inner_gradient_left]
  ring

lemma etaGrad_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (hb : ∀ u, |deriv Phi u| ≤ 15 / 16)
    (x : E3) : ‖gradient (etaOf ℓ) x‖ ^ 2 ≤ 15 / ℓ ^ 2 := by
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  rw [gradient_etaOf ℓ x, norm_smul, Real.norm_eq_abs, norm_gradient_psiOf hℓne x]
  by_cases h4 : psiOf ℓ x ≤ 4
  · have hx4 : 2 * ‖x‖ / ℓ ^ 2 ≤ 4 / ℓ := by
      rw [psiOf_eq_norm_sq hℓne] at h4
      have h2 : ‖x‖ ^ 2 ≤ 4 * ℓ ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at h4; linarith
      have h3 : ‖x‖ ≤ 2 * ℓ := by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 2 * ℓ), h2, hℓ]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg x, hℓ]
    have hb' : |deriv Phi (psiOf ℓ x)| ≤ 15 / 16 := hb _
    have h5 : |deriv Phi (psiOf ℓ x)| * (2 * ‖x‖ / ℓ ^ 2) ≤ (15 / 16) * (4 / ℓ) :=
      mul_le_mul hb' hx4 (by positivity) (by positivity)
    have h6 : ((15:ℝ) / 16) * (4 / ℓ) = 15 / (4 * ℓ) := by field_simp; ring
    have h7 : (15 / (4 * ℓ)) ^ 2 = 225 / (16 * ℓ ^ 2) := by field_simp; ring
    have h8 : ((|deriv Phi (psiOf ℓ x)| * (2 * ‖x‖ / ℓ ^ 2)) ^ 2)
        ≤ (15 / (4 * ℓ)) ^ 2 := by
      have h := mul_self_le_mul_self
        (show (0:ℝ) ≤ |deriv Phi (psiOf ℓ x)| * (2 * ‖x‖ / ℓ ^ 2) by positivity) h5
      rw [h6] at h
      simpa [sq] using h
    rw [h7] at h8
    have h9 : (225:ℝ) / (16 * ℓ ^ 2) ≤ 15 / ℓ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · push_neg at h4
    rw [deriv_Phi_eq_zero h4, abs_zero, zero_mul, sq, mul_zero]
    positivity

lemma etaGrad_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : 2 * ℓ < ‖x‖) :
    gradient (etaOf ℓ) x = 0 := by
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  rw [gradient_etaOf ℓ x, deriv_Phi_eq_zero (u := psiOf ℓ x) ?_, zero_smul]
  rw [psiOf_eq_norm_sq hℓne, lt_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg x]

lemma gradient_mul_apply {η φ : E3 → ℝ} {x : E3}
    (hη : DifferentiableAt ℝ η x) (hφ : DifferentiableAt ℝ φ x) :
    gradient (fun y => η y * φ y) x = η x • gradient φ x + φ x • gradient η x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradient_left, inner_gradient_left, fderiv_fun_mul hη hφ]
  simp [smul_apply, add_apply, smul_eq_mul, mul_comm]

lemma continuous_gradient {f : E3 → ℝ} (h : Continuous (fderiv ℝ f)) : Continuous (gradient f) := by
  have hc : gradient f = (InnerProductSpace.toDual ℝ E3).symm ∘ (fderiv ℝ f) := rfl
  rw [hc]
  exact (InnerProductSpace.toDual ℝ E3).symm.continuous.comp h

lemma gradient_periodic {ℓ : ℝ} {φ : E3 → ℝ}
    (hper : ∀ (n : Fin 3 → ℤ) (x : E3), φ (x + lat ℓ n) = φ x)
    (hφ : Differentiable ℝ φ) (n : Fin 3 → ℤ) (x : E3) :
    gradient φ (x + lat ℓ n) = gradient φ x := by
  have hkey : fderiv ℝ φ (x + lat ℓ n) = fderiv ℝ φ x := by
    have hfun : (fun y : E3 => φ (y + lat ℓ n)) = φ := funext fun y => hper n y
    have h1 : fderiv ℝ (fun y : E3 => φ (y + lat ℓ n)) x
        = fderiv ℝ φ (x + lat ℓ n) ∘SL fderiv ℝ (fun y : E3 => y + lat ℓ n) x :=
      fderiv_comp x (hφ (x + lat ℓ n)) (differentiableAt_id.add_const _)
    have h2 : fderiv ℝ (fun y : E3 => y + lat ℓ n) x = ContinuousLinearMap.id ℝ E3 :=
      ((hasFDerivAt_id x).add_const _).fderiv
    rw [hfun, h2, ContinuousLinearMap.comp_id] at h1
    exact h1.symm
  apply (InnerProductSpace.toDual ℝ E3).injective
  rw [toDual_gradient, toDual_gradient, hkey]

lemma hasCompactSupport_gradient_etaOf {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasCompactSupport (gradient (etaOf ℓ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * ℓ))
    (isCompact_closedBall 0 (2 * ℓ)) ?_
  intro x hx
  simp only [Function.mem_support, Metric.mem_closedBall, dist_zero_right] at hx ⊢
  by_contra hlt
  exact hx (etaGrad_zero hℓ (not_le.mp hlt))

lemma norm_gradient_mul_le {η φ : E3 → ℝ} {x : E3}
    (hη : DifferentiableAt ℝ η x) (hφ : DifferentiableAt ℝ φ x) (hη0 : 0 ≤ η x) :
    ‖gradient (fun y => η y * φ y) x‖ ^ 2
      ≤ 2 * (η x) ^ 2 * ‖gradient φ x‖ ^ 2 + 2 * (φ x) ^ 2 * ‖gradient η x‖ ^ 2 := by
  rw [gradient_mul_apply hη hφ]
  have haux : ∀ a b : E3, ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h1 := norm_add_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]
  refine le_trans (haux _ _) (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0, mul_pow]; ring_nf; linarith
  · rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring_nf; linarith


lemma localise_ineq {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hST : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ 45 / 16)
    (hPer : ∀ {B : ℝ}, 0 ≤ B → ∀ {g u : E3 → ℝ},
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ B) → (∀ x, 2 * ℓ < ‖x‖ → g x = 0) →
      Continuous g → (∀ x, 0 ≤ u x) → Continuous u →
      (∀ (n : Fin 3 → ℤ) (x : E3), u (x + lat ℓ n) = u x) →
      ∫ x, g x * u x ≤ 125 * B * ∫ y in cell ℓ, u y)
    (φ : E3 → ℝ) (hperφ : ∀ (n : Fin 3 → ℤ) (x : E3), φ (x + lat ℓ n) = φ x)
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x, ‖gradient (fun y => etaOf ℓ y * φ y) x‖ ^ 2
      ≤ 4000 * ((∫ x in boxL ℓ, ‖gradient φ x‖ ^ 2)
          + (ℓ ^ 2)⁻¹ * (∫ x in boxL ℓ, (φ x) ^ 2)) := by
  have hPhid : ∀ u, |deriv Phi u| ≤ 15 / 16 := deriv_Phi_bound hST
  have hηc : Continuous (etaOf ℓ) := (contDiff_etaOf ℓ).continuous
  have hφc : Continuous φ := hφ.continuous
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hηd : Differentiable ℝ (etaOf ℓ) := (contDiff_etaOf ℓ).differentiable (by norm_num)
  have hgradphic : Continuous (gradient φ) :=
    continuous_gradient (hφ.continuous_fderiv (by norm_num))
  have hgradetac : Continuous (gradient (etaOf ℓ)) :=
    continuous_gradient ((contDiff_etaOf ℓ).continuous_fderiv (by norm_num))
  -- integrability of the two pieces
  have hg1cs : HasCompactSupport (fun x : E3 => (etaOf ℓ x) ^ 2) :=
    (hasCompactSupport_etaOf hℓ).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hint1 : Integrable (fun x : E3 => (etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hηc.pow 2).mul ((hgradphic.norm).pow 2)
    · exact hg1cs.mul_right
  have hgnorm : HasCompactSupport (fun x : E3 => ‖gradient (etaOf ℓ) x‖ ^ 2) :=
    (hasCompactSupport_gradient_etaOf hℓ).comp_left (g := fun v : E3 => ‖v‖ ^ 2) (by norm_num)
  have hint2 : Integrable (fun x : E3 => (φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hφc.pow 2).mul ((hgradetac.norm).pow 2)
    · exact hgnorm.mul_left
  -- pointwise bound
  have hpt : ∀ x : E3, ‖gradient (fun y => etaOf ℓ y * φ y) x‖ ^ 2
      ≤ 2 * ((etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2)
        + 2 * ((φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2) := by
    intro x
    have h := norm_gradient_mul_le (η := etaOf ℓ) (φ := φ) (x := x)
      (hηd x) (hφd x) (etaOf_mem ℓ x).1
    linarith [h]
  have hRHS : Integrable (fun x : E3 =>
      2 * ((etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2)
        + 2 * ((φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2)) :=
    (hint1.const_mul 2).add (hint2.const_mul 2)
  have hstep1 : ∫ x, ‖gradient (fun y => etaOf ℓ y * φ y) x‖ ^ 2
      ≤ 2 * (∫ x, (etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2)
        + 2 * (∫ x, (φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2) := by
    have hm := integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hRHS
      (ae_of_all _ hpt)
    rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2),
      integral_const_mul, integral_const_mul] at hm
    exact hm
  -- the two periodisation bounds
  have hA : ∫ x, (etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2
      ≤ 125 * 1 * ∫ y in cell ℓ, ‖gradient φ y‖ ^ 2 := by
    refine hPer (B := 1) (g := fun x => (etaOf ℓ x) ^ 2) (u := fun x => ‖gradient φ x‖ ^ 2)
      (by norm_num) (fun x => sq_nonneg _) ?_ ?_ ?_ (fun x => by positivity)
      ((hgradphic.norm).pow 2) ?_
    · intro x; nlinarith [(etaOf_mem ℓ x).1, (etaOf_mem ℓ x).2]
    · intro x hx; rw [etaOf_eq_zero hℓ (le_of_lt hx)]; norm_num
    · exact hηc.pow 2
    · intro n x; rw [gradient_periodic hperφ hφd n x]
  have hB : ∫ x, (φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2
      ≤ 125 * (15 / ℓ ^ 2) * ∫ y in cell ℓ, (φ y) ^ 2 := by
    have key : ∫ x, ‖gradient (etaOf ℓ) x‖ ^ 2 * (φ x) ^ 2
        ≤ 125 * (15 / ℓ ^ 2) * ∫ y in cell ℓ, (φ y) ^ 2 := by
      refine hPer (B := 15 / ℓ ^ 2) (g := fun x => ‖gradient (etaOf ℓ) x‖ ^ 2)
        (u := fun x => (φ x) ^ 2)
        (by positivity) (fun x => sq_nonneg _) (fun x => etaGrad_bound hℓ hPhid x)
        ?_ ((hgradetac.norm).pow 2) (fun x => sq_nonneg _) (hφc.pow 2) ?_
      · intro x hx; rw [etaGrad_zero hℓ hx]; simp
      · intro n x; rw [hperφ n x]
    rwa [show (fun x : E3 => ‖gradient (etaOf ℓ) x‖ ^ 2 * (φ x) ^ 2)
        = (fun x : E3 => (φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2) from
      funext fun x => mul_comm _ _] at key
  -- nonnegativity of the two box integrals
  have hI1 : 0 ≤ ∫ y in boxL ℓ, ‖gradient φ y‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_boxL ℓ) (fun y _ => by positivity)
  have hI2 : 0 ≤ ∫ y in boxL ℓ, (φ y) ^ 2 :=
    setIntegral_nonneg (measurableSet_boxL ℓ) (fun y _ => sq_nonneg _)
  calc ∫ x, ‖gradient (fun y => etaOf ℓ y * φ y) x‖ ^ 2
      ≤ 2 * (∫ x, (etaOf ℓ x) ^ 2 * ‖gradient φ x‖ ^ 2)
        + 2 * (∫ x, (φ x) ^ 2 * ‖gradient (etaOf ℓ) x‖ ^ 2) := hstep1
    _ ≤ 2 * (125 * 1 * ∫ y in boxL ℓ, ‖gradient φ y‖ ^ 2)
        + 2 * (125 * (15 / ℓ ^ 2) * ∫ y in boxL ℓ, (φ y) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ ≤ 4000 * ((∫ x in boxL ℓ, ‖gradient φ x‖ ^ 2)
          + (ℓ ^ 2)⁻¹ * (∫ x in boxL ℓ, (φ x) ^ 2)) := by
        have hp : (0:ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
        have h2 : (0:ℝ) ≤ (ℓ ^ 2)⁻¹ * ∫ y in boxL ℓ, (φ y) ^ 2 := mul_nonneg hp hI2
        have e2 : 2 * (125 * (15 / ℓ ^ 2) * ∫ y in boxL ℓ, (φ y) ^ 2)
            = 3750 * ((ℓ ^ 2)⁻¹ * ∫ y in boxL ℓ, (φ y) ^ 2) := by
          ring_nf
        have e1 : 2 * (125 * 1 * ∫ y in boxL ℓ, ‖gradient φ y‖ ^ 2)
            = 250 * ∫ y in boxL ℓ, ‖gradient φ y‖ ^ 2 := by ring
        rw [e1, e2]
        rw [mul_add]
        linarith [hI1, h2]

end Work.BoseFixR
