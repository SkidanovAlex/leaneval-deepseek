import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Cauchy.bmCz.integrableOn_bmDzKernel_mul_sub
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy.bmCz

/-! ## Integration by parts for the `(1,0)`-operator `dCoord` -/

/-- **Integration by parts for the flat `∂`-operator on `ℂⁿ`.** -/
theorem integral_mul_dCoord_eq_neg {n : ℕ} (k : Fin n) {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (h1u : MeasureTheory.Integrable (fun x => fderiv ℝ u x (Pi.single k 1) * v x) MeasureTheory.volume)
    (hIu : MeasureTheory.Integrable (fun x => fderiv ℝ u x (Pi.single k Complex.I) * v x) MeasureTheory.volume)
    (h1v : MeasureTheory.Integrable (fun x => u x * fderiv ℝ v x (Pi.single k 1)) MeasureTheory.volume)
    (hIv : MeasureTheory.Integrable (fun x => u x * fderiv ℝ v x (Pi.single k Complex.I)) MeasureTheory.volume)
    (huv : MeasureTheory.Integrable (fun x => u x * v x) MeasureTheory.volume) :
    ∫ x, u x * dCoord k v x = -∫ x, dCoord k u x * v x := by
  have hudiff : ∀ x ∈ tsupport v, DifferentiableAt ℝ u x := fun x _ =>
    (hu.differentiable (by norm_num)).differentiableAt
  have hvdiff : ∀ x ∈ tsupport u, DifferentiableAt ℝ v x := fun x _ =>
    (hv.differentiable (by norm_num)).differentiableAt
  have hIBP1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k (1 : ℂ)) h1u h1v huv hudiff hvdiff
  have hIBPI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k Complex.I) hIu hIv huv hudiff hvdiff
  have hcongr1 : (fun x => u x * dCoord k v x)
      = fun x => (1 / 2 : ℂ) * (u x * fderiv ℝ v x (Pi.single k 1))
          - (1 / 2 * Complex.I) * (u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    funext x; simp only [dCoord]; ring
  have hL : ∫ x, u x * dCoord k v x
      = (1 / 2 : ℂ) * (∫ x, u x * fderiv ℝ v x (Pi.single k 1))
        - (1 / 2 * Complex.I) * (∫ x, u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    rw [hcongr1, integral_sub (h1v.const_mul _) (hIv.const_mul _), integral_const_mul,
      integral_const_mul]
  have hcongr2 : (fun x => dCoord k u x * v x)
      = fun x => (1 / 2 : ℂ) * (fderiv ℝ u x (Pi.single k 1) * v x)
          - (1 / 2 * Complex.I) * (fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    funext x; simp only [dCoord]; ring
  have hR : ∫ x, dCoord k u x * v x
      = (1 / 2 : ℂ) * (∫ x, fderiv ℝ u x (Pi.single k 1) * v x)
        - (1 / 2 * Complex.I) * (∫ x, fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    rw [hcongr2, integral_sub (h1u.const_mul _) (hIu.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hL, hR, hIBP1, hIBPI]
  ring

/-! ## The `(1,0)`-calculus -/

/-- The Fréchet derivative of the anti-holomorphic coordinate `w ↦ \bar w_k`. -/
lemma hasFDerivAt_star_coord {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    HasFDerivAt (fun w : Fin n → ℂ => star (w k))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)) z := by
  have h : (fun w : Fin n → ℂ => star (w k))
      = ⇑((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)) := by
    funext w; simp [ContinuousLinearMap.comp_apply]
  rw [h]
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)).hasFDerivAt

lemma differentiableAt_star_coord {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun w : Fin n → ℂ => star (w k)) z :=
  (hasFDerivAt_star_coord k z).differentiableAt

/-- Leibniz rule for the `(1,0)`-operator `∂_j = dCoord j`. -/
theorem dCoord_mul {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord j (fun w => u w * v w) z = dCoord j u z * v z + u z * dCoord j v z := by
  have hmul : (fun w => u w * v w) = u * v := by funext w; rw [Pi.mul_apply]
  rw [hmul]
  have hfg : fderiv ℝ (u * v) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z := by
    simpa using (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  rw [dCoord, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dCoord, dCoord]
  ring

/-- The `(1,0)`-derivative of an anti-holomorphic coordinate vanishes. -/
theorem dCoord_apply_conj_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    dCoord j (fun w : Fin n → ℂ => star (w k)) z = 0 := by
  have hfd : fderiv ℝ (fun w : Fin n → ℂ => star (w k)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) k) := by
    have h1 : (fun w : Fin n → ℂ => star (w k))
        = ⇑((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) k)) := by
      funext w; simp [ContinuousLinearMap.comp_apply]
    rw [h1, ContinuousLinearMap.fderiv]
  rw [dCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  by_cases h : j = k
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
    norm_num [Complex.conjCLE_apply, Complex.conj_I, Complex.I_mul_I]
  · have hkj : k ≠ j := fun hc => h hc.symm
    rw [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj]
    simp

/-- Radial chain rule for `∂`: `∂_k (Φ ∘ nrmSq) = Φ' · \bar z_k`. -/
lemma dCoord_comp_nrmSq {n : ℕ} (k : Fin n) {Φ : ℝ → ℝ} {Φ' : ℝ} {z : Fin n → ℂ}
    (hΦ : HasDerivAt Φ Φ' (nrmSq z)) :
    dCoord k (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ)) z = (Φ' : ℂ) * star (z k) := by
  have hns : DifferentiableAt ℝ nrmSq z := differentiableAt_nrmSq z
  have hg : DifferentiableAt ℝ (fun x : Fin n → ℂ => Φ (nrmSq x)) z :=
    hΦ.differentiableAt.comp z hns
  have hfd : fderiv ℝ (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ)) z
      = Complex.ofRealCLM ∘L (ContinuousLinearMap.toSpanSingleton ℝ Φ' ∘L fderiv ℝ nrmSq z) := by
    have h1 : fderiv ℝ (fun x : Fin n → ℂ => Φ (nrmSq x)) z
        = ContinuousLinearMap.toSpanSingleton ℝ Φ' ∘L fderiv ℝ nrmSq z := by
      rw [show (fun x : Fin n → ℂ => Φ (nrmSq x)) = Φ ∘ nrmSq from rfl,
        fderiv_comp z hΦ.differentiableAt hns, hΦ.hasFDerivAt.fderiv]
    rw [show (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ))
          = (⇑Complex.ofRealCLM) ∘ (fun x : Fin n → ℂ => Φ (nrmSq x)) from rfl,
      fderiv_comp z Complex.ofRealCLM.differentiableAt hg, h1, ContinuousLinearMap.fderiv]
  rw [dCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Complex.ofRealCLM_apply]
  rw [fderiv_nrmSq_single_one k z, fderiv_nrmSq_single_I k z]
  have hconj : star (z k) = ((z k).re : ℂ) - ((z k).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  rw [hconj]; push_cast; ring

/-- `∂_k` of the complexified squared norm is `\bar z_k`. -/
lemma dCoord_nrmSq {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    dCoord k (fun x : Fin n → ℂ => ((nrmSq x : ℝ) : ℂ)) z = star (z k) := by
  have h := dCoord_comp_nrmSq (n := n) k (Φ := fun t : ℝ => t) (Φ' := 1) (z := z)
    (hasDerivAt_id (nrmSq z))
  simpa using h

/-- `∂_k` of `z ↦ nrmSq z + c` is `\bar z_k`. -/
lemma dCoord_nrmSq_add {n : ℕ} (k : Fin n) (c : ℝ) (z : Fin n → ℂ) :
    dCoord k (fun x : Fin n → ℂ => ((nrmSq x + c : ℝ) : ℂ)) z = star (z k) := by
  have h1 : HasDerivAt (fun t : ℝ => t + c) (1 + 0) (nrmSq z) :=
    (hasDerivAt_id (nrmSq z)).add (hasDerivAt_const (nrmSq z) c)
  have h := dCoord_comp_nrmSq (n := n) k (Φ := fun t : ℝ => t + c) (Φ' := 1) (z := z)
    (by simpa using h1)
  simpa using h

/-- Chain rule for `∂_k` and a complex power. -/
lemma dCoord_zpow {n : ℕ} (k : Fin n) (m : ℤ) {u : (Fin n → ℂ) → ℂ} (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (huz : u z ≠ 0) :
    dCoord k (fun x => (u x) ^ m) z = ((m : ℂ) * (u z) ^ (m - 1)) * dCoord k u z := by
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
  rw [dCoord, dCoord, hfder]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `∂_k` of the radial weight `(nrmSq + ε²)^{-n}`. -/
lemma dCoord_radial {n : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin n) (z : Fin n → ℂ) :
    dCoord k (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))) z
      = -((n : ℂ) * star (z k)) / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1) := by
  have hGdiff : DifferentiableAt ℝ (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z := by
    have hsum : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ)))
        = fun x => ((nrmSq x : ℝ) : ℂ) + ((ε ^ 2 : ℝ) : ℂ) := by
      funext x; simp [Complex.ofReal_add]
    rw [hsum]
    exact (BmEpsAux.differentiableAt_nrmSq_complex z).add (differentiableAt_const ((ε ^ 2 : ℝ) : ℂ))
  have hGz : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z ≠ 0 := by
    show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
  have hexp : (-(n:ℤ) - 1 : ℤ) = -(((n+1:ℕ):ℤ)) := by omega
  rw [dCoord_zpow k (-(n:ℤ)) z hGdiff hGz]
  rw [show dCoord k (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z = star (z k) from
    dCoord_nrmSq_add k (ε^2) z]
  rw [show ((↑(-(n:ℤ)) : ℂ)) = -(n : ℂ) by push_cast; ring]
  rw [show (((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (-(n:ℤ) - 1))
      = (((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ (n + 1))⁻¹ by
    rw [hexp, zpow_neg, zpow_natCast]]
  rw [div_eq_mul_inv]
  ring

/-! ## The regularised `(1,0)`-derivative of the Bochner–Martinelli kernel -/

/-- The regularised `∂_{z_k}` of the Bochner–Martinelli kernel component. -/
def bmDzKerEps {n : ℕ} (j k : Fin n) (ε : ℝ) (x : Fin n → ℂ) : ℂ :=
  -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)
    / ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))

/-- `(eucNorm x)^{2n+2} = (nrmSq x)^{n+1}` as complex numbers. -/
lemma eucNorm_pow_eq_nrmSq {n : ℕ} (x : Fin n → ℂ) :
    ((eucNorm x : ℂ)) ^ (2 * n + 2) = (((nrmSq x : ℝ)) : ℂ) ^ (n + 1) := by
  have h2 : ((eucNorm x : ℂ)) ^ 2 = ((nrmSq x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, nrmSq_eq_eucNorm_sq]
  rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, h2]

/-- Rewriting the `(1,0)`-derivative of the kernel with the squared Euclidean norm. -/
lemma bmDzKernel_eq_nrmSq {n : ℕ} (j k : Fin n) (x : Fin n → ℂ) :
    bmDzKernel j k x = -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)
      / ((((nrmSq x : ℝ)) : ℂ) ^ (n + 1)) := by
  rw [bmDzKernel, eucNorm_pow_eq_nrmSq]
  ring

lemma nrmSq_smul_I {n : ℕ} (x : Fin n → ℂ) : nrmSq (Complex.I • x) = nrmSq x := by
  simp only [nrmSq, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]

/-- `bmDzKerEps` changes sign under the quarter turn `x ↦ i·x`. -/
lemma bmDzKerEps_smul_I {n : ℕ} (j k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    bmDzKerEps j k ε (Complex.I • x) = - bmDzKerEps j k ε x := by
  simp only [bmDzKerEps, nrmSq_smul_I, Pi.smul_apply, smul_eq_mul]
  rw [map_mul, map_mul, Complex.conj_I]
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  ring_nf
  rw [hI]
  ring

/-- `bmDzKerEps` is continuous for `ε > 0`. -/
lemma continuous_bmDzKerEps {n : ℕ} (j k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : Fin n → ℂ => bmDzKerEps j k ε x) := by
  have hpow : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1) ≠ 0 := by
    intro x
    apply pow_ne_zero
    have hp : 0 < nrmSq x + ε ^ 2 := add_pos_of_nonneg_of_pos (nrmSq_nonneg x) (sq_pos_of_ne_zero hε.ne')
    exact_mod_cast hp.ne'
  have hnum : Continuous
      (fun x : Fin n → ℂ => -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)) := by
    have hj : Continuous fun x : Fin n → ℂ => starRingEnd ℂ (x j) := by
      simp only [starRingEnd_apply]
      exact continuous_star.comp (continuous_apply j)
    have hk : Continuous fun x : Fin n → ℂ => starRingEnd ℂ (x k) := by
      simp only [starRingEnd_apply]
      exact continuous_star.comp (continuous_apply k)
    exact (continuous_const.mul hj).mul hk
  have hden : Continuous (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))) :=
    (Complex.continuous_ofReal.comp (continuous_nrmSq.add continuous_const)).pow (n + 1)
  exact Continuous.div hnum hden hpow

/-- Pointwise convergence of the regularised kernel to `bmDzKernel` as `ε → 0⁺`. -/
lemma bmDzKerEps_tendsto {n : ℕ} (j k : Fin n) (x : Fin n → ℂ) :
    Filter.Tendsto (fun ε : ℝ => bmDzKerEps j k ε x) (𝓝[>] (0 : ℝ)) (𝓝 (bmDzKernel j k x)) := by
  rw [bmDzKernel_eq_nrmSq]
  simp only [bmDzKerEps]
  rcases eq_or_ne x 0 with rfl | hx
  · have h : ∀ ε : ℝ,
        -((n : ℂ)) * starRingEnd ℂ ((0 : Fin n → ℂ) j) * starRingEnd ℂ ((0 : Fin n → ℂ) k)
          / ((((nrmSq (0 : Fin n → ℂ) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) = 0 := by
      intro ε; simp [nrmSq, starRingEnd_apply]
    have h0 : -((n : ℂ)) * starRingEnd ℂ ((0 : Fin n → ℂ) j) * starRingEnd ℂ ((0 : Fin n → ℂ) k)
        / ((((nrmSq (0 : Fin n → ℂ) : ℝ)) : ℂ) ^ (n + 1)) = 0 := by
      simp [nrmSq, starRingEnd_apply]
    rw [h0]
    simpa only [h] using (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  · have hden : ((((nrmSq x : ℝ)) : ℂ) ^ (n + 1)) ≠ 0 := by
      apply pow_ne_zero; rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (nrmSq_pos hx)
    have h1 : Filter.Tendsto (fun ε : ℝ => nrmSq x + ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (nrmSq x)) := by
      have hc : Continuous (fun ε : ℝ => nrmSq x + ε ^ 2) := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun ε : ℝ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 (((nrmSq x : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (nrmSq x)).comp h1
    have h3 : Filter.Tendsto (fun ε : ℝ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((((nrmSq x : ℝ)) : ℂ) ^ (n + 1))) := Filter.Tendsto.pow h2 (n + 1)
    exact Filter.Tendsto.div tendsto_const_nhds h3 hden

/-- The regularised kernel is dominated by the singular one. -/
lemma norm_bmDzKerEps_le {n : ℕ} (j k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    ‖bmDzKerEps j k ε x‖ ≤ ‖bmDzKernel j k x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [bmDzKerEps, bmDzKernel, nrmSq]
  · have hpos : 0 < nrmSq x := nrmSq_pos hx
    have hle : nrmSq x ≤ nrmSq x + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
    have hξ : ‖(((nrmSq x + ε ^ 2 : ℝ)) : ℂ)‖ = nrmSq x + ε ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (le_of_lt hpos) hle)]
    have hη : ‖(((nrmSq x : ℝ)) : ℂ)‖ = nrmSq x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
    rw [bmDzKerEps, bmDzKernel_eq_nrmSq]
    simp only [norm_div, norm_mul, norm_neg, norm_pow, hξ, hη]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos (n + 1))
      (pow_le_pow_left₀ (le_of_lt hpos) hle (n + 1))

/-- The `(1,0)`-derivative of the regularised Bochner–Martinelli kernel. -/
theorem dCoord_bmKerEps {n : ℕ} {ε : ℝ} (hε : 0 < ε) (k j : Fin n) (z : Fin n → ℂ) :
    dCoord j (bmKerEps k ε) z = bmDzKerEps j k ε z := by
  have hfun : bmKerEps k ε
      = fun x : Fin n → ℂ => star (x k) * ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ))) := by
    funext x
    rw [bmKerEps_eq_zpow, Complex.ofReal_zpow]
  rw [hfun]
  have hu : DifferentiableAt ℝ (fun w : Fin n → ℂ => star (w k)) z :=
    differentiableAt_star_coord k z
  have hv : DifferentiableAt ℝ
      (fun w : Fin n → ℂ => ((((nrmSq w + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))) z := by
    have hGdiff : DifferentiableAt ℝ (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z := by
      have hsum : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ)))
          = fun x => ((nrmSq x : ℝ) : ℂ) + ((ε ^ 2 : ℝ) : ℂ) := by
        funext x; simp [Complex.ofReal_add]
      rw [hsum]
      exact (BmEpsAux.differentiableAt_nrmSq_complex z).add (differentiableAt_const ((ε ^ 2 : ℝ) : ℂ))
    have hGz : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z ≠ 0 := by
      show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
    exact BmEpsAux.differentiableAt_zpow_comp z (-(n:ℤ)) hGdiff hGz
  rw [dCoord_mul j _ _ z hu hv]
  rw [dCoord_apply_conj_coord j k z, zero_mul, zero_add]
  rw [dCoord_radial hε j z]
  simp only [bmDzKerEps, starRingEnd_apply]
  ring

/-! ## Support and integrability helpers -/

/-- A function vanishing on `{x | R ≤ ‖x‖}` has compact support. -/
lemma hasCompactSupport_of_norm_le {n : ℕ} {f : (Fin n → ℂ) → ℂ} {R : ℝ}
    (h : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  exact hx (h x hcon.le)

/-- A continuous function times a continuous compactly supported one is integrable. -/
lemma integrable_mul_of_hasCompactSupport {n : ℕ} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x => a x * b x) volume :=
  (ha.mul hb).integrable_of_hasCompactSupport (hbc.mul_left (f := a))

/-- A function vanishing on `{x | R ≤ ‖x‖}` is zero near points with `R < ‖x‖`. -/
lemma fderiv_eq_zero_of_lt {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) {x : Fin n → ℂ} (hx : R < ‖x‖) :
    fderiv ℝ g x = 0 := by
  have hopen : IsOpen {y : Fin n → ℂ | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hg0 : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hsupp y hy.le
  have hfd : HasFDerivAt g (0 : (Fin n → ℂ) →L[ℝ] ℂ) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).congr_of_eventuallyEq hg0
  exact hfd.fderiv

/-- The directional derivative of a function vanishing outside a ball is compactly supported. -/
lemma hasCompactSupport_fderiv_apply {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
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
lemma contDiff_one_bmKerEps {n : ℕ} (k : Fin n) {ε : ℝ} (hε : 0 < ε) :
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
    have hpos : (0 : ℝ) < nrmSq x + ε ^ 2 := by have := nrmSq_nonneg x; positivity
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
  show ContDiff ℝ 1
    (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)
  have hfun : (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)
      = (fun x : Fin n → ℂ => (starRingEnd ℂ) (x k))
        * (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)⁻¹ := by
    funext x; simp [div_eq_mul_inv]
  rw [hfun]
  exact ContDiff.mul hnum (ContDiff.inv hden hne)

/-- `dCoord k g` is continuous when `g` is `C¹`. -/
lemma continuous_dCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (k : Fin n) :
    Continuous (dCoord k g) := by
  have hf : Continuous fun z : Fin n → ℂ => fderiv ℝ g z := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (1 : ℂ)) :=
    hf.clm_apply continuous_const
  have h2 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (Complex.I)) :=
    hf.clm_apply continuous_const
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

lemma dCoord_eq_zero_of_lt_norm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) {x : Fin n → ℂ}
    (hx : R < ‖x‖) : dCoord k g x = 0 := by
  have hmem : {y : Fin n → ℂ | R < ‖y‖} ∈ 𝓝 x :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) hx
  have heq : g =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hmem] with y hy
    exact hsupp y hy.le
  have hfd : fderiv ℝ g x = 0 := by
    rw [heq.fderiv_eq]; simp
  unfold dCoord
  rw [hfd]; simp

lemma hasCompactSupport_dCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) :
    HasCompactSupport (dCoord k g) := by
  rw [HasCompactSupport]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n → ℂ) R)
    (isClosed_tsupport (dCoord k g)) (closure_minimal ?_ Metric.isClosed_closedBall)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push_neg at hlt
  exact hx (dCoord_eq_zero_of_lt_norm hsupp k hlt)

/-- Integrability of the kernel against a compactly supported `C¹` function. -/
lemma integrable_bmKernel_mul_dCoord {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k j : Fin n) :
    Integrable (fun x : Fin n → ℂ => bmKernel k x * dCoord j g x) := by
  have h1 : Integrable (fun x : Fin n → ℂ => dCoord j g x • bmKernel k x) :=
    (locallyIntegrable_bmKernel hn k).integrable_smul_left_of_hasCompactSupport
      (continuous_dCoord hg j) (hasCompactSupport_dCoord hsupp j)
  simpa only [smul_eq_mul, mul_comm] using h1

/-- Integrability of a continuous function on a Euclidean ball. -/
lemma integrableOn_eucBall_of_continuous {n : ℕ} {F : (Fin n → ℂ) → ℂ} (hF : Continuous F)
    (r : ℝ) : IntegrableOn F (eucBall (n := n) r) volume :=
  ((hF.continuousOn).integrableOn_compact (isCompact_closedBall (0 : Fin n → ℂ) r)).mono_set
    (eucBall_subset_ball.trans Metric.ball_subset_closedBall)

/-! ## The regularised identity -/

/-- The regularised `∂`-Bochner–Martinelli identity. -/
lemma bmKerEps_mul_dCoord_integral {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) {ε : ℝ} (hε : 0 < ε) (j k : Fin n) :
    ∫ x, bmKerEps k ε x * dCoord j g x = -∫ x, bmDzKerEps j k ε x * g x := by
  have hsupp' : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0 :=
    fun x hx => hsupp x (le_trans hx (pi_norm_le_eucNorm x))
  have hgc : HasCompactSupport g := hasCompactSupport_of_norm_le hsupp'
  have hg_cont : Continuous g := hg.continuous
  have hfdg_cont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hker_cont : Continuous (bmKerEps k ε) := (contDiff_one_bmKerEps k hε).continuous
  have hkerd_cont : Continuous
      (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single j 1)) :=
    ((contDiff_one_bmKerEps k hε).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hkerdI_cont : Continuous
      (fun x : Fin n → ℂ => fderiv ℝ (bmKerEps k ε) x (Pi.single j Complex.I)) :=
    ((contDiff_one_bmKerEps k hε).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hstep : ∫ x, bmKerEps k ε x * dCoord j g x
      = -∫ x, dCoord j (bmKerEps k ε) x * g x :=
    integral_mul_dCoord_eq_neg j (contDiff_one_bmKerEps k hε) hg
      (integrable_mul_of_hasCompactSupport hkerd_cont hg_cont hgc)
      (integrable_mul_of_hasCompactSupport hkerdI_cont hg_cont hgc)
      (integrable_mul_of_hasCompactSupport hker_cont
        (hfdg_cont.clm_apply continuous_const) (hasCompactSupport_fderiv_apply hsupp' (Pi.single j 1)))
      (integrable_mul_of_hasCompactSupport hker_cont
        (hfdg_cont.clm_apply continuous_const) (hasCompactSupport_fderiv_apply hsupp' (Pi.single j Complex.I)))
      (integrable_mul_of_hasCompactSupport hker_cont hg_cont hgc)
  rw [hstep]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [dCoord_bmKerEps hε k j x]

/-! ## The two limits -/

/-- The left-hand side converges to the singular integral. -/
lemma bmLhs_dCoord_tendsto {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) (k j : Fin n) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * dCoord j g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, bmKernel k x * dCoord j g x)) := by
  have hsupp' : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0 :=
    fun x hx => hsupp x (le_trans hx (pi_norm_le_eucNorm x))
  have hbdd : Integrable (fun x => ‖bmKernel k x * dCoord j g x‖) :=
    (integrable_bmKernel_mul_dCoord hn hg hsupp' k j).norm
  have hF : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun x : Fin n → ℂ => bmKerEps k ε x * dCoord j g x) volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_bmKerEps k (ne_of_gt hε)).mul (continuous_dCoord hg j)).aestronglyMeasurable
  have hbd : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ x : Fin n → ℂ ∂volume,
        ‖bmKerEps k ε x * dCoord j g x‖ ≤ ‖bmKernel k x * dCoord j g x‖ := by
    filter_upwards with ε
    filter_upwards with x
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_bmKerEps_le k ε x) (norm_nonneg _)
  have hlim : ∀ᵐ x : Fin n → ℂ ∂volume,
      Filter.Tendsto (fun ε : ℝ => bmKerEps k ε x * dCoord j g x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (bmKernel k x * dCoord j g x)) := by
    filter_upwards with x
    exact (bmKerEps_tendsto k x).mul_const (dCoord j g x)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖bmKernel k x * dCoord j g x‖) hF hbd hbdd hlim

/-- The integral of the regularised kernel over a Euclidean ball vanishes (rotation symmetry). -/
theorem integral_bmDzKerEps_eucBall_eq_zero {n : ℕ} (j k : Fin n) (ε r : ℝ) :
    ∫ x in eucBall (n := n) r, bmDzKerEps j k ε x = 0 := by
  classical
  let e : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    MeasurableEquiv.piCongrRight (fun _ : Fin n => rotI.toMeasurableEquiv)
  have hcoe : ⇑e = fun x : Fin n → ℂ => Complex.I • x := by
    funext x i
    simp [e, MeasurableEquiv.piCongrRight, rotI, Pi.smul_apply, smul_eq_mul]
  have hmap : Measure.map (⇑e) volume = volume := by
    rw [hcoe]; exact map_smul_I_volume
  have hpre : ⇑e ⁻¹' eucBall (n := n) r = eucBall (n := n) r := by
    ext x
    simp only [Set.mem_preimage, mem_eucBall]
    rw [hcoe, eucNorm_smul_I]
  have hpt : ∀ x : Fin n → ℂ, bmDzKerEps j k ε (⇑e x) = - bmDzKerEps j k ε x := by
    intro x; rw [hcoe]; exact bmDzKerEps_smul_I j k ε x
  have hsub := (e.measurableEmbedding).setIntegral_map (μ := volume)
    (bmDzKerEps j k ε) (eucBall (n := n) r)
  rw [hmap, hpre] at hsub
  have hsym : ∫ x in eucBall (n := n) r, bmDzKerEps j k ε x
      = - ∫ x in eucBall (n := n) r, bmDzKerEps j k ε x := by
    calc ∫ x in eucBall (n := n) r, bmDzKerEps j k ε x
        = ∫ x in eucBall (n := n) r, bmDzKerEps j k ε (⇑e x) := hsub
      _ = ∫ x in eucBall (n := n) r, - bmDzKerEps j k ε x :=
            setIntegral_congr_fun (measurableSet_eucBall r) (fun x _ => hpt x)
      _ = - ∫ x in eucBall (n := n) r, bmDzKerEps j k ε x := integral_neg _
  have h2 : (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x) * 2 = 0 := by
    have h3 : (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x)
        + (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x) = 0 := by
      nth_rewrite 1 [hsym]; abel
    rw [show (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x) * 2
        = (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x)
          + (∫ x in eucBall (n := n) r, bmDzKerEps j k ε x) from by ring]
    exact h3
  exact (mul_eq_zero.mp h2).resolve_right (by norm_num)


/-- The right-hand side converges to the subtracted kernel integral over the ball. -/
lemma bmRhs_dCoord_tendsto {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) (j k : Fin n) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, bmDzKerEps j k ε x * g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in eucBall (n := n) (4 * R), bmDzKernel j k x * (g x - g 0))) := by
  have hfull : ∀ ε : ℝ, ∫ x, bmDzKerEps j k ε x * g x
      = ∫ x in eucBall (n := n) (4 * R), bmDzKerEps j k ε x * g x := by
    intro ε
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := eucBall (n := n) (4 * R))
      (f := fun x => bmDzKerEps j k ε x * g x) ?_).symm
    intro x hx
    have h4 : 4 * R ≤ eucNorm x := not_lt.mp (fun hc => hx (by simpa [mem_eucBall] using hc))
    have hxR : R ≤ eucNorm x := by nlinarith [hR]
    rw [hsupp x hxR, mul_zero]
  have hball : ∀ ε : ℝ, 0 < ε →
      (∫ x in eucBall (n := n) (4 * R), bmDzKerEps j k ε x * g x)
      = ∫ x in eucBall (n := n) (4 * R), bmDzKerEps j k ε x * (g x - g 0) := by
    intro ε hε
    have hpt : ∀ x : Fin n → ℂ, bmDzKerEps j k ε x * g x
        = bmDzKerEps j k ε x * (g x - g 0) + g 0 * bmDzKerEps j k ε x := by
      intro x; ring
    rw [setIntegral_congr_fun (measurableSet_eucBall (4 * R)) (fun x _ => hpt x)]
    rw [integral_add]
    · rw [integral_const_mul, integral_bmDzKerEps_eucBall_eq_zero, mul_zero, add_zero]
    · exact integrableOn_eucBall_of_continuous
        ((continuous_bmDzKerEps j k hε).mul (hg.continuous.sub continuous_const)) (4 * R)
    · exact integrableOn_eucBall_of_continuous
        (continuous_const.mul (continuous_bmDzKerEps j k hε)) (4 * R)
  have heq : (fun ε : ℝ => ∫ x, bmDzKerEps j k ε x * g x)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε : ℝ => ∫ x in eucBall (n := n) (4 * R), bmDzKerEps j k ε x * (g x - g 0)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hfull ε, hball ε hε]
  have hDCT : Filter.Tendsto
      (fun ε : ℝ => ∫ x in eucBall (n := n) (4 * R), bmDzKerEps j k ε x * (g x - g 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in eucBall (n := n) (4 * R), bmDzKernel j k x * (g x - g 0))) := by
    have hbound_int : Integrable (fun x => ‖bmDzKernel j k x‖ * ‖g x - g 0‖)
        (volume.restrict (eucBall (n := n) (4 * R))) :=
      integrableOn_bmDzKernel_mul_sub hn j k g R hR hg hsupp
    have hres := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (eucBall (n := n) (4 * R)))
      (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (F := fun ε x => bmDzKerEps j k ε x * (g x - g 0))
      (f := fun x => bmDzKernel j k x * (g x - g 0))
      (fun x => ‖bmDzKernel j k x‖ * ‖g x - g 0‖) ?_ ?_ hbound_int ?_
    · exact hres
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((continuous_bmDzKerEps j k hε).mul (hg.continuous.sub continuous_const)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_bmDzKerEps_le j k ε x) (norm_nonneg _)
    · filter_upwards with x
      exact (bmDzKerEps_tendsto j k x).mul_const (g x - g 0)
  exact hDCT.congr' heq.symm

/-! ## The main theorem -/

theorem integral_bmKernel_mul_dCoord {n : ℕ} (hn : 0 < n) (j k : Fin n)
    (g : (Fin n → ℂ) → ℂ) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ 1 g → (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      ∫ x, bmKernel k x * Work.CR.Flat.dCoord j g x
        = -∫ x in eucBall (4 * R), bmDzKernel j k x * (g x - g 0) := by
  intro hg hsupp
  have hreg : (fun ε : ℝ => ∫ x, bmKerEps k ε x * dCoord j g x)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε : ℝ => -∫ x, bmDzKerEps j k ε x * g x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact bmKerEps_mul_dCoord_integral hn hR hg hsupp hε j k
  have hL := bmLhs_dCoord_tendsto hn hg hsupp k j
  have hRhs := (bmRhs_dCoord_tendsto hn hR hg hsupp j k).neg
  have hL2 : Filter.Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * dCoord j g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-∫ x in eucBall (n := n) (4 * R), bmDzKernel j k x * (g x - g 0))) :=
    hRhs.congr' hreg.symm
  exact tendsto_nhds_unique hL hL2

end Work.CR.Flat.Cauchy.bmCz
