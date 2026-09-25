import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.Transport
import Submission.Work.NN.Final.FlatDbarInstance
import Submission.Work.NN.Final.Proj
import Submission.Work.NN.Final.Estimate
import Submission.Work.NN.Final.exists_extension
import Submission.Work.NN.Final.Lcoef_holderNorm_zero
import Submission.Work.NN.Final.Lcoef_holderNorm_one
import Submission.Work.NN.Final.proj02_integrable_flat
import Submission.Work.NN.Final.antilinear_sub_stdForm_bound
import Submission.Work.NN.Core.Solver
import Submission.Work.NN.Core.SmallBall
import Submission.Work.NN.Assemble.Setup

namespace Work.NN.Final

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Work.NN.Core
open Set
open scoped ContDiff

noncomputable section

variable {n : ℕ}

/-- The model space `ℝ^{2n}`, as a local shorthand (the name `E` is taken in this namespace by
`Work.NN.Final.E` of the telescoping chapter). -/
abbrev EN (n : ℕ) := LeanEval.Geometry.NewlanderNirenberg.E n

/-! ## §1  The rescaled normalisation

The small-perturbation argument needs the perturbation to be small on a *fixed* polydisc.  The way
to achieve this for a given integrable structure is to rescale the normalising linear isomorphism
`T` (rather than the structure): if `Ts x = (μ:ℂ)⁻¹ • T x` then the transported structure `Jtr J Ts`
is the pullback of `Jtr J T` by the map `z ↦ μ • z`.  In particular it is again an almost complex
structure and again integrable, with no additional work
(`Work.NN.Final.proj02_integrable_flat`), and its perturbation `Atr J Ts` is small when `μ` is
small. -/

/-- Multiplication by `c` on `ℂⁿ = F n`, as a continuous real-linear equivalence. -/
noncomputable def Fscale (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    Submission.F n ≃L[ℝ] Submission.F n :=
  ContinuousLinearEquiv.equivOfInverse (c • (1 : Submission.F n →L[ℝ] Submission.F n))
    (c⁻¹ • (1 : Submission.F n →L[ℝ] Submission.F n))
    (fun x => by simp [smul_smul, hc]) (fun x => by simp [smul_smul, hc])

@[simp] lemma Fscale_apply (n : ℕ) (c : ℂ) (hc : c ≠ 0) (x : Submission.F n) :
    Fscale n c hc x = c • x := rfl

@[simp] lemma Fscale_symm_apply (n : ℕ) (c : ℂ) (hc : c ≠ 0) (x : Submission.F n) :
    (Fscale n c hc).symm x = c⁻¹ • x := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  rw [Fscale_apply]
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The normalisation `T`, scaled by `μ` on the target: `x ↦ (μ:ℂ)⁻¹ • T x`.  The transported
structure `Jtr J (Tsh T μ _)` is the pullback of `Jtr J T` by `z ↦ μ • z`. -/
noncomputable def Tsh (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ) (hμ : μ ≠ 0) :
    EN n ≃L[ℝ] Submission.F n :=
  T.trans (Fscale n ((μ : ℂ))⁻¹
    (by simpa using inv_ne_zero (show (μ : ℂ) ≠ 0 by exact_mod_cast hμ)))

@[simp] lemma Tsh_apply (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ) (hμ : μ ≠ 0) (x : EN n) :
    Tsh T μ hμ x = (μ : ℂ)⁻¹ • T x := by
  rw [Tsh, ContinuousLinearEquiv.trans_apply]
  rfl

lemma Tsh_symm_apply (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ) (hμ : μ ≠ 0)
    (y : Submission.F n) :
    (Tsh T μ hμ).symm y = T.symm ((μ : ℂ) • y) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  rw [Tsh_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [smul_smul, inv_mul_cancel₀ (show (μ : ℂ) ≠ 0 by exact_mod_cast hμ), one_smul]

lemma Tsh_intertwines (J : EN n → EN n →L[ℝ] EN n) (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ)
    (hμ : μ ≠ 0) (hT : ∀ v, T (J 0 v) = Complex.I • T v) (v : EN n) :
    Tsh T μ hμ (J 0 v) = Complex.I • Tsh T μ hμ v := by
  rw [Tsh_apply, hT, Tsh_apply]
  exact (smul_comm Complex.I ((μ : ℂ)⁻¹) (T v)).symm

/-- The differential of the rescaled normalisation is the rescaled differential. -/
lemma tupleDeriv_Tsh (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ) (hμ : μ ≠ 0) :
    tupleDeriv (Tsh T μ hμ) = ((μ : ℂ)⁻¹) • (tupleDeriv T) := by
  ext x y
  show (ecInvL n) (Tsh T μ hμ x) y = ((μ : ℂ)⁻¹ • (ecInvL n) (T x)) y
  rw [Tsh_apply, ecInvL_smul]

lemma tupleDerivInv_Tsh (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ) (hμ : μ ≠ 0) (z : Cn n) :
    tupleDerivInv (Tsh T μ hμ) z = tupleDerivInv T ((μ : ℂ) • z) := by
  show (Tsh T μ hμ).symm (ecL n z) = T.symm (ecL n ((μ : ℂ) • z))
  rw [Tsh_symm_apply, ecL_smul]

/-- **The perturbation of the rescaled structure is the rescaled perturbation.** -/
lemma Atr_Tsh_apply (J : EN n → EN n →L[ℝ] EN n) (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ)
    (hμ : μ ≠ 0) (z w : Cn n) :
    Atr J (Tsh T μ hμ) z w
      = ((μ : ℂ)⁻¹) • (Atr J T ((μ : ℂ) • z) ((μ : ℂ) • w)) := by
  rw [Atr_apply, Atr_apply, tupleDeriv_Tsh, tupleDerivInv_Tsh, tupleDerivInv_Tsh]
  rw [smul_apply, smul_sub]
  congr 1
  have hc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have key : (((μ : ℂ)⁻¹) * Complex.I) * (μ : ℂ) = Complex.I := by
    rw [mul_assoc, mul_comm Complex.I (μ : ℂ), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [smul_smul ((μ : ℂ)⁻¹) Complex.I ((μ : ℂ) • w),
      smul_smul (((μ : ℂ)⁻¹) * Complex.I) (μ : ℂ) w, key]

/-- The transported structure of the rescaled normalisation is the standard structure plus the
rescaled perturbation. -/
lemma Jstd_add_Atr_Tsh (J : EN n → EN n →L[ℝ] EN n) (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ)
    (hμ : μ ≠ 0) :
    Work.NN.Core.JstdCn n + Atr J (Tsh T μ hμ) = Jtr J (Tsh T μ hμ) := by
  ext z w x
  simp only [Pi.add_apply, add_apply, Atr_apply, JstdCn_apply, Jtr_apply, Pi.smul_apply,
    Pi.sub_apply]
  ring


/-! ## §2  Auxiliary lemmas for the rescaled perturbation -/

/-- `VecHolder` depends only on the values of the function. -/
lemma VecHolder_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Cn n → E} {α ε : ℝ} {S : Set (Cn n)} (h : ∀ z ∈ S, f z = g z)
    (hf : VecHolder f α ε S) : VecHolder g α ε S := by
  refine ⟨fun z hz => ?_, fun z hz z' hz' => ?_⟩
  · rw [← h z hz]; exact hf.1 z hz
  · rw [← h z hz, ← h z' hz']; exact hf.2 z hz z' hz'

/-- **The rescaled perturbation is the perturbation at the rescaled point.** -/
lemma Atr_Tsh_eq (J : EN n → EN n →L[ℝ] EN n) (T : EN n ≃L[ℝ] Submission.F n) (μ : ℝ)
    (hμ : μ ≠ 0) (z : Cn n) : Atr J (Tsh T μ hμ) z = Atr J T ((μ : ℂ) • z) := by
  ext w
  rw [Atr_Tsh_apply]
  have hc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have h1 : ((μ : ℂ) • w) = (μ : ℝ) • w := by simp
  rw [h1, map_smul]
  rw [show (μ : ℝ) • (Atr J T ((μ : ℂ) • z) w)
        = (μ : ℂ) • (Atr J T ((μ : ℂ) • z) w) from by simp]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The unit polydisc is star-shaped under real scalings `c ∈ [0,1]`. -/
lemma mem_pd_smul_one (z : Cn n) (hz : z ∈ pd n (fun _ => 1) 4) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : (c : ℂ) • z ∈ pd n (fun _ => 1) 4 := by
  rw [mem_pd] at hz ⊢
  intro j
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc0]
  calc c * ‖z j‖ ≤ 1 * ‖z j‖ := by nlinarith [norm_nonneg (z j)]
    _ = ‖z j‖ := one_mul _
    _ < 4 * 1 := by linarith [hz j]

/-- **Monotonicity in the scaling**: if the perturbation is `C^{0,α}`-small at the scale `μ'` on
`pd n (fun _ => 1) 4`, the same holds at every smaller scale `μ ≤ μ'`. -/
lemma VecHolder_scale_mono {A : Cn n → Cn n →L[ℝ] Cn n} {α ε : ℝ} {μ μ' : ℝ}
    (hα0 : 0 < α) (hε : 0 < ε) (hμ0 : 0 ≤ μ) (hμμ' : μ ≤ μ') (hμ'0 : 0 < μ')
    (h : VecHolder (fun z => A ((μ' : ℂ) • z)) α ε (pd n (fun _ => 1) 4)) :
    VecHolder (fun z => A ((μ : ℂ) • z)) α ε (pd n (fun _ => 1) 4) := by
  have hμ'ne : (μ' : ℝ) ≠ 0 := ne_of_gt hμ'0
  have hc0 : 0 ≤ μ / μ' := by positivity
  have hc1 : μ / μ' ≤ 1 := by rw [div_le_one hμ'0]; exact hμμ'
  have hscale : ((μ' : ℂ) * ((μ / μ' : ℝ) : ℂ)) = (μ : ℂ) := by
    rw [← Complex.ofReal_mul, mul_div_cancel₀ μ hμ'ne]
  have hkey : ∀ z : Cn n, A ((μ : ℂ) • z) = A ((μ' : ℂ) • (((μ / μ' : ℝ) : ℂ) • z)) := by
    intro z
    rw [smul_smul, hscale]
  have hle1 : (μ / μ') ^ α ≤ 1 := by
    calc (μ / μ') ^ α ≤ (1 : ℝ) ^ α := Real.rpow_le_rpow hc0 hc1 (le_of_lt hα0)
      _ = 1 := Real.one_rpow α
  constructor
  · intro z hz
    show ‖A ((μ : ℂ) • z)‖ ≤ ε
    rw [hkey z]
    exact h.1 _ (mem_pd_smul_one z hz (μ / μ') hc0 hc1)
  · intro z hz z' hz'
    show ‖A ((μ : ℂ) • z) - A ((μ : ℂ) • z')‖ ≤ ε * ‖z - z'‖ ^ α
    rw [hkey z, hkey z']
    refine (h.2 _ (mem_pd_smul_one z hz (μ / μ') hc0 hc1) _
      (mem_pd_smul_one z' hz' (μ / μ') hc0 hc1)).trans ?_
    have hsub : ((μ / μ' : ℝ) : ℂ) • z - ((μ / μ' : ℝ) : ℂ) • z'
        = ((μ / μ' : ℝ) : ℂ) • (z - z') := by rw [smul_sub]
    have hnorm : ‖((μ / μ' : ℝ) : ℂ) • (z - z')‖ = (μ / μ') * ‖z - z'‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    rw [hsub, hnorm, Real.mul_rpow hc0 (norm_nonneg _)]
    calc ε * ((μ / μ') ^ α * ‖z - z'‖ ^ α)
        ≤ ε * (1 * ‖z - z'‖ ^ α) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε)
          exact mul_le_mul_of_nonneg_right hle1 (Real.rpow_nonneg (norm_nonneg _) _)
      _ = ε * ‖z - z'‖ ^ α := by rw [one_mul]

/-- **The rescaled polydisc is inside the domain of the transported structure.**  For every
sufficiently small `μ > 0` the points `μ • z`, `z ∈ pd n (fun _ => 1) 4`, lie in `tupleDerivInv T ⁻¹' U`. -/
lemma exists_small_dom {U : Set (EN n)} {T : EN n ≃L[ℝ] Submission.F n} (hU : IsOpen U)
    (h0U : (0 : EN n) ∈ U) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z : Cn n, z ∈ pd n (fun _ => 1) 4 → tupleDerivInv T ((μ : ℂ) • z) ∈ U := by
  have hW : {w : Cn n | tupleDerivInv T w ∈ U} ∈ nhds (0 : Cn n) :=
    (hU.preimage (tupleDerivInv T).continuous).mem_nhds (by simpa using h0U)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨δ / 8, by linarith, fun μ hμ hμle z hz => ?_⟩
  apply hball
  rw [Metric.mem_ball, dist_zero_right, norm_smul]
  have hz4 : ‖z‖ ≤ 4 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    intro j
    rw [mem_pd] at hz
    linarith [hz j]
  have hμb : ‖(μ : ℂ)‖ ≤ δ / 8 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ]
    linarith
  calc ‖(μ : ℂ)‖ * ‖z‖ ≤ (δ / 8) * 4 := by
        exact mul_le_mul hμb hz4 (norm_nonneg _) (by linarith)
    _ < δ := by linarith

/-! ## §3  The transport of a `ℂⁿ`-frame to `E n` -/

/-- The chain rule for a tuple of functions composed with the linear map `tupleDeriv T`. -/
lemma fderiv_tuple_comp_tupleDeriv {u : Fin n → Cn n → ℂ} {T : EN n ≃L[ℝ] Submission.F n}
    {y : EN n} (hu : ∀ j, DifferentiableAt ℝ (u j) (tupleDeriv T y)) :
    fderiv ℝ (fun y : EN n => fun j => u j (tupleDeriv T y)) y
      = (fderiv ℝ (fun w : Cn n => fun j => u j w) (tupleDeriv T y)).comp (tupleDeriv T) := by
  have h1 : DifferentiableAt ℝ (fun w : Cn n => fun j => u j w) (tupleDeriv T y) :=
    differentiableAt_pi.2 hu
  have h2 : (fun y : EN n => fun j => u j (tupleDeriv T y))
      = ((fun w : Cn n => fun j => u j w) ∘ (tupleDeriv T)) := rfl
  rw [h2, fderiv_comp y h1 (tupleDeriv T).differentiableAt,
    ContinuousLinearMap.fderiv]


/-- `tupleDeriv T` is a bijection. -/
lemma bijective_tupleDeriv (T : EN n ≃L[ℝ] Submission.F n) :
    Function.Bijective (fun x : EN n => tupleDeriv T x) := by
  constructor
  · intro a b h
    have h2 := congrArg (fun z => tupleDerivInv T z) h
    have h3 : tupleDerivInv T (tupleDeriv T a) = tupleDerivInv T (tupleDeriv T b) := h2
    rwa [tupleDerivInv_tupleDeriv, tupleDerivInv_tupleDeriv] at h3
  · intro z
    exact ⟨tupleDerivInv T z, tupleDeriv_tupleDerivInv T z⟩


/-- **Smoothness of the transported perturbation.**  (Copy of the proof of the delegated lemma
`Work.NN.Final.Atr_contDiffOn`, stated here so that this module is independent of the module that
proves it.) -/
theorem Atr_contDiffOn_aux {n : ℕ} {U : Set (EN n)}
    {J : EN n → EN n →L[ℝ] EN n} {T : EN n ≃L[ℝ] Submission.F n} {k : ℕ∞}
    (hJ : ContDiffOn ℝ k J U) :
    ContDiffOn ℝ k (Atr J T) {z : Cn n | tupleDerivInv T z ∈ U} := by
  have hJinv : ContDiffOn ℝ (k : WithTop ℕ∞) (fun z : Cn n => J (tupleDerivInv T z))
      {z : Cn n | tupleDerivInv T z ∈ U} :=
    ContDiffOn.comp hJ ((ContinuousLinearMap.contDiff (tupleDerivInv T)).contDiffOn)
      (fun _ hz => hz)
  have h2 : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun z : Cn n => (J (tupleDerivInv T z)).comp (tupleDerivInv T))
      {z : Cn n | tupleDerivInv T z ∈ U} :=
    ContDiffOn.clm_comp hJinv (contDiffOn_const (c := tupleDerivInv T))
  have h3 : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun z : Cn n => (tupleDeriv T).comp ((J (tupleDerivInv T z)).comp (tupleDerivInv T)))
      {z : Cn n | tupleDerivInv T z ∈ U} :=
    ContDiffOn.clm_comp (contDiffOn_const (c := tupleDeriv T)) h2
  have h4 : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun _ : Cn n => (Complex.I • (1 : Cn n →L[ℝ] Cn n)))
      {z : Cn n | tupleDerivInv T z ∈ U} := contDiffOn_const
  exact (h3.sub h4).congr (fun _ _ => rfl)

end

end Work.NN.Final
