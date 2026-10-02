/-
# `C²` regularity from a weighted `L²` Fourier transform

This file proves `Work.MRMT.Found.contDiff_two_of_memLp_fourier_weight`: if `q ∈ L²(ℂ)` is
(almost everywhere) supported on a compact set `K` and the weighted Fourier transform
`ξ ↦ (1 + ‖ξ‖²)² · 𝓕q(ξ)` is again square integrable, then `q` agrees a.e. with a compactly
supported `C²` function `Q`.

The proof is the plane case of the Sobolev embedding `H⁴(ℝ²) ⊂ C²`:

* the weight `(1 + ‖ξ‖²)²` being square integrable makes `𝓕q` an `L¹` function, and more
  generally `ξ ↦ ‖ξ‖ⁿ 𝓕q(ξ) ∈ L¹` for `n ≤ 2`; hence the inverse Fourier integral
  `Q := 𝓕⁻(𝓕q)` is `C²` (Fourier transforms of `L¹` functions with moments are smooth);
* the identification `Q = q` a.e. is obtained by testing against smooth compactly supported
  functions: on the Fourier side the pairing of `Q` against a test function is computed by
  self-adjointness of the Fourier transform, and the pairing of `q` is computed with Plancherel
  for `L²` together with the elementary identity `conj(𝓕⁻f) = 𝓕(conj f)`.

Finally `Q`, being continuous and equal a.e. to `q`, vanishes on the (open) complement of `K`,
so it is compactly supported.
-/
import Mathlib
import Submission.Work.MRMT.Found.PrincipalAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped ENNReal FourierTransform ComplexConjugate SchwartzMap ContDiff

namespace Work.MRMT.Found

/-! ## Elementary integrability of the weights `(1 + ‖ξ‖²)⁻ᵏ` -/

private theorem cw_weight_sq_memLp :
    MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) 2 (volume : Measure ℂ) := by
  rw [memLp_two_iff_integrable_sq (by simp only [Real.rpow_neg_one]; fun_prop)]
  have h2 : Integrable (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4) (by
      rw [Complex.finrank_real_complex]; norm_num)
    simpa [show -(4:ℝ)/2 = (-2:ℝ) by norm_num] using h
  refine h2.congr ?_
  filter_upwards with ξ
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- For `n ≤ 2`, `‖ξ‖ⁿ (1 + ‖ξ‖²)⁻²` is square integrable. -/
private theorem cw_weight_moment_memLp (n : ℕ) (hn : n ≤ 2) :
    MemLp (fun ξ : ℂ => ‖ξ‖ ^ n * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) 2 (volume : Measure ℂ) := by
  refine MemLp.of_le cw_weight_sq_memLp (by fun_prop) ?_
  filter_upwards with ξ
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have ha : (0:ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hn' : ‖ξ‖ ^ n ≤ 1 + ‖ξ‖ ^ 2 := by
    rcases le_or_gt 1 ‖ξ‖ with h | h
    · exact (pow_le_pow_right₀ h hn).trans (by nlinarith [sq_nonneg ‖ξ‖])
    · exact (pow_le_one₀ (norm_nonneg _) h.le).trans (by nlinarith [sq_nonneg ‖ξ‖])
  calc ‖ξ‖ ^ n * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)
      ≤ (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hn' (Real.rpow_nonneg (le_of_lt ha) _)
    _ = (1 + ‖ξ‖ ^ 2) ^ (1:ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by rw [Real.rpow_one]
    _ = (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) := by rw [← Real.rpow_add ha]; norm_num

/-- For `n ≤ 2`, `‖ξ‖ⁿ ((1 + ‖ξ‖²)²)⁻¹` is square integrable. -/
private theorem cw_weight_moment_memLp' (n : ℕ) (hn : n ≤ 2) :
    MemLp (fun ξ : ℂ => ‖ξ‖ ^ n * ((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ)⁻¹) 2 (volume : Measure ℂ) := by
  refine MemLp.ae_eq ?_ (cw_weight_moment_memLp n hn)
  filter_upwards with ξ
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

private theorem cw_fourierWeight_ne_zero (ξ : ℂ) : fourierWeight ξ ≠ 0 := by
  rw [fourierWeight_apply, Complex.ofReal_ne_zero]
  positivity

private theorem cw_inv_weight_memLp :
    MemLp (fun ξ : ℂ => (fourierWeight ξ)⁻¹) 2 (volume : Measure ℂ) := by
  have hm : MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) 2 (volume : Measure ℂ) := by
    simpa using cw_weight_moment_memLp 0 (by norm_num)
  refine MemLp.ae_eq ?_ hm.ofReal
  filter_upwards with ξ
  have h2 : (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) = ((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [fourierWeight_apply, ← Complex.ofReal_inv]
  exact congrArg (fun r : ℝ => (r : ℂ)) h2

/-- If `(1 + ‖ξ‖²)² F(ξ)` is in `L²`, then `F` is integrable. -/
private theorem cw_integrable_of_weight_memLp {F : ℂ → ℂ}
    (hW : MemLp (fun ξ : ℂ => fourierWeight ξ * F ξ) 2 (volume : Measure ℂ)) :
    Integrable F := by
  refine (MemLp.integrable_mul cw_inv_weight_memLp hW).congr ?_
  filter_upwards with ξ
  rw [Pi.mul_apply, inv_mul_cancel_left₀ (cw_fourierWeight_ne_zero ξ)]

/-- If `(1 + ‖ξ‖²)² F(ξ)` is in `L²`, then `‖ξ‖ⁿ ‖F ξ‖` is integrable for `n ≤ 2`. -/
private theorem cw_integrable_moment_of_weight_memLp {F : ℂ → ℂ}
    (hW : MemLp (fun ξ : ℂ => fourierWeight ξ * F ξ) 2 (volume : Measure ℂ))
    (n : ℕ) (hn : n ≤ 2) :
    Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖F ξ‖) := by
  have hG : MemLp (fun ξ : ℂ => ‖fourierWeight ξ * F ξ‖) 2 (volume : Measure ℂ) := hW.norm
  refine (MemLp.integrable_mul (cw_weight_moment_memLp' n hn) hG).congr ?_
  filter_upwards with ξ
  rw [Pi.mul_apply, fourierWeight_apply, norm_mul]
  have hnorm : ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ = (1 + ‖ξ‖ ^ 2) ^ 2 :=
    (RCLike.norm_ofReal ((1 + ‖ξ‖ ^ 2) ^ 2)).trans (abs_of_nonneg (by positivity))
  rw [hnorm, mul_assoc,
    inv_mul_cancel_left₀ (by positivity : ((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) ≠ 0)]

/-! ## Fourier-side lemmas -/

/-- `star (e^{2πit} z) = e^{-2πit} star z` for the standard character. -/
private theorem cw_star_fourierChar_smul (t : ℝ) (w : ℂ) :
    star (𝐞 t • w) = 𝐞 (-t) • star w := by
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
  congr 1
  change (starRingEnd ℂ) ↑(Real.fourierChar t) = ↑(Real.fourierChar (-t))
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- If `‖ξ‖ⁿ ‖f ξ‖` is integrable for `n ≤ 2`, then `𝓕⁻ f` is `C²`. -/
private theorem cw_contDiff_two_fourierInv_of_moments {F : ℂ → ℂ}
    (hmom : ∀ n : ℕ, n ≤ 2 → Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖F ξ‖)) :
    ContDiff ℝ 2 (𝓕⁻ F) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := 2) ?_
  intro n hn
  have hn' : n ≤ 2 := by exact_mod_cast hn
  refine (hmom n hn').comp_neg.congr ?_
  filter_upwards with v
  rw [norm_neg]

/-- Conjugation commutes with the inverse Fourier integral: `conj (𝓕⁻f x) = 𝓕(conj ∘ f) x`. -/
private theorem cw_conj_fourierInv {F : ℂ → ℂ} (x : ℂ) :
    star (𝓕⁻ F x) = 𝓕 (fun ξ => star (F ξ)) x := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  change (starRingEnd ℂ) (∫ (v : ℂ), 𝐞 (inner ℝ v x) • F v)
    = ∫ (v : ℂ), 𝐞 (-inner ℝ v x) • star (F v)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with v
  exact cw_star_fourierChar_smul (inner ℝ v x) (F v)

/-- For a real-valued Schwartz function `Ψ`, `conj (𝓕 Ψ ξ) = 𝓕 Ψ (-ξ)`. -/
private theorem cw_star_fourier_of_real (Ψ : 𝓢(ℂ, ℂ)) (hreal : ∀ x, star (Ψ x) = Ψ x)
    (ξ : ℂ) :
    star (𝓕 (Ψ : ℂ → ℂ) ξ) = 𝓕 (Ψ : ℂ → ℂ) (-ξ) := by
  have h1 := cw_conj_fourierInv (F := (Ψ : ℂ → ℂ)) ξ
  have h2 : (fun x => star ((Ψ : ℂ → ℂ) x)) = (Ψ : ℂ → ℂ) := funext hreal
  rw [h2] at h1
  rw [← h1, star_star, Real.fourierInv_eq_fourier_neg]

private theorem cw_continuous_innerₗ : Continuous fun p : ℂ × ℂ => (innerₗ ℂ p.1) p.2 := by
  have h : (fun p : ℂ × ℂ => (innerₗ ℂ p.1) p.2) = fun p => inner ℝ p.1 p.2 := by
    funext p
    exact innerₛₗ_apply_apply ℝ p.1 p.2
  rw [h]; exact continuous_inner

/-- Self-adjointness of the Fourier transform, in the form needed for the inverse transform. -/
private theorem cw_pairing_Q {F φ : ℂ → ℂ} (hφ : Integrable φ) (hF : Integrable F) :
    ∫ x, φ x • (𝓕⁻ F x) = ∫ ξ, 𝓕 φ ξ • F (-ξ) := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (L := innerₗ ℂ)
    Real.continuous_fourierChar cw_continuous_innerₗ hφ hF.comp_neg
  rw [flip_innerₗ] at h
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact h.symm

/-- Plancherel pairing of an `L²` function with a real-valued Schwartz test function. -/
private theorem cw_integral_mul_eq_fourier (f : Lp ℂ 2 (volume : Measure ℂ)) (Ψ : 𝓢(ℂ, ℂ))
    (hreal : ∀ x, star (Ψ x) = Ψ x) :
    ∫ x, (Ψ : ℂ → ℂ) x * (f : ℂ → ℂ) x
      = ∫ ξ, (𝓕 (Ψ : ℂ → ℂ)) ξ * ((𝓕 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (-ξ) := by
  have h1 : ∫ x, (Ψ : ℂ → ℂ) x * (f : ℂ → ℂ) x
      = inner ℂ (Ψ.toLp 2 (volume : Measure ℂ)) f := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp Ψ 2 (volume : Measure ℂ)] with x hx1
    have hstar : (starRingEnd ℂ) (Ψ x) = Ψ x := hreal x
    rw [hx1, RCLike.inner_apply, mul_comm, hstar]
  have key : inner ℂ ((𝓕 Ψ).toLp 2 (volume : Measure ℂ)) (𝓕 f)
      = ∫ ξ, (𝓕 (Ψ : ℂ → ℂ)) ξ * ((𝓕 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (-ξ) := by
    rw [MeasureTheory.L2.inner_def]
    trans ∫ a : ℂ, ((𝓕 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) a * (𝓕 (Ψ : ℂ → ℂ)) (-a)
    · refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp (𝓕 Ψ) 2 (volume : Measure ℂ)] with a h1
      have hstar : (starRingEnd ℂ) (𝓕 (⇑Ψ) a) = 𝓕 (⇑Ψ) (-a) := cw_star_fourier_of_real Ψ hreal a
      rw [h1, RCLike.inner_apply, SchwartzMap.fourier_coe, hstar]
    · trans ∫ a : ℂ, ((𝓕 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (-a) * (𝓕 (Ψ : ℂ → ℂ)) a
      · simpa using integral_neg_eq_self
          (fun a => ((𝓕 f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (-a) * (𝓕 (Ψ : ℂ → ℂ)) a)
          volume
      · refine integral_congr_ae ?_
        filter_upwards with a
        rw [mul_comm]
  rw [h1, ← Lp.inner_fourier_eq (Ψ.toLp 2 (volume : Measure ℂ)) f, SchwartzMap.toLp_fourier_eq Ψ]
  exact key

/-! ## The main theorem -/

theorem contDiff_two_of_memLp_fourier_weight {q : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hq : MeasureTheory.MemLp q 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hK0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∉ K → q z = 0)
    (hw : MeasureTheory.MemLp (fun ξ : ℂ => Work.MRMT.Found.fourierWeight ξ *
      (((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) ξ)
      2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ∃ Q : ℂ → ℂ, ContDiff ℝ 2 Q ∧ HasCompactSupport Q ∧
      Q =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] q := by
  set fLp : Lp ℂ 2 (volume : Measure ℂ) := (Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q) with hfLp
  set F : ℂ → ℂ := (fLp : ℂ → ℂ) with hFdef
  have hW : MemLp (fun ξ : ℂ => fourierWeight ξ * F ξ) 2 (volume : Measure ℂ) := hw
  have hF1 : Integrable F := cw_integrable_of_weight_memLp hW
  have hmom : ∀ n : ℕ, n ≤ 2 → Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖F ξ‖) :=
    fun n hn => cw_integrable_moment_of_weight_memLp hW n hn
  set Q : ℂ → ℂ := 𝓕⁻ F with hQdef
  have hQcd : ContDiff ℝ 2 Q := by
    rw [hQdef]
    exact cw_contDiff_two_fourierInv_of_moments hmom
  have hQq : Q =ᵐ[(volume : Measure ℂ)] q := by
    refine ae_eq_of_integral_contDiff_smul_eq (hQcd.continuous.locallyIntegrable)
      (hq.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) ?_
    intro g hgcd hgcs
    have hcsΨ : HasCompactSupport (fun x : ℂ => (g x : ℂ)) :=
      hgcs.comp_left (g := Complex.ofRealCLM) (by simp)
    have hcdΨ : ContDiff ℝ ∞ (fun x : ℂ => (g x : ℂ)) :=
      (Complex.ofRealCLM.contDiff.of_le le_top).comp hgcd
    set Ψ : 𝓢(ℂ, ℂ) := hcsΨ.toSchwartzMap hcdΨ with hΨdef
    have hΨapply : ∀ x : ℂ, (Ψ : ℂ → ℂ) x = (g x : ℂ) := fun x => rfl
    have hreal : ∀ x, star (Ψ x) = Ψ x := by
      intro x
      rw [hΨapply]
      exact Complex.conj_ofReal (g x)
    calc ∫ x, g x • Q x
        = ∫ x, (Ψ : ℂ → ℂ) x • Q x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [hΨapply, Complex.real_smul, smul_eq_mul]
      _ = ∫ ξ, (𝓕 (Ψ : ℂ → ℂ)) ξ • F (-ξ) := by
            rw [hQdef]
            exact cw_pairing_Q Ψ.integrable hF1
      _ = ∫ ξ, (𝓕 (Ψ : ℂ → ℂ)) ξ
            * ((𝓕 (hq.toLp q) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (-ξ) := rfl
      _ = ∫ x, (Ψ : ℂ → ℂ) x
            * ((hq.toLp q : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) x :=
            (cw_integral_mul_eq_fourier (hq.toLp q) Ψ hreal).symm
      _ = ∫ x, (Ψ : ℂ → ℂ) x * q x := by
            refine integral_congr_ae ?_
            filter_upwards [MemLp.coeFn_toLp hq] with x hx
            rw [hx]
      _ = ∫ x, g x • q x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [hΨapply, Complex.real_smul]
  have hoff : ∀ z ∉ K, Q z = 0 := by
    intro z hzK
    obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl z hzK
    have hU : IsOpen (Metric.ball z ε) := Metric.isOpen_ball
    have hae : Q =ᵐ[volume.restrict (Metric.ball z ε)] (fun _ : ℂ => 0) := by
      have h1 : Q =ᵐ[volume.restrict (Metric.ball z ε)] q := EventuallyEq.restrict hQq
      have h2 : ∀ᵐ w ∂(volume.restrict (Metric.ball z ε)), q w = 0 := by
        have hmem : ∀ᵐ w ∂(volume.restrict (Metric.ball z ε)), w ∈ Metric.ball z ε :=
          ae_restrict_mem Metric.isOpen_ball.measurableSet
        filter_upwards [ae_restrict_of_ae hK0, hmem] with w hw1 hw2
        exact hw1 (hεball hw2)
      filter_upwards [h1, h2] with w hw1 hw2
      rw [hw1, hw2]
    have heq : Set.EqOn Q (fun _ : ℂ => 0) (Metric.ball z ε) :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hQcd.continuous.continuousOn
        continuous_const.continuousOn
    exact heq (Metric.mem_ball_self hεpos)
  refine ⟨Q, hQcd, ?_, hQq⟩
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  by_contra hzK
  exact hz (hoff z hzK)

end Work.MRMT.Found
