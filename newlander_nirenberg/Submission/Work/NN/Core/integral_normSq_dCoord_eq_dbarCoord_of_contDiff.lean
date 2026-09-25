import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.NN.Core

variable {n : ℕ}

/-! ## Integration by parts for the `(1,0)`-operator `∂ = dCoord` -/

/-- **Integration by parts for the flat `∂`-operator on `ℂⁿ`.**  For `C¹` functions
`u`, `v : ℂⁿ → ℂ` such that all the products appearing are integrable,
`∫ x, u x * ∂_k v x = -∫ x, ∂_k u x * v x`, where `∂_k = dCoord k` is the flat
`(1,0)`-operator of `Submission.Work.CR.Flat.Polydisc`. -/
theorem integral_mul_dCoord_eq_neg (k : Fin n) {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (h1u : Integrable (fun x => fderiv ℝ u x (Pi.single k 1) * v x))
    (hIu : Integrable (fun x => fderiv ℝ u x (Pi.single k Complex.I) * v x))
    (h1v : Integrable (fun x => u x * fderiv ℝ v x (Pi.single k 1)))
    (hIv : Integrable (fun x => u x * fderiv ℝ v x (Pi.single k Complex.I)))
    (huv : Integrable (fun x => u x * v x)) :
    ∫ x, u x * Work.CR.Flat.dCoord k v x = -∫ x, Work.CR.Flat.dCoord k u x * v x := by
  have hudiff : ∀ x ∈ tsupport v, DifferentiableAt ℝ u x := fun x _ =>
    (hu.differentiable (by norm_num)).differentiableAt
  have hvdiff : ∀ x ∈ tsupport u, DifferentiableAt ℝ v x := fun x _ =>
    (hv.differentiable (by norm_num)).differentiableAt
  have hIBP1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k (1 : ℂ)) h1u h1v huv hudiff hvdiff
  have hIBPI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := v) (v := Pi.single k Complex.I) hIu hIv huv hudiff hvdiff
  have hcongr1 : (fun x => u x * Work.CR.Flat.dCoord k v x)
      = fun x => (1 / 2 : ℂ) * (u x * fderiv ℝ v x (Pi.single k 1))
          - (1 / 2 * Complex.I) * (u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    funext x; simp only [Work.CR.Flat.dCoord]; ring
  have hL : ∫ x, u x * Work.CR.Flat.dCoord k v x
      = (1 / 2 : ℂ) * (∫ x, u x * fderiv ℝ v x (Pi.single k 1))
        - (1 / 2 * Complex.I) * (∫ x, u x * fderiv ℝ v x (Pi.single k Complex.I)) := by
    rw [hcongr1, integral_sub (h1v.const_mul _) (hIv.const_mul _), integral_const_mul,
      integral_const_mul]
  have hcongr2 : (fun x => Work.CR.Flat.dCoord k u x * v x)
      = fun x => (1 / 2 : ℂ) * (fderiv ℝ u x (Pi.single k 1) * v x)
          - (1 / 2 * Complex.I) * (fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    funext x; simp only [Work.CR.Flat.dCoord]; ring
  have hR : ∫ x, Work.CR.Flat.dCoord k u x * v x
      = (1 / 2 : ℂ) * (∫ x, fderiv ℝ u x (Pi.single k 1) * v x)
        - (1 / 2 * Complex.I) * (∫ x, fderiv ℝ u x (Pi.single k Complex.I) * v x) := by
    rw [hcongr2, integral_sub (h1u.const_mul _) (hIu.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hL, hR, hIBP1, hIBPI]
  ring

/-! ## Conjugation intertwines `∂` and `∂̄` -/

/-- Scalar identity: conjugating `(1/2)(a - i b)` swaps the sign of the `i`-term. -/
lemma star_half_sub (a b : ℂ) :
    star ((1 / 2 : ℂ) * (a - Complex.I * b)) = (1 / 2 : ℂ) * (star a + Complex.I * star b) := by
  simp only [star_mul, star_sub, Complex.star_def, Complex.conj_I, Complex.conj_ofNat, map_one,
    map_div₀]
  ring

/-- Scalar identity: conjugating `(1/2)(a + i b)` swaps the sign of the `i`-term. -/
lemma star_half_add (a b : ℂ) :
    star ((1 / 2 : ℂ) * (a + Complex.I * b)) = (1 / 2 : ℂ) * (star a - Complex.I * star b) := by
  simp only [star_mul, star_add, Complex.star_def, Complex.conj_I, Complex.conj_ofNat, map_one,
    map_div₀]
  ring

/-- The real differential of `star ∘ φ` at a point where `φ` is real differentiable. -/
lemma fderiv_star_comp {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hd : DifferentiableAt ℝ φ z) :
    fderiv ℝ (fun w => star (φ w)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ φ z) := by
  have h1 : (fun w => star (φ w)) = (Complex.conjCLE : ℂ → ℂ) ∘ φ := by
    funext w; simp [Function.comp_apply]
  rw [h1, fderiv_comp (f := φ) z (g := (Complex.conjCLE : ℂ → ℂ))
    Complex.conjCLE.differentiableAt hd, ContinuousLinearEquiv.fderiv]

/-- `∂̄_j` of the conjugate of `φ` is the conjugate of `∂_j φ`. -/
lemma dbarCoord_star_comp (j : Fin n) {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hd : DifferentiableAt ℝ φ z) :
    Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z = star (Work.CR.Flat.dCoord j φ z) := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dCoord, fderiv_star_comp hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  exact (star_half_sub _ _).symm

/-- `∂_j` of the conjugate of `φ` is the conjugate of `∂̄_j φ`. -/
lemma dCoord_star_comp (j : Fin n) {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hd : DifferentiableAt ℝ φ z) :
    Work.CR.Flat.dCoord j (fun w => star (φ w)) z = star (Work.CR.Flat.dbarCoord j φ z) := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, fderiv_star_comp hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  exact (star_half_add _ _).symm

/-! ## Regularity of the pieces -/

/-- The `(1,0)`-derivative of a `C²` function is `C¹`. -/
lemma contDiff_one_dCoord {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 2 φ) (j : Fin n) :
    ContDiff ℝ 1 (fun z => Work.CR.Flat.dCoord j φ z) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  rw [Work.CR.Flat.Cauchy.dCoord_eq_comp j φ]
  exact (Work.CR.Flat.Cauchy.dCoordPhi j).contDiff.comp h1

/-- The `(0,1)`-derivative of a `C²` function is `C¹`. -/
lemma contDiff_one_dbarCoord {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 2 φ) (j : Fin n) :
    ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarCoord j φ z) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp j φ]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp h1

/-- The `(0,1)`-derivative of a `C¹` function is continuous. -/
lemma continuous_dbarCoord_of_contDiff {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 1 φ) (j : Fin n) :
    Continuous (fun z => Work.CR.Flat.dbarCoord j φ z) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h2 : Continuous (fun z => fderiv ℝ φ z (Pi.single j 1)) := h1.clm_apply continuous_const
  have h3 : Continuous (fun z => fderiv ℝ φ z (Pi.single j Complex.I)) :=
    h1.clm_apply continuous_const
  have hfun : (fun z => Work.CR.Flat.dbarCoord j φ z)
      = fun z => (1 / 2 : ℂ) * (fderiv ℝ φ z (Pi.single j 1)
          + Complex.I * fderiv ℝ φ z (Pi.single j Complex.I)) := rfl
  rw [hfun]
  exact continuous_const.mul (h2.add (continuous_const.mul h3))

/-- The `(1,0)`-derivative of a `C¹` function is continuous. -/
lemma continuous_dCoord_of_contDiff {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 1 φ) (j : Fin n) :
    Continuous (fun z => Work.CR.Flat.dCoord j φ z) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h2 : Continuous (fun z => fderiv ℝ φ z (Pi.single j 1)) := h1.clm_apply continuous_const
  have h3 : Continuous (fun z => fderiv ℝ φ z (Pi.single j Complex.I)) :=
    h1.clm_apply continuous_const
  have hfun : (fun z => Work.CR.Flat.dCoord j φ z)
      = fun z => (1 / 2 : ℂ) * (fderiv ℝ φ z (Pi.single j 1)
          - Complex.I * fderiv ℝ φ z (Pi.single j Complex.I)) := rfl
  rw [hfun]
  exact continuous_const.mul (h2.sub (continuous_const.mul h3))

/-- The conjugate of a `C²` function is `C²`. -/
lemma contDiff_two_star_comp {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z => star (φ z)) := by
  have h1 : (fun z => star (φ z)) = (Complex.conjCLE : ℂ → ℂ) ∘ φ := by
    funext z; simp [Function.comp_apply]
  rw [h1]
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hφ

/-- The `(1,0)`-derivative of a compactly supported function has compact support. -/
lemma hasCompactSupport_dCoord_flat {φ : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport φ)
    (j : Fin n) : HasCompactSupport (fun z => Work.CR.Flat.dCoord j φ z) :=
  (hcs.fderiv ℝ).comp_left
    (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ =>
      (1 / 2 : ℂ) * (L (Pi.single j 1) - Complex.I * L (Pi.single j Complex.I))) (by simp)

/-- The `(0,1)`-derivative of a compactly supported function has compact support. -/
lemma hasCompactSupport_dbarCoord_flat {φ : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport φ)
    (j : Fin n) : HasCompactSupport (fun z => Work.CR.Flat.dbarCoord j φ z) :=
  (hcs.fderiv ℝ).comp_left
    (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ =>
      (1 / 2 : ℂ) * (L (Pi.single j 1) + Complex.I * L (Pi.single j Complex.I))) (by simp)

/-- The conjugate of a compactly supported function has compact support. -/
lemma hasCompactSupport_star_comp {φ : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (fun z => star (φ z)) :=
  hcs.comp_left (g := star) (by simp)

/-! ## Elementary rewrite lemmas for the real part of an integral -/

/-- The real part of an integral is the integral of the real part. -/
lemma integral_re_eq {F : (Fin n → ℂ) → ℂ} (hF : Integrable F) :
    ∫ z, (F z).re = (∫ z, F z).re := by
  simpa only [Complex.reCLM_apply] using
    ContinuousLinearMap.integral_comp_comm Complex.reCLM hF

/-- The real part of the negative of an integral. -/
lemma re_neg_integral_eq {F : (Fin n → ℂ) → ℂ} (hF : Integrable F) :
    (-∫ z, F z).re = -∫ z, (F z).re := by
  rw [Complex.neg_re, ← integral_re_eq hF]

/-! ## The per-coordinate identity -/

/-- For a `C²` compactly supported `φ`, the `L²` norms of `∂_j φ` and `∂̄_j φ` agree. -/
lemma integral_normSq_dCoord_eq_dbarCoord_single {φ : (Fin n → ℂ) → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) (j : Fin n) :
    ∫ z, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2 = ∫ z, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2 := by
  have hd : ∀ z, DifferentiableAt ℝ φ z :=
    fun z => (hφ.differentiable (by norm_num)).differentiableAt
  have hstar_dc : ∀ z, Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z
      = star (Work.CR.Flat.dCoord j φ z) := fun z => dbarCoord_star_comp j (hd z)
  have hstar_dbc : ∀ z, Work.CR.Flat.dCoord j (fun w => star (φ w)) z
      = star (Work.CR.Flat.dbarCoord j φ z) := fun z => dCoord_star_comp j (hd z)
  have hcomm : ∀ z, Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z
      = Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z := fun z =>
    Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm j j φ z hφ.contDiffAt
  -- regularity
  have hcd_dc : ContDiff ℝ 1 (fun z => Work.CR.Flat.dCoord j φ z) := contDiff_one_dCoord hφ j
  have hcd_dbc : ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarCoord j φ z) := contDiff_one_dbarCoord hφ j
  have hcd_st : ContDiff ℝ 1 (fun z => star (φ z)) :=
    (contDiff_two_star_comp hφ).of_le (by norm_num)
  have hcs_dc : HasCompactSupport (fun z => Work.CR.Flat.dCoord j φ z) :=
    hasCompactSupport_dCoord_flat hcs j
  have hcs_dbc : HasCompactSupport (fun z => Work.CR.Flat.dbarCoord j φ z) :=
    hasCompactSupport_dbarCoord_flat hcs j
  have hcs_st : HasCompactSupport (fun z => star (φ z)) := hasCompactSupport_star_comp hcs
  have hcd_dbar_st : ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z) :=
    contDiff_one_dbarCoord (contDiff_two_star_comp hφ) j
  have hcd_d_st : ContDiff ℝ 1 (fun z => Work.CR.Flat.dCoord j (fun w => star (φ w)) z) :=
    contDiff_one_dCoord (contDiff_two_star_comp hφ) j
  -- compact supports of the second derivatives
  have hcs_dbar_dc : HasCompactSupport
      (fun z => Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z) :=
    hasCompactSupport_dbarCoord_flat hcs_dc j
  have hcs_d_dbc : HasCompactSupport
      (fun z => Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z) :=
    hasCompactSupport_dCoord_flat hcs_dbc j
  -- integrability of the conjugate pairings
  have hInt1 : Integrable (fun z =>
      Work.CR.Flat.dCoord j φ z * Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z) :=
    (hcd_dc.continuous.mul hcd_dbar_st.continuous).integrable_of_hasCompactSupport hcs_dc.mul_right
  have hInt2 : Integrable (fun z =>
      Work.CR.Flat.dbarCoord j φ z * Work.CR.Flat.dCoord j (fun w => star (φ w)) z) :=
    (hcd_dbc.continuous.mul hcd_d_st.continuous).integrable_of_hasCompactSupport hcs_dbc.mul_right
  have hInt3 : Integrable (fun z =>
      Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z * star (φ z)) :=
    ((continuous_dbarCoord_of_contDiff hcd_dc j).mul hcd_st.continuous).integrable_of_hasCompactSupport
      hcs_dbar_dc.mul_right
  have hInt4 : Integrable (fun z =>
      Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z * star (φ z)) :=
    ((continuous_dCoord_of_contDiff hcd_dbc j).mul hcd_st.continuous).integrable_of_hasCompactSupport
      hcs_d_dbc.mul_right
  -- integration by parts in the two pairings
  have hIBP1 : ∫ z, Work.CR.Flat.dCoord j φ z * Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z
      = -∫ z, Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z * star (φ z) := by
    refine Work.CR.Flat.integral_mul_dbarCoord_eq_neg j hcd_dc hcd_st ?_ ?_ ?_ ?_ ?_
    · exact ((hcd_dc.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        hcd_st.continuous).integrable_of_hasCompactSupport hcs_st.mul_left
    · exact ((hcd_dc.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        hcd_st.continuous).integrable_of_hasCompactSupport hcs_st.mul_left
    · exact (hcd_dc.continuous.mul ((hcd_st.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport hcs_dc.mul_right
    · exact (hcd_dc.continuous.mul ((hcd_st.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport hcs_dc.mul_right
    · exact (hcd_dc.continuous.mul hcd_st.continuous).integrable_of_hasCompactSupport hcs_dc.mul_right
  have hIBP2 : ∫ z, Work.CR.Flat.dbarCoord j φ z * Work.CR.Flat.dCoord j (fun w => star (φ w)) z
      = -∫ z, Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z * star (φ z) := by
    refine integral_mul_dCoord_eq_neg j hcd_dbc hcd_st ?_ ?_ ?_ ?_ ?_
    · exact ((hcd_dbc.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        hcd_st.continuous).integrable_of_hasCompactSupport hcs_st.mul_left
    · exact ((hcd_dbc.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        hcd_st.continuous).integrable_of_hasCompactSupport hcs_st.mul_left
    · exact (hcd_dbc.continuous.mul ((hcd_st.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport hcs_dbc.mul_right
    · exact (hcd_dbc.continuous.mul ((hcd_st.continuous_fderiv (by norm_num)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport hcs_dbc.mul_right
    · exact (hcd_dbc.continuous.mul hcd_st.continuous).integrable_of_hasCompactSupport hcs_dbc.mul_right
  -- the two integrals expressed through the conjugate pairings
  have hA : ∫ z, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2
      = -∫ z, (Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z
          * star (φ z)).re := by
    have hpt : ∀ z, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2
        = (Work.CR.Flat.dCoord j φ z
            * Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z).re := by
      intro z
      rw [hstar_dc z]
      rw [show (Work.CR.Flat.dCoord j φ z * star (Work.CR.Flat.dCoord j φ z) : ℂ)
            = Work.CR.Flat.dCoord j φ z * (starRingEnd ℂ) (Work.CR.Flat.dCoord j φ z) from rfl,
        Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    calc ∫ z, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2
        = ∫ z, (Work.CR.Flat.dCoord j φ z
            * Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z).re :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ z, Work.CR.Flat.dCoord j φ z
            * Work.CR.Flat.dbarCoord j (fun w => star (φ w)) z).re := integral_re_eq hInt1
      _ = (-∫ z, Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z
            * star (φ z)).re := by rw [hIBP1]
      _ = -∫ z, (Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z
            * star (φ z)).re := re_neg_integral_eq hInt3
  have hB : ∫ z, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2
      = -∫ z, (Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z
          * star (φ z)).re := by
    have hpt : ∀ z, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2
        = (Work.CR.Flat.dbarCoord j φ z
            * Work.CR.Flat.dCoord j (fun w => star (φ w)) z).re := by
      intro z
      rw [hstar_dbc z]
      rw [show (Work.CR.Flat.dbarCoord j φ z * star (Work.CR.Flat.dbarCoord j φ z) : ℂ)
            = Work.CR.Flat.dbarCoord j φ z * (starRingEnd ℂ) (Work.CR.Flat.dbarCoord j φ z) from rfl,
        Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    calc ∫ z, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2
        = ∫ z, (Work.CR.Flat.dbarCoord j φ z
            * Work.CR.Flat.dCoord j (fun w => star (φ w)) z).re :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ z, Work.CR.Flat.dbarCoord j φ z
            * Work.CR.Flat.dCoord j (fun w => star (φ w)) z).re := integral_re_eq hInt2
      _ = (-∫ z, Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z
            * star (φ z)).re := by rw [hIBP2]
      _ = -∫ z, (Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z
            * star (φ z)).re := re_neg_integral_eq hInt4
  rw [hA, hB]
  have hfin : (fun z => (Work.CR.Flat.dbarCoord j (fun w => Work.CR.Flat.dCoord j φ w) z
        * star (φ z)).re)
      = fun z => (Work.CR.Flat.dCoord j (fun w => Work.CR.Flat.dbarCoord j φ w) z
        * star (φ z)).re := by
    funext z
    simp only [hcomm z]
  rw [hfin]

/-! ## The main theorem -/

/-- `‖∂_j φ‖²` is integrable for a `C²` compactly supported `φ`. -/
lemma integrable_normSq_dCoord_flat {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) (j : Fin n) :
    Integrable (fun z => ‖Work.CR.Flat.dCoord j φ z‖ ^ 2) := by
  refine ((contDiff_one_dCoord hφ j).continuous.norm.pow 2).integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_dCoord_flat hcs j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)

/-- `‖∂̄_j φ‖²` is integrable for a `C²` compactly supported `φ`. -/
lemma integrable_normSq_dbarCoord_flat {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) (j : Fin n) :
    Integrable (fun z => ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2) := by
  refine ((contDiff_one_dbarCoord hφ j).continuous.norm.pow 2).integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_dbarCoord_flat hcs j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)

theorem integral_normSq_dCoord_eq_dbarCoord_of_contDiff {n : ℕ} {φ : (Fin n → ℂ) → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) :
    ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2)
      = ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2) := by
  calc ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2)
      = ∑ j : Fin n, ∫ z : Fin n → ℂ, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2 :=
        integral_finsetSum Finset.univ
          (fun j _ => integrable_normSq_dCoord_flat hφ hcs j)
    _ = ∑ j : Fin n, ∫ z : Fin n → ℂ, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2 :=
        Finset.sum_congr rfl (fun j _ => integral_normSq_dCoord_eq_dbarCoord_single hφ hcs j)
    _ = ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2) :=
        (integral_finsetSum Finset.univ
          (fun j _ => integrable_normSq_dbarCoord_flat hφ hcs j)).symm

end Work.NN.Core
