import Submission.FUP.PSHMollify
import Submission.FUP.PshWeights
import Submission.Commons.Analysis.Calculus.deriv_deriv_log_add_sum_sq
import Submission.Commons.Analysis.Calculus.iteratedDeriv_two_comp_add_smul
import Submission.Commons.Measure.EuclideanSpace.integrable_log_sum_sq_mul
import Submission.Commons.Measure.EuclideanSpace.integrable_abs_log_sum_sq_mul

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The logarithmic weight `Λ` of §5 of Cohen's paper

Cohen's §5 uses the plurisubharmonic weight

  `20 d · log |z|_∞ = 20 d · max_j log |z_j|`,

which is `-∞` at the origin.  In this development it is replaced by

  `Λ z = 10 d · log (∑ j, ‖z_j‖²)`,

which agrees with `20 d log|z|₂` off the origin (so `20d log|z|_∞ ≤ Λ ≤ 20d log|z|_∞ + C_d`),
is bounded on compact sets (the value at the origin is the junk value `0`) and is
plurisubharmonic; it therefore serves the same two purposes in §5:

* it is the term that makes `g` small near the origin (the estimates only involve points
  `z ≠ 0` of the *open* ball `B(x,|x|)`, where every logarithm is honest), and
* it is locally integrable, so `Λ` can be used as a Hörmander weight.

The module contains

* `logWeightEps ε z = 10 d · log (ε + ∑ j, ‖z_j‖²)` for `ε > 0` (smooth, and PSH by a direct
  second-derivative computation using `Commons.Analysis.Calculus.deriv_deriv_log_add_sum_sq`);
* `dbarDbarPos_logWeightEps`: Hörmander's positivity `∂∂̄ Λ_ε ≥ 0` for `Λ_ε`;
* `dbarDbarPos_logWeight`: the same for `Λ`, by dominated convergence along `ε = 1/(n+1)`
  (the only point where the pointwise convergence fails is the origin, which is null, and the
  majorant is `C(1 + |log (∑ ‖z_j‖²)|)|ψ|`, integrable by
  `Commons.Measure.EuclideanSpace.integrable_abs_log_sum_sq_mul`).
-/

namespace Submission.FUP

noncomputable def logWeightEps (ε : ℝ) (z : ℂᵈ) : ℝ :=
  10 * (d : ℝ) * Real.log (ε + ∑ j, ‖z j‖ ^ 2)

noncomputable def logWeight (z : ℂᵈ) : ℝ :=
  10 * (d : ℝ) * Real.log (∑ j, ‖z j‖ ^ 2)

lemma sum_sq_nonneg (z : ℂᵈ) : 0 ≤ ∑ j, ‖z j‖ ^ 2 :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma contDiff_sum_sq : ContDiff ℝ 2 (fun z : ℂᵈ => ∑ j, ‖z j‖ ^ 2) := by
  apply ContDiff.sum
  intro j _
  have hre : ContDiff ℝ 2 (fun z : ℂᵈ => (z j).re) :=
    Complex.reCLM.contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) j).contDiff)
  have him : ContDiff ℝ 2 (fun z : ℂᵈ => (z j).im) :=
    Complex.imCLM.contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) j).contDiff)
  have h : ContDiff ℝ 2 (fun z : ℂᵈ => (z j).re ^ 2 + (z j).im ^ 2) :=
    (hre.pow 2).add (him.pow 2)
  convert h using 2 with z
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma contDiff_logWeightEps (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (logWeightEps (d := d) ε) := by
  have h : ContDiff ℝ 2 (fun z : ℂᵈ => ε + ∑ j, ‖z j‖ ^ 2) :=
    contDiff_const.add contDiff_sum_sq
  have h2 : ContDiff ℝ 2 (fun z : ℂᵈ => Real.log (ε + ∑ j, ‖z j‖ ^ 2)) :=
    h.log (fun z => ne_of_gt (by linarith [sum_sq_nonneg z] : 0 < ε + ∑ j, ‖z j‖ ^ 2))
  have h3 := ContDiff.const_smul (𝕜 := ℝ) (10 * (d:ℝ)) h2
  convert h3 using 1
  funext z; simp only [logWeightEps, smul_eq_mul, mul_assoc]

lemma boundedOnCompact_logWeightEps (ε : ℝ) (hε : 0 < ε) :
    BoundedOnCompact (logWeightEps (d := d) ε) := by
  intro R
  refine ⟨10 * (d:ℝ) * max |Real.log ε| |Real.log (ε + (d:ℝ) * (max R 0) ^ 2)|, fun z hz => ?_⟩
  have hR0 : (0:ℝ) ≤ max R 0 := le_max_right _ _
  have hz' : ‖z‖ ≤ max R 0 := le_trans hz (le_max_left _ _)
  have hS : (∑ j, ‖z j‖ ^ 2) ≤ (d:ℝ) * (max R 0) ^ 2 := by
    calc ∑ j : Fin d, ‖z j‖ ^ 2 ≤ ∑ _j : Fin d, (max R 0) ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h1 : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
            nlinarith [norm_nonneg (z j), norm_nonneg z, hz', hR0]
      _ = (d:ℝ) * (max R 0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle : ε + ∑ j, ‖z j‖ ^ 2 ≤ ε + (d:ℝ) * (max R 0) ^ 2 := by linarith
  have hge : ε ≤ ε + ∑ j, ‖z j‖ ^ 2 := by linarith [sum_sq_nonneg z]
  have hA : Real.log ε ≤ Real.log (ε + ∑ j, ‖z j‖ ^ 2) := Real.log_le_log hε hge
  have hB : Real.log (ε + ∑ j, ‖z j‖ ^ 2) ≤ Real.log (ε + (d:ℝ) * (max R 0) ^ 2) :=
    Real.log_le_log (by linarith) hle
  have hkey : |Real.log (ε + ∑ j, ‖z j‖ ^ 2)|
      ≤ max |Real.log ε| |Real.log (ε + (d:ℝ) * (max R 0) ^ 2)| := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
      have h2 : |Real.log ε| ≤ max |Real.log ε| |Real.log (ε + (d:ℝ) * (max R 0) ^ 2)| :=
        le_max_left _ _
      linarith
    · exact le_trans (le_trans hB (le_abs_self _)) (le_max_right _ _)
  rw [logWeightEps, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 10 * (d:ℝ))]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

lemma iteratedDeriv_logWeightEps_line (ε : ℝ) (hε : 0 < ε) (z w : ℂᵈ) :
    iteratedDeriv 2 (fun θ : ℝ => logWeightEps (d := d) ε (z + θ • w)) 0
      = 10 * (d:ℝ) * ((2 * (∑ j, ‖w j‖ ^ 2) * (ε + ∑ j, ‖z j‖ ^ 2)
          - (2 * (∑ j, (z j * star (w j)).re)) ^ 2) / (ε + ∑ j, ‖z j‖ ^ 2) ^ 2) := by
  have hGcd : ContDiffAt ℝ ((2:ℕ) : WithTop ℕ∞)
      (fun θ : ℝ => Real.log (ε + ∑ j, ‖z j + (θ : ℂ) * w j‖ ^ 2)) 0 := by
    refine ContDiffAt.log ?_ ?_
    · exact (contDiffAt_const (c := ε)).add
        (contDiff_sum_sq.contDiffAt.comp 0
          ((contDiffAt_const (c := z)).add (contDiffAt_id.smul_const w)))
    · exact ne_of_gt (by positivity)
  show iteratedDeriv 2 (fun θ : ℝ =>
      10 * (d:ℝ) * Real.log (ε + ∑ j, ‖z j + (θ : ℂ) * w j‖ ^ 2)) 0 = _
  rw [iteratedDeriv_const_mul (10 * (d:ℝ)) hGcd]
  congr 1
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  exact Commons.Analysis.Calculus.deriv_deriv_log_add_sum_sq ε hε z w

lemma hessian_arith {N S Ar Ai ε : ℝ} (hN : 0 ≤ N) (hS : 0 ≤ S) (hε : 0 < ε)
    (hcs : Ar ^ 2 + Ai ^ 2 ≤ N * S) :
    0 ≤ (2 * N * (ε + S) - (2 * Ar) ^ 2) / (ε + S) ^ 2
      + (2 * N * (ε + S) - (2 * Ai) ^ 2) / (ε + S) ^ 2 := by
  have hpos : 0 < (ε + S) ^ 2 := by positivity
  rw [← add_div]
  apply div_nonneg _ hpos.le
  nlinarith [hcs, hN, hε, hS]

lemma conj_I_eq : star (Complex.I) = -Complex.I := by simp

lemma smul_I_re (a : ℂ) : ((-Complex.I) * a).re = a.im := by
  rw [Complex.mul_re]
  simp

/-- The pointwise Hermitian-Hessian bound `∂∂̄Λ_ε ≥ 0`. -/
lemma hessian_logWeightEps (ε : ℝ) (hε : 0 < ε) (z w : ℂᵈ) :
    4 * ((0:ℝ) * ∑ j, ‖w j‖ ^ 2) ≤
      (iteratedFDeriv ℝ 2 (logWeightEps (d := d) ε) z) ![w, w]
        + (iteratedFDeriv ℝ 2 (logWeightEps (d := d) ε) z) ![Complex.I • w, Complex.I • w] := by
  simp only [zero_mul, mul_zero]
  rw [← Commons.Analysis.Calculus.iteratedDeriv_two_comp_add_smul
        (logWeightEps (d := d) ε) (contDiff_logWeightEps ε hε) z w,
    ← Commons.Analysis.Calculus.iteratedDeriv_two_comp_add_smul
        (logWeightEps (d := d) ε) (contDiff_logWeightEps ε hε) z (Complex.I • w)]
  rw [iteratedDeriv_logWeightEps_line ε hε z w,
    iteratedDeriv_logWeightEps_line ε hε z (Complex.I • w)]
  have hN : ∑ j, ‖(Complex.I • w) j‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  have hAi : ∑ j, (z j * star ((Complex.I • w) j)).re = ∑ j, (z j * star (w j)).im := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : z j * star ((Complex.I : ℂ) • w j) = -Complex.I * (z j * star (w j)) := by
      rw [smul_eq_mul, star_mul, conj_I_eq]; ring
    rw [show (Complex.I • w) j = (Complex.I : ℂ) • w j from rfl, h1, smul_I_re]
  rw [hN, hAi]
  have hcs : (∑ j, (z j * star (w j)).re) ^ 2 + (∑ j, (z j * star (w j)).im) ^ 2
      ≤ (∑ j, ‖z j‖ ^ 2) * (∑ j, ‖w j‖ ^ 2) := by
    have h1 : ‖∑ j, z j * star (w j)‖ ^ 2
        = (∑ j, (z j * star (w j)).re) ^ 2 + (∑ j, (z j * star (w j)).im) ^ 2 := by
      have hAdef : (∑ j, z j * star (w j)) = ((∑ j, (z j * star (w j)).re : ℝ) : ℂ)
          + ((∑ j, (z j * star (w j)).im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_sum, Complex.im_sum]
      rw [Complex.sq_norm, Complex.normSq_apply, hAdef]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [← h1]
    have h2 : ‖∑ j, z j * star (w j)‖ ≤ ∑ j, ‖z j‖ * ‖w j‖ := by
      calc ‖∑ j, z j * star (w j)‖ ≤ ∑ j, ‖z j * star (w j)‖ := norm_sum_le _ _
        _ = ∑ j, ‖z j‖ * ‖w j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, norm_star]
    have h4 : (∑ j, ‖z j‖ * ‖w j‖) ^ 2 ≤ (∑ j, ‖z j‖ ^ 2) * (∑ j, ‖w j‖ ^ 2) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
        (fun j => ‖z j‖) (fun j => ‖w j‖)
      simpa using this
    calc ‖∑ j, z j * star (w j)‖ ^ 2 ≤ (∑ j, ‖z j‖ * ‖w j‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (∑ j, z j * star (w j))]) h2
      _ ≤ _ := h4
  have hcs' : (∑ j, (z j * star (w j)).re) ^ 2 + (∑ j, (z j * star (w j)).im) ^ 2
      ≤ (∑ j, ‖w j‖ ^ 2) * (∑ j, ‖z j‖ ^ 2) := by rw [mul_comm]; exact hcs
  have h10 : (0:ℝ) ≤ 10 * (d:ℝ) := by positivity
  have h := hessian_arith (N := ∑ j, ‖w j‖ ^ 2) (S := ∑ j, ‖z j‖ ^ 2)
    (Ar := ∑ j, (z j * star (w j)).re) (Ai := ∑ j, (z j * star (w j)).im) (ε := ε)
    (sum_sq_nonneg w) (sum_sq_nonneg z) hε hcs'
  nlinarith [h, h10]

/-- **`∂∂̄ Λ_ε ≥ 0`** for the regularised logarithmic weight. -/
theorem dbarDbarPos_logWeightEps (ε : ℝ) (hε : 0 < ε) :
    DbarDbarPos (logWeightEps (d := d) ε) (fun _ : ℂᵈ => (0:ℝ)) :=
  dbarDbarPos_of_hessian (contDiff_logWeightEps ε hε) measurable_const
    (fun R => ⟨0, fun z _ => by simp⟩) (boundedOnCompact_logWeightEps ε hε)
    (hessian_logWeightEps ε hε)

/-- The origin is a null set of `ℂᵈ` (for `d ≥ 1`). -/
lemma volume_singleton_zero (hd : 1 ≤ d) : (volume : Measure ℂᵈ) {0} = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  rw [volume_pi, Measure.pi_singleton]
  exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin d)) (by simp)

lemma ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z ∂(volume : Measure ℂᵈ), z ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simpa using volume_singleton_zero (d := d) hd

lemma sq_sum_pos_of_ne_zero {z : ℂᵈ} (hz : z ≠ 0) : 0 < ∑ j, ‖z j‖ ^ 2 := by
  rcases lt_or_eq_of_le (sum_sq_nonneg z) with h | h
  · exact h
  · exfalso
    apply hz
    funext j
    have h1 : ‖z j‖ ^ 2 = 0 := by
      have := Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2)
        (fun i _ => sq_nonneg ‖z i‖) (Finset.mem_univ j)
      rw [← h] at this; simpa using this
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h1)

/-- **`∂∂̄ Λ ≥ 0`** for the logarithmic weight `Λ z = 10 d log(∑ j, ‖z_j‖²)`. -/
theorem dbarDbarPos_logWeight (hd : 1 ≤ d) :
    DbarDbarPos (logWeight (d := d)) (fun _ : ℂᵈ => (0:ℝ)) := by
  intro α hα hsα
  set ψ : ℂᵈ → ℝ := dbarDbarTest α with hψdef
  have hψc : Continuous ψ := continuous_dbarDbarTest hα
  have hψs : HasCompactSupport ψ := hasCompactSupport_dbarDbarTest hsα
  have hψabs_c : Continuous (fun z => |ψ z|) := hψc.abs
  have hψabs_s : HasCompactSupport (fun z => |ψ z|) := hψs.abs
  refine ⟨by simp, ?_, ?_⟩
  · have hint := Commons.Measure.EuclideanSpace.integrable_log_sum_sq_mul
      (d := d) hd ψ hψc hψs
    refine ((hint.const_mul (10 * (d:ℝ))).congr ?_)
    filter_upwards with z
    simp only [Pi.mul_apply, logWeight]
    ring
  · have hLHS : (∫ z, (0:ℝ) * formNormSq α z) = 0 := by simp
    rw [hLHS]
    -- dominated convergence along `ε = 1/(n+1)`
    have hbound_int : Integrable (fun z : ℂᵈ =>
        10 * (d:ℝ) * (|Real.log (∑ j, ‖z j‖ ^ 2)| + Real.log 6) * |ψ z|) := by
      have h1 : Integrable (fun z : ℂᵈ => |Real.log (∑ j, ‖z j‖ ^ 2)| * |ψ z|) :=
        Commons.Measure.EuclideanSpace.integrable_abs_log_sum_sq_mul
          (d := d) hd (fun z => |ψ z|) hψabs_c hψabs_s
      have h2 : Integrable (fun z : ℂᵈ => Real.log 6 * |ψ z|) :=
        (Continuous.integrable_of_hasCompactSupport hψabs_c hψabs_s).const_mul (Real.log 6)
      have h3 : Integrable (fun z : ℂᵈ => (|Real.log (∑ j, ‖z j‖ ^ 2)| + Real.log 6) * |ψ z|) := by
        have h := h1.add h2
        refine h.congr ?_
        filter_upwards with z
        simp only [Pi.add_apply]
        ring
      have h4 := h3.const_mul (10 * (d:ℝ))
      refine h4.congr ?_
      filter_upwards with z
      ring
    have hlog_bound : ∀ (n : ℕ) (z : ℂᵈ), z ≠ 0 →
        |Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)|
          ≤ |Real.log (∑ j, ‖z j‖ ^ 2)| + Real.log 6 := by
      intro n z hz
      have hSn : 0 < (∑ j, ‖z j‖ ^ 2) := sq_sum_pos_of_ne_zero hz
      have hεpos : 0 < 1 / ((n:ℝ) + 1) := by positivity
      have hε1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast Nat.le_add_left 1 n
      rw [abs_le]
      by_cases hcase : 2 * (1 / ((n:ℝ) + 1)) ≤ ∑ j, ‖z j‖ ^ 2
      · have hεS : 1 / ((n:ℝ) + 1) ≤ ∑ j, ‖z j‖ ^ 2 := by linarith
        have hA : Real.log (∑ j, ‖z j‖ ^ 2)
            ≤ Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2) :=
          Real.log_le_log hSn (by linarith)
        have hB : Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)
            ≤ Real.log (∑ j, ‖z j‖ ^ 2) + Real.log 2 := by
          have h := Real.log_le_log (by linarith : 0 < 1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)
            (by linarith : 1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2 ≤ (∑ j, ‖z j‖ ^ 2) * 2)
          rw [Real.log_mul (ne_of_gt hSn) (by norm_num : (2:ℝ) ≠ 0)] at h
          linarith
        have h2l : Real.log 2 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
        constructor
        · have hna : -|Real.log (∑ j, ‖z j‖ ^ 2)| ≤ Real.log (∑ j, ‖z j‖ ^ 2) := neg_abs_le _
          linarith
        · have hl : Real.log (∑ j, ‖z j‖ ^ 2) ≤ |Real.log (∑ j, ‖z j‖ ^ 2)| := le_abs_self _
          linarith
      · have hlt : ∑ j, ‖z j‖ ^ 2 < 2 * (1 / ((n:ℝ) + 1)) := lt_of_not_ge hcase
        have hhalf : (∑ j, ‖z j‖ ^ 2) / 2 ≤ 1 / ((n:ℝ) + 1) := by linarith
        have hA : Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2) ≤ Real.log 6 := by
          have h := Real.log_le_log (by linarith : 0 < 1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)
            (by linarith : 1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2 ≤ 3 * (1 / ((n:ℝ) + 1)))
          rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt hεpos)] at h
          have h4 : Real.log (1 / ((n:ℝ) + 1)) ≤ 0 := Real.log_nonpos hεpos.le hε1
          have h5 : Real.log 3 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
          linarith
        have hB : Real.log (∑ j, ‖z j‖ ^ 2) - Real.log 2
            ≤ Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2) := by
          have h1 : Real.log ((∑ j, ‖z j‖ ^ 2) / 2) ≤ Real.log (1 / ((n:ℝ) + 1)) :=
            Real.log_le_log (by positivity) hhalf
          have h2 : Real.log ((∑ j, ‖z j‖ ^ 2) / 2)
              = Real.log (∑ j, ‖z j‖ ^ 2) - Real.log 2 :=
            Real.log_div (ne_of_gt hSn) (by norm_num)
          have h3 : Real.log (1 / ((n:ℝ) + 1))
              ≤ Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2) :=
            Real.log_le_log hεpos (by linarith)
          linarith
        constructor
        · have hna : -|Real.log (∑ j, ‖z j‖ ^ 2)| ≤ Real.log (∑ j, ‖z j‖ ^ 2) := neg_abs_le _
          have h6 : Real.log 2 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
          linarith
        · have hl : (0:ℝ) ≤ |Real.log (∑ j, ‖z j‖ ^ 2)| := abs_nonneg _
          linarith
    have hlim : Tendsto (fun n : ℕ =>
        ∫ z, logWeightEps (d := d) (1 / ((n:ℝ) + 1)) z * ψ z) atTop
        (𝓝 (∫ z, logWeight z * ψ z)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun z : ℂᵈ => 10 * (d:ℝ) * (|Real.log (∑ j, ‖z j‖ ^ 2)| + Real.log 6) * |ψ z|)
        ?_ hbound_int ?_ ?_
      · intro n
        exact (((contDiff_logWeightEps (d := d) (1 / ((n:ℝ) + 1))
          (by positivity)).continuous).mul hψc).aestronglyMeasurable
      · intro n
        filter_upwards [ae_ne_zero (d := d) hd] with z hz
        have hlog := hlog_bound n z hz
        have hlogW : |logWeightEps (d := d) (1 / ((n:ℝ) + 1)) z|
            ≤ 10 * (d:ℝ) * (|Real.log (∑ j, ‖z j‖ ^ 2)| + Real.log 6) := by
          rw [logWeightEps, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 10 * (d:ℝ))]
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hlogW (abs_nonneg _)
      · filter_upwards [ae_ne_zero (d := d) hd] with z hz
        have hSn : 0 < (∑ j, ‖z j‖ ^ 2) := sq_sum_pos_of_ne_zero hz
        have hεlim : Tendsto (fun n : ℕ => (1 / ((n:ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2) atTop
            (𝓝 (∑ j, ‖z j‖ ^ 2)) := by
          simpa using hεlim.add_const (∑ j, ‖z j‖ ^ 2)
        have h2 : Tendsto (fun n : ℕ => Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)) atTop
            (𝓝 (Real.log (∑ j, ‖z j‖ ^ 2))) :=
          (Real.continuousAt_log (ne_of_gt hSn)).tendsto.comp h1
        have h3 : Tendsto (fun n : ℕ =>
            (10 * (d:ℝ)) * Real.log (1 / ((n:ℝ) + 1) + ∑ j, ‖z j‖ ^ 2)) atTop
            (𝓝 ((10 * (d:ℝ)) * Real.log (∑ j, ‖z j‖ ^ 2))) := h2.const_mul _
        simpa only [logWeightEps, logWeight] using h3.mul_const (ψ z)
    have hnonneg : ∀ n : ℕ, 0 ≤ ∫ z, logWeightEps (d := d) (1 / ((n:ℝ) + 1)) z * ψ z := by
      intro n
      obtain ⟨-, -, hineq⟩ :=
        dbarDbarPos_logWeightEps (d := d) (1 / ((n:ℝ) + 1)) (by positivity) α hα hsα
      simpa [hψdef] using hineq
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hnonneg)

end Submission.FUP
