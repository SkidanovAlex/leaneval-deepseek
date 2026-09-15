import Submission.FUP.RayTail
import Submission.FUP.ExtensionOperator
import Submission.FUP.PSHMean
import Submission.Commons.Measure.Real.integral_comp_mul_inv_one_add_sq
import Submission.Commons.Measure.Real.setIntegral_Iio_neg_eq_Ioi
import Submission.Commons.MeasureTheory.Integral.continuous_poisson_extension
import Submission.Commons.MeasureTheory.Integral.integrableOn_inv_sq_of_le_abs
import Submission.Commons.MeasureTheory.Integral.integral_Ioi_inv_sq

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff ENNReal

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# Uniform convergence of `Eω̃_{≤n}` to `Eω̃`

This module repairs the false `Eomega_seq_statement` of `ExtensionOperator.lean` (see
`ROADMAP.md`, Session 19 and Session 21).  The correct quantitative input is the decay of the
*ray tails* of the modified weight (`RayTail.lean`); here we deduce from it that the harmonic
extensions of the compactly supported truncations `T_n = ω̃_{≤n}` converge to the harmonic
extension of `ω̃` uniformly on compact subsets of `ℂᵈ` (Lemma 3.1 of the paper,
`lem:Ew_conv_cpct_subsets`, for the weights produced by §4).
-/

/-- The Euclidean norm `enorm` of `ℂᵈ` is continuous. -/
lemma continuous_enorm : Continuous (enorm : ℂᵈ → ℝ) := by
  have h : (enorm : ℂᵈ → ℝ) = fun z => Real.sqrt (∑ i : Fin d, ‖z i‖ ^ 2) := rfl
  rw [h]
  fun_prop

/-! ## Continuity of the extension operator -/

/-- **`Eω` is continuous** for a compactly supported continuous weight. -/
lemma continuous_Eomega {wt : ℝᵈ → ℝ} (hcont : Continuous wt) (hcpt : HasCompactSupport wt) :
    Continuous fun p : ℝᵈ × ℝᵈ => Eomega wt p.1 p.2 := by
  have h := Commons.MeasureTheory.Integral.continuous_poisson_extension hcont hcpt
  have h2 : (fun p : ℝᵈ × ℝᵈ => Eomega wt p.1 p.2)
      = fun p : ℝᵈ × ℝᵈ => (1 / π) * ∫ t : ℝ, wt (p.1 + t • p.2) * (1 + t ^ 2)⁻¹ := by
    funext p
    rw [Eomega]
  rw [h2]
  exact continuous_const.mul h

/-- **`Eω`, as a function on `ℂᵈ`, is continuous** for a compactly supported continuous weight. -/
lemma continuous_EomegaC {wt : ℝᵈ → ℝ} (hcont : Continuous wt) (hcpt : HasCompactSupport wt) :
    Continuous (EomegaC wt) := by
  have h1 := continuous_Eomega hcont hcpt
  have hre : Continuous (reVec : ℂᵈ → ℝᵈ) := by
    have h : Continuous fun z : ℂᵈ => (fun i : Fin d => (z i).re : Fin d → ℝ) :=
      continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)
    change Continuous (fun z : ℂᵈ =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i : Fin d => (z i).re))
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp h
  have him : Continuous (imVec : ℂᵈ → ℝᵈ) := by
    have h : Continuous fun z : ℂᵈ => (fun i : Fin d => (z i).im : Fin d → ℝ) :=
      continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i)
    change Continuous (fun z : ℂᵈ =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i : Fin d => (z i).im))
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp h
  exact h1.comp (hre.prodMk him)

/-! ## Basic facts about the pieces -/

/-- Every piece vanishes at the origin. -/
lemma omegaTildePiece_apply_zero (k : ℕ) {w : ℝᵈ → ℝ}
    (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0) :
    omegaTildePiece (d := d) k w 0 = 0 := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0; exact omegaTildePiece_zero_eq_zero w hwzero 0
  · exact omegaTildePiece_eq_zero_of_norm_le_pred k h1 w (by simp)

/-- The truncations dominate the modified weight. -/
lemma omegaTildeSum_le_truncSum {w : ℝᵈ → ℝ}
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) (n : ℕ) (x : ℝᵈ) :
    omegaTildeSum (d := d) w x ≤ truncSum (d := d) n w x := by
  obtain ⟨N, hN⟩ := exists_omegaTildePiece_eq_zero_of_ge (d := d) w x
  have hsumm : Summable (fun k => omegaTildePiece (d := d) k w x) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      exact hN k hk
  have h := hsumm.sum_add_tsum_nat_add n
  have hle := tsum_nonpos (L := SummationFilter.unconditional _)
    (f := fun j => omegaTildePiece (d := d) (j + n) w x) (fun j => hwk (j + n) x)
  rw [truncSum_apply]
  rw [show omegaTildeSum (d := d) w x = ∑' i : ℕ, omegaTildePiece (d := d) i w x from rfl]
  rw [← h]
  linarith

lemma continuous_inv_one_add_sq : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ :=
  (continuous_const.add (continuous_id.pow 2)).inv₀
    (fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne')

/-- The ray restriction of a piece vanishes on `[-1,1]` for `k ≥ 1`. -/
lemma omegaTildePiece_ray_zero (k : ℕ) (hk1 : 1 ≤ k) (w : ℝᵈ → ℝ) (ŷ : ℝᵈ) (hŷ : ‖ŷ‖ = 1)
    {t : ℝ} (ht : |t| ≤ 1) : omegaTildePiece (d := d) k w (t • ŷ) = 0 := by
  refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
  rw [norm_smul, hŷ, mul_one, Real.norm_eq_abs]
  calc |t| ≤ 1 := ht
    _ ≤ (2 : ℝ) ^ (k - 1) := by
        calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
          _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- **A single piece against the Poisson weight.**  For a unit vector `ŷ` and `σ > 0`,
`∫ |ω̃_k(u ŷ)| (σ²+u²)⁻¹ du` is at most `2|q_k|`, plus a correction localised at `k ≤ 1`. -/
lemma integral_abs_omegaTildePiece_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) {Creg : ℝ}
    (hCreg : 0 < Creg)
    (hwbound : ∀ (b : ℕ), b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    {σ : ℝ} (hσ : 0 < σ) (ŷ : ℝᵈ) (hŷ : ‖ŷ‖ = 1) (k : ℕ) :
    (∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
      ≤ 2 * |qk k w| + 32 * (Creg * tildeConst d) * (if k < 2 then 1 else 0) := by
  set C : ℝ := Creg * tildeConst d with hCdef
  have hC0 : 0 < C := by rw [hCdef]; exact mul_pos hCreg (tildeConst_pos d)
  rcases Nat.eq_zero_or_pos k with h0 | hk1
  · subst h0
    have hz : (fun u : ℝ => |omegaTildePiece (d := d) 0 w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
        = fun _ => (0 : ℝ) := by
      funext u
      rw [omegaTildePiece_zero_eq_zero w hwzero (u • ŷ), abs_zero, zero_mul]
    rw [hz, integral_zero]
    have h2 : 0 ≤ 2 * |qk 0 w| := by positivity
    have h3 : 0 ≤ 32 * C := by positivity
    split_ifs <;> linarith
  · have hline : Continuous fun u : ℝ => omegaTildePiece (d := d) k w (u • ŷ) :=
      (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
    have hcs : HasCompactSupport fun u : ℝ => omegaTildePiece (d := d) k w (u • ŷ) :=
      hasCompactSupport_omegaTildePiece_ray k w ŷ hŷ
    have hdiv : Integrable (fun t : ℝ => omegaTildePiece (d := d) k w (t • ŷ) / t ^ 2) :=
      Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport hline hcs
        (fun t ht => omegaTildePiece_ray_zero k hk1 w ŷ hŷ ht)
    have hint2 : Integrable (fun u : ℝ => |omegaTildePiece (d := d) k w (u • ŷ)| * (u ^ 2)⁻¹) := by
      refine hdiv.abs.congr ?_
      filter_upwards with t
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2), div_eq_mul_inv]
    have hden : Continuous fun u : ℝ => (σ ^ 2 + u ^ 2)⁻¹ :=
      (continuous_const.add (continuous_id.pow 2)).inv₀
        (fun u => (by positivity : (0 : ℝ) < σ ^ 2 + u ^ 2).ne')
    have hint1 : Integrable (fun u : ℝ => |omegaTildePiece (d := d) k w (u • ŷ)|
        * (σ ^ 2 + u ^ 2)⁻¹) := by
      have hcont := hline.abs.mul hden
      have hcs' : HasCompactSupport fun u : ℝ => |omegaTildePiece (d := d) k w (u • ŷ)|
          * (σ ^ 2 + u ^ 2)⁻¹ := hcs.abs.mul_right (f' := fun u : ℝ => (σ ^ 2 + u ^ 2)⁻¹)
      exact hcont.integrable_of_hasCompactSupport hcs'
    have hle1 : (∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
        ≤ ∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (u ^ 2)⁻¹ := by
      refine integral_mono_ae hint1 hint2 (Eventually.of_forall fun u => ?_)
      by_cases hu : u = 0
      · subst hu
        show |omegaTildePiece (d := d) k w (0 • ŷ)| * (σ ^ 2 + 0 ^ 2)⁻¹
            ≤ |omegaTildePiece (d := d) k w (0 • ŷ)| * (0 ^ 2)⁻¹
        rw [zero_smul, omegaTildePiece_apply_zero k hwzero]
        simp
      · have hu2 : (0 : ℝ) < u ^ 2 := sq_pos_of_ne_zero hu
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact inv_anti₀ hu2 (by nlinarith [sq_nonneg σ, sq_nonneg u])
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      have hvan : ∀ u : ℝ, u ∉ Set.Icc (-4 : ℝ) 4 →
          |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹ = 0 := by
        intro u hu
        have h4 : (4 : ℝ) ≤ |u| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
          rcases hu with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        rw [omegaTildePiece_eq_zero_of_norm_ge 1 w (by
          rw [norm_smul, hŷ, mul_one, Real.norm_eq_abs]
          calc (2 : ℝ) ^ (1 + 1) = 4 := by norm_num
            _ ≤ |u| := h4), abs_zero, zero_mul]
      have hpt : ∀ u : ℝ, |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹ ≤ 2 * C := by
        intro u
        rcases lt_or_ge |u| 1 with hu1 | hu1
        · rw [omegaTildePiece_ray_zero 1 le_rfl w ŷ hŷ (le_of_lt hu1), abs_zero, zero_mul]
          positivity
        · have h1 : |omegaTildePiece (d := d) 1 w (u • ŷ)| ≤ 2 * C := by
            have h := abs_omegaTildePiece_le hd 1 le_rfl hw hwzero hCreg hwbound (u • ŷ)
            have h2 : Creg * tildeConst d * 2 ^ 1 = 2 * C := by rw [hCdef]; ring
            linarith [h]
          have hu2 : (0 : ℝ) < u ^ 2 := by nlinarith [sq_abs u, hu1, abs_nonneg u]
          have h2 : (u ^ 2)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ hu2]
            nlinarith [sq_abs u, hu1]
          calc |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹
              ≤ 2 * C * 1 := mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = 2 * C := by ring
      have hmono : (∫ u in Set.Icc (-4 : ℝ) 4,
            |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹)
          ≤ ∫ u in Set.Icc (-4 : ℝ) 4, 2 * C := by
        refine setIntegral_mono hint2.integrableOn
          (show IntegrableOn (fun _ : ℝ => 2 * C) (Set.Icc (-4 : ℝ) 4) volume from
            integrable_const (2 * C)) hpt
      have hval : (∫ u in Set.Icc (-4 : ℝ) 4, 2 * C) = 16 * C := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 - (-4)), smul_eq_mul]
        ring
      have hmain : (∫ u : ℝ, |omegaTildePiece (d := d) 1 w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
          ≤ 2 * |qk 1 w| + 32 * C := by
        calc (∫ u : ℝ, |omegaTildePiece (d := d) 1 w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
            ≤ ∫ u : ℝ, |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹ := hle1
          _ = ∫ u in Set.Icc (-4 : ℝ) 4,
                |omegaTildePiece (d := d) 1 w (u • ŷ)| * (u ^ 2)⁻¹ :=
                (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
          _ ≤ ∫ u in Set.Icc (-4 : ℝ) 4, 2 * C := hmono
          _ = 16 * C := hval
          _ ≤ 2 * |qk 1 w| + 32 * C := by have := abs_nonneg (qk 1 w); linarith
      simpa only [Nat.reduceLT, ↓reduceIte, mul_one] using hmain
    · have h4 : (∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (u ^ 2)⁻¹)
          = 2 * |qk k w| := by
        rw [← integral_abs_omegaTildePiece_div_sq k hk2 hw (fun x => hwk k x) ŷ hŷ]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [div_eq_mul_inv]
      have hif : (if k < 2 then (1 : ℝ) else 0) = 0 := if_neg (by omega)
      calc (∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
          ≤ ∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (u ^ 2)⁻¹ := hle1
        _ = 2 * |qk k w| := h4
        _ ≤ 2 * |qk k w| + 32 * C * (if k < 2 then 1 else 0) := by
              rw [hif, mul_zero, add_zero]

/-! ## The weighted piece series -/

/-- The unshifted `ℓ¹` sum `∑_k |q_k|` is finite. -/
theorem summable_abs_qk (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr) :
    Summable (fun k : ℕ => |qk k w|) :=
  (summable_nat_add_iff 2).mp
    (summable_abs_qk_shift (d := d) hd hw hwnonpos hCreg hreg hint hgrle)

/-- The pieces are continuous. -/
lemma continuous_omegaTildePiece {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (k : ℕ) :
    Continuous (omegaTildePiece (d := d) k w) := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    have hfun : omegaTildePiece (d := d) 0 w = omegaPiece 0 w :=
      funext fun x => omegaTildePiece_of_lt 0 w (by norm_num) x
    rw [hfun]
    exact (contDiff_omegaPiece hw 0 le_rfl).continuous
  · exact (contDiff_omegaTildePiece k hw h1).continuous

/-- The ray restrictions of the pieces are continuous. -/
lemma continuous_omegaTildePiece_ray {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (k : ℕ) (y : ℝᵈ) :
    Continuous fun t : ℝ => omegaTildePiece (d := d) k w (t • y) :=
  (continuous_omegaTildePiece hw k).comp (by fun_prop)

/-- Each weighted piece is integrable. -/
lemma integrable_abs_omegaTildePiece_ray {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (k : ℕ)
    (y : ℝᵈ) :
    Integrable (fun t : ℝ => |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹) := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_omegaTildePiece k w).exists_bound_of_continuous
    (continuous_omegaTildePiece hw k)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (((continuous_omegaTildePiece_ray hw k y).abs).mul continuous_inv_one_add_sq
      |>.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹),
    abs_abs]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC (t • y)) (by positivity)

/-- **The weighted piece series is integrable.**  For every direction `y` the series
`∑_k |ω̃_k(t y)| (1+t²)⁻¹` is integrable: after the substitution `u = t ‖y‖` the `k`-th term has
integral at most `‖y‖ (2|q_k| + C(d) C_reg)` (with the correction only for `k ≤ 1`). -/
lemma integrable_tsum_abs_omegaTildePiece (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ (b : ℕ), b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (y : ℝᵈ) :
    Integrable (fun t : ℝ => ∑' k : ℕ,
      |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹) := by
  have hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := fun x => by
    simpa [norm_iteratedFDeriv_zero] using hwbound 0 (by norm_num) x
  set σ : ℝ := ‖y‖ with hσdef
  have hσnn : 0 ≤ σ := by rw [hσdef]; exact norm_nonneg _
  set B : ℕ → ℝ := fun k =>
    σ * (2 * |qk k w| + 32 * (Creg * tildeConst d) * (if k < 2 then 1 else 0)) with hBdef
  have hBnn : ∀ k : ℕ, 0 ≤ B k := by
    intro k
    rw [hBdef]
    refine mul_nonneg hσnn (add_nonneg (by positivity) ?_)
    have h3 : 0 ≤ Creg * tildeConst d := le_of_lt (mul_pos hCreg (tildeConst_pos d))
    split_ifs <;> positivity
  have hBsum : Summable B := by
    have h1 : Summable (fun k : ℕ => σ * (2 * |qk k w|)) := by
      have h := (summable_abs_qk (d := d) hd hw hwnonpos hCreg hreg hint hgrle).mul_left (2 * σ)
      exact h.congr fun k => by ring
    have h2 : Summable (fun k : ℕ =>
        σ * (32 * (Creg * tildeConst d) * (if k < 2 then 1 else 0))) := by
      refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) fun k hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rw [if_neg (by omega : ¬ k < 2), mul_zero, mul_zero]
    refine (h1.add h2).congr fun k => ?_
    rw [hBdef]
    ring
  have hAle : ∀ k : ℕ,
      (∫ t : ℝ, |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹) ≤ B k := by
    intro k
    by_cases hy : y = 0
    · have hz : (fun t : ℝ => |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹)
          = fun _ => (0 : ℝ) := by
        funext t
        rw [hy, smul_zero, omegaTildePiece_apply_zero k hwzero, abs_zero, zero_mul]
      rw [hz, integral_zero]
      exact hBnn k
    · have hσpos : 0 < σ := by rw [hσdef]; exact norm_pos_iff.mpr hy
      set ŷ : ℝᵈ := σ⁻¹ • y with hŷdef
      have hŷ : ‖ŷ‖ = 1 := by
        rw [hŷdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσpos), hσdef,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
      have hy_eq : σ • ŷ = y := by
        rw [hŷdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hσpos), one_smul]
      have hsubst : (∫ t : ℝ, |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹)
          = σ * ∫ u : ℝ, |omegaTildePiece (d := d) k w (u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹ := by
        have hrw : ∀ t : ℝ, t • y = (t * σ) • ŷ := by
          intro t; rw [← hy_eq, mul_smul]
        simp only [hrw]
        exact Commons.Measure.Real.integral_comp_mul_inv_one_add_sq
          (g := fun u : ℝ => |omegaTildePiece (d := d) k w (u • ŷ)|) hσpos
      rw [hsubst, hBdef]
      exact mul_le_mul_of_nonneg_left
        (integral_abs_omegaTildePiece_le hd hw hwzero hwk hCreg hwbound hσpos ŷ hŷ k) hσnn
  have hlin : ∀ k : ℕ, (∫⁻ t : ℝ,
        ENNReal.ofReal (|omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹))
      = ENNReal.ofReal (∫ t : ℝ,
        |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹) := fun k =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_abs_omegaTildePiece_ray hw k y)
      (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (by positivity))).symm
  have hfin : (∑' k : ℕ, ∫⁻ t : ℝ,
      ENNReal.ofReal (|omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹)) ≠ ⊤ := by
    simp only [hlin]
    have hbound : (∑' k : ℕ, ENNReal.ofReal
          (∫ t : ℝ, |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹))
        ≤ ENNReal.ofReal (∑' k : ℕ, B k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hBnn hBsum]
      exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hAle k)
    exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hbound
  exact (Commons.MeasureTheory.Integral.integrable_tsum_of_nonneg
    (f := fun k t => |omegaTildePiece (d := d) k w (t • y)| * (1 + t ^ 2)⁻¹)
    (fun k => (integrable_abs_omegaTildePiece_ray hw k y).aestronglyMeasurable)
    (fun k t => mul_nonneg (abs_nonneg _) (by positivity)) hfin).1

/-- The modified weight, restricted to a ray, is integrable against `(1+t²)⁻¹`. -/
lemma integrable_omegaTilde_ray (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ (b : ℕ), b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (y : ℝᵈ) :
    Integrable (fun t : ℝ => omegaTildeSum (d := d) w (t • y) * (1 + t ^ 2)⁻¹) := by
  refine Integrable.mono' (integrable_tsum_abs_omegaTildePiece hd hw hwnonpos hwzero hwk hCreg
    hwbound hint hgrle y) ?_ (Eventually.of_forall fun t => ?_)
  · exact (((contDiff_omegaTildeSum hd hw).continuous.comp
      (continuous_id.smul continuous_const)).mul continuous_inv_one_add_sq).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹)]
    have hsumm : Summable (fun k : ℕ => |omegaTildePiece (d := d) k w (t • y)|) := by
      obtain ⟨N, hN⟩ := exists_omegaTildePiece_eq_zero_of_ge (d := d) w (t • y)
      refine summable_of_ne_finset_zero (s := Finset.range N) fun k hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      rw [hN k hk, abs_zero]
    have h1 : |omegaTildeSum (d := d) w (t • y)|
        ≤ ∑' k : ℕ, |omegaTildePiece (d := d) k w (t • y)| := by
      rw [omegaTildeSum]
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun k : ℕ => omegaTildePiece (d := d) k w (t • y)) hsumm
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The shifted modified weight, restricted to a line, is integrable against `(1+t²)⁻¹`. -/
lemma integrable_omegaTilde_shift (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ (b : ℕ), b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (x y : ℝᵈ) :
    Integrable (fun t : ℝ => omegaTildeSum (d := d) w (x + t • y) * (1 + t ^ 2)⁻¹) := by
  have hΛ : 0 ≤ Creg * omegaLipConst d := by
    refine mul_nonneg hCreg.le ?_
    rw [omegaLipConst]; linarith [tildeLipConst_nonneg d]
  have hLip : ∀ t : ℝ,
      |omegaTildeSum (d := d) w (x + t • y) - omegaTildeSum (d := d) w (t • y)|
        ≤ (Creg * omegaLipConst d) * ‖x‖ := by
    intro t
    have h := lipschitz_omegaTildeSum (d := d) hd hw hwzero hCreg hwbound (x + t • y) (t • y)
    have h2 : x + t • y - t • y = x := by abel
    rw [h2] at h
    exact h
  have hG : Integrable (fun t : ℝ =>
      |omegaTildeSum (d := d) w (t • y)| * (1 + t ^ 2)⁻¹
        + (Creg * omegaLipConst d) * ‖x‖ * (1 + t ^ 2)⁻¹) := by
    have hA : Integrable (fun t : ℝ =>
        |omegaTildeSum (d := d) w (t • y)| * (1 + t ^ 2)⁻¹) := by
      refine (integrable_omegaTilde_ray hd hw hwnonpos hwzero hwk hCreg hwbound hint hgrle y).abs.congr ?_
      filter_upwards with t
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹)]
    exact hA.add (integrable_inv_one_add_sq.const_mul _)
  have haesm : AEStronglyMeasurable
      (fun t : ℝ => omegaTildeSum (d := d) w (x + t • y) * (1 + t ^ 2)⁻¹) volume :=
    (((contDiff_omegaTildeSum hd hw).continuous.comp
      (by fun_prop)).mul continuous_inv_one_add_sq).aestronglyMeasurable
  have hae : ∀ᵐ t : ℝ ∂volume,
      ‖omegaTildeSum (d := d) w (x + t • y) * (1 + t ^ 2)⁻¹‖
        ≤ |omegaTildeSum (d := d) w (t • y)| * (1 + t ^ 2)⁻¹
          + (Creg * omegaLipConst d) * ‖x‖ * (1 + t ^ 2)⁻¹ := by
    refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹)]
    have h1 : |omegaTildeSum (d := d) w (x + t • y)|
        ≤ |omegaTildeSum (d := d) w (t • y)| + (Creg * omegaLipConst d) * ‖x‖ := by
      have h2 := hLip t
      have h3 : |omegaTildeSum (d := d) w (x + t • y)| - |omegaTildeSum (d := d) w (t • y)|
          ≤ |omegaTildeSum (d := d) w (x + t • y) - omegaTildeSum (d := d) w (t • y)| :=
        abs_sub_abs_le_abs_sub _ _
      linarith
    calc |omegaTildeSum (d := d) w (x + t • y)| * (1 + t ^ 2)⁻¹
        ≤ (|omegaTildeSum (d := d) w (t • y)| + (Creg * omegaLipConst d) * ‖x‖)
            * (1 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = |omegaTildeSum (d := d) w (t • y)| * (1 + t ^ 2)⁻¹
            + (Creg * omegaLipConst d) * ‖x‖ * (1 + t ^ 2)⁻¹ := by ring
  exact Integrable.mono' hG haesm hae

/-- The `u^{-2}` bound for the Poisson weight on `(c, ∞)`. -/
lemma setIntegral_Ioi_one_add_sq_inv_le {c : ℝ} (hc : 1 ≤ c) :
    (∫ u in Set.Ioi c, (1 + u ^ 2)⁻¹) ≤ c⁻¹ := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hle : ∀ u ∈ Set.Ioi c, (1 + u ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ := by
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt (lt_of_le_of_lt hc hu)
    have h2 : (0 : ℝ) < u ^ 2 := pow_pos (lt_of_lt_of_le one_pos hu1) 2
    exact inv_anti₀ h2 (by linarith)
  refine le_trans (setIntegral_mono_of_nonneg (fun u hu => by positivity) hle
    ((Commons.MeasureTheory.Integral.integrableOn_inv_sq_of_le_abs hcpos).mono_set
      (fun u hu => ?_))) ?_
  · exact le_trans (le_of_lt hu) (le_abs_self u)
  · exact le_of_eq (Commons.MeasureTheory.Integral.integral_Ioi_inv_sq hcpos)

/-- **The estimate of §4.**  Let `T ≤ 0`, `wt ≤ T`, `T = wt` on the ball of radius `3c/2`, `wt`
Lipschitz with constant `CLip`, and let `wt` have ray tails bounded by `Q` beyond radius `c`.  Then
the extensions of `T` and `wt` differ by at most `(‖Im z‖/π)(4Q + 4 CLip‖Re z‖/c)` at `z`. -/
theorem abs_EomegaC_sub_le {T wt : ℝᵈ → ℝ} {CLip c Q : ℝ} {z : ℂᵈ}
    {σ : ℝ} (hσdef : σ = ‖imVec z‖) (hσpos : 0 < σ)
    (hCLip : 0 ≤ CLip)
    (hLip : ∀ x₁ x₂ : ℝᵈ, |wt x₁ - wt x₂| ≤ CLip * ‖x₁ - x₂‖)
    (hsign : ∀ x, wt x ≤ T x) (hTnonpos : ∀ x, T x ≤ 0)
    (hvan : ∀ x : ℝᵈ, ‖x‖ ≤ 3 * c / 2 → T x = wt x)
    (hTint : Integrable (fun t : ℝ => T (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹))
    (hWint : Integrable (fun t : ℝ => wt (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹))
    (hWintU : Integrable (fun u : ℝ => wt (reVec z + u • (σ⁻¹ • imVec z)) * (1 + u ^ 2)⁻¹))
    (hWint0 : Integrable (fun u : ℝ => wt (u • (σ⁻¹ • imVec z)) * (1 + u ^ 2)⁻¹))
    (hc : 1 ≤ c) (hx : ‖reVec z‖ ≤ c / 2)
    (hQ : ∀ v : ℝᵈ, ‖v‖ = 1 → rayTail wt c v ≤ Q) :
    |EomegaC T z - EomegaC wt z| ≤ σ / π * (4 * Q + 4 * CLip * ‖reVec z‖ / c) := by
  set ŷ : ℝᵈ := σ⁻¹ • imVec z with hŷdef
  have hŷ : ‖ŷ‖ = 1 := by
    have h1 : ‖imVec z‖ ≠ 0 := by rw [← hσdef]; exact ne_of_gt hσpos
    rw [hŷdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσpos), hσdef]
    exact inv_mul_cancel₀ h1
  have hy_eq : σ • ŷ = imVec z := by
    rw [hŷdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hσpos), one_smul]
  -- (1) difference of the extensions as a single integral
  have hdiff : EomegaC T z - EomegaC wt z
      = (1 / π) * ∫ t : ℝ,
          (T (reVec z + t • imVec z) - wt (reVec z + t • imVec z)) * (1 + t ^ 2)⁻¹ := by
    have hcongr : (fun t : ℝ => T (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹
        - wt (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹)
        = fun t : ℝ =>
            (T (reVec z + t • imVec z) - wt (reVec z + t • imVec z)) * (1 + t ^ 2)⁻¹ := by
      funext t; ring
    simp only [EomegaC, Eomega]
    rw [← mul_sub, ← integral_sub hTint hWint, hcongr]
  -- (2) substitute `u = t σ`
  have hsubst : (∫ t : ℝ,
        (T (reVec z + t • imVec z) - wt (reVec z + t • imVec z)) * (1 + t ^ 2)⁻¹)
      = σ * ∫ u : ℝ,
          (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹ := by
    have hrw : ∀ t : ℝ, reVec z + t • imVec z = reVec z + (t * σ) • ŷ := by
      intro t; rw [← hy_eq, mul_smul]
    simp only [hrw]
    exact Commons.Measure.Real.integral_comp_mul_inv_one_add_sq
      (g := fun u : ℝ => T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) hσpos
  -- (3) the main bound on the `u`-integral
  have hmain : |∫ u : ℝ,
        (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹|
      ≤ 4 * Q + 4 * CLip * ‖reVec z‖ / c := by
    set S : Set ℝ := Set.Ioi c ∪ Set.Iio (-c) with hSdef
    have hSmeas : MeasurableSet S := measurableSet_Ioi.union measurableSet_Iio
    have hdisj : Disjoint (Set.Ioi c) (Set.Iio (-c)) := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      simp only [Set.mem_Ioi] at hu1
      simp only [Set.mem_Iio] at hu2
      linarith
    have hmemS : ∀ u ∉ S, |u| ≤ c := by
      intro u hu
      simp only [hSdef, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, not_or, not_lt] at hu
      obtain ⟨h1, h2⟩ := hu
      rw [abs_le]
      exact ⟨by linarith, h1⟩
    have hmemS' : ∀ u ∈ S, 1 ≤ |u| := by
      intro u hu
      simp only [hSdef, Set.mem_union, Set.mem_Ioi, Set.mem_Iio] at hu
      rcases hu with h | h
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    -- integrability of the majorants (in the exact syntactic form needed below)
    have hintW : Integrable (fun u : ℝ => |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹) := by
      refine (hWintU.abs).congr ?_
      filter_upwards with u
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + u ^ 2)⁻¹)]
    have hint0 : Integrable (fun u : ℝ => |wt (u • ŷ)| * (1 + u ^ 2)⁻¹) := by
      refine (hWint0.abs).congr ?_
      filter_upwards with u
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + u ^ 2)⁻¹)]
    have hmaj2 : Integrable (fun u : ℝ => 2 * |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹) := by
      have h := hintW.const_mul 2
      refine h.congr ?_
      filter_upwards with u
      ring
    have hmaj3 : Integrable (fun u : ℝ =>
        2 * (|wt (u • ŷ)| + CLip * ‖reVec z‖) * (1 + u ^ 2)⁻¹) := by
      have h1 : Integrable (fun u : ℝ =>
          |wt (u • ŷ)| * (1 + u ^ 2)⁻¹ + CLip * ‖reVec z‖ * (1 + u ^ 2)⁻¹) :=
        hint0.add (integrable_inv_one_add_sq.const_mul _)
      have h := h1.const_mul 2
      refine h.congr ?_
      filter_upwards with u
      ring
    have hconstI : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq
    -- step (a): integrate the absolute value, and restrict to `S`
    have hstep1 : |∫ u : ℝ, (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹|
        ≤ ∫ u in S, |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹ := by
      refine le_trans (by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := fun u : ℝ =>
          (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹)) ?_
      have hvan' : ∀ u ∉ S,
          |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹ = 0 := by
        intro u hu
        have h1 : ‖reVec z + u • ŷ‖ ≤ 3 * c / 2 := by
          calc ‖reVec z + u • ŷ‖ ≤ ‖reVec z‖ + ‖u • ŷ‖ := norm_add_le _ _
            _ = ‖reVec z‖ + |u| := by rw [norm_smul, hŷ, mul_one, Real.norm_eq_abs]
            _ ≤ c / 2 + c := add_le_add hx (hmemS u hu)
            _ = 3 * c / 2 := by ring
        rw [hvan _ h1, sub_self, abs_zero, zero_mul]
      have hcongr : (fun u : ℝ =>
          |(T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹|)
          = fun u : ℝ =>
            |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹ := by
        funext u
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (σ ^ 2 + u ^ 2)⁻¹)]
      rw [hcongr, ← setIntegral_eq_integral_of_forall_compl_eq_zero hvan']
    -- step (b): bound by `2 |wt (x + u ŷ)| (1+u²)⁻¹`
    have hstep2 : (∫ u in S, |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹)
        ≤ ∫ u in S, 2 * |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹ := by
      refine setIntegral_mono_of_nonneg
        (fun u _ => mul_nonneg (abs_nonneg _) (by positivity)) (fun u hu => ?_)
        hmaj2.integrableOn
      have h1 : |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| ≤ |wt (reVec z + u • ŷ)| := by
        have h2 : 0 ≤ T (reVec z + u • ŷ) - wt (reVec z + u • ŷ) := sub_nonneg.mpr (hsign _)
        rw [abs_of_nonneg h2]
        calc T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)
            ≤ -wt (reVec z + u • ŷ) := by linarith [hTnonpos (reVec z + u • ŷ)]
          _ = |wt (reVec z + u • ŷ)| := by
                rw [abs_of_nonpos (le_trans (hsign (reVec z + u • ŷ))
                  (hTnonpos (reVec z + u • ŷ)))]
      have h2 : (σ ^ 2 + u ^ 2)⁻¹ ≤ 2 * (1 + u ^ 2)⁻¹ := by
        have hu1 : (1 : ℝ) ≤ |u| := hmemS' u hu
        have h6 : 1 + u ^ 2 ≤ 2 * (σ ^ 2 + u ^ 2) := by nlinarith [sq_nonneg σ, sq_abs u, hu1]
        calc (σ ^ 2 + u ^ 2)⁻¹ ≤ (2⁻¹ * (1 + u ^ 2))⁻¹ :=
              inv_anti₀ (by positivity) (by linarith [h6])
          _ = 2 * (1 + u ^ 2)⁻¹ := by
                rw [show (2 : ℝ)⁻¹ * (1 + u ^ 2) = (1 + u ^ 2) / 2 by ring, inv_div,
                  div_eq_mul_inv]
      calc |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹
          ≤ |wt (reVec z + u • ŷ)| * (2 * (1 + u ^ 2)⁻¹) :=
            mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
        _ = 2 * |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹ := by ring
    -- step (c): Lipschitz shift
    have hstep3 : (∫ u in S, 2 * |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹)
        ≤ ∫ u in S, 2 * (|wt (u • ŷ)| + CLip * ‖reVec z‖) * (1 + u ^ 2)⁻¹ := by
      refine setIntegral_mono_of_nonneg (fun u _ => by positivity) (fun u hu => ?_)
        hmaj3.integrableOn
      have h1 : |wt (reVec z + u • ŷ)| ≤ |wt (u • ŷ)| + CLip * ‖reVec z‖ := by
        have h2 := hLip (u • ŷ) (reVec z + u • ŷ)
        have h3 : u • ŷ - (reVec z + u • ŷ) = -reVec z := by abel
        rw [h3, norm_neg, abs_sub_comm] at h2
        have h4 : |wt (reVec z + u • ŷ)| - |wt (u • ŷ)|
            ≤ |wt (reVec z + u • ŷ) - wt (u • ŷ)| := abs_sub_abs_le_abs_sub _ _
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    -- step (d): split the integral
    have hstep4 : (∫ u in S, 2 * (|wt (u • ŷ)| + CLip * ‖reVec z‖) * (1 + u ^ 2)⁻¹)
        = 2 * ((∫ u in S, |wt (u • ŷ)| * (1 + u ^ 2)⁻¹)
            + CLip * ‖reVec z‖ * ∫ u in S, (1 + u ^ 2)⁻¹) := by
      have hsplit : (fun u : ℝ => 2 * (|wt (u • ŷ)| + CLip * ‖reVec z‖) * (1 + u ^ 2)⁻¹)
          = fun u : ℝ => 2 * (|wt (u • ŷ)| * (1 + u ^ 2)⁻¹)
              + 2 * (CLip * ‖reVec z‖ * (1 + u ^ 2)⁻¹) := by
        funext u; ring
      rw [hsplit, integral_add (hint0.integrableOn.const_mul 2)
        ((hconstI.const_mul (CLip * ‖reVec z‖)).integrableOn.const_mul 2)]
      simp only [integral_const_mul]
      ring
    -- step (e): the two remaining integrals
    have hray : (∫ u in S, |wt (u • ŷ)| * (1 + u ^ 2)⁻¹) ≤ 2 * Q := by
      rw [hSdef, setIntegral_union hdisj measurableSet_Iio hint0.integrableOn
        hint0.integrableOn]
      have h1 : (∫ u in Set.Ioi c, |wt (u • ŷ)| * (1 + u ^ 2)⁻¹) ≤ Q := hQ ŷ hŷ
      have h2 : (∫ u in Set.Iio (-c), |wt (u • ŷ)| * (1 + u ^ 2)⁻¹) ≤ Q := by
        rw [Commons.Measure.Real.setIntegral_Iio_neg_eq_Ioi]
        refine le_trans (le_of_eq ?_) (hQ (-ŷ) (by simpa using hŷ))
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        rw [neg_smul, smul_neg]
        ring_nf
      linarith
    have hconst : (∫ u in S, (1 + u ^ 2)⁻¹) ≤ 2 / c := by
      rw [hSdef, setIntegral_union hdisj measurableSet_Iio hconstI.integrableOn
        hconstI.integrableOn]
      have h1 : (∫ u in Set.Ioi c, (1 + u ^ 2)⁻¹) ≤ c⁻¹ :=
        setIntegral_Ioi_one_add_sq_inv_le hc
      have h2 : (∫ u in Set.Iio (-c), (1 + u ^ 2)⁻¹) ≤ c⁻¹ := by
        rw [Commons.Measure.Real.setIntegral_Iio_neg_eq_Ioi]
        refine le_trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun u _ => by
          show (1 + (-u) ^ 2)⁻¹ = (1 + u ^ 2)⁻¹
          ring_nf)) h1
      have h3 : (2 : ℝ) / c = c⁻¹ + c⁻¹ := by rw [div_eq_mul_inv]; ring
      linarith
    calc |∫ u : ℝ, (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹|
        ≤ ∫ u in S, |T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)| * (σ ^ 2 + u ^ 2)⁻¹ := hstep1
      _ ≤ ∫ u in S, 2 * |wt (reVec z + u • ŷ)| * (1 + u ^ 2)⁻¹ := hstep2
      _ ≤ ∫ u in S, 2 * (|wt (u • ŷ)| + CLip * ‖reVec z‖) * (1 + u ^ 2)⁻¹ := hstep3
      _ = 2 * ((∫ u in S, |wt (u • ŷ)| * (1 + u ^ 2)⁻¹)
            + CLip * ‖reVec z‖ * ∫ u in S, (1 + u ^ 2)⁻¹) := hstep4
      _ ≤ 2 * (2 * Q + CLip * ‖reVec z‖ * (2 / c)) := by
            refine mul_le_mul_of_nonneg_left (add_le_add hray ?_) (by norm_num)
            exact mul_le_mul_of_nonneg_left hconst (mul_nonneg hCLip (norm_nonneg _))
      _ = 4 * Q + 4 * CLip * ‖reVec z‖ / c := by ring
  calc |EomegaC T z - EomegaC wt z|
      = (1 / π) * |∫ t : ℝ,
          (T (reVec z + t • imVec z) - wt (reVec z + t • imVec z)) * (1 + t ^ 2)⁻¹| := by
        rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
    _ = (1 / π) * (σ * |∫ u : ℝ,
          (T (reVec z + u • ŷ) - wt (reVec z + u • ŷ)) * (σ ^ 2 + u ^ 2)⁻¹|) := by
        rw [hsubst, abs_mul, abs_of_pos hσpos]
    _ ≤ (1 / π) * (σ * (4 * Q + 4 * CLip * ‖reVec z‖ / c)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hσpos.le)
          (by positivity)
    _ = σ / π * (4 * Q + 4 * CLip * ‖reVec z‖ / c) := by ring

/-- **Uniform convergence of the extensions of the truncations.** -/
theorem tendstoUniformlyOn_EomegaC_truncSum (hd : 1 ≤ d) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0)
    (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0) {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ (b : ℕ), b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) :
    ∀ K : Set ℂᵈ, IsCompact K →
      TendstoUniformlyOn (fun n z => EomegaC (truncSum (d := d) n w) z)
        (fun z => EomegaC (omegaTildeSum (d := d) w) z) atTop K := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  set Λ : ℝ := Creg * omegaLipConst d with hΛdef
  have hΛnn : 0 ≤ Λ := by
    rw [hΛdef]
    refine mul_nonneg hCreg.le ?_
    rw [omegaLipConst]; linarith [tildeLipConst_nonneg d]
  have hLip : ∀ x₁ x₂ : ℝᵈ,
      |omegaTildeSum (d := d) w x₁ - omegaTildeSum (d := d) w x₂| ≤ Λ * ‖x₁ - x₂‖ :=
    fun x₁ x₂ => lipschitz_omegaTildeSum hd hw hwzero hCreg hwbound x₁ x₂
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℝ, ∀ z ∈ K, enorm z ≤ M := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, by simp⟩
    · obtain ⟨M, hM⟩ := (hK.image continuous_enorm).bddAbove
      exact ⟨M, fun z hz => hM ⟨z, hz, rfl⟩⟩
  set M : ℝ := max M₀ 0 with hMdef
  have hM : ∀ z ∈ K, enorm z ≤ M := fun z hz => le_trans (hM₀ z hz) (le_max_left _ _)
  have hMnn : 0 ≤ M := le_max_right _ _
  set δ : ℝ := ε * π / (16 * (M + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp (qkTail_tendsto_zero w) δ hδpos
  set K₂ : ℕ := max K₁ 2 with hK₂def
  have htail : qkTail K₂ w ≤ δ := by
    have h := hK₁ K₂ (le_max_left _ _)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (qkTail_nonneg _ _)] using h.le
  have hK₂2 : 2 ≤ K₂ := le_max_right K₁ 2
  set D : ℝ := max 4 (max ((2 : ℝ) ^ K₂) (max (2 * (M + 1))
    (16 * Λ * (M + 1) ^ 2 / (π * ε)))) with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _)
  obtain ⟨m, hm⟩ := exists_two_pow_gt D
  refine eventually_atTop.mpr ⟨m + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  set c : ℝ := (2 : ℝ) ^ (n - 2) with hcdef
  have hmn : m ≤ n - 2 := by omega
  have hcm : (2 : ℝ) ^ m ≤ c := by rw [hcdef]; exact pow_le_pow_right₀ (by norm_num) hmn
  have hc : D < c := lt_of_lt_of_le hm hcm
  have hc4 : 4 ≤ c := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hc)
  have hcK : (2 : ℝ) ^ K₂ ≤ c :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hc)
  have hcM : 2 * (M + 1) ≤ c :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hc)
  have hcΛ : 16 * Λ * (M + 1) ^ 2 / (π * ε) ≤ c :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hc)
  have hP : (2 : ℝ) ^ (n - 1) = 2 * c := by
    rw [hcdef, ← pow_succ']
    congr 1
    omega
  intro z hz
  rw [dist_eq_norm]
  have hzM : enorm z ≤ M := hM z hz
  by_cases hσ : imVec z = 0
  · have h1 : EomegaC (truncSum (d := d) n w) z = EomegaC (omegaTildeSum (d := d) w) z := by
      have hrn : (n - 1) + 1 = n := by omega
      rw [EomegaC, EomegaC, hσ, Eomega_apply_zero, Eomega_apply_zero]
      rw [truncSum_apply, omegaTildeSum_eq_sum_range (n - 1) w ?_, hrn]
      · have h2 : ‖reVec z‖ ≤ enorm z := norm_reVec_le_enorm z
        have h4 : M < (2 : ℝ) ^ (n - 1) := by rw [hP]; linarith
        linarith
    rw [h1, sub_self, norm_zero]
    exact hε
  · have hσpos : 0 < ‖imVec z‖ := norm_pos_iff.mpr hσ
    have hz' : ‖reVec z‖ ≤ enorm z := norm_reVec_le_enorm z
    have hxM : ‖reVec z‖ ≤ M := le_trans hz' hzM
    have hx : ‖reVec z‖ ≤ c / 2 := by linarith
    have hTint : Integrable (fun t : ℝ =>
        truncSum (d := d) n w (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹) := by
      obtain ⟨C, hC⟩ := (truncSum_hasCompactSupport n w).exists_bound_of_continuous
        (truncSum_contDiff n hw).continuous
      refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
        ((((truncSum_contDiff n hw).continuous.comp (by fun_prop)).mul
          continuous_inv_one_add_sq).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC _) (by positivity)
    have hWint := integrable_omegaTilde_shift hd hw hwnonpos hwzero hwk hCreg hwbound hint
      hgrle (reVec z) (imVec z)
    have hWintU := integrable_omegaTilde_shift hd hw hwnonpos hwzero hwk hCreg hwbound hint
      hgrle (reVec z) ((‖imVec z‖)⁻¹ • imVec z)
    have hWint0 := integrable_omegaTilde_ray hd hw hwnonpos hwzero hwk hCreg hwbound hint
      hgrle ((‖imVec z‖)⁻¹ • imVec z)
    have hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := fun x => by
      simpa [norm_iteratedFDeriv_zero] using hwbound 0 (by norm_num) x
    have hQ : ∀ v : ℝᵈ, ‖v‖ = 1 → rayTail (omegaTildeSum (d := d) w) c v ≤ qkTail K₂ w :=
      fun v hv => rayTail_omegaTildeSum_le hd hw hwnonpos hwzero hwk hCreg hreg hint hgrle
        v hv (by linarith : (4 : ℝ) ≤ c) hK₂2 hcK
    have hvan : ∀ x : ℝᵈ, ‖x‖ ≤ 3 * c / 2 →
        truncSum (d := d) n w x = omegaTildeSum (d := d) w x := by
      intro x hx3
      have h4 : 3 * c / 2 < (2 : ℝ) ^ (n - 1) := by rw [hP]; linarith
      have hrn : (n - 1) + 1 = n := by omega
      rw [truncSum_apply, omegaTildeSum_eq_sum_range (n - 1) w (lt_of_le_of_lt hx3 h4), hrn]
    have hb := abs_EomegaC_sub_le (T := truncSum (d := d) n w)
      (wt := omegaTildeSum (d := d) w) (CLip := Λ) (c := c) (Q := qkTail K₂ w) (z := z)
      (σ := ‖imVec z‖) rfl hσpos hΛnn hLip (fun x => omegaTildeSum_le_truncSum hwk n x)
      (fun x => truncSum_nonpos n hwk x) hvan hTint hWint hWintU hWint0 (by linarith)
      (by linarith) hQ
    have hb' : |EomegaC (truncSum (d := d) n w) z - EomegaC (omegaTildeSum (d := d) w) z|
        < ε := by
      refine lt_of_le_of_lt hb ?_
      have hμ : (0 : ℝ) < M + 1 := by linarith
      have hcpos : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc4
      have hσμ : ‖imVec z‖ ≤ M + 1 := by
        linarith [le_trans (norm_imVec_le_enorm z) hzM]
      have hρμ : ‖reVec z‖ ≤ M + 1 := by linarith [hxM]
      have hXle : 4 * qkTail K₂ w + 4 * Λ * ‖reVec z‖ / c
          ≤ 4 * δ + 4 * Λ * (M + 1) / c := by
        refine add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num)) ?_
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hρμ (by positivity)
      have h1 : ‖imVec z‖ / π * (4 * qkTail K₂ w + 4 * Λ * ‖reVec z‖ / c)
          ≤ (M + 1) / π * (4 * δ + 4 * Λ * (M + 1) / c) := by
        have h1a : ‖imVec z‖ * π⁻¹ ≤ (M + 1) * π⁻¹ :=
          mul_le_mul_of_nonneg_right hσμ (by positivity)
        have h1b : (0 : ℝ) ≤ 4 * qkTail K₂ w + 4 * Λ * ‖reVec z‖ / c :=
          add_nonneg (mul_nonneg (by norm_num) (qkTail_nonneg _ _))
            (div_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) hcpos.le)
        have h1c : (0 : ℝ) ≤ (M + 1) * π⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul h1a hXle h1b h1c
      have hfin : (M + 1) / π * (4 * δ + 4 * Λ * (M + 1) / c) < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ Real.pi_pos]
        have h2 : (M + 1) * (4 * δ) = ε * π / 4 := by
          rw [hδdef]
          field_simp
          ring
        have h3 : (M + 1) * (4 * Λ * (M + 1) / c) ≤ ε * π / 4 := by
          rw [show (M + 1) * (4 * Λ * (M + 1) / c) = 4 * Λ * (M + 1) ^ 2 / c by ring]
          rw [div_le_iff₀ hcpos]
          have h9 := hcΛ
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < π * ε)] at h9
          nlinarith [h9, hε.le, hΛnn, hμ]
        rw [mul_add]
        nlinarith [h2, h3, hε, Real.pi_pos]
      exact lt_of_le_of_lt h1 hfin
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hb'

end Submission.FUP
