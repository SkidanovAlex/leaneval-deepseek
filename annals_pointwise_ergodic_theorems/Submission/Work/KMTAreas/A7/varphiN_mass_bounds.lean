import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTAreas.A7

open MeasureTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary rescalings of a function of one real variable -/

/-- Substitution rule for the integral of the modulus of a rescaled function:
`∫ ‖f (c y)‖ dy = c⁻¹ ∫ ‖f‖` for `c > 0`. -/
lemma integral_norm_comp_mul_left_varphiN (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ y : ℝ, ‖f (c * y)‖) = c⁻¹ * (∫ y : ℝ, ‖f y‖) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => ‖f y‖) c
  rw [h, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]

/-- The second derivative of a rescaled `C²` function: `(f (c ·))'' = c² · f''(c ·)`. -/
lemma iteratedDeriv_two_comp_mul_left_varphiN (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (c x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => f (c * y)) x
      = (c ^ 2 : ℝ) • iteratedDeriv 2 f (c * x) :=
  congrFun (iteratedDeriv_comp_const_smul (𝕜 := ℝ) (F := ℂ) hf c) x

/-! ## Integrability of the cutoff `η` and of its second derivative -/

lemma hasCompactSupport_kmtEta_varphiN : HasCompactSupport Work.KMTContract.kmtEta := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h : ¬ (1 ≤ |x|) := fun hc => hx (Work.KMTContract.kmtEta_zero hc)
  rw [not_le] at h
  exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma integrable_kmtEta_varphiN : Integrable Work.KMTContract.kmtEta :=
  (contDiff_kmtEta 2).continuous.integrable_of_hasCompactSupport hasCompactSupport_kmtEta_varphiN

lemma hasCompactSupport_iteratedDeriv_two_kmtEta_varphiN :
    HasCompactSupport (iteratedDeriv 2 Work.KMTContract.kmtEta) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasCompactSupport_kmtEta_varphiN.deriv).deriv

lemma integrable_iteratedDeriv_two_kmtEta_varphiN :
    Integrable (fun y : ℝ => ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖) := by
  have hcont : Continuous (iteratedDeriv 2 Work.KMTContract.kmtEta) :=
    (contDiff_kmtEta 2).continuous_iteratedDeriv 2 le_rfl
  exact (hcont.integrable_of_hasCompactSupport hasCompactSupport_iteratedDeriv_two_kmtEta_varphiN).norm

/-! ## The mass bound -/

lemma varphiN_mass_le (N k : ℕ) (hk : k ≠ 0) :
    (∫ y : ℝ, ‖varphiN N k y‖)
      ≤ (3 / 2) * (∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖)
          / (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
  set I : ℝ := ∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖ with hI
  set a : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) with ha
  set b : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) with hb
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hapos : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos h2 _
  have hbpos : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos h2 _
  have hdef : ∀ y : ℝ, varphiN N k y
      = Work.KMTContract.kmtEta (a * y) - Work.KMTContract.kmtEta (b * y) := by
    intro y
    simp only [varphiN, if_neg hk, ha, hb]
  have hIA : Integrable (fun y : ℝ => ‖Work.KMTContract.kmtEta (a * y)‖) :=
    integrable_kmtEta_varphiN.norm.comp_mul_left' (ne_of_gt hapos)
  have hIB : Integrable (fun y : ℝ => ‖Work.KMTContract.kmtEta (b * y)‖) :=
    integrable_kmtEta_varphiN.norm.comp_mul_left' (ne_of_gt hbpos)
  have hIf : Integrable (fun y : ℝ => ‖varphiN N k y‖) := (integrable_varphiN N k).norm
  have hle : (∫ y, ‖varphiN N k y‖)
      ≤ ∫ y, (‖Work.KMTContract.kmtEta (a * y)‖ + ‖Work.KMTContract.kmtEta (b * y)‖) := by
    refine integral_mono hIf (hIA.add hIB) ?_
    intro y
    change ‖varphiN N k y‖
      ≤ ‖Work.KMTContract.kmtEta (a * y)‖ + ‖Work.KMTContract.kmtEta (b * y)‖
    rw [hdef y]
    exact norm_sub_le _ _
  have hsum : (∫ y, (‖Work.KMTContract.kmtEta (a * y)‖ + ‖Work.KMTContract.kmtEta (b * y)‖))
      = (∫ y, ‖Work.KMTContract.kmtEta (a * y)‖)
        + (∫ y, ‖Work.KMTContract.kmtEta (b * y)‖) :=
    integral_add hIA hIB
  have hA : (∫ y, ‖Work.KMTContract.kmtEta (a * y)‖) = a⁻¹ * I :=
    integral_norm_comp_mul_left_varphiN _ hapos
  have hB : (∫ y, ‖Work.KMTContract.kmtEta (b * y)‖) = b⁻¹ * I :=
    integral_norm_comp_mul_left_varphiN _ hbpos
  have hb_eq : b = 2 * a := by
    rw [hb, ha, Real.rpow_add h2, Real.rpow_one]
    ring
  have hkey : a⁻¹ + b⁻¹ = (3 / 2) * a⁻¹ := by
    rw [hb_eq, mul_inv]
    norm_num
    ring
  calc (∫ y, ‖varphiN N k y‖)
      ≤ ∫ y, (‖Work.KMTContract.kmtEta (a * y)‖ + ‖Work.KMTContract.kmtEta (b * y)‖) := hle
    _ = (∫ y, ‖Work.KMTContract.kmtEta (a * y)‖)
          + (∫ y, ‖Work.KMTContract.kmtEta (b * y)‖) := hsum
    _ = a⁻¹ * I + b⁻¹ * I := by rw [hA, hB]
    _ = (3 / 2) * I / (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
        rw [← add_mul, hkey, ha, div_eq_mul_inv]
        ring

lemma varphiN_mass_le_zero (N : ℕ) :
    (∫ y : ℝ, ‖varphiN N 0 y‖)
      ≤ (3 / 2) * (∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖)
          / (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) := by
  set I : ℝ := ∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖ with hI
  set c : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) with hc
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos h2 _
  have hI0 : 0 ≤ I := by rw [hI]; exact integral_nonneg (fun y => norm_nonneg _)
  have hcval : c = (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by rw [hc, sub_zero]
  have hdef : ∀ y : ℝ, varphiN N 0 y = Work.KMTContract.kmtEta (c * y) := by
    intro y
    rw [hcval]
    rfl
  have hfe : (fun y : ℝ => ‖varphiN N 0 y‖)
      = fun y => ‖Work.KMTContract.kmtEta (c * y)‖ := by
    funext y
    rw [hdef y]
  rw [hfe, integral_norm_comp_mul_left_varphiN _ hcpos]
  have hEq : (3 / 2) * I / c = (3 / 2) * (c⁻¹ * I) := by
    rw [div_eq_mul_inv]; ring
  rw [hEq]
  have hnn : 0 ≤ c⁻¹ * I := mul_nonneg (inv_nonneg.mpr hcpos.le) hI0
  linarith

/-! ## The second-derivative bound -/

lemma varphiN_deriv_le (N k : ℕ) (hk : k ≠ 0) :
    (∫ y : ℝ, ‖iteratedDeriv 2 (varphiN N k) y‖)
      ≤ 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
          * (∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖) := by
  set J : ℝ := ∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ with hJ
  set a : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) with ha
  set b : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) with hb
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hapos : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos h2 _
  have hbpos : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos h2 _
  have hdef : ∀ y : ℝ, varphiN N k y
      = Work.KMTContract.kmtEta (a * y) - Work.KMTContract.kmtEta (b * y) := by
    intro y
    simp only [varphiN, if_neg hk, ha, hb]
  have hca : ContDiff ℝ 2 (fun y : ℝ => Work.KMTContract.kmtEta (a * y)) :=
    (contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
  have hcb : ContDiff ℝ 2 (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) :=
    (contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
  have hchain_a : ∀ y : ℝ,
      iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (a * y)) y
        = (a ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (a * y) := fun y =>
    (iteratedDeriv_two_comp_mul_left_varphiN _ (contDiff_kmtEta 2) a y)
  have hchain_b : ∀ y : ℝ,
      iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) y
        = (b ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (b * y) := fun y =>
    (iteratedDeriv_two_comp_mul_left_varphiN _ (contDiff_kmtEta 2) b y)
  have hpt : ∀ y : ℝ, ‖iteratedDeriv 2 (varphiN N k) y‖
      ≤ a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
        + b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖ := by
    intro y
    have hsub : iteratedDeriv 2 (varphiN N k) y
        = iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (a * y)) y
          - iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) y := by
      rw [show varphiN N k = (fun y : ℝ => Work.KMTContract.kmtEta (a * y))
          - (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) from funext hdef]
      exact iteratedDeriv_sub hca.contDiffAt hcb.contDiffAt
    rw [hsub]
    calc ‖iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (a * y)) y
            - iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) y‖
        ≤ ‖iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (a * y)) y‖
            + ‖iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (b * y)) y‖ :=
          norm_sub_le _ _
      _ = ‖(a ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
            + ‖(b ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖ := by
          rw [hchain_a y, hchain_b y]
      _ = a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
            + b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg a),
            Real.norm_of_nonneg (sq_nonneg b)]
  have hJa : Integrable
      (fun y : ℝ => a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖) :=
    (integrable_iteratedDeriv_two_kmtEta_varphiN.comp_mul_left' (ne_of_gt hapos)).const_mul (a ^ 2)
  have hJb : Integrable
      (fun y : ℝ => b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) :=
    (integrable_iteratedDeriv_two_kmtEta_varphiN.comp_mul_left' (ne_of_gt hbpos)).const_mul (b ^ 2)
  have hIf : Integrable (fun y : ℝ => ‖iteratedDeriv 2 (varphiN N k) y‖) :=
    integrable_iteratedDeriv_varphiN N k 2 le_rfl
  have hle : (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖)
      ≤ ∫ y, (a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
          + b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) :=
    integral_mono hIf (hJa.add hJb) hpt
  have hsplit : (∫ y, (a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
          + b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖))
      = (∫ y, a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖)
        + (∫ y, b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) :=
    integral_add hJa hJb
  have hIa : (∫ y, a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖) = a * J := by
    rw [integral_const_mul (a ^ 2) (fun y => ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖),
      integral_norm_comp_mul_left_varphiN _ hapos]
    field_simp [ne_of_gt hapos]
    ring
  have hIb : (∫ y, b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) = b * J := by
    rw [integral_const_mul (b ^ 2) (fun y => ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖),
      integral_norm_comp_mul_left_varphiN _ hbpos]
    field_simp [ne_of_gt hbpos]
    ring
  have hb_eq : b = 2 * a := by
    rw [hb, ha, Real.rpow_add h2, Real.rpow_one]
    ring
  calc (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖)
      ≤ ∫ y, (a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖
          + b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) := hle
    _ = (∫ y, a ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (a * y)‖)
          + (∫ y, b ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (b * y)‖) := hsplit
    _ = a * J + b * J := by rw [hIa, hIb]
    _ = 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * J := by
        rw [hb_eq, ha]
        ring

lemma varphiN_deriv_le_zero (N : ℕ) :
    (∫ y : ℝ, ‖iteratedDeriv 2 (varphiN N 0) y‖)
      ≤ 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ))
          * (∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖) := by
  set J : ℝ := ∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ with hJ
  set c : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) with hc
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos h2 _
  have hJ0 : 0 ≤ J := by rw [hJ]; exact integral_nonneg (fun y => norm_nonneg _)
  have hcval : c = (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by rw [hc, sub_zero]
  have hdef : ∀ y : ℝ, varphiN N 0 y = Work.KMTContract.kmtEta (c * y) := by
    intro y
    rw [hcval]
    rfl
  have hchain : ∀ y : ℝ,
      iteratedDeriv 2 (fun y : ℝ => Work.KMTContract.kmtEta (c * y)) y
        = (c ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (c * y) := fun y =>
    (iteratedDeriv_two_comp_mul_left_varphiN _ (contDiff_kmtEta 2) c y)
  have hpt : ∀ y : ℝ, ‖iteratedDeriv 2 (varphiN N 0) y‖
      ≤ c ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖ := by
    intro y
    have : iteratedDeriv 2 (varphiN N 0) y
        = (c ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (c * y) := by
      rw [show varphiN N 0 = (fun y : ℝ => Work.KMTContract.kmtEta (c * y)) from funext hdef]
      exact hchain y
    rw [this, norm_smul, Real.norm_of_nonneg (sq_nonneg c)]
  have hJc : Integrable (fun y : ℝ => c ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖) :=
    (integrable_iteratedDeriv_two_kmtEta_varphiN.comp_mul_left' (ne_of_gt hcpos)).const_mul (c ^ 2)
  have hIf : Integrable (fun y : ℝ => ‖iteratedDeriv 2 (varphiN N 0) y‖) :=
    integrable_iteratedDeriv_varphiN N 0 2 le_rfl
  have hle : (∫ y, ‖iteratedDeriv 2 (varphiN N 0) y‖)
      ≤ ∫ y, c ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖ :=
    integral_mono hIf hJc hpt
  have hval : (∫ y, c ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖) = c * J := by
    rw [integral_const_mul (c ^ 2) (fun y => ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖),
      integral_norm_comp_mul_left_varphiN _ hcpos]
    field_simp [ne_of_gt hcpos]
    ring
  have hfin : c * J ≤ 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) * J := by
    have hnn : 0 ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) * J :=
      mul_nonneg (Real.rpow_pos_of_pos h2 _).le hJ0
    rw [hc]
    linarith
  calc (∫ y, ‖iteratedDeriv 2 (varphiN N 0) y‖)
      ≤ ∫ y, c ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (c * y)‖ := hle
    _ = c * J := hval
    _ ≤ 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (0 : ℝ)) * J := hfin

/-! ## The requested bounds -/

theorem varphiN_mass_bounds (N k : ℕ) (hk : 2 ^ k ≤ N) :
    (∫ y : ℝ, ‖Work.KMTAreas.A7.varphiN N k y‖)
        ≤ (3 / 2) * (∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖)
            / (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) ∧
      (∫ y : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphiN N k) y‖)
        ≤ 3 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
            * (∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖) ∧
      1 ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · rw [hk0]
      simpa using varphiN_mass_le_zero N
    · exact varphiN_mass_le N k hk0
  · by_cases hk0 : k = 0
    · rw [hk0]
      simpa using varphiN_deriv_le_zero N
    · exact varphiN_deriv_le N k hk0
  · have h2 : (1 : ℝ) < 2 := by norm_num
    have hkle : k ≤ Nat.log 2 (max N 2) := by
      rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : max N 2 ≠ 0)]
      exact hk.trans (le_max_left _ _)
    have hleR : (k : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
      rw [Work.Analysis.EndVar.logN]
      exact_mod_cast hkle
    have hD : 0 ≤ (Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) := by linarith
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hD

end

end Work.KMTAreas.A7
