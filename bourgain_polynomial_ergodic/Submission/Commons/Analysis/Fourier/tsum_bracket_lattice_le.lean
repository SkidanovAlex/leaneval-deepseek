import Mathlib
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_assembly_d2

open MeasureTheory
open scoped BigOperators ENNReal

namespace Commons.Analysis.Fourier

namespace TsumBracketAux

/-- The Japanese bracket of exponent `d` on `Fin d → ℝ` is integrable for `d ≥ 1`. -/
lemma integrable_bracket (d : ℕ) (hd : 1 ≤ d) :
    Integrable (fun y : Fin d → ℝ => (1 + ‖y‖^2) ^ (-(d:ℝ))) volume := by
  have hd2 : (Module.finrank ℝ (Fin d → ℝ) : ℝ) < 2 * (d:ℝ) := by
    rw [Module.finrank_pi]
    have h1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    simp only [Fintype.card_fin]
    nlinarith
  have hH := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Fin d → ℝ)))
      (r := 2*(d:ℝ)) hd2
  have hexp : -(2 * (d:ℝ)) / 2 = -(d:ℝ) := by ring
  simpa only [hexp] using hH

/-- Pointwise bracket comparison on a grid box of side `2` (sup norm). -/
lemma box_pointwise (d : ℕ) (_hd : 1 ≤ d) (γ : Fin d → ℝ) (n : Fin d → ℤ)
    (x : Fin d → ℝ) (hx : x ∈ LogvinenkoSereda.d2_upperBox n γ) :
    (9:ℝ) ^ (-(d:ℝ)) * (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ))
      ≤ (1 + ‖x‖^2) ^ (-(d:ℝ)) := by
  set v : Fin d → ℝ := fun i => γ i + 2*(n i:ℝ) with hv
  have hx' : ∀ i, v i ≤ x i ∧ x i < v i + 2 := by
    intro i
    have h := hx i
    rw [hv]
    constructor <;> linarith [h.1, h.2]
  have hdiff : ‖x - v‖ ≤ 2 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    have h := hx' i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hnorm_x : ‖x‖ ≤ ‖v‖ + 2 := by
    calc ‖x‖ = ‖v + (x - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖x - v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + 2 := by linarith
  have hbase : 1 + ‖x‖^2 ≤ 9 * (1 + ‖v‖^2) := by
    have h1 : 0 ≤ ‖v‖ := norm_nonneg _
    have h2 : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [hnorm_x, h1, h2, sq_nonneg (‖v‖ - 2)]
  have hposx : 0 < 1 + ‖x‖^2 := by positivity
  have hposv : 0 < 1 + ‖v‖^2 := by positivity
  rw [hv] at hbase hposv ⊢
  calc (9:ℝ) ^ (-(d:ℝ)) * (1 + ‖(fun i : Fin d => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ))
      = (9 * (1 + ‖(fun i : Fin d => γ i + 2*(n i:ℝ))‖^2)) ^ (-(d:ℝ)) := by
        rw [Real.mul_rpow (by norm_num) hposv.le]
    _ ≤ (1 + ‖x‖^2) ^ (-(d:ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos hposx hbase
        exact neg_nonpos.mpr (Nat.cast_nonneg d)

/-- Integral lower bound on a grid box. -/
lemma box_integral_lower (d : ℕ) (hd : 1 ≤ d) (γ : Fin d → ℝ) (n : Fin d → ℤ)
    (hint : Integrable (fun y : Fin d → ℝ => (1 + ‖y‖^2) ^ (-(d:ℝ))) volume) :
    (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ)) ≤
      (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2) ^ (-(d:ℝ)) := by
  set v : Fin d → ℝ := fun i => γ i + 2*(n i:ℝ) with hv
  set c : ℝ := (9:ℝ) ^ (-(d:ℝ)) * (1 + ‖v‖^2) ^ (-(d:ℝ)) with hc
  have hboxmeas : MeasurableSet (LogvinenkoSereda.d2_upperBox n γ) :=
    LogvinenkoSereda.d2_measurableSet_upperBox n γ
  have hvolne : volume (LogvinenkoSereda.d2_upperBox n γ) ≠ ∞ := by
    rw [LogvinenkoSereda.d2v_volume_upperBox]; exact ENNReal.ofReal_ne_top
  have hcle : ∀ x ∈ LogvinenkoSereda.d2_upperBox n γ, c ≤ (1 + ‖x‖^2) ^ (-(d:ℝ)) := by
    intro x hx
    rw [hc, hv]
    exact box_pointwise d hd γ n x hx
  have hcInt : IntegrableOn (fun _ : Fin d → ℝ => c) (LogvinenkoSereda.d2_upperBox n γ) volume :=
    integrableOn_const hvolne (by simp)
  have hInt : IntegrableOn (fun y : Fin d → ℝ => (1 + ‖y‖^2)^(-(d:ℝ)))
      (LogvinenkoSereda.d2_upperBox n γ) volume := hint.integrableOn
  have hmono : ∫ x in LogvinenkoSereda.d2_upperBox n γ, c
      ≤ ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) :=
    setIntegral_mono_on hcInt hInt hboxmeas hcle
  rw [setIntegral_const] at hmono
  simp only [Measure.real, smul_eq_mul] at hmono
  rw [LogvinenkoSereda.d2v_volume_upperBox_toReal] at hmono
  have hBne : (9:ℝ)^d ≠ 0 := by positivity
  have hkey : (9:ℝ)^d * c = (1 + ‖v‖^2)^(-(d:ℝ)) := by
    rw [hc, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 9), Real.rpow_natCast]
    rw [← mul_assoc, mul_inv_cancel₀ hBne, one_mul]
  have hstep : (2:ℝ)^d * (1 + ‖v‖^2)^(-(d:ℝ))
      ≤ (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) := by
    have h1 : (9:ℝ)^d * ((2:ℝ)^d * c)
        ≤ (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    calc (2:ℝ)^d * (1 + ‖v‖^2)^(-(d:ℝ))
        = (2:ℝ)^d * ((9:ℝ)^d * c) := by rw [hkey]
      _ = (9:ℝ)^d * ((2:ℝ)^d * c) := by ring
      _ ≤ (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) := h1
  have h2pow : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have hvnn : 0 ≤ (1 + ‖v‖^2)^(-(d:ℝ)) := by positivity
  have hgoal : (1 + ‖v‖^2)^(-(d:ℝ))
      ≤ (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) := by
    calc (1 + ‖v‖^2)^(-(d:ℝ)) = 1 * (1 + ‖v‖^2)^(-(d:ℝ)) := by ring
      _ ≤ (2:ℝ)^d * (1 + ‖v‖^2)^(-(d:ℝ)) := mul_le_mul_of_nonneg_right h2pow hvnn
      _ ≤ _ := hstep
  rw [hv] at hgoal
  exact hgoal

/-- Uniform bound on the lattice sum of the `d`-bracket over `Fin d → ℝ`. -/
lemma lattice_sum_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : Fin d → ℝ,
      (∑' (n : Fin d → ℤ), (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ))) ≤ C := by
  have hint := integrable_bracket d hd
  refine ⟨max 1 ((9:ℝ)^d * ∫ y : Fin d → ℝ, (1 + ‖y‖^2)^(-(d:ℝ))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro γ
  have htsum := LogvinenkoSereda.d2_hasSum_setIntegral_gridBoxIco γ
    (fun y : Fin d → ℝ => (1 + ‖y‖^2)^(-(d:ℝ))) hint
  set I : ℝ := ∫ y : Fin d → ℝ, (1 + ‖y‖^2)^(-(d:ℝ)) with hIdef
  have hterm : ∀ n : Fin d → ℤ,
      (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ))
        ≤ (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ)) :=
    fun n => box_integral_lower d hd γ n hint
  have hsummF : Summable (fun n : Fin d → ℤ =>
      ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ))) := by
    have h := htsum.summable
    convert h using 1
  have hsummK : Summable (fun n : Fin d → ℤ =>
      (9:ℝ)^d * ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ))) :=
    hsummF.mul_left _
  have hgf : Summable (fun n : Fin d → ℤ =>
      (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm hsummK
  have hle := Summable.tsum_le_tsum hterm hgf hsummK
  have htsumI : (∑' n : Fin d → ℤ,
      ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ))) = I := by
    have h := htsum.tsum_eq
    convert h using 1
  calc (∑' n : Fin d → ℤ, (1 + ‖(fun i => γ i + 2*(n i:ℝ))‖^2) ^ (-(d:ℝ)))
      ≤ (∑' n : Fin d → ℤ, (9:ℝ)^d *
          ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ))) := hle
    _ = (9:ℝ)^d * (∑' n : Fin d → ℤ,
          ∫ x in LogvinenkoSereda.d2_upperBox n γ, (1 + ‖x‖^2)^(-(d:ℝ))) := by
        rw [tsum_mul_left]
    _ = (9:ℝ)^d * I := by rw [htsumI]
    _ ≤ max 1 ((9:ℝ)^d * ∫ y : Fin d → ℝ, (1 + ‖y‖^2)^(-(d:ℝ))) := by
        rw [hIdef]; exact le_max_right _ _

end TsumBracketAux

theorem tsum_bracket_lattice_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : EuclideanSpace ℝ (Fin d),
      (∑' (ℓ : Fin d → ℤ), (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ))) ≤ C := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨1, one_pos, ?_⟩
    intro η
    rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i) (fun b hb => by
      exact absurd (Subsingleton.elim b _) hb)]
    norm_num
  · obtain ⟨C, hCpos, hCbound⟩ := TsumBracketAux.lattice_sum_bound d hd
    refine ⟨C, hCpos, ?_⟩
    intro η
    have hcongr : (∑' (ℓ : Fin d → ℤ),
        (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ)))
        = (∑' (ℓ : Fin d → ℤ),
            (1 + ‖(fun i : Fin d => η i + 2*(ℓ i:ℝ))‖ ^ 2) ^ (-(d:ℝ))) := by
      apply tsum_congr
      intro ℓ
      have hbase : (η + (fun i : Fin d => 2 * (ℓ i : ℝ)))
          = (fun i : Fin d => η i + 2*(ℓ i:ℝ)) := by
        ext i; simp
      rw [hbase]
    rw [hcongr]
    exact hCbound (fun i => η i)

end Commons.Analysis.Fourier
