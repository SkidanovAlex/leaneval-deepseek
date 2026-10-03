import Mathlib
import Submission.Work.Analysis.Fourier.lattice_sup_lp_sampling

open MeasureTheory
open scoped ENNReal FourierTransform BigOperators

namespace Work.Analysis.Fourier

/-- `L^p` bound for a finite "comb" of translates of a Schwartz function: for `1 < p < ∞` there is `K > 0` such that for every finitely supported `b : ℤ → ℂ`,
`∫⁻_ℝ ‖Σ_{m∈s} b_m φ(x-m)‖^p ≤ K^p · Σ_{m∈s} ‖b_m‖^p`.

Route: pointwise `‖Σ_m b_m φ(x-m)‖ ≤ Σ_m ‖b_m‖‖φ(x-m)‖`, then Hölder on the finite sum with exponents `(p, p/(p-1))` after writing `‖b_m‖‖φ(x-m)‖ = (‖b_m‖‖φ(x-m)‖^{1/p})·(‖φ(x-m)‖^{1/(p/(p-1))})`, then
`(Σ_m ‖φ(x-m)‖^{p/(p-1)})^{1/(p/(p-1))} ≤ Σ_m ‖φ(x-m)‖` (finite `ℓ^q ⊆ ℓ^1`), and
`Σ_{m∈s} ‖φ(x-m)‖ ≤ Σ'_{n:ℤ} ‖φ(x-n)‖ ≤ A` where `A` is the uniform lattice bound on `φ` given by
`Commons.Analysis.Fourier.schwartz_lattice_sum_bound` (import it explicitly). Integrating, use translation invariance of `volume` and `φ.integrable`. Here `open scoped ENNReal FourierTransform BigOperators`. -/
theorem comb_lintegral_le {p : ℝ} (hp : 1 < p) (φ : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset ℤ) (b : ℤ → ℂ),
      ∫⁻ x : ℝ, ‖(∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)))‖ₑ ^ p
        ≤ ENNReal.ofReal (K ^ p) * ∑ m ∈ s, ENNReal.ofReal ‖b m‖ ^ p := by
  classical
  obtain ⟨A, hApos, hAbound⟩ := Commons.Analysis.Fourier.schwartz_lattice_sum_bound φ
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0:ℝ) ≤ p - 1 := by linarith
  -- the `L¹` mass of `φ`
  set C : ℝ := ∫ x : ℝ, ‖(φ : ℝ → ℂ) x‖ with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; exact integral_nonneg (fun x => norm_nonneg _)
  have hW : (∫⁻ x : ℝ, ‖(φ : ℝ → ℂ) x‖ₑ) = ENNReal.ofReal C := by
    rw [hCdef]
    exact (ofReal_integral_norm_eq_lintegral_enorm φ.integrable).symm
  -- summability of the lattice translates of `φ`
  have hsumφ : ∀ y : ℝ, Summable (fun n : ℤ => ‖(φ : ℝ → ℂ) (y - (n : ℝ))‖) := by
    intro y
    obtain ⟨B, _hBpos, hBdecay⟩ := Commons.Analysis.Fourier.schwartzMap_real_decay φ 2
    have hsumB : Summable (fun n : ℤ => 1 / |(n:ℝ) - (⌊y⌋:ℝ) - 1/2| ^ (2:ℝ)) :=
      Commons.Analysis.Fourier.summable_int_one_div_abs_shift_half_sq ⌊y⌋
    have hsumA : Summable (fun n : ℤ => (1 + |y - (n:ℝ)|) ^ (-(2:ℝ))) :=
      Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
        (fun n => Commons.Analysis.Fourier.lattice_decay_pointwise y n) hsumB
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => hBdecay (y - (n:ℝ))) (hsumA.mul_left B)
  -- uniform lattice bound, in `ℝ≥0∞`
  have hWt : ∀ x : ℝ, (∑' m : ℤ, ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) ≤ ENNReal.ofReal A := by
    intro x
    have h1 : (∑' m : ℤ, ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ)
        = ∑' m : ℤ, ENNReal.ofReal ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ :=
      tsum_congr (fun m => by simp)
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) (hsumφ x)]
    exact ENNReal.ofReal_le_ofReal (hAbound x)
  refine ⟨(A ^ (p - 1) * C + 1) ^ (1 / p), ?_, ?_⟩
  · refine Real.rpow_pos_of_pos ?_ _
    have h : 0 ≤ A ^ (p - 1) * C := mul_nonneg (Real.rpow_nonneg hApos.le _) hCnn
    linarith
  intro s b
  -- zero-extension of `b` to all of `ℤ`
  let b' : ℤ → ℂ := fun m => if m ∈ s then b m else 0
  have hb'mem : ∀ m ∈ s, b' m = b m := by intro m hm; simp [b', hm]
  have hb'not : ∀ m : ℤ, m ∉ s → b' m = 0 := by intro m hm; simp [b', hm]
  have hsumeq : ∀ x : ℝ, (∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)))
      = ∑' m : ℤ, b' m * (φ : ℝ → ℂ) (x - (m:ℝ)) := by
    intro x
    rw [tsum_eq_sum (s := s) (f := fun m : ℤ => b' m * (φ : ℝ → ℂ) (x - (m:ℝ)))
      (fun m hm => by rw [hb'not m hm, zero_mul])]
    exact Finset.sum_congr rfl (fun m hm => by rw [hb'mem m hm])
  -- pointwise `enorm` triangle inequality
  have hpoint : ∀ x : ℝ, ‖(∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)))‖ₑ
      ≤ ∑' m : ℤ, ‖b' m‖ₑ * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ := by
    intro x
    rw [hsumeq x]
    refine (enorm_tsum_le_tsum_enorm).trans ?_
    exact ENNReal.tsum_le_tsum (fun m => le_of_eq (enorm_mul _ _))
  -- weighted Hölder, for the counting measure on `ℤ`
  have hholder : ∀ x : ℝ,
      (∑' m : ℤ, ‖b' m‖ₑ * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) ^ p
        ≤ (∑' m : ℤ, ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) ^ (p - 1)
          * ∑' m : ℤ, ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ := by
    intro x
    have hf : AEMeasurable (fun m : ℤ => ‖b' m‖ₑ) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have hw : AEMeasurable (fun m : ℤ => ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ)
        (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have h := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral_measure
      (Measure.count : Measure ℤ) hp hf hw
    rw [lintegral_count, lintegral_count, lintegral_count] at h
    exact h
  have hmain : ∀ x : ℝ, ‖(∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)))‖ₑ ^ p
      ≤ ENNReal.ofReal A ^ (p - 1)
        * ∑' m : ℤ, ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ := by
    intro x
    refine (ENNReal.rpow_le_rpow (hpoint x) hp0.le).trans ?_
    refine (hholder x).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hWt x) hp1) bot_le
  have hmeasφ : ∀ m : ℤ, AEMeasurable
      (fun x : ℝ => ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) volume := by
    intro m
    exact (((φ.continuous.comp (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable
  have hmeas : ∀ m : ℤ, AEMeasurable
      (fun x : ℝ => ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) volume :=
    fun m => aemeasurable_const.mul (hmeasφ m)
  have hshift : ∀ m : ℤ, (∫⁻ x : ℝ, ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ) = ENNReal.ofReal C := by
    intro m
    calc (∫⁻ x : ℝ, ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ)
        = ∫⁻ x : ℝ, ‖(φ : ℝ → ℂ) x‖ₑ :=
          lintegral_sub_right_eq_self (fun y : ℝ => ‖(φ : ℝ → ℂ) y‖ₑ) ((m:ℤ):ℝ)
      _ = ENNReal.ofReal C := hW
  have hKpow : ((A ^ (p - 1) * C + 1) ^ (1 / p)) ^ p = A ^ (p - 1) * C + 1 := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ A ^ (p - 1) * C + 1), one_div,
      inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hcoef : (∑' m : ℤ, ‖b' m‖ₑ ^ p) = ∑ m ∈ s, ENNReal.ofReal ‖b m‖ ^ p := by
    rw [tsum_eq_sum (s := s) (f := fun m : ℤ => ‖b' m‖ₑ ^ p)
      (fun m hm => by rw [hb'not m hm]; simp [ENNReal.zero_rpow_of_pos hp0])]
    exact Finset.sum_congr rfl (fun m hm => by rw [hb'mem m hm]; simp)
  calc ∫⁻ x : ℝ, ‖(∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)))‖ₑ ^ p
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1)
          * ∑' m : ℤ, ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ :=
        lintegral_mono hmain
    _ = ENNReal.ofReal A ^ (p - 1)
          * ∫⁻ x : ℝ, ∑' m : ℤ, ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ := by
        rw [lintegral_const_mul'' _ (AEMeasurable.tsum hmeas)]
    _ = ENNReal.ofReal A ^ (p - 1)
          * ∑' m : ℤ, ∫⁻ x : ℝ, ‖b' m‖ₑ ^ p * ‖(φ : ℝ → ℂ) (x - (m:ℝ))‖ₑ := by
        rw [lintegral_tsum hmeas]
    _ = ENNReal.ofReal A ^ (p - 1) * ∑' m : ℤ, ‖b' m‖ₑ ^ p * ENNReal.ofReal C := by
        congr 1
        refine tsum_congr (fun m => ?_)
        rw [lintegral_const_mul'' (‖b' m‖ₑ ^ p) (hmeasφ m), hshift m]
    _ = ENNReal.ofReal (A ^ (p - 1) * C) * ∑' m : ℤ, ‖b' m‖ₑ ^ p := by
        rw [ENNReal.tsum_mul_right,
          mul_comm (∑' m : ℤ, ‖b' m‖ₑ ^ p) (ENNReal.ofReal C), ← mul_assoc,
          ENNReal.ofReal_rpow_of_nonneg hApos.le hp1,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hApos.le (p - 1))]
    _ = ENNReal.ofReal (A ^ (p - 1) * C) * ∑ m ∈ s, ENNReal.ofReal ‖b m‖ ^ p := by
        rw [hcoef]
    _ ≤ ENNReal.ofReal (((A ^ (p - 1) * C + 1) ^ (1 / p)) ^ p)
          * ∑ m ∈ s, ENNReal.ofReal ‖b m‖ ^ p := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [hKpow]
        exact ENNReal.ofReal_le_ofReal (by linarith)

end Work.Analysis.Fourier
