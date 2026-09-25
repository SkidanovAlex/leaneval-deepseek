/-
# Auxiliary estimates for the Calderón–Zygmund Hölder bound `czKernel_holderBound`

This file collects the n-dimensional (real dimension `2n`) radial-integral estimates and
measure-theoretic infrastructure used to prove `czKernel_holderBound`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

open scoped NNReal ENNReal Pointwise
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ### The polar formula for an annulus of the ambient norm -/

/-- The `n`-dimensional polar formula for the annulus `a ≤ ‖x‖ < b` of the ambient
(sup) norm on `Fin n → ℂ`: `∫ ‖x‖^s = finrank · vol(B₁) · (b^{s+2n} - a^{s+2n})/(s+2n)`.
Unlike the disc version this is valid for every `s ≠ -2n`, which is what the far-field
Calderón–Zygmund estimate needs. -/
theorem norm_rpow_shell_integral {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : s ≠ -(2 * (n : ℝ)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in {x : Fin n → ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b}, ‖x‖ ^ s
      = (Module.finrank ℝ (Fin n → ℂ) : ℝ)
        * (volume : Measure (Fin n → ℂ)).real (Metric.ball 0 1)
        * ((b ^ (s + 2 * (n : ℝ)) - a ^ (s + 2 * (n : ℝ))) / (s + 2 * (n : ℝ))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set D := Module.finrank ℝ (Fin n → ℂ) with hD
  have hDnat : D = 2 * n := by
    rw [hD, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hDge : 1 ≤ D := by omega
  have hDge2 : 2 ≤ D := by omega
  have hDR : (D : ℝ) = 2 * (n : ℝ) := by
    rw [hDnat]; push_cast; ring
  have hDcast : (((D - 1 : ℕ)) : ℝ) + 1 = (D : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hDge : D - 1 + 1 = D)
  have hmeas : MeasurableSet {x : Fin n → ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b} :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  set g : ℝ → ℝ := fun y => if a ≤ y ∧ y < b then y ^ s else 0 with hg
  have step1 : ∫ x in {x : Fin n → ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b}, ‖x‖ ^ s
      = ∫ x : Fin n → ℂ, g ‖x‖ := by
    rw [← integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ {x : Fin n → ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b}
    · rw [Set.indicator_of_mem hx]
      simp only [hg]
      rw [if_pos (by simpa only [Set.mem_setOf_eq] using hx)]
    · rw [Set.indicator_of_notMem hx]
      simp only [hg]
      rw [if_neg (by simpa only [Set.mem_setOf_eq] using hx)]
  rw [step1, MeasureTheory.integral_fun_norm_addHaar]
  -- the one-dimensional integral
  have hint : ∫ y in Set.Ioi (0:ℝ), y ^ (D - 1) • g y
      = (b ^ (s + (D : ℝ)) - a ^ (s + (D : ℝ))) / (s + (D : ℝ)) := by
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ a := by
      rw [MeasureTheory.ae_iff]; simp
    have hpt : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Set.Ioi (0:ℝ) →
        y ^ (D - 1) • g y
          = (Set.Ioo a b).indicator (fun y : ℝ => y ^ (s + (((D - 1 : ℕ)) : ℝ))) y := by
      filter_upwards [hne] with y hya hyIoi
      have hypos : 0 < y := hyIoi
      simp only [hg]
      by_cases hlt : y < b
      · by_cases hle : a ≤ y
        · rw [if_pos ⟨hle, hlt⟩,
            Set.indicator_of_mem (show y ∈ Set.Ioo a b from ⟨lt_of_le_of_ne hle (Ne.symm hya), hlt⟩)]
          rw [smul_eq_mul, ← Real.rpow_natCast y (D - 1), ← Real.rpow_add hypos,
            show (((D - 1 : ℕ)) : ℝ) + s = s + (((D - 1 : ℕ)) : ℝ) from by ring]
        · rw [if_neg (fun h => hle h.1), Set.indicator_of_notMem (fun h => hle h.1.le)]
          ring
      · rw [if_neg (fun h => hlt h.2), Set.indicator_of_notMem (fun h => hlt h.2)]
        ring
    rw [setIntegral_congr_ae measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ioo a b = Set.Ioo a b from by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨fun h => h.2, fun h => ⟨ha.trans h.1, h⟩⟩]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hab]
    have hr : s + (((D - 1 : ℕ)) : ℝ) ≠ -1 := by
      intro hcon
      have : s = -(2 * (n : ℝ)) := by
        rw [← hDR]; linarith [hDcast]
      exact hs this
    have h0 : (0:ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab, Set.mem_Icc]
      rintro ⟨h1, h2⟩
      linarith
    rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
    rw [show s + (((D - 1 : ℕ)) : ℝ) + 1 = s + (D : ℝ) from by rw [add_assoc, hDcast]]
  rw [hint, ← hD]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [hDR]
  ring


/-! ### Measure-theoretic infrastructure -/

open Work.CR.Flat.Cauchy.bmCz in
/-- A set on which `eucNorm` is bounded has finite volume. -/
lemma volume_lt_top_of_subset_eucNorm {n : ℕ} {s : Set (Fin n → ℂ)} {M : ℝ}
    (h : ∀ x ∈ s, eucNorm x ≤ M) : volume s < ⊤ := by
  have hsub : s ⊆ Metric.ball (0 : Fin n → ℂ) (M + 1) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_trans (pi_norm_le_eucNorm x) (h x hx)) (lt_add_one M)
  exact lt_of_le_of_lt (MeasureTheory.measure_mono hsub)
    (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ))))

/-- A function bounded on a finite-measure measurable set is integrable. -/
lemma integrableOn_of_norm_le_const_aux {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Fin n → ℂ)} (hsm : MeasurableSet s)
    (hfin : volume s < ⊤) {F : (Fin n → ℂ) → E} (hm : AEStronglyMeasurable F (volume.restrict s))
    {M : ℝ} (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

open Work.CR.Flat.Cauchy.bmCz in
/-- `x ↦ eucNorm x ^ s` is integrable on a Euclidean ball when `s > -2n`. -/
lemma integrableOn_eucNorm_rpow_ball {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : -(2 * (n : ℝ)) < s)
    (ρ : ℝ) : IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s) (eucBall (n := n) ρ) volume := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfin : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := Nat.succ_le_of_lt Module.finrank_pos
  have hD : ((Module.finrank ℝ (Fin n → ℂ) : ℕ) : ℝ) = 2 * (n : ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
    ring
  have hIntNorm : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ s) (Metric.ball 0 ρ) volume := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow hfin (f := fun x : Fin n → ℂ => ‖x‖ ^ s)
      (C := 1) (α := -s) ?_ ?_ ?_
    · rw [hD]; linarith
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s), neg_neg, one_mul]
    · exact (measurable_norm.pow_const s).aestronglyMeasurable
  have hmaj : IntegrableOn (fun x : Fin n → ℂ => ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s)
      (eucBall (n := n) ρ) volume :=
    MeasureTheory.IntegrableOn.mono_set (hIntNorm.const_mul _) eucBall_subset_ball
  refine hmaj.mono' ((measurable_eucNorm_rpow s).aestronglyMeasurable.mono_measure
    Measure.restrict_le_self) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) s)]
  exact eucNorm_rpow_le s x

open Work.CR.Flat.Cauchy.bmCz in
/-- `x ↦ eucNorm x ^ s` is integrable on a Euclidean annulus with inner radius `a > 0`. -/
lemma integrableOn_eucNorm_rpow_shell {n : ℕ} {s : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s) (eucShell (n := n) a b) volume := by
  refine integrableOn_of_norm_le_const_aux (E := ℝ) (F := fun x : Fin n → ℂ => eucNorm x ^ s)
    (M := max (a ^ s) (b ^ s)) (measurableSet_eucShell a b)
    (volume_lt_top_of_subset_eucNorm (M := b) (fun x hx => le_of_lt hx.2)) ?_ ?_
  · exact (measurable_eucNorm_rpow s).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · intro x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) s)]
    rcases le_or_gt s 0 with hs | hs
    · exact le_trans (Real.rpow_le_rpow_of_nonpos ha hx.1 hs) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow (eucNorm_nonneg x) hx.2.le hs.le) (le_max_right _ _)

open Work.CR.Flat.Cauchy.bmCz in
/-- `x ↦ ‖x‖ ^ s` (ambient sup norm) is integrable on a Euclidean annulus with inner radius
`a > 0`. -/
lemma integrableOn_norm_rpow_eucShell {n : ℕ} (hn : 0 < n) {s : ℝ} {a b : ℝ} (ha : 0 < a)
    (_hab : a ≤ b) :
    IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ s) (eucShell (n := n) a b) volume := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  refine integrableOn_of_norm_le_const_aux (E := ℝ) (F := fun x : Fin n → ℂ => ‖x‖ ^ s)
    (M := max ((a / Real.sqrt n) ^ s) (b ^ s)) (measurableSet_eucShell a b)
    (volume_lt_top_of_subset_eucNorm (M := b) (fun x hx => le_of_lt hx.2)) ?_ ?_
  · exact (measurable_norm.pow_const s).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · intro x hx
    have hge : a / Real.sqrt n ≤ ‖x‖ := by
      rw [div_le_iff₀ hsq]
      calc a ≤ eucNorm x := hx.1
        _ ≤ Real.sqrt n * ‖x‖ := eucNorm_le_sqrt_mul_norm x
        _ = ‖x‖ * Real.sqrt n := mul_comm _ _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s)]
    rcases le_or_gt s 0 with hs | hs
    · have hpos : 0 < a / Real.sqrt n := div_pos ha hsq
      exact le_trans (Real.rpow_le_rpow_of_nonpos hpos hge hs) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow (norm_nonneg x) (le_of_lt (lt_of_le_of_lt (pi_norm_le_eucNorm x) hx.2))
        hs.le) (le_max_right _ _)

/-- Translation of a set integral on `ℂⁿ`. -/
lemma setIntegral_translate_euc {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin n → ℂ) (F : (Fin n → ℂ) → E) (A : Set (Fin n → ℂ)) :
    ∫ w in A, F (w + c) = ∫ u in (fun x : Fin n → ℂ => x + c) '' A, F u := by
  have hmp : MeasureTheory.MeasurePreserving (fun x : Fin n → ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : Fin n → ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb F ((fun x : Fin n → ℂ => x + c) '' A)
  rw [show (fun x : Fin n → ℂ => x + c) ⁻¹' ((fun x : Fin n → ℂ => x + c) '' A) = A from by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩] at h
  exact h

/-- The Euclidean annulus is the difference of the two Euclidean balls. -/
lemma eucShell_eq_eucBall_diff {n : ℕ} {a b : ℝ} :
    eucShell (n := n) a b = eucBall b \ eucBall a := by
  ext x
  simp only [mem_eucShell, mem_eucBall, Set.mem_diff]
  exact ⟨fun h => ⟨h.2, not_lt.mpr h.1⟩, fun h => ⟨le_of_not_gt h.2, h.1⟩⟩

open Work.CR.Flat.Cauchy.bmCz in
/-- For `s + 2n < 0` the integral of `eucNorm ^ s` over an annulus with inner radius `a > 0` is
bounded by `C * a ^ (s + 2n)`, uniformly in the outer radius. -/
theorem eucShell_integral_le_neg {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : s + 2 * (n : ℝ) < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∫ x in eucShell (n := n) a b, (eucNorm x) ^ s ≤ C * a ^ (s + 2 * (n : ℝ)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set t : ℝ := s + 2 * (n : ℝ) with ht
  have htneg : t < 0 := hs
  have hsne : s ≠ -(2 * (n : ℝ)) := by
    intro hcon
    have : t = 0 := by rw [ht, hcon]; ring
    rw [this] at htneg
    exact lt_irrefl 0 htneg
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  set F : ℝ := (Module.finrank ℝ (Fin n → ℂ) : ℝ)
      * (volume : Measure (Fin n → ℂ)).real (Metric.ball 0 1) with hF
  have hFpos : 0 < F := by
    rw [hF]
    have h1 : (0:ℝ) < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
      exact_mod_cast Module.finrank_pos
    have h2 : 0 < (volume : Measure (Fin n → ℂ)).real (Metric.ball 0 1) := by
      rw [MeasureTheory.Measure.real_def]
      exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
        (ne_of_lt (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))
    exact mul_pos h1 h2
  have hcoef : 0 < ((Real.sqrt n) ^ s + 1) * F :=
    mul_pos (by have := Real.rpow_pos_of_pos hsq s; linarith) hFpos
  set C : ℝ := ((Real.sqrt n) ^ s + 1) * F * (Real.sqrt n) ^ (-t) / (-t) with hC
  refine ⟨C, ?_, ?_⟩
  · rw [hC]
    exact div_pos (mul_pos hcoef (Real.rpow_pos_of_pos hsq _)) (by linarith)
  · intro a b ha hab
    have hSmeas : MeasurableSet {x : Fin n → ℂ | a / Real.sqrt n ≤ ‖x‖ ∧ ‖x‖ < b} :=
      (isClosed_le continuous_const continuous_norm).measurableSet.inter
        (isOpen_lt continuous_norm continuous_const).measurableSet
    have hsub : eucShell (n := n) a b ⊆ {x : Fin n → ℂ | a / Real.sqrt n ≤ ‖x‖ ∧ ‖x‖ < b} := by
      intro x hx
      rw [mem_eucShell] at hx
      refine ⟨?_, lt_of_le_of_lt (pi_norm_le_eucNorm x) hx.2⟩
      rw [div_le_iff₀ hsq]
      calc a ≤ eucNorm x := hx.1
        _ ≤ Real.sqrt n * ‖x‖ := eucNorm_le_sqrt_mul_norm x
        _ = ‖x‖ * Real.sqrt n := mul_comm _ _
    have hIntS : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ s)
        {x : Fin n → ℂ | a / Real.sqrt n ≤ ‖x‖ ∧ ‖x‖ < b} volume := by
      refine integrableOn_of_norm_le_const_aux (E := ℝ) (F := fun x : Fin n → ℂ => ‖x‖ ^ s)
        (M := max ((a / Real.sqrt n) ^ s) (b ^ s)) hSmeas ?_ ?_ ?_
      · refine volume_lt_top_of_subset_eucNorm (M := Real.sqrt n * b) ?_
        intro x hx
        calc eucNorm x ≤ Real.sqrt n * ‖x‖ := eucNorm_le_sqrt_mul_norm x
          _ ≤ Real.sqrt n * b :=
              mul_le_mul_of_nonneg_left (le_of_lt hx.2) (Real.sqrt_nonneg n)
      · exact (measurable_norm.pow_const s).aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · intro x hx
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s)]
        rcases le_or_gt s 0 with hsp | hsp
        · exact le_trans (Real.rpow_le_rpow_of_nonpos (div_pos ha hsq) hx.1 hsp) (le_max_left _ _)
        · exact le_trans (Real.rpow_le_rpow (norm_nonneg x) hx.2.le hsp.le) (le_max_right _ _)
    have hInt1 : IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s)
        (eucShell (n := n) a b) volume := integrableOn_eucNorm_rpow_shell ha hab
    have hInt2 : IntegrableOn (fun x : Fin n → ℂ => ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s)
        (eucShell (n := n) a b) volume :=
      MeasureTheory.Integrable.const_mul (integrableOn_norm_rpow_eucShell hn ha hab) _
    have hdiv : a / Real.sqrt n ≤ b := by
      rw [div_le_iff₀ hsq]
      exact le_trans hab (le_mul_of_one_le_right (le_of_lt (lt_of_lt_of_le ha hab)) hsq1)
    have hform := norm_rpow_shell_integral hn hsne (div_pos ha hsq) hdiv
    have hbt : 0 ≤ b ^ t := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le ha hab)) t
    have hstep1 : (b ^ t - (a / Real.sqrt n) ^ t) / t ≤ (a / Real.sqrt n) ^ t / (-t) := by
      have hdiff : (b ^ t - (a / Real.sqrt n) ^ t) / t - (a / Real.sqrt n) ^ t / (-t)
          = b ^ t / t := by field_simp; ring
      have h2 : b ^ t / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hbt htneg.le
      linarith [hdiff]
    have hstep2 : (a / Real.sqrt n) ^ t = a ^ t * (Real.sqrt n) ^ (-t) := by
      rw [Real.div_rpow ha.le hsq.le t, div_eq_mul_inv, Real.rpow_neg hsq.le t]
    have hcoef2 : 0 ≤ ((Real.sqrt n) ^ s + 1) * F := hcoef.le
    calc ∫ x in eucShell (n := n) a b, eucNorm x ^ s
        ≤ ∫ x in eucShell (n := n) a b, ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s :=
          MeasureTheory.setIntegral_mono_on hInt1 hInt2 (measurableSet_eucShell a b)
            (fun x _ => eucNorm_rpow_le s x)
      _ = ((Real.sqrt n) ^ s + 1) * ∫ x in eucShell (n := n) a b, ‖x‖ ^ s := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ((Real.sqrt n) ^ s + 1)
            * ∫ x in {x : Fin n → ℂ | a / Real.sqrt n ≤ ‖x‖ ∧ ‖x‖ < b}, ‖x‖ ^ s := by
          refine mul_le_mul_of_nonneg_left ?_ (by
            have := Real.rpow_pos_of_pos hsq s; linarith)
          exact MeasureTheory.setIntegral_mono_set hIntS
            (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) s)
            (Filter.Eventually.of_forall fun x hx => hsub hx)
      _ = ((Real.sqrt n) ^ s + 1) * F * ((b ^ t - (a / Real.sqrt n) ^ t) / t) := by
          rw [hform, hF, ht]; ring
      _ ≤ ((Real.sqrt n) ^ s + 1) * F * ((a / Real.sqrt n) ^ t / (-t)) :=
          mul_le_mul_of_nonneg_left hstep1 hcoef2
      _ = C * a ^ t := by rw [hstep2, hC]; ring
      _ = C * a ^ (s + 2 * (n : ℝ)) := by rw [ht]

/-- Bound for the norm of a set integral via a pointwise majorant. -/
lemma norm_setIntegral_le_of_norm_le' {n : ℕ} {s : Set (Fin n → ℂ)} (hs : MeasurableSet s)
    {F : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → ℝ} (hf : IntegrableOn f s volume)
    (h : ∀ x ∈ s, ‖F x‖ ≤ f x) : ‖∫ x in s, F x‖ ≤ ∫ x in s, f x := by
  rw [← integral_indicator hs (f := F), ← integral_indicator hs (f := f)]
  refine MeasureTheory.norm_integral_le_of_norm_le (hf.integrable_indicator hs)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact h x hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

open Work.CR.Flat.Cauchy.bmCz in
/-- The pointwise Calderón–Zygmund bound: the kernel against a difference of the Hölder
function is dominated by `A K |y|^{α-2n}`. -/
lemma norm_Phi_mul_le {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {A K : ℝ} (hA : 0 < A)
    (hK : 0 ≤ K) {Φ : (Fin n → ℂ) → ℂ}
    (hP1 : ∀ x : Fin n → ℂ, x ≠ 0 → ‖Φ x‖ ≤ A / (eucNorm x) ^ (2 * n))
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α)
    (w y : Fin n → ℂ) :
    ‖Φ y * (g (w + y) - g w)‖ ≤ A * K * (eucNorm y) ^ (α - 2 * (n : ℝ)) := by
  have hne : α - 2 * (n : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0]; push_cast; linarith
    · intro hcon
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnpos
      linarith
  by_cases hy : y = 0
  · subst hy
    simp only [add_zero, sub_self, mul_zero, norm_zero, eucNorm_zero]
    rw [Real.zero_rpow hne, mul_zero]
  · rw [norm_mul]
    have h1 : ‖Φ y‖ ≤ A / (eucNorm y) ^ (2 * n) := hP1 y hy
    have h2 : ‖g (w + y) - g w‖ ≤ K * ‖y‖ ^ α := by
      have := hg (w + y) w
      rwa [add_sub_cancel_left] at this
    have hypos : 0 < eucNorm y := eucNorm_pos hy
    have hpow : 0 < (eucNorm y) ^ (2 * n) := pow_pos hypos _
    have h3 : ‖y‖ ^ α ≤ (eucNorm y) ^ α :=
      Real.rpow_le_rpow (norm_nonneg y) (pi_norm_le_eucNorm y) hα.le
    have step : (A / (eucNorm y) ^ (2 * n)) * (K * ‖y‖ ^ α)
        ≤ A * K * (eucNorm y) ^ (α - 2 * (n : ℝ)) := by
      have h4 : (A / (eucNorm y) ^ (2 * n)) * (K * ‖y‖ ^ α)
          ≤ (A / (eucNorm y) ^ (2 * n)) * (K * (eucNorm y) ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK) (by positivity)
      refine le_trans h4 ?_
      rw [div_eq_mul_inv]
      rw [show eucNorm y ^ (2*n : ℕ) = (eucNorm y) ^ (2 * (n : ℝ)) from by
        rw [← Real.rpow_natCast (eucNorm y) (2*n), Nat.cast_mul, Nat.cast_ofNat]]
      rw [← Real.rpow_neg hypos.le (2 * (n : ℝ))]
      rw [show A * (eucNorm y) ^ (-(2 * (n : ℝ))) * (K * (eucNorm y) ^ α)
          = A * K * ((eucNorm y) ^ α * (eucNorm y) ^ (-(2 * (n : ℝ)))) from by ring]
      rw [← Real.rpow_add hypos]
      rw [show α + -(2 * (n : ℝ)) = α - 2 * (n : ℝ) from by ring]
    calc ‖Φ y‖ * ‖g (w + y) - g w‖
        ≤ (A / (eucNorm y) ^ (2 * n)) * (K * ‖y‖ ^ α) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ A * K * (eucNorm y) ^ (α - 2 * (n : ℝ)) := step

/-- A function dominated on an annulus `a ≤ |x| < b` with `a > 0` by `C * eucNorm ^ s` is
integrable there (for any real `s`). -/
lemma integrableOn_of_le_eucNorm_rpow_shell {n : ℕ} {s : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {P : (Fin n → ℂ) → ℂ} (hPm : AEStronglyMeasurable P (volume.restrict (eucShell (n := n) a b)))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ eucShell (n := n) a b, ‖P x‖ ≤ C * eucNorm x ^ s) :
    IntegrableOn P (eucShell (n := n) a b) volume := by
  have hmaj : IntegrableOn (fun x : Fin n → ℂ => C * eucNorm x ^ s) (eucShell (n := n) a b) volume :=
    MeasureTheory.Integrable.const_mul (integrableOn_eucNorm_rpow_shell (n := n) (s := s) ha hab) C
  refine hmaj.mono' hPm ?_
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_eucShell a b)]
  filter_upwards with x hx
  exact h x hx

/-- A function dominated on a ball by `C * eucNorm ^ s` with `s > -2n` is integrable there. -/
lemma integrableOn_of_le_eucNorm_rpow_ball {n : ℕ} (hn : 0 < n) {s : ℝ} {ρ : ℝ}
    (hs : -(2 * (n : ℝ)) < s) {P : (Fin n → ℂ) → ℂ}
    (hPm : AEStronglyMeasurable P (volume.restrict (eucBall (n := n) ρ)))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ eucBall (n := n) ρ, ‖P x‖ ≤ C * eucNorm x ^ s) :
    IntegrableOn P (eucBall (n := n) ρ) volume := by
  have hmaj : IntegrableOn (fun x : Fin n → ℂ => C * eucNorm x ^ s) (eucBall (n := n) ρ) volume :=
    MeasureTheory.Integrable.const_mul (integrableOn_eucNorm_rpow_ball (n := n) hn hs ρ) C
  refine hmaj.mono' hPm ?_
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_eucBall ρ)]
  filter_upwards with x hx
  exact h x hx

open Work.CR.Flat.Cauchy.bmCz in
/-- Triangle inequality for `eucNorm`. -/
lemma eucNorm_sub_le {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x - y) ≤ eucNorm x + eucNorm y := by
  have h1 : eucNorm (x - y) = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h2 : eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h3 : eucNorm y = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm y‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have hsub : (WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x - (WithLp.equiv 2 (Fin n → ℂ)).symm y := by
    simp [WithLp.equiv_symm_apply]
  rw [h1, h2, h3, hsub]
  exact norm_sub_le _ _

open Work.CR.Flat.Cauchy.bmCz in
/-- Triangle inequality for `eucNorm`, addition form. -/
lemma eucNorm_add_le {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x + y) ≤ eucNorm x + eucNorm y := by
  have h1 : eucNorm (x + y) = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm (x + y)‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h2 : eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h3 : eucNorm y = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm y‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have hsub : (WithLp.equiv 2 (Fin n → ℂ)).symm (x + y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x + (WithLp.equiv 2 (Fin n → ℂ)).symm y := by
    simp [WithLp.equiv_symm_apply]
  rw [h1, h2, h3, hsub]
  exact norm_add_le _ _

/-- The translate of an a.e. strongly measurable function is a.e. strongly measurable. -/
lemma aestronglyMeasurable_comp_sub {n : ℕ} {Φ : (Fin n → ℂ) → ℂ}
    (hΦm : AEStronglyMeasurable Φ volume) (c : Fin n → ℂ) :
    AEStronglyMeasurable (fun u : Fin n → ℂ => Φ (u - c)) volume := by
  have hmp : MeasureTheory.MeasurePreserving (fun x : Fin n → ℂ => x + (-c)) volume volume :=
    MeasureTheory.measurePreserving_add_right volume (-c)
  have h := hΦm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  simpa only [Function.comp_def, sub_eq_add_neg] using h

open Work.CR.Flat.Cauchy.bmCz in
/-- Scaling of the Euclidean norm. -/
lemma eucNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : eucNorm (c • x) = ‖c‖ * eucNorm x := by
  have h1 : eucNorm (c • x) = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm (c • x)‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h2 : eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
    rw [PiLp.norm_eq_of_L2]; simp [eucNorm]
  have h3 : (WithLp.equiv 2 (Fin n → ℂ)).symm (c • x)
      = c • (WithLp.equiv 2 (Fin n → ℂ)).symm x := by
    simp [WithLp.equiv_symm_apply]
  rw [h1, h2, h3, norm_smul]

open Work.CR.Flat.Cauchy.bmCz in
/-- Scaling of the volume of a Euclidean ball. -/
lemma volume_eucBall_real {n : ℕ} (hn : 0 < n)
    (hD : ((Module.finrank ℝ (Fin n → ℂ) : ℕ) : ℝ) = 2 * (n : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume : Measure (Fin n → ℂ)).real (eucBall (n := n) ρ)
      = ρ ^ (2 * (n : ℝ))
          * (volume : Measure (Fin n → ℂ)).real (eucBall (n := n) 1) := by
  rcases eq_or_lt_of_le hρ with h0 | hpos
  · rw [← h0]
    have hemp : eucBall (n := n) 0 = ∅ := by
      ext x
      simp only [mem_eucBall, Set.mem_empty_iff_false, iff_false, not_lt]
      exact eucNorm_nonneg x
    rw [hemp, MeasureTheory.Measure.real_def, measure_empty, ENNReal.toReal_zero,
      Real.zero_rpow (by positivity), zero_mul]
  · have hsmul : eucBall (n := n) ρ = ρ • (eucBall (n := n) 1 : Set (Fin n → ℂ)) := by
      ext x
      simp only [mem_eucBall, Set.mem_smul_set]
      constructor
      · intro hx
        refine ⟨ρ⁻¹ • x, ?_, ?_⟩
        · rw [eucNorm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_eq_div,
            div_lt_one hpos]
          exact hx
        · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
      · rintro ⟨y, hy, rfl⟩
        rw [eucNorm_smul, Real.norm_of_nonneg hpos.le]
        calc ρ * eucNorm y < ρ * 1 := mul_lt_mul_of_pos_left hy hpos
          _ = ρ := mul_one ρ
    rw [hsmul, MeasureTheory.Measure.real_def,
      MeasureTheory.Measure.addHaar_smul_of_nonneg volume hpos.le (eucBall (n := n) 1),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ _),
      ← Real.rpow_natCast ρ (Module.finrank ℝ (Fin n → ℂ)), hD,
      ← MeasureTheory.Measure.real_def]

open Work.CR.Flat.Cauchy.bmCz in
/-- Volume of a Euclidean annulus. -/
lemma volume_eucShell_real {n : ℕ} (hn : 0 < n)
    (hD : ((Module.finrank ℝ (Fin n → ℂ) : ℕ) : ℝ) = 2 * (n : ℝ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume : Measure (Fin n → ℂ)).real (eucShell (n := n) a b)
      = (b ^ (2 * (n : ℝ)) - a ^ (2 * (n : ℝ)))
          * (volume : Measure (Fin n → ℂ)).real (eucBall (n := n) 1) := by
  have hmeas : MeasurableSet (eucShell (n := n) a b) := measurableSet_eucShell a b
  have hsub : eucBall (n := n) a ⊆ eucBall (n := n) b := by
    intro x hx
    rw [mem_eucBall] at hx ⊢
    linarith
  have hunion : eucBall (n := n) b = eucBall (n := n) a ∪ eucShell (n := n) a b := by
    ext x
    simp only [mem_eucBall, mem_eucShell, Set.mem_union]
    constructor
    · intro hx
      rcases lt_or_ge (eucNorm x) a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨h1, h2⟩)
      · linarith
      · exact h2
  have hdisj : Disjoint (eucBall (n := n) a) (eucShell (n := n) a b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_eucBall] at hx
    simp only [mem_eucShell] at hx'
    linarith [hx'.1]
  have hfin : (volume : Measure (Fin n → ℂ)) (eucBall (n := n) b) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (eucBall_subset_ball))
      (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))
  have hfinA : (volume : Measure (Fin n → ℂ)) (eucBall (n := n) a) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (eucBall_subset_ball))
      (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))
  have hfinS : (volume : Measure (Fin n → ℂ)) (eucShell (n := n) a b) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono
        (show eucShell (n := n) a b ⊆ eucBall (n := n) b from fun x hx => hx.2))
      (lt_of_le_of_lt (MeasureTheory.measure_mono (eucBall_subset_ball))
        (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ))))))
  have hm : (volume : Measure (Fin n → ℂ)) (eucBall (n := n) b)
      = (volume : Measure (Fin n → ℂ)) (eucBall (n := n) a)
        + (volume : Measure (Fin n → ℂ)) (eucShell (n := n) a b) := by
    rw [hunion, MeasureTheory.measure_union hdisj hmeas]
  have h1 := volume_eucBall_real (n := n) hn hD (le_trans ha hab)
  have h2 := volume_eucBall_real (n := n) hn hD ha
  have hkey : ((volume : Measure (Fin n → ℂ)) (eucBall (n := n) b)).toReal
      = ((volume : Measure (Fin n → ℂ)) (eucBall (n := n) a)).toReal
        + ((volume : Measure (Fin n → ℂ)) (eucShell (n := n) a b)).toReal := by
    rw [hm, ENNReal.toReal_add hfinA hfinS]
  have hshell : ((volume : Measure (Fin n → ℂ)) (eucShell (n := n) a b)).toReal
      = ((volume : Measure (Fin n → ℂ)) (eucBall (n := n) b)).toReal
        - ((volume : Measure (Fin n → ℂ)) (eucBall (n := n) a)).toReal := by
    linarith [hkey]
  rw [MeasureTheory.Measure.real_def, hshell, ← MeasureTheory.Measure.real_def,
    ← MeasureTheory.Measure.real_def, h1, h2]
  ring

/-- Translation of a set integral, subtraction form. -/
lemma setIntegral_translate_euc_sub {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin n → ℂ) (F : (Fin n → ℂ) → E) (A : Set (Fin n → ℂ)) :
    ∫ w in A, F (w - c) = ∫ u in (fun x : Fin n → ℂ => x - c) '' A, F u := by
  simpa only [sub_eq_add_neg] using setIntegral_translate_euc (-c) F A

/-- Integrability transports across the translation `x ↦ x + c`. -/
lemma integrableOn_add_iff {n : ℕ} {E : Type*} [NormedAddCommGroup E] {c : Fin n → ℂ}
    {F : (Fin n → ℂ) → E} {A : Set (Fin n → ℂ)} :
    IntegrableOn (fun x : Fin n → ℂ => F (x + c)) A volume ↔
      IntegrableOn F ((fun x : Fin n → ℂ => x + c) '' A) volume := by
  have hmp : MeasureTheory.MeasurePreserving (fun x : Fin n → ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : Fin n → ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have hpre : (fun x : Fin n → ℂ => x + c) ⁻¹' ((fun x : Fin n → ℂ => x + c) '' A) = A := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩
  have h := hmp.integrableOn_comp_preimage (f := F) hemb (s := (fun x : Fin n → ℂ => x + c) '' A)
  rw [hpre] at h
  simpa only [Function.comp_def] using h

/-- Integrability transports across the substitution `u ↦ u - c` on a translated set. -/
lemma integrableOn_comp_sub_iff' {n : ℕ} {E : Type*} [NormedAddCommGroup E] {c : Fin n → ℂ}
    {F : (Fin n → ℂ) → E} {A : Set (Fin n → ℂ)} :
    IntegrableOn (fun u : Fin n → ℂ => F (u - c)) ((fun x : Fin n → ℂ => x + c) '' A) volume ↔
      IntegrableOn F A volume := by
  have hmp : MeasureTheory.MeasurePreserving (fun x : Fin n → ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : Fin n → ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have hpre : (fun x : Fin n → ℂ => x + c) ⁻¹' ((fun x : Fin n → ℂ => x + c) '' A) = A := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩
  have h := hmp.integrableOn_comp_preimage (f := fun u : Fin n → ℂ => F (u - c)) hemb
    (s := (fun x : Fin n → ℂ => x + c) '' A)
  rw [hpre] at h
  simpa only [Function.comp_def, add_sub_cancel_right] using h.symm

end Work.CR.Flat.Cauchy
