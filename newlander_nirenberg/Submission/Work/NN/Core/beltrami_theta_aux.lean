/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary `C^{0,α}`-toolkit for the Beltrami fixed-point lemma

This file collects the elementary facts about the `C^{0,α}`-norm
`Work.CR.Flat.holderNorm 0 α` of `Submission/Work/CR/Flat/Holder.lean` that the proof of
`Work.NN.Core.beltrami_theta_fixedpoint` needs, stated *without* regularity hypotheses
(the general `holderNorm_add_le` etc. require `ContDiffOn`, which is not available for functions
that are only known to be `α`-Hölder):

* `BTheta.holderNorm_zero_add_le`, `BTheta.holderNorm_zero_neg`,
  `BTheta.holderNorm_zero_sub_le`, `BTheta.holderNorm_zero_sum_le`,
  `BTheta.holderNorm_zero_const_mul_le`: the triangle inequality, negation, subtraction,
  finite sums and pointwise multiplication by a constant for the `C^{0,α}`-norm;
* `BTheta.holderNorm_zero_mul_le_ofReal`: a pointwise product of two functions whose
  `C^{0,α}`-norms are at most `A` and `B` has `C^{0,α}`-norm at most `3 A B`;
* `BTheta.bounds_of_holderNorm_zero_le`: the real-valued sup and Hölder bounds extracted from an
  `ℝ≥0∞`-valued bound.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

namespace BTheta

variable {n : ℕ}

/-! ## The `0`-th iterated within-derivative is the function itself -/

/-- `D^0 f = f`: the norm of the difference of two `0`-th iterated within-derivatives equals the
norm of the difference of the values.  (A private copy of
`Work.NN.Core.norm_iteratedFDerivWithin_zero_sub`, kept here so that this file's imports stay
light.) -/
lemma norm_iteratedFDerivWithin_zero_sub (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
    (x y : Fin n → ℂ) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [sub_apply, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y) (0 : Fin 0 → Fin n → ℂ)
    simp only [sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → Fin n → ℂ) i‖) = 1 from by simp, mul_one] at h
    exact h

/-- `‖D^0 f x‖ = ‖f x‖`. -/
lemma norm_iteratedFDerivWithin_zero_apply' (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
    (x : Fin n → ℂ) : ‖iteratedFDerivWithin ℝ 0 f Ω x‖ = ‖f x‖ :=
  norm_iteratedFDerivWithin_zero

/-! ## The triangle inequality for the `C^{0,α}`-norm -/

lemma iterDerivNorm_zero_add_le (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.iterDerivNorm 0 (f + g) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.iterDerivNorm 0 g Ω := by
  refine iSup₂_le fun z hz => ?_
  rw [norm_iteratedFDerivWithin_zero (f := f + g)]
  have h1 : ENNReal.ofReal ‖(f + g) z‖ ≤ ENNReal.ofReal ‖f z‖ + ENNReal.ofReal ‖g z‖ := by
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using norm_add_le (f z) (g z))
  have h2 : ENNReal.ofReal ‖f z‖ ≤ Work.CR.Flat.iterDerivNorm 0 f Ω := by
    simpa only [norm_iteratedFDerivWithin_zero] using Work.CR.Flat.le_iterDerivNorm 0 f Ω hz
  have h3 : ENNReal.ofReal ‖g z‖ ≤ Work.CR.Flat.iterDerivNorm 0 g Ω := by
    simpa only [norm_iteratedFDerivWithin_zero] using Work.CR.Flat.le_iterDerivNorm 0 g Ω hz
  exact h1.trans (add_le_add h2 h3)

lemma holderSeminorm_zero_add_le {α : ℝ} (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderSeminorm 0 α (f + g) Ω
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [norm_iteratedFDerivWithin_zero_sub (f + g) Ω x y]
  have hden : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have h1 : ENNReal.ofReal (‖(f + g) x - (f + g) y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
    have heq : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
      simp only [Pi.add_apply]; ring
    rw [heq]
    calc ENNReal.ofReal (‖(f x - f y) + (g x - g y)‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_add_le _ _) hden)
      _ = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
            + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
          rw [add_div, ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hden)
            (div_nonneg (norm_nonneg _) hden)]
  have h2 : ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω := by
    simpa only [norm_iteratedFDerivWithin_zero_sub] using
      Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy
  have h3 : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 0 α g Ω := by
    simpa only [norm_iteratedFDerivWithin_zero_sub] using
      Work.CR.Flat.le_holderSeminorm 0 α g Ω hx hy hxy
  exact h1.trans (add_le_add h2 h3)

/-- Triangle inequality for the `C^{0,α}`-norm, with no regularity hypotheses. -/
theorem holderNorm_zero_add_le {α : ℝ} (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (f + g) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm,
    Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one]
  exact (add_le_add (iterDerivNorm_zero_add_le f g Ω)
    (holderSeminorm_zero_add_le f g Ω)).trans (le_of_eq (add_add_add_comm _ _ _ _))

/-- Negation is an isometry for the `C^{0,α}`-norm. -/
lemma holderNorm_zero_neg {α : ℝ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (-f) Ω = Work.CR.Flat.holderNorm 0 α f Ω := by
  have hsup : Work.CR.Flat.iterDerivNorm 0 (-f) Ω = Work.CR.Flat.iterDerivNorm 0 f Ω := by
    refine iSup_congr fun z => iSup_congr fun _ => ?_
    rw [norm_iteratedFDerivWithin_zero, norm_iteratedFDerivWithin_zero, Pi.neg_apply, norm_neg]
  have hsem : Work.CR.Flat.holderSeminorm 0 α (-f) Ω
      = Work.CR.Flat.holderSeminorm 0 α f Ω := by
    refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun y => iSup_congr fun _ =>
      iSup_congr fun _ => ?_
    rw [norm_iteratedFDerivWithin_zero_sub (-f) Ω x y,
      norm_iteratedFDerivWithin_zero_sub f Ω x y]
    have hneg : (-f) x - (-f) y = -(f x - f y) := by
      simp only [Pi.neg_apply]; ring
    rw [hneg, norm_neg]
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.sum_range_one,
    Finset.sum_range_one, hsup, hsem]

lemma holderNorm_zero_sub_le {α : ℝ} (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (f - g) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  simpa only [sub_eq_add_neg] using (holderNorm_zero_add_le f (-g) Ω).trans
    (add_le_add le_rfl (le_of_eq (holderNorm_zero_neg g Ω)))

/-- The `C^{0,α}`-norm of a finite sum (no regularity hypotheses). -/
lemma holderNorm_zero_sum_le {α : ℝ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (fun z => ∑ j ∈ s, g j z) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.holderNorm 0 α (g j) Ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (fun z : Fin n → ℂ => ∑ j ∈ (∅ : Finset ι), g j z) = 0 := by
        funext z; simp
      rw [h0, Work.CR.Flat.holderNorm_zero, Finset.sum_empty]
  | insert a t ha ih =>
      have hfun : (fun z : Fin n → ℂ => ∑ j ∈ insert a t, g j z)
          = g a + (fun z : Fin n → ℂ => ∑ j ∈ t, g j z) := by
        funext z; rw [Finset.sum_insert ha]; rfl
      rw [hfun, Finset.sum_insert ha]
      exact (holderNorm_zero_add_le (g a) _ Ω).trans (add_le_add le_rfl ih)

/-- Pointwise multiplication by a constant. -/
lemma holderNorm_zero_const_mul_le {α : ℝ} (c : ℂ) (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 0 α f Ω := by
  have hsup : Work.CR.Flat.iterDerivNorm 0 (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.iterDerivNorm 0 f Ω := by
    refine iSup₂_le fun z hz => ?_
    rw [norm_iteratedFDerivWithin_zero, norm_mul]
    calc ENNReal.ofReal (‖c‖ * ‖f z‖) = ENNReal.ofReal ‖c‖ * ENNReal.ofReal ‖f z‖ :=
          ENNReal.ofReal_mul (norm_nonneg _)
      _ ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.iterDerivNorm 0 f Ω :=
          mul_le_mul_right (by
            simpa only [norm_iteratedFDerivWithin_zero] using
              Work.CR.Flat.le_iterDerivNorm 0 f Ω hz) _
  have hsem : Work.CR.Flat.holderSeminorm 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderSeminorm 0 α f Ω := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub (fun z => c * f z) Ω x y]
    have h1 : ENNReal.ofReal (‖c * f x - c * f y‖ / ‖x - y‖ ^ α)
        = ENNReal.ofReal ‖c‖ * ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) := by
      rw [show c * f x - c * f y = c * (f x - f y) by ring, norm_mul, mul_div_assoc,
        ENNReal.ofReal_mul (norm_nonneg _)]
    rw [h1]
    exact mul_le_mul_right (by
      simpa only [norm_iteratedFDerivWithin_zero_sub] using
        Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy) _
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.sum_range_one,
    Finset.sum_range_one]
  exact (add_le_add hsup hsem).trans (le_of_eq (mul_add _ _ _).symm)

/-! ## Real bounds extracted from an `ℝ≥0∞`-bound -/

/-- From `‖f‖_{C^{0,α}} ≤ ofReal A` one gets the sup bound `‖f x‖ ≤ A` and the Hölder bound
`‖f x - f y‖ ≤ A ‖x - y‖^α` on `Ω`. -/
lemma bounds_of_holderNorm_zero_le {α A : ℝ} (hA : 0 ≤ A) {f : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} (hf : Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal A) :
    (∀ x ∈ Ω, ‖f x‖ ≤ A) ∧ (∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have h1 : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal A :=
      (Work.CR.Flat.norm_apply_le_holderNorm 0 α f Ω hx).trans hf
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp h1
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · rw [sub_self, sub_self, norm_zero, norm_zero]
      exact mul_nonneg hA (Real.rpow_nonneg le_rfl α)
    · have h1 : ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) ≤ ENNReal.ofReal A := by
        have h2 := Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy
        rw [norm_iteratedFDerivWithin_zero_sub f Ω x y] at h2
        exact h2.trans ((Work.CR.Flat.holderSeminorm_le_holderNorm 0 α f Ω le_rfl).trans hf)
      have h2 : ‖f x - f y‖ / ‖x - y‖ ^ α ≤ A :=
        (ENNReal.ofReal_le_ofReal_iff hA).mp h1
      have hden : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      calc ‖f x - f y‖ = (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α :=
            (div_mul_cancel₀ _ hden.ne').symm
        _ ≤ A * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right h2 hden.le

/-- The `C^{0,α}`-norm of a pointwise product, from `ℝ≥0∞`-bounds on the two factors. -/
theorem holderNorm_zero_mul_le_ofReal {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f g : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (hf : Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal A)
    (hg : Work.CR.Flat.holderNorm 0 α g Ω ≤ ENNReal.ofReal B) :
    Work.CR.Flat.holderNorm 0 α (fun x => f x * g x) Ω ≤ ENNReal.ofReal (3 * A * B) := by
  obtain ⟨hf1, hf2⟩ := bounds_of_holderNorm_zero_le hA hf
  obtain ⟨hg1, hg2⟩ := bounds_of_holderNorm_zero_le hB hg
  have hsup : Work.CR.Flat.iterDerivNorm 0 (fun x => f x * g x) Ω
      ≤ ENNReal.ofReal (A * B) := by
    refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_zero, norm_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (hf1 x hx) (hg1 x hx) (norm_nonneg _) hA)
  have hsem : Work.CR.Flat.holderSeminorm 0 α (fun x => f x * g x) Ω
      ≤ ENNReal.ofReal (2 * (A * B)) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hden : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hden, norm_iteratedFDerivWithin_zero_sub (fun x => f x * g x) Ω x y]
    have hsplit : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
    rw [hsplit]
    calc ‖f x * (g x - g y) + (f x - f y) * g y‖
        ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ A * (B * ‖x - y‖ ^ α) + (A * ‖x - y‖ ^ α) * B :=
          add_le_add (mul_le_mul (hf1 x hx) (hg2 x hx y hy) (norm_nonneg _) hA)
            (mul_le_mul (hf2 x hx y hy) (hg1 y hy) (norm_nonneg _) (mul_nonneg hA hden.le))
      _ = 2 * (A * B) * ‖x - y‖ ^ α := by ring
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  refine (add_le_add hsup hsem).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact le_of_eq (by ring)

end BTheta

end Work.NN.Core
