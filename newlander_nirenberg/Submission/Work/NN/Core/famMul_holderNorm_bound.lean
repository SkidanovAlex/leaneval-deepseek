import Mathlib
import Submission.Work.NN.Core.beltrami_theta_aux

set_option linter.unusedVariables false

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set

variable {n : ℕ}

/-! ## Complex conjugation preserves the `C^{0,α}`-norm -/

/-- Conjugating the values of a function does not change its `C^{0,α}`-norm: `starRingEnd ℂ`
is an isometry of `ℂ` over `ℝ`. -/
lemma holderNorm_zero_star {α : ℝ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (fun z => starRingEnd ℂ (f z)) Ω
      = Work.CR.Flat.holderNorm 0 α f Ω := by
  have hsup : Work.CR.Flat.iterDerivNorm 0 (fun z => starRingEnd ℂ (f z)) Ω
      = Work.CR.Flat.iterDerivNorm 0 f Ω := by
    simp only [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup_congr fun z => iSup_congr fun _ => by rw [Complex.norm_conj]
  have hsem : Work.CR.Flat.holderSeminorm 0 α (fun z => starRingEnd ℂ (f z)) Ω
      = Work.CR.Flat.holderSeminorm 0 α f Ω := by
    have hpt : ∀ x y : Fin n → ℂ,
        ENNReal.ofReal (‖starRingEnd ℂ (f x) - starRingEnd ℂ (f y)‖ / ‖x - y‖ ^ α)
          = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) := by
      intro x y
      rw [← map_sub (starRingEnd ℂ) (f x) (f y), Complex.norm_conj]
    unfold Work.CR.Flat.holderSeminorm
    simp only [BTheta.norm_iteratedFDerivWithin_zero_sub]
    exact iSup_congr fun x => iSup_congr fun _ => iSup_congr fun y => iSup_congr fun _ =>
      iSup_congr fun _ => hpt x y
  simp only [Work.CR.Flat.holderNorm, Finset.sum_range_one, Nat.zero_add, hsup, hsem]

/-! ## The product bound for the `C^{0,α}`-norm (no regularity hypotheses) -/

lemma iterDerivNorm_zero_mul_le (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.iterDerivNorm 0 (fun z => f z * g z) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω := by
  simp only [Work.CR.Flat.iterDerivNorm_zero]
  refine iSup₂_le fun z hz => ?_
  rw [norm_mul]
  calc ENNReal.ofReal (‖f z‖ * ‖g z‖)
      = ENNReal.ofReal ‖f z‖ * ENNReal.ofReal ‖g z‖ := ENNReal.ofReal_mul (norm_nonneg _)
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖) * (⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖) :=
        mul_le_mul' (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)

lemma holderSeminorm_zero_mul_le {α : ℝ} (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderSeminorm 0 α (fun z => f z * g z) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
        + Work.CR.Flat.holderSeminorm 0 α f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [BTheta.norm_iteratedFDerivWithin_zero_sub (fun z => f z * g z) Ω x y]
  have hd : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hf1 : ENNReal.ofReal ‖f x‖ ≤ Work.CR.Flat.iterDerivNorm 0 f Ω := by
    simpa only [norm_iteratedFDerivWithin_zero] using Work.CR.Flat.le_iterDerivNorm 0 f Ω hx
  have hg1 : ENNReal.ofReal ‖g y‖ ≤ Work.CR.Flat.iterDerivNorm 0 g Ω := by
    simpa only [norm_iteratedFDerivWithin_zero] using Work.CR.Flat.le_iterDerivNorm 0 g Ω hy
  have hf2 : ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω := by
    simpa only [BTheta.norm_iteratedFDerivWithin_zero_sub] using
      Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy
  have hg2 : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 0 α g Ω := by
    simpa only [BTheta.norm_iteratedFDerivWithin_zero_sub] using
      Work.CR.Flat.le_holderSeminorm 0 α g Ω hx hy hxy
  have hsplit : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
  have h1 : ‖f x * g x - f y * g y‖ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
    rw [hsplit]
    calc ‖f x * (g x - g y) + (f x - f y) * g y‖
        ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
  have h2 : ‖f x * g x - f y * g y‖ / ‖x - y‖ ^ α
      ≤ ‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
        + (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g y‖ := by
    calc ‖f x * g x - f y * g y‖ / ‖x - y‖ ^ α
        ≤ (‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖) / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right h1 hd
      _ = ‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
            + (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g y‖ := by
          rw [add_div, mul_div_assoc, ← div_mul_eq_mul_div]
  calc ENNReal.ofReal (‖f x * g x - f y * g y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal (‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
          + (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g y‖) := ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal ‖f x‖ * ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) * ENNReal.ofReal ‖g y‖ := by
        rw [ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hd))
          (mul_nonneg (div_nonneg (norm_nonneg _) hd) (norm_nonneg _))]
        congr 1
        · exact ENNReal.ofReal_mul (norm_nonneg _)
        · exact ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hd)
    _ ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
          + Work.CR.Flat.holderSeminorm 0 α f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω :=
        add_le_add (mul_le_mul' hf1 hg2) (mul_le_mul' hf2 hg1)

/-- The elementary `ℝ≥0∞`-inequality behind the grouping of the Leibniz terms. -/
private lemma mul_add_le_mul_add_aux (a b c d : ℝ≥0∞) :
    a * c + (a * d + b * c) ≤ (a + b) * (c + d) := by
  calc a * c + (a * d + b * c) = (a * c + a * d) + b * c := by ac_rfl
    _ ≤ (a * c + a * d) + (b * c + b * d) := by
        gcongr
        exact le_add_right le_rfl
    _ = (a + b) * (c + d) := by rw [mul_add, add_mul, add_mul]; ac_rfl

/-- The `C^{0,α}`-norm is submultiplicative: `N(fg) ≤ N(f) N(g)`, with no regularity
hypotheses (only the order `0` is involved, where `D^0` is the identity). -/
theorem holderNorm_zero_mul_le {α : ℝ} (f g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (fun z => f z * g z) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω * Work.CR.Flat.holderNorm 0 α g Ω := by
  simp only [Work.CR.Flat.holderNorm, Finset.sum_range_one, Nat.zero_add]
  refine (add_le_add (iterDerivNorm_zero_mul_le f g Ω)
    (holderSeminorm_zero_mul_le f g Ω)).trans ?_
  exact mul_add_le_mul_add_aux _ _ _ _

/-! ## The main family bound -/

theorem famMul_holderNorm_bound {n : ℕ} {α : ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (β : Fin n → Fin n → (Fin n → ℂ) → ℂ) (Y : Fin n → (Fin n → ℂ) → ℂ)
    (hβ : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal δ)
    (hY : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) :
    ∀ i, Work.CR.Flat.holderNorm 0 α
        (fun z => ∑ j, (starRingEnd ℂ (β i j z)) * Y j z) Set.univ
      ≤ ENNReal.ofReal (3 * δ) * ∑ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ := by
  intro i
  have hsum := BTheta.holderNorm_zero_sum_le (α := α) (s := Finset.univ)
    (fun j z => starRingEnd ℂ (β i j z) * Y j z) Set.univ
  calc Work.CR.Flat.holderNorm 0 α
        (fun z => ∑ j, (starRingEnd ℂ (β i j z)) * Y j z) Set.univ
      ≤ ∑ j, Work.CR.Flat.holderNorm 0 α
          (fun z => starRingEnd ℂ (β i j z) * Y j z) Set.univ := by
        simpa using hsum
    _ ≤ ∑ j, Work.CR.Flat.holderNorm 0 α (fun z => starRingEnd ℂ (β i j z)) Set.univ
          * Work.CR.Flat.holderNorm 0 α (Y j) Set.univ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact holderNorm_zero_mul_le (fun z => starRingEnd ℂ (β i j z)) (Y j) Set.univ
    _ ≤ ∑ j, ENNReal.ofReal δ * Work.CR.Flat.holderNorm 0 α (Y j) Set.univ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_left ((holderNorm_zero_star (β i j) Set.univ).trans_le (hβ i j)) _
    _ = ENNReal.ofReal δ * ∑ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ :=
        (Finset.mul_sum Finset.univ
          (fun j => Work.CR.Flat.holderNorm 0 α (Y j) Set.univ) (ENNReal.ofReal δ)).symm
    _ ≤ ENNReal.ofReal (3 * δ) * ∑ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ := by
        refine mul_le_mul_left ?_ _
        exact ENNReal.ofReal_le_ofReal (by linarith)

end Work.NN.Core
