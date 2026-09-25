/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Order-zero Schauder estimate for the annulus potential `fiberPotAnn`

`fiberPotAnn j l A η` is the `l`-th derivative in the `j`-th fibre of the fixed-disc Cauchy
potential, i.e. the integral `-(1/π) ∫_{w ∈ A} η (z with z j := w) ((w - z j)⁻¹)^(l+1) dw` over a
*xed* set `A` (see `Submission.Work.NN.Core.VanishingDefs`).  Here `A = fiberAnnulus (s j) R` is the
annulus `{s j ≤ ‖w‖ ∧ ‖w‖ < R}`.

Because the annulus stays at distance `s j - r j > 0` from the pole `z j` for `z ∈ polydisc 0 r`,
the kernel is smooth and bounded there, and the order-zero estimate

  `‖fiberPotAnn j l (fiberAnnulus (s j) R) η‖_{C^{0,α}(polydisc 0 r)}
      ≤ C ‖η‖_{C^{0,α}(fiberAccess r j R)}`

holds for *arbitrary* continuous data `η` -- no vanishing and no support hypothesis is needed.  The
data is only ever read on the access polydisc `fiberAccess r j R` (the polydisc whose `j`-th radius
is `R`).

The proof is elementary once the kernel is smooth: the sup bound is immediate from the kernel bound
`((s j - r j)⁻¹)^(l+1)` and the area bound `volume (fiberAnnulus (s j) R) ≤ π R²`, and the `α`
seminorm is bounded by splitting the integrand difference into a difference of the *data* (the
`α`-Hölder bound of `η` on the access polydisc, times the sup of the kernel) and a difference of the
*kernels* (the Lipschitz bound of `a ↦ ((w - a)⁻¹)^(l+1)`, converted to the exponent `α` through
`‖z - z'‖ ≤ (2‖r‖)^(1-α) ‖z - z'‖^α`).  When `holderNorm 0 α η (fiberAccess r j R) = ∞` there is
nothing to prove; otherwise its value is read off as `A0 + K0` with `A0` the `∞`-norm and `K0` the
`α`-seminorm of `η` on the access polydisc.
-/
import Mathlib
import Submission.Work.NN.Core.VanishingDefs
import Submission.Work.NN.Core.norm_inv_pow_sub_inv_pow_le
import Submission.Work.NN.Core.norm_fiberPotAnn_sub_le
import Submission.Work.NN.Ratio.holderNorm_zero_le_of_bounds

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-- Sup bound for the annulus potential. -/
private lemma norm_fiberPotAnn_le_of_bound {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) (l : ℕ)
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {η : Cn n → ℂ} {A0 : ℝ} (hA0 : 0 ≤ A0)
    (hA : ∀ x ∈ fiberAccess r j R, ‖η x‖ ≤ A0)
    {z : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z‖
      ≤ (s j - r j)⁻¹ ^ (l + 1) * R ^ 2 * A0 := by
  set A := fiberAnnulus (s j) R with hAdef
  have hd : 0 < s j - r j := by linarith [hr j, hrs j]
  have hzj : ‖z j‖ < r j := by simpa using hz j
  have hdle : s j - r j ≤ s j - ‖z j‖ := by linarith
  have hkern : ∀ w ∈ A, ‖η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)‖
      ≤ A0 * ((s j - r j)⁻¹ ^ (l + 1)) := by
    intro w hw
    rw [norm_mul]
    refine mul_le_mul (hA _ (mem_fiberAccess_update hz hw.2)) ?_ (norm_nonneg _) hA0
    exact norm_pow_inv_le_of_mem_fiberAnnulus hd l hw hdle
  have hint := norm_setIntegral_le_of_norm_le_const (volume_fiberAnnulus_lt_top (s j) R) hkern
  rw [Measure.real_def] at hint
  rw [fiberPotAnn_apply]
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hvol : (volume A).toReal ≤ R ^ 2 * Real.pi := volume_fiberAnnulus_toReal_le hR.le
  have hA0k : 0 ≤ A0 * (s j - r j)⁻¹ ^ (l + 1) := by positivity
  calc Real.pi⁻¹ * ‖∫ (w : ℂ) in A, η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)‖
      ≤ Real.pi⁻¹ * (A0 * (s j - r j)⁻¹ ^ (l+1) * (R^2 * Real.pi)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hint.trans (mul_le_mul_of_nonneg_left hvol hA0k)
    _ = (s j - r j)⁻¹ ^ (l+1) * R^2 * A0 := by
        rw [show Real.pi⁻¹ * (A0 * (s j - r j)⁻¹ ^ (l+1) * (R^2 * Real.pi))
              = A0 * (s j - r j)⁻¹ ^ (l+1) * R^2 * (Real.pi⁻¹ * Real.pi) by ring]
        rw [inv_mul_cancel₀ Real.pi_ne_zero, mul_one]
        ring

/-- The `0`-th iterated derivative is the function itself. -/
private lemma nrm_iter_zero_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (v : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 v Ω x - iteratedFDerivWithin ℝ 0 v Ω y‖ = ‖v x - v y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖v x - v y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 v Ω x - iteratedFDerivWithin ℝ 0 v Ω y) (0 : Fin 0 → X)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → X) i‖) = 1 from by simp, mul_one] at h
    exact h

theorem holderNorm_zero_fiberPotAnn_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    (hsR : ∀ i, s i < R) (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : (Fin n → ℂ) → ℂ, Continuous η →
      Work.CR.Flat.holderNorm 0 α
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
          (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C *
          Work.CR.Flat.holderNorm 0 α η (Work.NN.Core.fiberAccess r j R) := by
  have hd : 0 < s j - r j := by linarith [hr j, hrs j]
  refine ⟨(s j - r j)⁻¹ ^ (l + 1) * R ^ 2
      + R ^ 2 * (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2) * (2 * ‖r‖) ^ (1 - α)
          + (s j - r j)⁻¹ ^ (l + 1)), by positivity, ?_⟩
  intro η hη
  have hLip : ∀ w ∈ fiberAnnulus (s j) R, ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
      ‖((w - a)⁻¹) ^ (l + 1) - ((w - b)⁻¹) ^ (l + 1)‖
        ≤ (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2)) * ‖a - b‖ := by
    intro w hw a b ha hb
    have hda : s j - r j ≤ ‖w - a‖ := by
      have h := norm_sub_le_of_mem_fiberAnnulus (s := s j) (R := R) (z := a) hw
      linarith
    have hdb : s j - r j ≤ ‖w - b‖ := by
      have h := norm_sub_le_of_mem_fiberAnnulus (s := s j) (R := R) (z := b) hw
      linarith
    have h := norm_inv_pow_sub_inv_pow_le hd hda hdb (e := l + 1)
    rwa [show (w - a) - (w - b) = -(a - b) from by ring, norm_neg,
      show l + 1 + 1 = l + 2 from rfl] at h
  set S : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 0 η (Work.NN.Core.fiberAccess r j R) with hSdef
  set H : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 0 α η (Work.NN.Core.fiberAccess r j R) with hHdef
  have hHN : Work.CR.Flat.holderNorm 0 α η (Work.NN.Core.fiberAccess r j R) = S + H := by
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ← hSdef, ← hHdef]
  have hCnn : 0 < (s j - r j)⁻¹ ^ (l + 1) * R ^ 2
      + R ^ 2 * (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2) * (2 * ‖r‖) ^ (1 - α)
          + (s j - r j)⁻¹ ^ (l + 1)) := by positivity
  by_cases hStop : S = ⊤
  · rw [hHN, hStop, top_add, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; exact hCnn)]
    exact le_top
  by_cases hHtop : H = ⊤
  · rw [hHN, hHtop, add_top, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; exact hCnn)]
    exact le_top
  set A0 : ℝ := S.toReal with hA0def
  set K0 : ℝ := H.toReal with hK0def
  have hA0nn : 0 ≤ A0 := hA0def ▸ ENNReal.toReal_nonneg
  have hK0nn : 0 ≤ K0 := hK0def ▸ ENNReal.toReal_nonneg
  have hSeq : ENNReal.ofReal A0 = S := hA0def ▸ ENNReal.ofReal_toReal hStop
  have hHeq : ENNReal.ofReal K0 = H := hK0def ▸ ENNReal.ofReal_toReal hHtop
  have hvA : ∀ x ∈ Work.NN.Core.fiberAccess r j R, ‖η x‖ ≤ A0 := by
    intro x hx
    have h1 : ENNReal.ofReal ‖η x‖ ≤ S := by
      rw [hSdef, Work.CR.Flat.iterDerivNorm_zero]
      exact le_iSup₂_of_le x hx le_rfl
    rw [← hSeq] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hA0nn).mp h1
  have hvK : ∀ x ∈ Work.NN.Core.fiberAccess r j R, ∀ y ∈ Work.NN.Core.fiberAccess r j R,
      ‖η x - η y‖ ≤ K0 * ‖x - y‖ ^ α := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow (ne_of_gt hα)]
    · have h3 : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have h1 : ENNReal.ofReal (‖η x - η y‖ / ‖x - y‖ ^ α) ≤ H := by
        rw [hHdef]
        have h := Work.CR.Flat.le_holderSeminorm 0 α η (Work.NN.Core.fiberAccess r j R) hx hy hxy
        rwa [nrm_iter_zero_sub η (Work.NN.Core.fiberAccess r j R) x y] at h
      have h2 : ‖η x - η y‖ / ‖x - y‖ ^ α ≤ K0 :=
        (ENNReal.ofReal_le_ofReal_iff hK0nn).mp (by rw [hHeq]; exact h1)
      rwa [div_le_iff₀ h3] at h2
  have h1 : ∀ z ∈ Work.CR.Flat.polydisc (0 : Cn n) r,
      ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z‖
        ≤ ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * A0 := by
    intro z hz
    have := norm_fiberPotAnn_le_of_bound hR j l hr hrs hA0nn hvA hz
    calc ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z‖
        ≤ (s j - r j)⁻¹ ^ (l + 1) * R ^ 2 * A0 := this
      _ = ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * A0 := by ring
  have h2 : ∀ z ∈ Work.CR.Flat.polydisc (0 : Cn n) r,
      ∀ z' ∈ Work.CR.Flat.polydisc (0 : Cn n) r,
      ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z
          - fiberPotAnn j l (fiberAnnulus (s j) R) η z'‖
        ≤ (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2)) * (2 * ‖r‖) ^ (1 - α)
              + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0)) * ‖z - z'‖ ^ α := by
    intro z hz z' hz'
    exact norm_fiberPotAnn_sub_le hR j hα.le hα1.le hr hrs hη hA0nn hK0nn (by positivity)
      hvA hvK hLip hz hz'
  have hsm : Work.CR.Flat.holderNorm 0 α (fiberPotAnn j l (fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2 * A0)
        + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0)) :=
    Work.NN.Ratio.holderNorm_zero_le_of_bounds (α := α)
      (A := (s j - r j)⁻¹ ^ (l + 1) * R ^ 2 * A0)
      (B := R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2)) * (2 * ‖r‖) ^ (1 - α)
              + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0))
      (by positivity) (by positivity) h1 h2
  have hmain : Work.CR.Flat.holderNorm 0 α (fiberPotAnn j l (fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * S
        + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1))) * (S + H) := by
    refine hsm.trans ?_
    rw [show ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2 * A0)
          = ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * ENNReal.ofReal A0
        from ENNReal.ofReal_mul (by positivity)]
    rw [show ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0))
          = ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1))) * ENNReal.ofReal (A0 + K0)
        from ENNReal.ofReal_mul (by positivity)]
    rw [show ENNReal.ofReal (A0 + K0) = ENNReal.ofReal A0 + ENNReal.ofReal K0
        from ENNReal.ofReal_add hA0nn hK0nn]
    rw [hSeq, hHeq]
  calc Work.CR.Flat.holderNorm 0 α (fiberPotAnn j l (fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * S
        + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1))) * (S + H) := hmain
    _ ≤ ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2) * (S + H)
        + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1))) * (S + H) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (le_add_right le_rfl) bot_le
    _ = (ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2)
        + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
              * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)))) * (S + H) := by
        rw [add_mul]
    _ = ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2
        + R ^ 2 * (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2) * (2 * ‖r‖) ^ (1 - α)
            + (s j - r j)⁻¹ ^ (l + 1))) * (S + H) := by
        rw [show (ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2)
              + ENNReal.ofReal (R ^ 2 * ((((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2))
                  * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1))))
            = ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2
              + R ^ 2 * (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2) * (2 * ‖r‖) ^ (1 - α)
                  + (s j - r j)⁻¹ ^ (l + 1)))
          from (ENNReal.ofReal_add (by positivity) (by positivity)).symm]
    _ = ENNReal.ofReal ((s j - r j)⁻¹ ^ (l + 1) * R ^ 2
        + R ^ 2 * (((l + 1 : ℕ) : ℝ) * (s j - r j)⁻¹ ^ (l + 2) * (2 * ‖r‖) ^ (1 - α)
            + (s j - r j)⁻¹ ^ (l + 1)))
        * Work.CR.Flat.holderNorm 0 α η (Work.NN.Core.fiberAccess r j R) := by rw [hHN]

end Work.NN.Core
