import Mathlib
import Submission.Work.KMTAreas.SupNorm.Norms
import Submission.Work.KMTAreas.SupNorm.eLpNorm_min_inv_sq_le_corrected

/-!
# The `Lᵖ` bound for a sup-norm error of the form `min A (B / x²)`

This module proves the numerical `Lᵖ` estimate for an error term `E` whose pointwise
sup-norm bound is

`‖E x‖ ≤ min A (B / x²)`  for `x ≠ 0`,

where the two constants are dominated by

`A ≤ ν · δ · ηI0`  and  `B ≤ Kb · (ν / δ + 1)`

with `0 ≤ ν ≤ 1`, `0 < δ ≤ 1` and `ηI0 = ∫ ‖η‖` the `L¹` norm of the cutoff.

The resulting bound is

`‖E‖_{Lᵖ} ≤ 2^{3/(2q)} · Kb^{1/(2q)} · ηI0^{1 - 1/(2q)} · (2q/(2q-1))^{1/q} · ν^{1 - 1/(2q)} · δ^{1 - 1/q}`,

where `q = p.toReal`.  It is the `Lᵖ` form of the sup-norm bound for a Fourier multiplier
with symbol on a single `δ`-window (`norm_fourierInv_error_le`), with the two scales
`ν` (the symbol oscillation on the window) and `δ` (the window width) tracked separately.

The proof has two parts.

* The *analytic* part is the sharp computation of the `Lᵖ` norm of the envelope
  `min A (B/x²)`, which is `eLpNorm_min_inv_sq_le_corrected`: it gives
  `‖E‖_{Lᵖ} ≤ (2 · A^{q-1/2} · √B · 2q/(2q-1))^{1/q}`.  Since the hypothesis of that lemma
  is required at *every* point while our `hE` only holds for `x ≠ 0`, we first modify `E`
  at the single point `0` (a null set), which does not change the `Lᵖ` norm.

* The *arithmetic* part (`key_real`) replaces `A, B` by their bounds: with `A ≤ νδηI0` and
  `B ≤ Kb(ν/δ+1)` the base `2 A^{q-1/2} B^{1/2} · 2q/(2q-1)` becomes
  `2^{3/2} Kb^{1/2} ηI0^{q-1/2} (2q/(2q-1)) ν^{q-1/2} δ^{q-1} · ((ν+δ)/2)^{1/2}`,
  and `ν + δ ≤ 2` removes the last factor, giving exactly the stated constant.
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory

/-- The numerical heart of `eLpNorm_error_le`: with `q ≥ 1` and the two scale bounds
`A ≤ ν δ η`, `B ≤ Kb (ν/δ + 1)` (`0 ≤ ν ≤ 1`, `0 < δ ≤ 1`) the sharp envelope constant
`(2 A^{q-1/2} B^{1/2} · 2q/(2q-1))^{1/q}` is dominated by
`2^{3/(2q)} Kb^{1/(2q)} η^{1-1/(2q)} (2q/(2q-1))^{1/q} ν^{1-1/(2q)} δ^{1-1/q}`.

Indeed, distributing the `1/q`-power over the product turns the left-hand side into
`(ν^{1-1/(2q)} η^{1-1/(2q)} Kb^{1/(2q)} (2q/(2q-1))^{1/q}) · (2^{1/q} δ^{1-1/(2q)} (ν/δ+1)^{1/(2q)})`,
and the second factor is at most `2^{3/(2q)} δ^{1-1/q}` because `ν/δ + 1 ≤ 2/δ ⟺ ν + δ ≤ 2`. -/
private lemma key_real {ν δ Kb η q : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKb : 0 ≤ Kb) (hη : 0 ≤ η) (hq : 1 ≤ q) :
    (2 * (ν * δ * η) ^ (q - 1 / 2) * (Kb * (ν / δ + 1)) ^ (1 / 2 : ℝ)
        * (2 * q / (2 * q - 1))) ^ (1 / q)
      ≤ 2 ^ (3 / (2 * q)) * Kb ^ (1 / (2 * q)) * η ^ (1 - 1 / (2 * q))
        * (2 * q / (2 * q - 1)) ^ (1 / q) * ν ^ (1 - 1 / (2 * q)) * δ ^ (1 - 1 / q) := by
  have hδ0 : (0 : ℝ) ≤ δ := hδ.le
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hb : (0 : ℝ) ≤ 1 / (2 * q) := by positivity
  have hc0 : (0 : ℝ) ≤ 2 * q / (2 * q - 1) := by
    apply div_nonneg (by linarith); linarith
  have hA0 : (0 : ℝ) ≤ ν * δ * η := mul_nonneg (mul_nonneg hν hδ0) hη
  have hB0 : (0 : ℝ) ≤ Kb * (ν / δ + 1) := mul_nonneg hKb (by positivity)
  have he1 : (q - 1 / 2) * (1 / q) = 1 - 1 / (2 * q) := by field_simp
  have he2 : (1 / 2 : ℝ) * (1 / q) = 1 / (2 * q) := by field_simp
  have hdiv : (2 / δ) ^ (1 / (2 * q)) = 2 ^ (1 / (2 * q)) * δ ^ (-(1 / (2 * q))) := by
    rw [Real.div_rpow (by norm_num) hδ0, Real.rpow_neg hδ0]
    rfl
  have hcore : 2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (ν / δ + 1) ^ (1 / (2 * q))
      ≤ 2 ^ (3 / (2 * q)) * δ ^ (1 - 1 / q) := by
    have h1 : ν / δ + 1 ≤ 2 / δ := by
      rw [div_add_one (ne_of_gt hδ)]
      exact div_le_div_of_nonneg_right (by linarith) hδ0
    have h2 : (ν / δ + 1) ^ (1 / (2 * q)) ≤ (2 / δ) ^ (1 / (2 * q)) :=
      Real.rpow_le_rpow (by positivity) h1 hb
    calc 2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (ν / δ + 1) ^ (1 / (2 * q))
        ≤ 2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (2 / δ) ^ (1 / (2 * q)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (2 ^ (1 / (2 * q)) * δ ^ (-(1 / (2 * q)))) := by
          rw [hdiv]
      _ = 2 ^ (1 / q) * 2 ^ (1 / (2 * q)) * (δ ^ (1 - 1 / (2 * q)) * δ ^ (-(1 / (2 * q)))) := by
          ring
      _ = 2 ^ (1 / q + 1 / (2 * q)) * δ ^ ((1 - 1 / (2 * q)) + -(1 / (2 * q))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add hδ]
      _ = 2 ^ (3 / (2 * q)) * δ ^ (1 - 1 / q) := by
          rw [show (1 : ℝ) / q + 1 / (2 * q) = 3 / (2 * q) by field_simp; ring,
              show (1 : ℝ) - 1 / (2 * q) + -(1 / (2 * q)) = 1 - 1 / q by ring]
  have hmain : (2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (ν / δ + 1) ^ (1 / (2 * q)))
        * (ν ^ (1 - 1 / (2 * q)) * η ^ (1 - 1 / (2 * q)) * Kb ^ (1 / (2 * q))
            * (2 * q / (2 * q - 1)) ^ (1 / q))
      ≤ (2 ^ (3 / (2 * q)) * δ ^ (1 - 1 / q))
        * (ν ^ (1 - 1 / (2 * q)) * η ^ (1 - 1 / (2 * q)) * Kb ^ (1 / (2 * q))
            * (2 * q / (2 * q - 1)) ^ (1 / q)) :=
    mul_le_mul_of_nonneg_right hcore (by positivity)
  calc (2 * (ν * δ * η) ^ (q - 1 / 2) * (Kb * (ν / δ + 1)) ^ (1 / 2 : ℝ)
          * (2 * q / (2 * q - 1))) ^ (1 / q)
      = (2 ^ (1 / q) * δ ^ (1 - 1 / (2 * q)) * (ν / δ + 1) ^ (1 / (2 * q)))
        * (ν ^ (1 - 1 / (2 * q)) * η ^ (1 - 1 / (2 * q)) * Kb ^ (1 / (2 * q))
            * (2 * q / (2 * q - 1)) ^ (1 / q)) := by
        rw [Real.mul_rpow (by positivity) hc0, Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hA0, ← Real.rpow_mul hB0,
            Real.mul_rpow (mul_nonneg hν hδ0) hη, Real.mul_rpow hν hδ0,
            Real.mul_rpow hKb (by positivity), he1, he2]
        ring
    _ ≤ (2 ^ (3 / (2 * q)) * δ ^ (1 - 1 / q))
        * (ν ^ (1 - 1 / (2 * q)) * η ^ (1 - 1 / (2 * q)) * Kb ^ (1 / (2 * q))
            * (2 * q / (2 * q - 1)) ^ (1 / q)) := hmain
    _ = 2 ^ (3 / (2 * q)) * Kb ^ (1 / (2 * q)) * η ^ (1 - 1 / (2 * q))
        * (2 * q / (2 * q - 1)) ^ (1 / q) * ν ^ (1 - 1 / (2 * q)) * δ ^ (1 - 1 / q) := by ring

theorem eLpNorm_error_le {E : ℝ → ℂ} {A B ν δ Kb : ℝ} {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hKb : 0 ≤ Kb) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hE : ∀ x : ℝ, x ≠ 0 → ‖E x‖ ≤ min A (B / x ^ 2))
    (hAb : A ≤ ν * δ * Work.KMTAreas.SupNorm.etaI0) (hBb : B ≤ Kb * (ν / δ + 1))
    (hEm : MeasureTheory.AEStronglyMeasurable E MeasureTheory.volume) :
    MeasureTheory.eLpNorm E p MeasureTheory.volume
      ≤ ENNReal.ofReal (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
          * Work.KMTAreas.SupNorm.etaI0 ^ (1 - 1 / (2 * p.toReal))
          * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
          * ν ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal)) := by
  have hpt : p ≠ ⊤ := ne_of_lt hp2
  have hδ0 : (0 : ℝ) ≤ δ := hδ.le
  have hA0 : (0 : ℝ) ≤ ν * δ * etaI0 := mul_nonneg (mul_nonneg hν hδ0) etaI0_nonneg
  have hB0 : (0 : ℝ) ≤ Kb * (ν / δ + 1) := mul_nonneg hKb (by positivity)
  set q : ℝ := p.toReal with hqdef
  have hq1 : 1 ≤ q := by rw [hqdef]; exact ENNReal.toReal_mono hpt hp1
  -- The pointwise domination of the envelope: `min A (B/x²) ≤ min (νδηI0) (Kb(ν/δ+1)/x²)`.
  have hmin : ∀ x : ℝ, min A (B / x ^ 2) ≤ min (ν * δ * etaI0) (Kb * (ν / δ + 1) / x ^ 2) := by
    intro x
    refine min_le_min hAb ?_
    by_cases hx : x = 0
    · subst hx; simp
    · exact div_le_div_of_nonneg_right hBb (by
        have h1 : (0 : ℝ) < |x| := abs_pos.mpr hx
        have h2 : (0 : ℝ) < |x| ^ 2 := pow_pos h1 2
        rw [sq_abs] at h2
        exact le_of_lt h2)
  -- Modify `E` at the single point `0`; the `Lᵖ` norm does not see null sets.
  let F : ℝ → ℂ := fun x => if x = 0 then 0 else E x
  have hFae : F =ᵐ[volume] E := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
    by_contra hx0
    exact hx (if_neg hx0)
  have hFeq : MeasureTheory.eLpNorm F p MeasureTheory.volume
      = MeasureTheory.eLpNorm E p MeasureTheory.volume := MeasureTheory.eLpNorm_congr_ae hFae
  have hF : ∀ x : ℝ, ‖F x‖ ≤ min (ν * δ * etaI0) (Kb * (ν / δ + 1) / x ^ 2) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [show F 0 = 0 from if_pos rfl, norm_zero]
      exact le_min hA0 (by positivity)
    · rw [show F x = E x from if_neg hx]
      exact le_trans (hE x hx) (hmin x)
  -- The remaining arithmetic.
  have hc0 : (0 : ℝ) < 2 * q - 1 := by linarith
  have hcq : (0 : ℝ) ≤ 2 * q / (2 * q - 1) := div_nonneg (by linarith) hc0.le
  have h1p : (1 / p : ENNReal).toReal = 1 / q := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, hqdef]
  have hX : (0 : ℝ) ≤ 2 * (ν * δ * etaI0) ^ (q - 1 / 2) * (Kb * (ν / δ + 1)) ^ (1 / 2 : ℝ)
      * (2 * q / (2 * q - 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg hB0 _)) hcq
  have hkey := key_real (ν := ν) (δ := δ) (Kb := Kb) (η := etaI0) (q := q)
      hν hν1 hδ hδ1 hKb etaI0_nonneg hq1
  calc MeasureTheory.eLpNorm E p MeasureTheory.volume
      = MeasureTheory.eLpNorm F p MeasureTheory.volume := hFeq.symm
    _ ≤ ENNReal.ofReal (2 * (ν * δ * etaI0) ^ (q - 1 / 2) * (Kb * (ν / δ + 1)) ^ (1 / 2 : ℝ)
          * (2 * q / (2 * q - 1))) ^ (1 / p).toReal := by
        have h := eLpNorm_min_inv_sq_le_corrected (E := F) hA0 hB0 hp1 hpt hF (hEm.congr hFae.symm)
        rw [← hqdef] at h
        exact h
    _ = ENNReal.ofReal ((2 * (ν * δ * etaI0) ^ (q - 1 / 2) * (Kb * (ν / δ + 1)) ^ (1 / 2 : ℝ)
          * (2 * q / (2 * q - 1))) ^ (1 / q)) := by
        rw [h1p, ENNReal.ofReal_rpow_of_nonneg hX (by positivity)]
    _ ≤ ENNReal.ofReal (2 ^ (3 / (2 * q)) * Kb ^ (1 / (2 * q)) * etaI0 ^ (1 - 1 / (2 * q))
        * (2 * q / (2 * q - 1)) ^ (1 / q) * ν ^ (1 - 1 / (2 * q)) * δ ^ (1 - 1 / q)) :=
        ENNReal.ofReal_le_ofReal hkey

end Work.KMTAreas.SupNorm
