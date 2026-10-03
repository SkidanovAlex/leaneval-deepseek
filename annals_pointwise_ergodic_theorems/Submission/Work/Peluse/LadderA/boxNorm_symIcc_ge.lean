import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

open Work.Peluse

/-!
# Comparing the box norm over the windows `symIcc N` and `symIcc Nb`

The box norm `boxNorm t Q S f` depends on the support window `S` only through the normalising
factor `|S|⁻¹` (`boxNormPow t Q S f = (|S'| / |S|) · boxNormPow t Q S' f` for any nonempty `S'`).
Hence enlarging the window from `symIcc N` to `symIcc Nb ⊇ symIcc N` (with `Nb ≤ Kb * N`) can
only lose the factor `(|symIcc Nb| / |symIcc N|) ≤ Kb + 1`, and taking the `1/2^t`-th root
(an exponent in `[0,1]`) of that factor shrinks it further, so that

`boxNorm t Q (symIcc N) f / (Kb + 1) ≤ boxNorm t Q (symIcc Nb) f`.

The three ingredients are: the cardinalities `|symIcc L| = 2L + 1`, the elementary arithmetic
`2·Nb + 1 ≤ (Kb + 1)·(2·N + 1)` from `Nb ≤ Kb·N`, and the window-ratio identity for the box norm.
-/

/-- The cardinality of the symmetric interval: `|symIcc L| = 2L + 1`. -/
private lemma card_symIcc_local (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]; omega

/-- The cube sum depends on the support window only through the factor `|S|⁻¹`. -/
private lemma boxSumPow_scale_local (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ)
    (f : ℤ → ℂ) (hS' : S'.Nonempty) :
    boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * (S'.card : ℂ) * boxSumPow t Q S' f := by
  have hb : (S'.card : ℂ) ≠ 0 := by
    have h := Finset.card_ne_zero.mpr hS'
    exact_mod_cast h
  rw [boxSumPow, boxSumPow, prodCubeSum_eq, prodCubeSum_eq]
  field_simp

/-- The support window of a box-norm power is only a normalisation factor. -/
private lemma boxNormPow_window_ratio_local (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ)
    (f : ℤ → ℂ) (hS' : S'.Nonempty) :
    boxNormPow t Q S f = ((S'.card : ℝ) / (S.card : ℝ)) * boxNormPow t Q S' f := by
  have h := boxSumPow_scale_local t Q S S' f hS'
  have hnorm : ‖((S.card : ℂ))⁻¹‖ = ((S.card : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [boxNormPow, h, norm_mul, norm_mul, boxNormPow, hnorm]
  simp only [Complex.norm_natCast]
  ring

/-- **Enlarging the window of a box norm costs only the ratio of cardinalities.**  For `1 ≤ N`,
`N ≤ Nb`, `Nb ≤ Kb · N` and any `f : ℤ → ℂ`,

`‖f‖_{□^t_Q(symIcc N)} / (Kb + 1) ≤ ‖f‖_{□^t_Q(symIcc Nb)}`. -/
theorem boxNorm_symIcc_ge {t : ℕ} (Q : Fin t → Finset ℤ) {N Nb Kb : ℕ} (hN : 1 ≤ N)
    (hNN : N ≤ Nb) (hNb : Nb ≤ Kb * N) (f : ℤ → ℂ) :
    Work.Peluse.boxNorm t Q (Work.Peluse.symIcc N) f / ((Kb : ℝ) + 1)
      ≤ Work.Peluse.boxNorm t Q (Work.Peluse.symIcc Nb) f := by
  have hneNb : (symIcc Nb).Nonempty :=
    Finset.card_pos.mp (by rw [card_symIcc_local]; omega)
  have hKb0 : (0 : ℝ) ≤ (Kb : ℝ) := Nat.cast_nonneg Kb
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- the cardinality ratio is at most `Kb + 1`
  have hratio : ((symIcc Nb).card : ℝ) / ((symIcc N).card : ℝ) ≤ (Kb : ℝ) + 1 := by
    rw [card_symIcc_local, card_symIcc_local]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have h' : (Nb : ℝ) ≤ (Kb : ℝ) * (N : ℝ) := by exact_mod_cast hNb
    nlinarith [h', hKb0, hN0]
  -- the two box-norm powers differ by exactly that ratio
  have hprod := boxNormPow_window_ratio_local t Q (symIcc N) (symIcc Nb) f hneNb
  rw [boxNorm, boxNorm, hprod]
  set r : ℝ := 1 / (2 : ℝ) ^ t with hr
  have hR0 : (0 : ℝ) ≤ ((symIcc Nb).card : ℝ) / ((symIcc N).card : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ boxNormPow t Q (symIcc Nb) f := norm_nonneg _
  rw [Real.mul_rpow hR0 hB0]
  -- the root of the ratio is again at most `Kb + 1`
  have hRr : (((symIcc Nb).card : ℝ) / ((symIcc N).card : ℝ)) ^ r ≤ (Kb : ℝ) + 1 := by
    have h1 : (((symIcc Nb).card : ℝ) / ((symIcc N).card : ℝ)) ^ r
        ≤ ((Kb : ℝ) + 1) ^ r := Real.rpow_le_rpow hR0 hratio (by positivity)
    have h2 : ((Kb : ℝ) + 1) ^ r ≤ (Kb : ℝ) + 1 := by
      have hD1 : (1 : ℝ) ≤ (Kb : ℝ) + 1 := by linarith
      have hr1 : r ≤ 1 := by
        rw [hr, div_le_one (by positivity)]
        exact one_le_pow₀ (by norm_num)
      simpa using Real.rpow_le_rpow_of_exponent_le hD1 hr1
    linarith
  have hBr : (0 : ℝ) ≤ (boxNormPow t Q (symIcc Nb) f) ^ r := Real.rpow_nonneg hB0 r
  have hD : (0 : ℝ) < (Kb : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hD]
  calc (((symIcc Nb).card : ℝ) / ((symIcc N).card : ℝ)) ^ r * (boxNormPow t Q (symIcc Nb) f) ^ r
      ≤ ((Kb : ℝ) + 1) * (boxNormPow t Q (symIcc Nb) f) ^ r :=
        mul_le_mul_of_nonneg_right hRr hBr
    _ = (boxNormPow t Q (symIcc Nb) f) ^ r * ((Kb : ℝ) + 1) := by ring

end Work.Peluse.LadderA
