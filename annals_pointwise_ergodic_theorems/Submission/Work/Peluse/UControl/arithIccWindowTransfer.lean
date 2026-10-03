import Mathlib
import Submission.Work.Peluse.Peel.arithIcc_sum_window_eq
import Submission.Work.Peluse.Peel.tsum_sq_eq_sum_symIcc
import Submission.Work.Peluse.Track.boxNormPow_v2_degenerate
import Submission.Work.Peluse.TransferUp.boxNormPow_arithIcc_raw_mono
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up

/-!
# Transferring the box-norm power from a shorter to a longer arithmetic progression

Let `Q(H) : Fin k → Finset ℤ` be the family of arithmetic progressions
`Q(H) i = arithIcc (d i) H = {d i, 2 d i, …, H d i}` (of cardinality `H` when `d i ≠ 0`, and the
singleton `{0}` when `d i = 0`).  For every level `k ≥ 2` the *raw* box quantity

`rawPow k Q S f = (∏_i |Q i|²) · boxNormPow k Q S f`

is monotone in the direction sets (`Work.Peluse.TransferUp.rawPow_mono_of_two_le`): the cube
average over a larger product of direction sets is larger, because all of its terms are
nonnegative at level `≥ 2`.  Hence

`(∏_i |Q(H') i|²) · boxNormPow k Q(H') S f ≤ (∏_i |Q(H) i|²) · boxNormPow k Q(H) S f`

for `H' ≤ H`.  The cardinality factor of `arithIcc (d i) ·` is at most the length up to the ratio
`H/H'` (`card_arithIcc_mul_le`: for `d i ≠ 0` it *is* the length, for `d i = 0` it is `1`), so
`∏_i |Q(H) i|² ≤ (H/H')^{2k} ∏_i |Q(H') i|²`, and dividing the raw inequality by the positive
normalising factor `∏_i |Q(H) i|²` gives the statement: the box-norm power at the *shorter* window
`H'` is bounded by the one at the *longer* window `H`, with the loss `(H'/H)^{2k}`.

The level hypothesis `2 ≤ k` is essential: at level `1` the cube sum is `∑_x ‖∑_{h∈Q 0} f(x+h)‖²`,
whose value is *not* monotone in `Q 0` (e.g. `f(x) = (-1)^x · 1_{symIcc N}`, `Q 0 = {1}` versus
`Q 0 = {1,2}`: the second sum vanishes pointwise on the bulk).

This is the general form of the scale-comparison step used by the concatenation chapter; the
specialisation to the `2`-fold PET family is `Work.Peluse.UControl.petFamPow_transfer_up`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The degenerate arithmetic progression: for `H ≥ 1` the set `0[H]` is the singleton `{0}`. -/
private lemma arithIcc_zero_eq_singleton {H : ℕ} (hH : 1 ≤ H) :
    Work.Peluse.arithIcc (0 : ℤ) H = {0} := by
  ext x
  rw [Work.Peluse.arithIcc, Finset.mem_image]
  constructor
  · rintro ⟨n, _hn, heq⟩
    rw [Finset.mem_singleton]
    rw [← heq]
    simp
  · intro hx
    rw [Finset.mem_singleton] at hx
    refine ⟨1, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · rw [← hx]; simp

/-- **The cardinality comparison.**  For `1 ≤ H' ≤ H` and any direction `d`, the cardinalities of
the two arithmetic progressions satisfy `|d[H]| · H' ≤ |d[H']| · H`.  For `d ≠ 0` both cards are
the respective lengths (an identity); for `d = 0` both are `1` (since `H', H ≥ 1`) and the
inequality is `H' ≤ H`. -/
private lemma card_arithIcc_mul_le {d : ℤ} {H' H : ℕ} (h1 : 1 ≤ H') (h2 : H' ≤ H) :
    ((Work.Peluse.arithIcc d H).card : ℝ) * (H' : ℝ)
      ≤ ((Work.Peluse.arithIcc d H').card : ℝ) * (H : ℝ) := by
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    rw [arithIcc_zero_eq_singleton (le_trans h1 h2), arithIcc_zero_eq_singleton h1]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    exact_mod_cast h2
  · rw [Work.Peluse.BoxNormDilation.card_arithIcc hd H,
      Work.Peluse.BoxNormDilation.card_arithIcc hd H']
    exact le_of_eq (mul_comm _ _)

theorem arithIccWindowTransfer {k : ℕ} (hk : 2 ≤ k) (d : Fin k → ℤ) {N H' H : ℕ} (f : ℤ → ℂ)
    (h1 : 1 ≤ H') (h2 : H' ≤ H) (hsup : Work.Peluse.SupportIn f N) :
    (((H' : ℝ) / (H : ℝ)) ^ (2 * k)) *
        Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H')
          (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H)
          (Work.Peluse.symIcc N) f := by
  have hf : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  set X : ℝ := Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H)
      (Work.Peluse.symIcc N) f with hX
  set X' : ℝ := Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H')
      (Work.Peluse.symIcc N) f with hX'
  have hXnn : 0 ≤ X := by
    rw [hX]; exact Work.Peluse.BoxNormDilation.boxNormPow_nonneg _ _ _ _
  have hX'nn : 0 ≤ X' := by
    rw [hX']; exact Work.Peluse.BoxNormDilation.boxNormPow_nonneg _ _ _ _
  have hcardpos : ∀ i : Fin k, (0 : ℝ) < ((Work.Peluse.arithIcc (d i) H).card : ℝ) := by
    intro i
    have hne : (Work.Peluse.arithIcc (d i) H).Nonempty :=
      ⟨d i * 1, Finset.mem_image.mpr ⟨1, by rw [Finset.mem_Icc]; omega, by ring⟩⟩
    have hc : 0 < (Work.Peluse.arithIcc (d i) H).card := Finset.card_pos.mpr hne
    exact_mod_cast hc
  -- the raw monotonicity of the unnormalised quantity
  have hraw : (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H').card : ℝ)) ^ 2) * X'
      ≤ (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) * X := by
    have := Work.Peluse.TransferUp.rawPow_mono_of_two_le (t := k) hk
      (Q := fun i : Fin k => Work.Peluse.arithIcc (d i) H')
      (Q' := fun i : Fin k => Work.Peluse.arithIcc (d i) H)
      (f := f) (Work.Peluse.symIcc N) hf
      (fun i => Finset.image_subset_image (Finset.Icc_subset_Icc_right h2))
    simpa only [Work.Peluse.TransferUp.rawPow, hX, hX'] using this
  -- the two normalising factors differ by at most `(H/H')^{2k}`
  have hkey : ((H' : ℝ) / (H : ℝ)) ^ (2 * k)
      * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2)
      ≤ ∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H').card : ℝ)) ^ 2 := by
    have hr : (0 : ℝ) ≤ (H' : ℝ) / (H : ℝ) := div_nonneg (Nat.cast_nonneg _) hHpos.le
    have hpt : ∀ i : Fin k,
        ((H' : ℝ) / (H : ℝ) * ((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2
          ≤ (((Work.Peluse.arithIcc (d i) H').card : ℝ)) ^ 2 := by
      intro i
      have hle : (H' : ℝ) / (H : ℝ) * ((Work.Peluse.arithIcc (d i) H).card : ℝ)
          ≤ ((Work.Peluse.arithIcc (d i) H').card : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hHpos]
        linarith [card_arithIcc_mul_le (d := d i) h1 h2]
      exact pow_le_pow_left₀ (mul_nonneg hr (le_of_lt (hcardpos i))) hle 2
    calc ((H' : ℝ) / (H : ℝ)) ^ (2 * k)
          * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2)
        = (∏ _i : Fin k, ((H' : ℝ) / (H : ℝ)) ^ 2)
          * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ = ∏ i : Fin k, (((H' : ℝ) / (H : ℝ)) ^ 2
            * (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) := by
          rw [Finset.prod_mul_distrib]
      _ = ∏ i : Fin k, (((H' : ℝ) / (H : ℝ))
            * ((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2 := by
          refine Finset.prod_congr rfl (fun i _ => by rw [mul_pow])
      _ ≤ ∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H').card : ℝ)) ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hpt i)
  have hApos : 0 < ∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (hcardpos i) 2)
  have hstep : ((H' : ℝ) / (H : ℝ)) ^ (2 * k) * X'
      * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2)
      ≤ X * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) := by
    calc ((H' : ℝ) / (H : ℝ)) ^ (2 * k) * X'
          * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2)
        = (((H' : ℝ) / (H : ℝ)) ^ (2 * k)
            * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2)) * X' := by ring
      _ ≤ (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H').card : ℝ)) ^ 2) * X' :=
          mul_le_mul_of_nonneg_right hkey hX'nn
      _ ≤ (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) * X := hraw
      _ = X * (∏ i : Fin k, (((Work.Peluse.arithIcc (d i) H).card : ℝ)) ^ 2) := by ring
  exact le_of_mul_le_mul_right hstep hApos

end

end Work.Peluse.UControl
