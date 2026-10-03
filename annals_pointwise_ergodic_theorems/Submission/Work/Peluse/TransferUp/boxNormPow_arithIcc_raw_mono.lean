/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.TransferUp.rawPow_succ_peel
import Submission.Work.Peluse.TransferUp.rawPow_mono_two
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Peel.boxNormPow_diag_peel

/-!
# Monotonicity of the raw box quantity in the direction sets

This file proves `Work.Peluse.TransferUp.boxNormPow_arithIcc_raw_mono`, the "raw monotonicity"
step of the scale-comparison arguments of `Submission/Work/Peluse/TransferUp/`.

## The mathematics

Write `Q(H) : Fin t → Finset ℤ` for the family of arithmetic progressions
`Q(H) i = arithIcc (d i) (H i) = {d i, 2 (d i), …, (H i) (d i)}`, of cardinality `H i` (the
directions `d i` are non-zero).  Peluse's box-norm power of order `t` normalises the cube sum by
the *cardinalities* `|Q i|`, so the quantity which grows with the directions is the *raw* one

`rawPow t Q S f = (∏_i |Q i|²) · boxNormPow t Q S f`

(`Work.Peluse.TransferUp.rawPow`).  The target statement says that `rawPow` — equivalently
`(∏_i (H i)²) · boxNormPow` along the progressions `Q(H)` — is monotone in `H`:

`H ≤ H'  ⟹  (∏_i (H i)²) boxNormPow t Q(H) S f ≤ (∏_i (H' i)²) boxNormPow t Q(H') S f`.

The hypothesis `2 ≤ t` is essential: for `t = 1` the level-one cube sum is the sum of squares
`∑_x ‖∑_{h ∈ Q 0} f (x + h)‖²`, whose summands themselves depend on `Q 0`, and whose value is *not*
monotone in `Q 0` (take `Q 0 = {1}` versus `Q 0 = {1,2}` and `f = δ₀ - 2δ₁ + δ₂`: the value drops
from `6` to `4`).

## The proof

Let `Raw(t, Q, S, f) = (∏_i |Q i|²) · boxSumPow t Q S f` be the *complex* raw cube average, so that
`rawPow t Q S f = ‖Raw(t, Q, S, f)‖` and (by the peel identity, in the form
`Work.Peluse.TransferUp.rawPow_succ_peel`)

`Raw(t+1, Q, S, f) = ∑_{h, h' ∈ Q 0} Raw(t, Q[1:], S, Δ'_{h,h'} f)`,

where `Δ'_{h,h'} f (u) = f (u + h) · conj (f (u + h'))`.

1. `Work.Peluse.TransferUp.rawPow_succ_peel` (a colleague's lemma) is the peel identity above for
   `rawPow` itself, obtained from the complex peel `Work.Peluse.Concat.boxNormPow_succ_peel_gen` by
   cancelling the factor `|Q 0|²` against `|Q 0|⁻²` (both sides are `0` when `Q 0 = ∅`).
2. `rawPow_le_of_subset_coord0`: the peel identity exhibits `rawPow (t+1) (consTup A Q) S f` as a
   double sum over `A × A` of nonnegative summands which do **not** depend on `A`; hence growing the
   first coordinate `A ⊆ A'` increases the sum.  This uses `t ≥ 1` (so that the level-`t` quantity
   being summed is a modulus).
3. `rawPow_mono_aux` (induction on the level, base case `t = 2` supplied by a colleague's
   `Work.Peluse.TransferUp.rawPow_mono_two`): for `t = k+2` the peel identity reduces the statement
   to the level `k+1+2` statement for the differences `Δ'_{h,h'} f` (induction hypothesis, applied
   termwise) plus the first-coordinate step 2 for the two copies of the first coordinate set.
4. The target statement follows after replacing `H i` by `|arithIcc (d i) (H i)| = H i`
   (`Work.Peluse.BoxNormDilation.card_arithIcc`) and `arithIcc (d i) (H i) ⊆ arithIcc (d i) (H' i)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.TransferUp

noncomputable section

/-- **Growth of the first coordinate.**  For `t ≥ 1`, enlarging the first direction set
`A ⊆ A'` (the remaining directions being kept fixed) does not decrease the raw box quantity.
This is where the hypothesis `2 ≤ t` of the target statement enters: the peel identity writes
`rawPow (t+1)` as a sum over `A × A` of the nonnegative level-`t` quantities
`rawPow t Q S (Δ'_{h,h'} f)`, which do not depend on `A`. -/
theorem rawPow_le_of_subset_coord0 {t : ℕ} (ht : 1 ≤ t) {A A' : Finset ℤ} (hAA : A ⊆ A')
    {Q : Fin t → Finset ℤ} (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    rawPow (t + 1) (consTup A Q) S f ≤ rawPow (t + 1) (consTup A' Q) S f := by
  rw [rawPow_succ_peel (t := t) ht (consTup A Q) S hf,
      rawPow_succ_peel (t := t) ht (consTup A' Q) S hf]
  have hlam : (fun i : Fin t => (consTup A Q) i.succ) = Q := by funext i; simp
  have hlam' : (fun i : Fin t => (consTup A' Q) i.succ) = Q := by funext i; simp
  rw [hlam, hlam']
  simp only [consTup_zero]
  calc (∑ h ∈ A, ∑ h' ∈ A, rawPow t Q S (fun u : ℤ => f (u + h) * star (f (u + h'))))
      ≤ (∑ h ∈ A', ∑ h' ∈ A, rawPow t Q S (fun u : ℤ => f (u + h) * star (f (u + h')))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hAA
          (fun h _ _ => Finset.sum_nonneg (fun h' _ => rawPow_nonneg t Q S _))
    _ ≤ (∑ h ∈ A', ∑ h' ∈ A', rawPow t Q S (fun u : ℤ => f (u + h) * star (f (u + h')))) :=
        Finset.sum_le_sum (fun h _ => Finset.sum_le_sum_of_subset_of_nonneg hAA
          (fun h' _ _ => rawPow_nonneg t Q S _))

/-! ## Monotonicity in all coordinates -/

/-- **Monotonicity of the raw box quantity.**  For `t ≥ 2` and direction sets `Q ⊆ Q'` (coordinate
by coordinate) the raw box quantity grows.  The induction on `k` with `t = k + 2` peels the first
coordinate (`rawPow_succ_peel`), applies the induction hypothesis to the differences
`Δ'_{h,h'} f = f (· + h) · conj (f (· + h'))`, and finally grows the first coordinate by
`rawPow_le_of_subset_coord0`. -/
theorem rawPow_mono_aux : ∀ k : ℕ, ∀ (Q Q' : Fin (k + 2) → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ), Work.Peluse.FinSuppZ f → (∀ i, Q i ⊆ Q' i) →
      rawPow (k + 2) Q S f ≤ rawPow (k + 2) Q' S f := by
  intro k
  induction k with
  | zero => exact fun Q Q' S f hf h => rawPow_mono_two S hf h
  | succ k ih =>
      intro Q Q' S f hf h
      -- grow the first coordinate from `Q 0` to `Q' 0` (the tail still `Q`)
      have h1 : rawPow (k + 2 + 1) (consTup (Q 0) (fun i => Q i.succ)) S f
          ≤ rawPow (k + 2 + 1) (consTup (Q' 0) (fun i => Q i.succ)) S f :=
        rawPow_le_of_subset_coord0 (t := k + 2) (by omega) (h 0) S hf
      -- then the tail is compared termwise inside the peel identity
      have h2 : rawPow (k + 2 + 1) (consTup (Q' 0) (fun i => Q i.succ)) S f
          ≤ rawPow (k + 2 + 1) (consTup (Q' 0) (fun i => Q' i.succ)) S f := by
        rw [rawPow_succ_peel (t := k + 2) (by omega) (consTup (Q' 0) (fun i => Q i.succ)) S hf,
            rawPow_succ_peel (t := k + 2) (by omega) (consTup (Q' 0) (fun i => Q' i.succ)) S hf]
        have hlam : (fun i : Fin (k + 2) => (consTup (Q' 0) (fun j => Q j.succ)) i.succ)
            = (fun i : Fin (k + 2) => Q i.succ) := by funext i; simp
        have hlam' : (fun i : Fin (k + 2) => (consTup (Q' 0) (fun j => Q' j.succ)) i.succ)
            = (fun i : Fin (k + 2) => Q' i.succ) := by funext i; simp
        rw [hlam, hlam']
        simp only [consTup_zero]
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        exact ih (fun i => Q i.succ) (fun i => Q' i.succ) S
          (fun u => f (u + a) * star (f (u + b)))
          (Work.Peluse.Peel.finSuppZ_mul_star_shift f hf a b) (fun i => h i.succ)
      calc rawPow (k + 2 + 1) Q S f
          = rawPow (k + 2 + 1) (consTup (Q 0) (fun i => Q i.succ)) S f :=
              congrArg (fun R => rawPow (k + 2 + 1) R S f) (consTup_self Q).symm
        _ ≤ rawPow (k + 2 + 1) (consTup (Q' 0) (fun i => Q i.succ)) S f := h1
        _ ≤ rawPow (k + 2 + 1) (consTup (Q' 0) (fun i => Q' i.succ)) S f := h2
        _ = rawPow (k + 2 + 1) Q' S f :=
              congrArg (fun R => rawPow (k + 2 + 1) R S f) (consTup_self Q')

/-- **Monotonicity of the raw box quantity**, for an arbitrary level `t ≥ 2`. -/
theorem rawPow_mono_of_two_le {t : ℕ} (ht : 2 ≤ t) {Q Q' : Fin t → Finset ℤ} (S : Finset ℤ)
    {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) (h : ∀ i, Q i ⊆ Q' i) :
    rawPow t Q S f ≤ rawPow t Q' S f := by
  have hk := rawPow_mono_aux (t - 2)
  rw [Nat.sub_add_cancel ht] at hk
  exact hk Q Q' S f hf h

/-! ## The target statement -/

/-- **Raw monotonicity of the box-norm power along arithmetic progressions.**  For `2 ≤ t`,
non-zero directions `d i ≠ 0` and boxes `H ≤ H'`, the *raw* box quantity
`(∏_i (H i)²) · boxNormPow t (arithIcc (d i) (H i)) S f` is monotone in `H`: the factor
`∏_i (H i)²` cancels the normalisation `∏_i |arithIcc (d i) (H i)|⁻²` of Peluse's box norm (the
progressions have exactly `H i` elements), leaving the cube average over the full product of the
direction sets, which grows with them because all its terms are nonnegative. -/
theorem boxNormPow_arithIcc_raw_mono {t : ℕ} (ht : 2 ≤ t) {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0) {H H' : Fin t → ℕ} (hH : ∀ i, 1 ≤ H i) (hle : ∀ i, H i ≤ H' i) (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) : (∏ i : Fin t, ((H i : ℝ)) ^ 2) * Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (H i)) S f ≤ (∏ i : Fin t, ((H' i : ℝ)) ^ 2) * Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (H' i)) S f := by
  have hcard : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) (H i)).card = H i :=
    fun i => Work.Peluse.BoxNormDilation.card_arithIcc (hd i) (H i)
  have hcard' : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) (H' i)).card = H' i :=
    fun i => Work.Peluse.BoxNormDilation.card_arithIcc (hd i) (H' i)
  have hp : (∏ i : Fin t, ((H i : ℝ)) ^ 2)
      = ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (H i)).card : ℝ)) ^ 2 :=
    Finset.prod_congr rfl (fun i _ => by rw [hcard i])
  have hp' : (∏ i : Fin t, ((H' i : ℝ)) ^ 2)
      = ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (H' i)).card : ℝ)) ^ 2 :=
    Finset.prod_congr rfl (fun i _ => by rw [hcard' i])
  rw [hp, hp']
  refine rawPow_mono_of_two_le ht S hf (fun i => ?_)
  rw [Work.Peluse.arithIcc, Work.Peluse.arithIcc]
  exact Finset.image_subset_image (Finset.Icc_subset_Icc_right (hle i))

end

end Work.Peluse.TransferUp
