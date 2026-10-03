/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# `‖f‖_{□^t_Q(S)}^{2^t} ≤ ‖f‖_∞^{2^t-1} · ‖f‖_{ℓ¹} / |S|`

The `2 ^ t`-th power of Peluse's Gowers box norm is bounded by the sup norm to the power
`2 ^ t - 1` times the `ℓ¹`-norm, divided by the normalising cardinality `|S|`:

`boxNormPow t Q S F ≤ M ^ (2 ^ t - 1) * (∑' x, ‖F x‖) / |S|`

whenever `‖F‖_∞ ≤ M`, `F` is finitely supported and `S` is nonempty.  This is the elementary
interpolation bound between the sup-norm bound `boxNormPow_le_of_bound` (`≤ M^{2^t}`, when `F`
vanishes off `S`) and the `ℓ¹`-bound (which holds with *no* normalisation ansatz on `S`, which is
why the support box enters only through `|S|^{-1}`).

The proof is the direct one.  Unfolding the cube average,

`boxNormPow t Q S F = (1/|S|) (∏_i |Q_i|)^{-2} ‖∑_{h,h'} ∑_x ∏_{ω} C^{|ω|} F (x + ω·h + (1-ω)·h')‖`,

and for fixed shift tuples `(h, h')` the `x`-sum is estimated by distinguishing the corner
`ω = 0` (where `cornerShift h h' 0 = ∑_i h'_i`): the remaining `2 ^ t - 1` factors of the product
have modulus at most `M`, and the `x`-sum of `‖F (x + ∑_i h'_i)‖` is `‖F‖_{ℓ¹}` by translation
invariance.  Hence each inner sum is at most `M^{2^t-1} ‖F‖_{ℓ¹}`; summing over the `∏_i |Q_i|`
choices of `h` and of `h'` and using `(∏_i |Q_i|)^{-2} (∏_i |Q_i|)^2 ≤ 1` gives the claim.

The statement does not need `1 ≤ t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The modulus is preserved by iterating conjugation. -/
lemma boxL1_norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- A finitely supported function has summable norm. -/
lemma boxL1_summable_norm (F : ℤ → ℂ)
    (hsupp : ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0) :
    Summable (fun x : ℤ => ‖F x‖) := by
  obtain ⟨s, hs⟩ := hsupp
  exact summable_of_ne_finset_zero (s := s) (fun x hx => by simp [hs x hx])

/-- **The inner cube-term bound.**  For fixed shift tuples `h, h'`, the `x`-sum of the cube term
`∏_ω C^{|ω|} F (x + cornerShift h h' ω)` is at most `M ^ (2 ^ t - 1) · ‖F‖_{ℓ¹}`. -/
lemma boxL1_tsum_cubeTerm_le {t : ℕ} (Q : Fin t → Finset ℤ) (F : ℤ → ℂ) {M : ℝ}
    (hbd : ∀ x : ℤ, ‖F x‖ ≤ M)
    (hsupp : ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ M ^ (2 ^ t - 1) * ∑' x : ℤ, ‖F x‖ := by
  set c : (Fin t → Bool) → ℤ :=
    fun ω => cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω with hc
  set ω0 : Fin t → Bool := fun _ => false with hω0
  have hcardU : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp [Fintype.card_bool, Fintype.card_fin]
  have hcardE : (Finset.univ.erase ω0 : Finset (Fin t → Bool)).card = 2 ^ t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ ω0), hcardU]
  have hpt : ∀ x : ℤ, ‖∏ ω : Fin t → Bool, (star^[weight ω]) (F (x + c ω))‖
      ≤ M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖ := by
    intro x
    have hn : (∏ ω : Fin t → Bool, ‖(star^[weight ω]) (F (x + c ω))‖)
        = ∏ ω : Fin t → Bool, ‖F (x + c ω)‖ :=
      Finset.prod_congr rfl (fun ω _ => boxL1_norm_star_iterate (weight ω) (F (x + c ω)))
    have hsplit : (∏ ω : Fin t → Bool, ‖F (x + c ω)‖)
        = ‖F (x + c ω0)‖ *
          ∏ ω ∈ ((Finset.univ : Finset (Fin t → Bool)).erase ω0), ‖F (x + c ω)‖ :=
      (Finset.mul_prod_erase (Finset.univ : Finset (Fin t → Bool))
        (fun ω => ‖F (x + c ω)‖) (Finset.mem_univ ω0)).symm
    have htail : ∏ ω ∈ ((Finset.univ : Finset (Fin t → Bool)).erase ω0), ‖F (x + c ω)‖
        ≤ M ^ (2 ^ t - 1) := by
      calc ∏ ω ∈ ((Finset.univ : Finset (Fin t → Bool)).erase ω0), ‖F (x + c ω)‖
          ≤ ∏ ω ∈ ((Finset.univ : Finset (Fin t → Bool)).erase ω0), M :=
            Finset.prod_le_prod₀ (fun ω _ => norm_nonneg _) (fun ω _ => hbd _)
        _ = M ^ (2 ^ t - 1) := by rw [Finset.prod_const, hcardE]
    rw [norm_prod, hn, hsplit]
    calc ‖F (x + c ω0)‖ *
          ∏ ω ∈ ((Finset.univ : Finset (Fin t → Bool)).erase ω0), ‖F (x + c ω)‖
        ≤ ‖F (x + c ω0)‖ * M ^ (2 ^ t - 1) :=
          mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ = M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖ := by ring
  obtain ⟨s, hs⟩ := hsupp
  have hsummc : Summable (fun x : ℤ => ‖F (x + c ω0)‖) := by
    refine summable_of_ne_finset_zero (s := s.image (fun y => y - c ω0)) ?_
    intro x hx
    have hz : F (x + c ω0) = 0 := by
      apply hs
      intro hmem
      exact hx (Finset.mem_image.mpr ⟨x + c ω0, hmem, by ring⟩)
    simp [hz]
  have hsummM : Summable (fun x : ℤ => M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖) :=
    hsummc.mul_left _
  have hsumm1 : Summable (fun x : ℤ =>
      ‖∏ ω : Fin t → Bool, (star^[weight ω]) (F (x + c ω))‖) :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => hpt x) hsummM
  have h1 : (∑' x : ℤ, ‖∏ ω : Fin t → Bool, (star^[weight ω]) (F (x + c ω))‖)
      ≤ ∑' x : ℤ, M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖ :=
    hsumm1.tsum_le_tsum hpt hsummM
  have h2 : (∑' x : ℤ, M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖)
      = M ^ (2 ^ t - 1) * ∑' x : ℤ, ‖F (x + c ω0)‖ := tsum_mul_left
  have h3 : (∑' x : ℤ, ‖F (x + c ω0)‖) = ∑' x : ℤ, ‖F x‖ :=
    Equiv.tsum_eq (Equiv.addRight (c ω0)) (fun x => ‖F x‖)
  calc ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + c ω))‖
      ≤ ∑' x : ℤ, ‖∏ ω : Fin t → Bool, (star^[weight ω]) (F (x + c ω))‖ :=
        norm_tsum_le_tsum_norm hsumm1
    _ ≤ ∑' x : ℤ, M ^ (2 ^ t - 1) * ‖F (x + c ω0)‖ := h1
    _ = M ^ (2 ^ t - 1) * (∑' x : ℤ, ‖F x‖) := by rw [h2, h3]

/-- For natural numbers `a i`, the product of the inverses times the product is at most `1`. -/
lemma boxL1_prod_inv_mul_prod_le_one {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    (∏ i, ((a i : ℝ))⁻¹) * (∏ i, (a i : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one₀ (fun i _ => ?_) (fun i _ => ?_)
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · rcases eq_or_ne (a i) 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ (by exact_mod_cast h)]

/-- **The box-norm power is bounded by the sup norm to the power `2 ^ t - 1` times the
`ℓ¹`-norm, divided by `|S|`.** -/
theorem boxNormPow_le_L1 {t : ℕ} (ht : 1 ≤ t) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (F : ℤ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hbd : ∀ x : ℤ, ‖F x‖ ≤ M)
    (hsupp : ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0) (hS : 0 < S.card) :
    Work.Peluse.boxNormPow t Q S F
      ≤ M ^ (2 ^ t - 1) * (∑' x : ℤ, ‖F x‖) / (S.card : ℝ) := by
  set L1 : ℝ := ∑' x : ℤ, ‖F x‖ with hL1
  set P : ℝ := ∏ i : Fin t, ((Q i).card : ℝ) with hP
  set Pin : ℝ := ∏ i : Fin t, ((Q i).card : ℝ)⁻¹ with hPin
  set X : ℝ := M ^ (2 ^ t - 1) * L1 with hX
  set Raw : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) with hRaw
  have hXnn : 0 ≤ X := mul_nonneg (pow_nonneg hM _) (tsum_nonneg (fun x => norm_nonneg _))
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  have hPinnn : 0 ≤ Pin := Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  -- inner bound for each pair of shift tuples
  have hinner : ∀ h h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ ≤ X := by
    intro h h'
    have h0 := boxL1_tsum_cubeTerm_le Q F hbd hsupp h h'
    rwa [hX, hL1]
  -- the raw double sum
  have hRaw_le : ‖Raw‖ ≤ (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
      (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * X := by
    rw [hRaw]
    calc ‖∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
          Finset.sum_le_sum (fun h _ => norm_sum_le _ _)
      _ ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i}, X :=
          Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => hinner h h'))
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * X) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
          (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * X := by ring
  have hcardα : (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) = P := by
    rw [hP, Fintype.card_pi]
    push_cast
    exact Finset.prod_congr rfl (fun i _ => by rw [Fintype.card_coe])
  have hnormA : ‖(∏ i : Fin t, (((Q i).card : ℂ))⁻¹)‖ = Pin := by
    rw [hPin, norm_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [norm_inv, Complex.norm_natCast]
  have hbox : Work.Peluse.boxNormPow t Q S F
      = ‖((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
          (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * Raw‖ := by
    rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum_eq, hRaw]
  have hnormbox : ‖((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
        (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * Raw‖
      = ((S.card : ℝ))⁻¹ * Pin * Pin * ‖Raw‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, hnormA]
  have hPP : Pin * Pin * P * P ≤ 1 := by
    have hnn : 0 ≤ Pin * P := mul_nonneg hPinnn hPnn
    have h4 := mul_le_mul (boxL1_prod_inv_mul_prod_le_one (fun i : Fin t => (Q i).card))
      (boxL1_prod_inv_mul_prod_le_one (fun i : Fin t => (Q i).card)) hnn (by norm_num : (0:ℝ) ≤ 1)
    have hPinP : Pin * P
        = (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) * (∏ i : Fin t, ((Q i).card : ℝ)) := by
      rw [hPin, hP]
    rw [hPinP] at h4
    nlinarith [h4]
  have hSnn : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hSinvnn : (0:ℝ) ≤ ((S.card : ℝ))⁻¹ := inv_nonneg.mpr hSnn
  have hlast : ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * X) ≤ ((S.card : ℝ))⁻¹ * X := by
    have h1 : ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * X)
        = ((S.card : ℝ))⁻¹ * ((Pin * Pin * P * P) * X) := by ring
    rw [h1]
    calc ((S.card : ℝ))⁻¹ * ((Pin * Pin * P * P) * X)
        ≤ ((S.card : ℝ))⁻¹ * (1 * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPP hXnn) hSinvnn
      _ = ((S.card : ℝ))⁻¹ * X := by ring
  rw [hbox, hnormbox]
  calc ((S.card : ℝ))⁻¹ * Pin * Pin * ‖Raw‖
      ≤ ((S.card : ℝ))⁻¹ * Pin * Pin *
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
            (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * X) := by
        have : (0:ℝ) ≤ ((S.card : ℝ))⁻¹ * Pin * Pin :=
          mul_nonneg (mul_nonneg hSinvnn hPinnn) hPinnn
        exact mul_le_mul_of_nonneg_left hRaw_le this
    _ = ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * X) := by rw [hcardα]
    _ ≤ ((S.card : ℝ))⁻¹ * X := hlast
    _ = M ^ (2 ^ t - 1) * L1 / (S.card : ℝ) := by rw [hX]; ring

end

end Work.Peluse.Ulower
