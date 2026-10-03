import Mathlib
import Submission.Work.Peluse.LadderP.stateBSumBound

namespace Work.Peluse.LadderP

/-!
# The "bad mass" estimate of the power-loss ladder

The Lemma 5.1 input of the ladder step is applied on the data whose exceptional set
`stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)` has at most `ε M₁` elements.  The
consumer (`LadderP.massLower`) needs the *mass* of the complementary ("bad") data to be at most `γ`
in the `M₁^{-(2j+1)}`-normalisation:

`((M₁:ℝ))⁻¹ ^ (2*j+1) * ∑_{h₁,h₁',h'_s} [ε M₁ < #stepBad …] ≤ γ`.

The input `hcount` is the *pair* (`Fin (j+1) → Fin M₁`) average of the cardinalities of the bad
sets, of size `C_s (M₁η + log (j+2))`; it is produced by `LadderP.stepBadCount`.  The passage from
the pair average to the triple average is *lossless* because the bad set only sees the head
`headPart h = h₁` of its first argument: `stepBad` is independent of the last coordinate of `h`
(`stepShift_irrel_last`), so every slice `h (last) = hs` carries the same multiset of bad sets, and
the `M₁^{-(2j+1)}`-normalised triple average is exactly the pair average.

The chain is: the pointwise inequality `εM₁·[bad] ≤ #stepBad`, the identity
`∑_{hs} (slice sum of cardinalities) = ∑_{h,h'} #stepBad` and the constancy of the slices, the
`hcount` bound, `hlog` (`log ≤ M₁η`) and `hconst` (`C_s·2M₁η ≤ εγM₁`).
-/

noncomputable section

open scoped BigOperators

/-- `stepBad` only sees the shift family, so equal shift families give equal bad sets. -/
lemma stepBad_congr {j M₁ : ℕ} (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool))
    {h h' h₂ h₂' : Fin (j+1) → Fin M₁}
    (hsh : ∀ i : Fin (2^j), stepShiftE E h h' i = stepShiftE E h₂ h₂' i) :
    stepBad j M₁ η E h h' = stepBad j M₁ η E h₂ h₂' := by
  unfold stepBad
  refine Finset.filter_congr (fun a _ => ?_)
  simp only [hsh]

/-- The bad set does not depend on the last coordinate of its first argument. -/
lemma stepBad_snoc_last_irrel {j M₁ : ℕ} (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool))
    (h₁ : Fin j → Fin M₁) (hs hs' : Fin M₁) (h' : Fin (j+1) → Fin M₁) :
    stepBad j M₁ η E (Fin.snoc h₁ hs) h' = stepBad j M₁ η E (Fin.snoc h₁ hs') h' :=
  stepBad_congr η E (fun i => stepShift_irrel_last h₁ hs hs' h' (E i))

/-- The pair sum of the cardinalities of the bad sets, split according to the head and the last
coordinate of the first argument (hence as the sum over the slices `h (last) = hs`). -/
lemma pairCardSum_eq_sliceSum (j M₁ : ℕ) (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool)) :
    (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
        ((stepBad j M₁ η E h h').card : ℝ))
      = ∑ hs : Fin M₁, ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ((stepBad j M₁ η E (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ) := by
  have hsplit : (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
        ((stepBad j M₁ η E h h').card : ℝ))
      = ∑ h₁ : Fin j → Fin M₁, ∑ hs : Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ((stepBad j M₁ η E (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ) := by
    rw [sum_univ_snoc j M₁ (fun h => ∑ h' : Fin (j+1) → Fin M₁,
      ((stepBad j M₁ η E h h').card : ℝ))]
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    refine Finset.sum_congr rfl (fun hs _ => ?_)
    rw [sum_univ_snoc j M₁ (fun h' => ((stepBad j M₁ η E (Fin.snoc h₁ hs) h').card : ℝ))]
  rw [hsplit, Finset.sum_comm]

/-- The slice sums of the cardinalities of the bad sets do not depend on the slice `hs`. -/
lemma sliceSum_eq (j M₁ : ℕ) (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool)) (hs hs' : Fin M₁) :
    (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ((stepBad j M₁ η E (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ))
      = ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ((stepBad j M₁ η E (Fin.snoc h₁ hs') (Fin.snoc h₁' h'_s)).card : ℝ) := by
  refine Finset.sum_congr rfl (fun h₁ _ => Finset.sum_congr rfl (fun h₁' _ =>
    Finset.sum_congr rfl (fun h'_s _ => ?_)))
  rw [stepBad_snoc_last_irrel η E h₁ hs hs' (Fin.snoc h₁' h'_s)]

theorem badMassLe (j M₁ : ℕ) (hM₁ : 1 ≤ M₁) {η ε γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hε0 : 0 < ε) (hs : Fin M₁) {C_s : ℝ} (hC_s : 0 < C_s)
    (hcount : ((M₁ : ℝ))⁻¹ ^ (2 * (j + 1)) *
        ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
          ((Work.Peluse.LadderP.stepBad j M₁ η (Work.Peluse.LadderP.enumAll j) h h').card : ℝ)
        ≤ C_s * ((M₁ : ℝ) * η + Real.log ((j : ℝ) + 2)))
    (hlog : Real.log ((j : ℝ) + 2) ≤ (M₁ : ℝ) * η)
    (hconst : C_s * (2 * (M₁ : ℝ) * η) ≤ ε * γ * (M₁ : ℝ)) :
    ((M₁ : ℝ))⁻¹ ^ (2 * j + 1) *
      ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        (if ε * (M₁ : ℝ)
            < ((Work.Peluse.LadderP.stepBad j M₁ η (Work.Peluse.LadderP.enumAll j)
                (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)
          then (1 : ℝ) else 0) ≤ γ := by
  classical
  have hM₁pos : (0:ℝ) < (M₁:ℝ) := by exact_mod_cast hM₁
  have hM₁ne : (M₁:ℝ) ≠ 0 := ne_of_gt hM₁pos
  -- the total pair sum of the cardinalities of the bad sets
  set A : ℝ := ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
      ((stepBad j M₁ η (enumAll j) h h').card : ℝ) with hAdef
  -- the slices `h (last) = hs`
  set Slf : Fin M₁ → ℝ := fun hs' =>
      ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs') (Fin.snoc h₁' h'_s)).card : ℝ)
    with hSlf
  -- the mass of the bad triples
  set T : ℝ := ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
      (if ε * (M₁:ℝ)
          < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)
        then (1:ℝ) else 0) with hTdef
  -- `hcount`, transported to `A`
  have hcountA : ((M₁:ℝ))⁻¹ ^ (2*(j+1)) * A
      ≤ C_s * ((M₁:ℝ) * η + Real.log ((j:ℝ) + 2)) := hcount
  -- the `C_s`-bound of the average cardinality
  have hCsl : C_s * ((M₁:ℝ) * η + Real.log ((j:ℝ) + 2)) ≤ ε * γ * (M₁:ℝ) := by
    have h1 : (M₁:ℝ) * η + Real.log ((j:ℝ) + 2) ≤ 2 * (M₁:ℝ) * η := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h1 hC_s.le) hconst
  have hA_le : A ≤ (M₁:ℝ)^(2*(j+1)) * (ε * γ * (M₁:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hcountA (by positivity : (0:ℝ) ≤ (M₁:ℝ)^(2*(j+1)))
    have hL : (M₁:ℝ)^(2*(j+1)) * (((M₁:ℝ))⁻¹^(2*(j+1)) * A) = A := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hM₁ne, one_pow, one_mul]
    rw [hL] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hCsl (by positivity))
  -- the slices are all equal, and their sum is `A`
  have hA_eq : A = ∑ hs' : Fin M₁, Slf hs' := by
    rw [hAdef, hSlf]
    exact pairCardSum_eq_sliceSum j M₁ η (enumAll j)
  have hslice : ∀ hs' : Fin M₁, Slf hs' = Slf hs := by
    intro hs'
    rw [hSlf]
    exact sliceSum_eq j M₁ η (enumAll j) hs' hs
  have hA_eq2 : A = (M₁:ℝ) * Slf hs := by
    rw [hA_eq]
    calc (∑ hs' : Fin M₁, Slf hs') = ∑ _hs' : Fin M₁, Slf hs :=
          Finset.sum_congr rfl (fun hs' _ => hslice hs')
      _ = (M₁:ℝ) * Slf hs := by
          simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  -- the slice at `hs` is bounded by the pair sum over `M₁`
  have hSl_bound : Slf hs ≤ (M₁:ℝ)^(2*j+1) * (ε * γ * (M₁:ℝ)) := by
    have h2 : (M₁:ℝ) * Slf hs ≤ (M₁:ℝ)^(2*(j+1)) * (ε*γ*(M₁:ℝ)) := by
      rw [← hA_eq2]; exact hA_le
    have h3 : (M₁:ℝ)^(2*(j+1)) = (M₁:ℝ) * (M₁:ℝ)^(2*j+1) := by
      rw [show 2*(j+1) = 2*j+1+1 by omega, pow_succ]
      ring
    rw [h3, mul_assoc] at h2
    exact le_of_mul_le_mul_left h2 hM₁pos
  -- the pointwise comparison of the bad mass with the cardinality
  have hpt : ∀ h₁ : Fin j → Fin M₁, ∀ h₁' : Fin j → Fin M₁, ∀ h'_s : Fin M₁,
      ε * (M₁:ℝ) *
          (if ε * (M₁:ℝ)
              < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs)
                    (Fin.snoc h₁' h'_s)).card : ℝ)
            then (1:ℝ) else 0)
        ≤ ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs)
              (Fin.snoc h₁' h'_s)).card : ℝ) := by
    intro h₁ h₁' h'_s
    by_cases hbad : ε * (M₁:ℝ)
        < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs)
              (Fin.snoc h₁' h'_s)).card : ℝ)
    · rw [if_pos hbad]; linarith
    · rw [if_neg hbad]; simp
  have hT_bound : ε * (M₁:ℝ) * T ≤ Slf hs := by
    rw [hTdef, hSlf]
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum (fun h₁ _ => Finset.sum_le_sum (fun h₁' _ =>
      Finset.sum_le_sum (fun h'_s _ => hpt h₁ h₁' h'_s)))
  -- conclusion
  have hT_le : T ≤ (M₁:ℝ)^(2*j+1) * γ := by
    have hkey : ε * (M₁:ℝ) * T ≤ ε * (M₁:ℝ) * ((M₁:ℝ)^(2*j+1) * γ) :=
      le_trans hT_bound (le_trans hSl_bound (le_of_eq (by ring)))
    exact le_of_mul_le_mul_left hkey (by positivity : (0:ℝ) < ε * (M₁:ℝ))
  calc ((M₁:ℝ))⁻¹ ^ (2*j+1) * T
      ≤ ((M₁:ℝ))⁻¹ ^ (2*j+1) * ((M₁:ℝ)^(2*j+1) * γ) :=
        mul_le_mul_of_nonneg_left hT_le (by positivity)
    _ = γ := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hM₁ne, one_pow, one_mul]

end

end Work.Peluse.LadderP
