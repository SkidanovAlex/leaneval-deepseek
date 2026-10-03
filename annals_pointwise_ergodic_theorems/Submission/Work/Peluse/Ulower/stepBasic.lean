import Mathlib
import Submission.Work.Peluse.Ulower.helpers
import Submission.Work.Peluse.Ulower.Defs
import Submission.Work.Peluse.Ulower.supportIn_off_Icc

/-!
# Elementary tools for the degree-lowering assembly

* the support of an iterated `Δ'`-difference (`iterDelta'_supportIn`),
* monotonicity of the box-norm power in the support box (`boxNormPow_le_of_subset`),
* the absorption of a constant into a power of `(δ·δ')` (`exists_pow_le_of_lt_one`,
  `final_compare`) — this is what lets a bound `C·δ^A·δ'^B` with an unspecified positive constant
  `C` produce the target's `(δ·D/Ns)^K` once `δ·δ'` is bounded away from `1`.
-/

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Membership in `symIcc` -/

lemma mem_symIcc_iff (L : ℕ) (x : ℤ) : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc]
  exact mem_Icc_neg_natAbs_iff

/-! ## The support of an iterated `Δ'`-difference -/

/-- `iterDelta' k sh F` vanishes off `symIcc (L + ∑ i, |(sh i).1| + |(sh i).2|)` whenever `F`
vanishes off `symIcc L`. -/
lemma iterDelta'_supportIn : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) {L : ℕ} {F : ℤ → ℂ},
    (∀ x : ℤ, x ∉ symIcc L → F x = 0) →
    ∀ x : ℤ, x ∉ symIcc (L + ∑ i : Fin k, ((sh i).1.natAbs + (sh i).2.natAbs)) →
      iterDelta' k sh F x = 0 := by
  intro k
  induction k with
  | zero =>
      intro sh L F hF x hx
      exact hF x (by simpa using hx)
  | succ k ih =>
      intro sh L F hF x hx
      have hG := ih (fun i : Fin k => sh i.succ) hF
      have hsum : (∑ i : Fin (k + 1), ((sh i).1.natAbs + (sh i).2.natAbs))
          = ((sh 0).1.natAbs + (sh 0).2.natAbs)
            + ∑ i : Fin k, ((sh i.succ).1.natAbs + (sh i.succ).2.natAbs) := by
        rw [Fin.sum_univ_succ]
      have hx' : L + (((sh 0).1.natAbs + (sh 0).2.natAbs)
            + ∑ i : Fin k, ((sh i.succ).1.natAbs + (sh i.succ).2.natAbs)) < x.natAbs := by
        rw [← hsum]
        exact Nat.lt_of_not_le (fun h => hx (by rw [mem_symIcc_iff]; exact h))
      have key : ∀ a : ℤ, a.natAbs ≤ ((sh 0).1.natAbs + (sh 0).2.natAbs) →
          x + a ∉ symIcc (L + ∑ i : Fin k, ((sh i.succ).1.natAbs + (sh i.succ).2.natAbs)) := by
        intro a ha hm
        rw [mem_symIcc_iff] at hm
        have h1 := Int.natAbs_add_le (x + a) (-a)
        rw [Int.natAbs_neg, add_neg_cancel_right] at h1
        omega
      have hdef : iterDelta' (k + 1) sh F x =
          star (iterDelta' k (fun i => sh i.succ) F (x + (sh 0).1)) *
            iterDelta' k (fun i => sh i.succ) F (x + (sh 0).2) := rfl
      rw [hdef, hG (x + (sh 0).1) (key (sh 0).1 (by omega)),
        hG (x + (sh 0).2) (key (sh 0).2 (by omega))]
      simp

/-! ## Monotonicity of the box-norm power in the support box -/

lemma boxNormPow_nonneg' (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ boxNormPow t Q S f := by
  rw [boxNormPow]; exact norm_nonneg _

/-- The box-norm power decreases when the support box grows. -/
lemma boxNormPow_le_of_subset {t : ℕ} (Q : Fin t → Finset ℤ) {S S' : Finset ℤ}
    (hSS' : S ⊆ S') (hS : S.Nonempty) (f : ℤ → ℂ) :
    boxNormPow t Q S' f ≤ boxNormPow t Q S f := by
  have hS'ne : S'.Nonempty := hS.mono hSS'
  have h := boxNormPow_eq_mul_card t Q S S' f hS'ne
  have hcardS : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hcard : (1 : ℝ) ≤ (S'.card : ℝ) / (S.card : ℝ) := by
    rw [le_div_iff₀ hcardS]
    have := Finset.card_le_card hSS'
    have : (S.card : ℝ) ≤ (S'.card : ℝ) := by exact_mod_cast ‹S.card ≤ S'.card›
    linarith
  calc boxNormPow t Q S' f
      = 1 * boxNormPow t Q S' f := (one_mul _).symm
    _ ≤ ((S'.card : ℝ) / (S.card : ℝ)) * boxNormPow t Q S' f := by
        exact mul_le_mul_of_nonneg_right hcard (boxNormPow_nonneg' t Q S' f)
    _ = boxNormPow t Q S f := h.symm

/-! ## Absorbing a constant into a power of `δ·δ'` -/

/-- For `0 ≤ r < 1` and `C > 0` some power of `r` is `≤ C`. -/
lemma exists_pow_le_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {C : ℝ} (hC : 0 < C) :
    ∃ m : ℕ, r ^ m ≤ C := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hev : ∀ᶠ m : ℕ in Filter.atTop, r ^ m < C :=
    h.eventually (Iio_mem_nhds hC)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp hev
  exact ⟨m, le_of_lt (hm m le_rfl)⟩

/-- **The final comparison.**  If `C > 0`, `0 ≤ δ, δ' ≤ 1` and `δ·δ' ≤ r` with `r < 1`, then for
some exponent `K` one has `(δ·δ')^K ≤ C·δ^A·δ'^B` for all `A, B` — this is what converts the
constant-laden bound of the chain (`C·δ^A·δ'^B ≤ boxNormPow 2`) into the target's conclusion
`(δ·D/Ns)^K ≤ boxNormPow 2`. -/
lemma final_compare {δ δ' C r : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδ'0 : 0 ≤ δ') (hδ'1 : δ' ≤ 1)
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : δ * δ' ≤ r) {A B : ℕ} :
    ∃ K : ℕ, 1 ≤ K ∧ (δ * δ') ^ K ≤ C * δ ^ A * δ' ^ B := by
  obtain ⟨m, hm⟩ := exists_pow_le_of_lt_one hr0 hr1 hC
  refine ⟨A + B + m + 1, by omega, ?_⟩
  have hprod : (δ * δ') ^ (A + B) ≤ δ ^ A * δ' ^ B := by
    have hfac : (δ * δ') ^ (A + B) = (δ ^ A * δ' ^ B) * (δ ^ B * δ' ^ A) := by
      rw [mul_pow, pow_add, pow_add]; ring
    rw [hfac]
    have hb : δ ^ B * δ' ^ A ≤ 1 := by
      have h1 : δ ^ B ≤ 1 := pow_le_one₀ hδ0 hδ1
      have h2 : δ' ^ A ≤ 1 := pow_le_one₀ hδ'0 hδ'1
      calc δ ^ B * δ' ^ A ≤ 1 * 1 := mul_le_mul h1 h2 (pow_nonneg hδ'0 A) (by norm_num)
        _ = 1 := by norm_num
    exact mul_le_of_le_one_right (by positivity) hb
  have hpow : (δ * δ') ^ (A + B + m + 1) = (δ * δ') ^ (A + B) * (δ * δ') ^ (m + 1) := by
    rw [show A + B + m + 1 = (A + B) + (m + 1) from by omega, pow_add]
  rw [hpow]
  have hsmall : (δ * δ') ^ (m + 1) ≤ C := by
    have h1 : (δ * δ') ^ (m + 1) ≤ r ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hδ0 hδ'0) hr _
    have h2 : r ^ (m + 1) ≤ r ^ m := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    linarith
  calc (δ * δ') ^ (A + B) * (δ * δ') ^ (m + 1)
      ≤ (δ ^ A * δ' ^ B) * C :=
        mul_le_mul hprod hsmall (by positivity) (by positivity)
    _ = C * δ ^ A * δ' ^ B := by ring

end

end Work.Peluse.Ulower
