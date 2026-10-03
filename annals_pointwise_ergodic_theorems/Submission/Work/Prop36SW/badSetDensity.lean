import Mathlib
import Submission.Work.Prop36SW.card_badSet_pFlat_le
import Submission.Work.Peluse.UControl.parBox_card

/-!
# Density of the chain's bad set: `Work.Prop36SW.badSetDensity`

`Work.Prop36SW.card_badSet_pFlat_le` counts the parameters `x` in the closed box `Abox D (m+1) H`
at which some slot coefficient `pFlat D d c m Λ s` vanishes, by
`(|D.S (m+1)| · m) · (2H+1)^(nD D (m+1) - 1)`.  Since the box has cardinality
`(2H+1)^(nD D (m+1))` (`card_Abox` + `parBox_card`), dividing by one factor of `2H+1` converts the
count into a *density*: the bad set has relative measure at most

    (|D.S (m+1)| · m) / (2H+1),

so if `4 · |D.S (m+1)| · m ≤ γ · (2H+1)` then the bad set occupies at most a `γ`-fraction of the box.
-/

namespace Work.Prop36SW

open Work.Peluse.UControl
open Work.Peluse.Prop36SW

noncomputable section

/-- Degenerate case of the level count.  If the flat parameter space of level `m+1` is empty, i.e.
`nD D (m+1) = 0`, then for `m ≥ 1` the level-`m` attachment map (which sends every level-`(m+1)`
slot to a *nonempty* subset of the level-`m` slots) forces `D.S (m+1)` to be empty as well, so the
slot count `|D.S (m+1)| · m` vanishes.  (For `m = 0` the factor `m` already vanishes.) -/
private lemma card_S_mul_eq_zero_of_nD_eq_zero {D : IdxDatum} {m : ℕ}
    (h : nD D (m + 1) = 0) : Fintype.card (D.S (m + 1)) * m = 0 := by
  by_cases hm : m = 0
  · rw [hm, mul_zero]
  · have hsum : ∑ j : Fin (m + 1), Fintype.card (D.S j) = 0 := by
      rw [← Fintype.card_sigma]
      exact h
    have hSm : Fintype.card (D.S (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) = 0 :=
      Finset.sum_eq_zero_iff.mp hsum _ (Finset.mem_univ _)
    have hSm' : IsEmpty (D.S m) := Fintype.card_eq_zero_iff.mp hSm
    have hSempty : IsEmpty (D.S (m + 1)) :=
      ⟨fun s => by
        obtain ⟨a, _⟩ := (D.par m s).2
        exact hSm'.false a⟩
    rw [Fintype.card_eq_zero_iff.mpr hSempty, zero_mul]

theorem badSetDensity (D : Work.Peluse.UControl.IdxDatum) (d m Λ H : ℕ) (c : ℤ) (γ : ℝ)
    (hc : c ≠ 0) (hΛ : Λ ≠ 0) (hd : m < d) (hH : 1 ≤ H)
    (hγ : 4 * ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ) ≤ γ * (2 * (H : ℝ) + 1)) :
    4 * (((Work.Peluse.Prop36SW.Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
        Work.Peluse.Prop36SW.pFlat D d c m Λ s x = 0)).card : ℝ)
      ≤ γ * ((Work.Peluse.Prop36SW.Abox D (m + 1) H).card : ℝ) := by
  classical
  have hcard := card_badSet_pFlat_le D d m Λ H c hc hΛ hd hH
  -- the box has cardinality `(2H+1)^(nD D (m+1))`
  have hAbox : (Abox D (m + 1) H).card = (2 * H + 1) ^ (nD D (m + 1)) := by
    rw [card_Abox, parBox_card]
    congr 1
    simp only [nD, Fintype.card_sigma]
  rcases eq_or_ne (nD D (m + 1)) 0 with hn0 | hn0
  · -- degenerate case: the flat parameter space is empty, so the slot count vanishes
    have hpow1 : ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1) = 1 := by
      rw [hn0, Nat.zero_sub, pow_zero]
    have h1 : (((Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s x = 0)).card : ℝ)
        ≤ ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ)
          * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1) := by
      exact_mod_cast hcard
    rw [hpow1, mul_one] at h1
    have hK0 : Fintype.card (D.S (m + 1)) * m = 0 := card_S_mul_eq_zero_of_nD_eq_zero hn0
    have hzero : ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ) = 0 := by
      rw [hK0]
      simp
    rw [hzero] at h1
    have hγnn : 0 ≤ γ := by
      have hpos : (0 : ℝ) < 2 * (H : ℝ) + 1 := by
        have h1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
        linarith
      have h4 : (4 : ℝ) * ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ) = 0 := by
        rw [hzero]
        ring
      have hγ' : 0 ≤ γ * (2 * (H : ℝ) + 1) := by
        rw [h4] at hγ
        exact hγ
      exact le_of_mul_le_mul_right (by linarith) hpos
    have hnn : (0 : ℝ) ≤ γ * ((Abox D (m + 1) H).card : ℝ) :=
      mul_nonneg hγnn (Nat.cast_nonneg _)
    linarith
  · -- main case: `2H + 1 > 0` and the box has at least one factor of it to spare
    have hnp : 0 < nD D (m + 1) := Nat.pos_of_ne_zero hn0
    have h1 : (((Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s x = 0)).card : ℝ)
        ≤ ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ)
          * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1) := by
      exact_mod_cast hcard
    have hNcast : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    have hNnn : (0 : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) := by positivity
    have hpow : ((2 * H + 1 : ℕ) : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1)
        = ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1)) := by
      conv_rhs => rw [← Nat.sub_add_cancel hnp]
      rw [pow_succ']
    calc 4 * (((Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
            pFlat D d c m Λ s x = 0)).card : ℝ)
        ≤ 4 * (((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ)
            * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (4 * ((Fintype.card (D.S (m + 1)) * m : ℕ) : ℝ))
            * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1) := by ring
      _ ≤ (γ * (2 * (H : ℝ) + 1)) * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1) :=
          mul_le_mul_of_nonneg_right hγ (pow_nonneg hNnn _)
      _ = γ * ((2 * (H : ℝ) + 1) * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1) - 1)) := by ring
      _ = γ * ((2 * H + 1 : ℕ) : ℝ) ^ (nD D (m + 1)) := by rw [← hNcast, hpow]
      _ = γ * ((Abox D (m + 1) H).card : ℝ) := by rw [hAbox, Nat.cast_pow]

end

end Work.Prop36SW
