import Mathlib
import Submission.Deep
import Submission.PairSum

/-!
# Sum-identities for `Echi`, `Eext`, `Efix` (no dependence on the deep lemma)
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- Double-counting: sum over `U,V,A` of `|χ(U∪V,A)|` equals `C(u+v,u)` times
the sum over `W,A` of `|χ(W,A)|`. -/
lemma num_identity {S : Finset (Finset α)} {X : Finset α} {u v : ℕ}
    (hv : v ≤ X.card - u) :
    (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S,
        ((chi S (U ∪ V) A).card : ℝ)) =
      ((u + v).choose u : ℝ) *
        (∑ A ∈ S, ∑ W ∈ cardSubsets X (u + v), ((chi S W A).card : ℝ)) := by
  calc
    (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S,
        ((chi S (U ∪ V) A).card : ℝ))
        = (∑ U ∈ cardSubsets X u, ∑ A ∈ S, ∑ V ∈ cardSubsets (X \ U) v,
            ((chi S (U ∪ V) A).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro U hU
            exact Finset.sum_comm
    _ = (∑ A ∈ S, ∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v,
            ((chi S (U ∪ V) A).card : ℝ)) := by
            exact Finset.sum_comm
    _ = (∑ A ∈ S, ((u + v).choose u : ℝ) *
            (∑ W ∈ cardSubsets X (u + v), ((chi S W A).card : ℝ))) := by
            apply Finset.sum_congr rfl
            intro A hA
            exact PairSum.pair_sum_eq (X := X) (u := u) (v := v)
              (F := fun W : Finset α => ((chi S W A).card : ℝ)) hv (by
                intro U V W hW; rw [hW])
    _ = ((u + v).choose u : ℝ) *
            (∑ A ∈ S, ∑ W ∈ cardSubsets X (u + v), ((chi S W A).card : ℝ)) := by
            rw [← Finset.mul_sum]

/-- `Eext` is at most `Efix`: adding a random `v`-subset can only shrink `|χ|`. -/
lemma Eext_le_Efix {S : Finset (Finset α)} {X U : Finset α} {v : ℕ}
    (hSne : S.Nonempty) (hv : v ≤ (X \ U).card) :
    Eext S X U v ≤ Efix S U := by
  have hV0n : 0 < (cardSubsets (X \ U) v).card := by
    rw [card_cardSubsets]
    exact Nat.choose_pos hv
  have hS0n : 0 < S.card := Finset.card_pos.mpr hSne
  have hVpos : 0 < ((cardSubsets (X \ U) v).card : ℝ) := by exact_mod_cast hV0n
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS0n
  have hVle : ∀ V ∈ cardSubsets (X \ U) v,
      (∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) ≤ (∑ A ∈ S, ((chi S U A).card : ℝ)) := by
    intro V hV
    have hUU : U ⊆ U ∪ V := Finset.subset_union_left
    apply Finset.sum_le_sum
    intro A hA
    exact_mod_cast (chi_card_mono (S := S) (U := U) (W := U ∪ V) (A := A) hA hUU)
  have hnum : (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) ≤
      (cardSubsets (X \ U) v).card * (∑ A ∈ S, ((chi S U A).card : ℝ)) := by
    calc
      (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ))
          ≤ (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S U A).card : ℝ)) := by
              apply Finset.sum_le_sum
              intro V hV
              exact hVle V hV
      _ = (cardSubsets (X \ U) v).card * (∑ A ∈ S, ((chi S U A).card : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
  unfold Eext Efix
  calc
    (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) /
          (((cardSubsets (X \ U) v).card : ℝ) * (S.card : ℝ))
        ≤ ((cardSubsets (X \ U) v).card * (∑ A ∈ S, ((chi S U A).card : ℝ)) : ℝ) /
          (((cardSubsets (X \ U) v).card : ℝ) * (S.card : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ) := by
            field_simp [ne_of_gt hVpos, ne_of_gt hSpos]

/-- `Echi S X (u+v)` equals the average over `u`-subsets `U` of `Eext S X U v`. -/
lemma Echi_eq_avg_Eext {S : Finset (Finset α)} {X : Finset α} {u v : ℕ}
    (hU : u ≤ X.card) (hv : v ≤ X.card - u) (hSne : S.Nonempty) :
    Echi S X (u + v) =
      (∑ U ∈ cardSubsets X u, Eext S X U v) / (cardSubsets X u).card := by
  have huvn : u + v ≤ X.card := by
    calc
      u + v ≤ u + (X.card - u) := Nat.add_le_add_left hv u
      _ = X.card := Nat.add_sub_of_le hU
  let T : ℝ := ∑ A ∈ S, ∑ W ∈ cardSubsets X (u + v), ((chi S W A).card : ℝ)
  have hS0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hSne))
  have hW0 : ((X.card.choose (u + v) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos huvn))
  have hU0 : ((X.card.choose u : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos hU))
  have hV0 : (((X.card - u).choose v : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos hv))
  have hEextU : ∀ U ∈ cardSubsets X u,
      Eext S X U v =
        (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) /
          ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ)) := by
    intro U hUmem
    have hUc : U.card = u := (Finset.mem_powersetCard.mp hUmem).2
    have hUsub : U ⊆ X := (Finset.mem_powersetCard.mp hUmem).1
    have hcard : (cardSubsets (X \ U) v).card = (X.card - u).choose v := by
      rw [card_cardSubsets]
      congr 1
      rw [Finset.card_sdiff_of_subset hUsub, hUc]
    unfold Eext
    rw [hcard]
  have hsumEext : (∑ U ∈ cardSubsets X u, Eext S X U v) =
      ((u + v).choose u : ℝ) * T /
        ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ)) := by
    calc
      (∑ U ∈ cardSubsets X u, Eext S X U v)
        = (∑ U ∈ cardSubsets X u,
            (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) /
              ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ))) := by
            apply Finset.sum_congr rfl
            intro U hU
            exact hEextU U hU
      _ = (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S,
            ((chi S (U ∪ V) A).card : ℝ)) /
              ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ)) := by
            rw [← Finset.sum_div]
      _ = ((u + v).choose u : ℝ) * T /
              ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ)) := by
            rw [num_identity (S := S) (X := X) (u := u) (v := v) hv]
  have hLHS : Echi S X (u + v) = T / ((S.card : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ)) := by
    unfold Echi
    rw [card_cardSubsets]
  have hden : ((X.card.choose (u + v) : ℕ) : ℝ) * (((u + v).choose u : ℕ) : ℝ) =
      ((X.card.choose u : ℕ) : ℝ) * (((X.card - u).choose v : ℕ) : ℝ) := by
    exact_mod_cast (PairSum.choose_mul_eq (n := X.card) (u := u) (v := v) huvn)
  calc
    Echi S X (u + v) = T / ((S.card : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ)) := hLHS
    _ = (((u + v).choose u : ℝ) * T /
            ((((X.card - u).choose v : ℕ) : ℝ) * (S.card : ℝ))) /
          ((X.card.choose u : ℕ) : ℝ) := by
          field_simp [hS0, hW0, hU0, hV0, hden]
          ring_nf
          calc
            T * (((X.card - u).choose v : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
                = T * ((((X.card - u).choose v : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)) := by ring
            _ = T * (((X.card.choose u : ℕ) : ℝ) * (((X.card - u).choose v : ℕ) : ℝ)) := by ring
            _ = T * (((X.card.choose (u + v) : ℕ) : ℝ) * (((u + v).choose u : ℕ) : ℝ)) := by
                  rw [← hden]
            _ = T * ((X.card.choose (u + v) : ℕ) : ℝ) * (((u + v).choose u : ℕ) : ℝ) := by ring
    _ = (∑ U ∈ cardSubsets X u, Eext S X U v) / (cardSubsets X u).card := by
          rw [hsumEext, card_cardSubsets]

/-- average of `Efix` over `u`-subsets equals `Echi u`. -/
lemma Echi_eq_avg_Efix {S : Finset (Finset α)} {X : Finset α} {u : ℕ}
    (hSne : S.Nonempty) :
    Echi S X u = (∑ U ∈ cardSubsets X u, Efix S U) / (cardSubsets X u).card := by
  have hS0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hSne))
  let T' : ℝ := ∑ U ∈ cardSubsets X u, ∑ A ∈ S, ((chi S U A).card : ℝ)
  have h1 : Echi S X u = T' / ((S.card : ℝ) * ((cardSubsets X u).card : ℝ)) := by
    unfold Echi
    rw [Finset.sum_comm]
  have h2 : (∑ U ∈ cardSubsets X u, Efix S U) = T' / (S.card : ℝ) := by
    unfold Efix
    rw [← Finset.sum_div]
  calc
    Echi S X u = T' / ((S.card : ℝ) * ((cardSubsets X u).card : ℝ)) := h1
    _ = (T' / (S.card : ℝ)) / ((cardSubsets X u).card : ℝ) := by
          rw [div_div]
    _ = (∑ U ∈ cardSubsets X u, Efix S U) / (cardSubsets X u).card := by
          rw [h2]

/-- If every `u`-subset `U` satisfies `Eext ≤ c0·Efix(U)` then `Echi(u+v) ≤ c0·Echi(u)`. -/
lemma Echi_step_of_fixed {S : Finset (Finset α)} {X : Finset α} {u v : ℕ} {c0 : ℝ}
    (hU : u ≤ X.card) (hv : v ≤ X.card - u) (hSne : S.Nonempty)
    (hstep : ∀ U ∈ cardSubsets X u, Eext S X U v ≤ c0 * Efix S U) :
    Echi S X (u + v) ≤ c0 * Echi S X u := by
  have hCpos : 0 < (cardSubsets X u).card := by
    rw [card_cardSubsets]
    exact Nat.choose_pos hU
  calc
    Echi S X (u + v)
        = (∑ U ∈ cardSubsets X u, Eext S X U v) / (cardSubsets X u).card := by
            exact Echi_eq_avg_Eext (hU := hU) (hv := hv) (hSne := hSne)
    _ ≤ (∑ U ∈ cardSubsets X u, c0 * Efix S U) / (cardSubsets X u).card := by
            exact div_le_div_of_nonneg_right
              (Finset.sum_le_sum (fun U hU' => hstep U hU'))
              (by exact_mod_cast (le_of_lt hCpos))
    _ = c0 * ((∑ U ∈ cardSubsets X u, Efix S U) / (cardSubsets X u).card) := by
            rw [← mul_div_assoc]
            congr 1
            rw [Finset.mul_sum]
    _ = c0 * Echi S X u := by
            rw [← Echi_eq_avg_Efix (S := S) (X := X) (u := u) hSne]

/-- antitone: bigger random sets give smaller expected `|χ|`. -/
lemma Echi_antitone {S : Finset (Finset α)} {X : Finset α} {w u : ℕ}
    (hu : u ≤ w) (hw : w ≤ X.card) :
    Echi S X w ≤ Echi S X u := by
  by_cases hSne : S.Nonempty
  · have hU : u ≤ X.card := le_trans hu hw
    have hv : w - u ≤ X.card - u := Nat.sub_le_sub_right hw u
    have hstep : ∀ U ∈ cardSubsets X u, Eext S X U (w - u) ≤ 1 * Efix S U := by
      intro U hUmem
      have hUsub : U ⊆ X := (Finset.mem_powersetCard.mp hUmem).1
      have hUc : U.card = u := (Finset.mem_powersetCard.mp hUmem).2
      have hcarddiff : (X \ U).card = X.card - u := by
        rw [Finset.card_sdiff_of_subset hUsub, hUc]
      have hvU : w - u ≤ (X \ U).card := by
        rw [hcarddiff]
        exact hv
      simpa using Eext_le_Efix (S := S) (X := X) (U := U) (v := w - u) hSne hvU
    have hineq : Echi S X (u + (w - u)) ≤ 1 * Echi S X u := by
      exact Echi_step_of_fixed (S := S) (X := X) (u := u) (v := w - u) (c0 := 1)
        hU hv hSne hstep
    simpa [Nat.add_sub_of_le hu] using hineq
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    simp [hS, Echi]

end Submission.Sun
