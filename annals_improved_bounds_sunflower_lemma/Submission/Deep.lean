import Mathlib
import Submission.SunBasic
import Submission.Chi

/-!
# The deep petal estimate (Rao's coding lemma, exact-size form)

`rao_petal` is the engine behind the sunflower bound: an `r`-spread family of
`k`-sets contains a member inside a uniformly random subset of density ≥ γ,
with failure ≤ ε, provided `r ≥ Bpetal / γ · log(2k/ε)`.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-! ## Constants -/
noncomputable def rho : ℝ := 2 ^ 16
noncomputable def kap : ℝ := 2 ^ 40
noncomputable def c0 : ℝ := (5 : ℝ) / 6
noncomputable def Bpetal : ℝ := 2 ^ 60

/-- subsets of `X` of cardinality `w` -/
def cardSubsets (X : Finset α) (w : ℕ) : Finset (Finset α) := X.powersetCard w

lemma card_cardSubsets (X : Finset α) (w : ℕ) : (cardSubsets X w).card = X.card.choose w := by
  simp [cardSubsets]

/-- average of `|χ(A,W)|` over `A ∈ S` and `W` a `w`-subset of `X` (a real) -/
noncomputable def Echi (S : Finset (Finset α)) (X : Finset α) (w : ℕ) : ℝ :=
  (∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) /
    ((S.card : ℝ) * (cardSubsets X w).card)

/-- average over `A ∈ S` of `|χ(A,U)|` for a fixed `U` -/
noncomputable def Efix (S : Finset (Finset α)) (U : Finset α) : ℝ :=
  (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ)

/-- average over `V` (v-subsets of `X\U`) and `A ∈ S` of `|χ(A,U∪V)|` -/
noncomputable def Eext (S : Finset (Finset α)) (X U : Finset α) (v : ℕ) : ℝ :=
  (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) /
    ((cardSubsets (X \ U) v).card * (S.card : ℝ))

/-- count-form spreadness -/
def Spread (X : Finset α) (S : Finset (Finset α)) (k : ℕ) (r : ℝ) : Prop :=
  (∀ A ∈ S, A ⊆ X) ∧
  ∀ T : Finset α, T ⊆ X → T.Nonempty →
    (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card)

/-- `E_0 ≤ k` -/
lemma Echi_zero_le {S : Finset (Finset α)} {X : Finset α} {k : ℕ}
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k) : Echi S X 0 ≤ k := by
  unfold Echi
  have hsubsets : cardSubsets X 0 = {∅} := by
    ext W
    constructor
    · intro hW
      have hW' := (Finset.mem_powersetCard.mp hW)
      have hW0 : W = ∅ := Finset.card_eq_zero.mp hW'.2
      simp [hW0]
    · intro hW
      have hW0 : W = ∅ := by simpa using hW
      simp [cardSubsets, hW0]
  rw [hsubsets]
  simp
  by_cases hSempty : S = ∅
  · simp [hSempty]
  · have hSposN : 0 < S.card := by
      exact Nat.pos_of_ne_zero (by simpa using hSempty)
    have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSposN
    have hle : (∑ A ∈ S, ((chi S ∅ A).card : ℝ)) ≤ (∑ A ∈ S, (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro A hA
      have hk : (chi S ∅ A).card ≤ k := by
        apply chi_card_le_k (S := S) (U := ∅) (A := A) hA
        intro A' hA'
        rw [Finset.sdiff_empty, huni A' hA']
      exact_mod_cast hk
    calc
      (∑ A ∈ S, ((chi S ∅ A).card : ℝ)) / (S.card : ℝ) ≤
          (∑ A ∈ S, (k : ℝ)) / (S.card : ℝ) := by
            exact div_le_div_of_nonneg_right hle (by positivity)
      _ = k := by
        simp [Finset.sum_const, nsmul_eq_mul]
        field_simp [ne_of_gt hSpos]
lemma chi_ne_empty_of_no_member {S : Finset (Finset α)} {W : Finset α}
    (hbad : ¬ ∃ A ∈ S, A ⊆ W) {A : Finset α} (hA : A ∈ S) :
    chi S W A ≠ ∅ := by
  intro h
  exact hbad ((chi_eq_empty_iff (S:=S) (U:=W) (A:=A) hA).1 h)

lemma card_pos_of_ne_empty {α} [DecidableEq α] {s : Finset α} (h : s ≠ ∅) : 0 < s.card :=
  Finset.card_pos.mpr ⟨Classical.choose (Finset.nonempty_iff_ne_empty.mpr h), Classical.choose_spec (Finset.nonempty_iff_ne_empty.mpr h)⟩

lemma Echi_lower_contains {S : Finset (Finset α)} {X : Finset α} (w : ℕ)
    (hSne : S.Nonempty) (hw : w ≤ X.card) :
    ((cardSubsets X w).filter (fun W : Finset α => ¬ ∃ A ∈ S, A ⊆ W)).card ≤
      (cardSubsets X w).card * Echi S X w := by
  unfold Echi
  let bad : Finset (Finset α) := (cardSubsets X w).filter (fun W : Finset α => ¬ ∃ A ∈ S, A ⊆ W)
  have hWposN : 0 < (cardSubsets X w).card := by
    rw [card_cardSubsets]; exact Nat.choose_pos hw
  have hSposN : 0 < S.card := Finset.card_pos.mpr hSne
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSposN
  have hWpos : 0 < ((cardSubsets X w).card : ℝ) := by exact_mod_cast hWposN
  -- each bad W: Σ_A |chi| ≥ |S|
  have hbadW : ∀ W ∈ bad, (S.card : ℝ) ≤ (∑ A ∈ S, ((chi S W A).card : ℝ)) := by
    intro W hW
    have hbad : ¬ ∃ A ∈ S, A ⊆ W := (Finset.mem_filter.mp hW).2
    calc
      (S.card : ℝ) = (∑ A ∈ S, (1 : ℝ)) := by simp
      _ ≤ (∑ A ∈ S, ((chi S W A).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro A hA
        have hne : chi S W A ≠ ∅ := chi_ne_empty_of_no_member (S:=S) (W:=W) hbad hA
        have hc : 1 ≤ (chi S W A).card := by
          have : (chi S W A).card ≠ 0 := by
            intro h0; exact hne (Finset.card_eq_zero.mp h0)
          omega
        exact_mod_cast hc
  have hsum1 : (bad.card : ℝ) * (S.card : ℝ) ≤ (∑ W ∈ bad, ∑ A ∈ S, ((chi S W A).card : ℝ)) := by
    calc
      (bad.card : ℝ) * (S.card : ℝ) = (∑ W ∈ bad, (S.card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (∑ W ∈ bad, ∑ A ∈ S, ((chi S W A).card : ℝ)) := by
        apply Finset.sum_le_sum; intro W hW; exact hbadW W hW
  have hsum2 : (∑ W ∈ bad, ∑ A ∈ S, ((chi S W A).card : ℝ)) ≤ (∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) := by
    have hsw : (∑ W ∈ bad, ∑ A ∈ S, ((chi S W A).card : ℝ)) = (∑ A ∈ S, ∑ W ∈ bad, ((chi S W A).card : ℝ)) := by
      rw [Finset.sum_comm]
    rw [hsw]
    apply Finset.sum_le_sum
    intro A hA
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun W : Finset α => ¬ ∃ A ∈ S, A ⊆ W) (cardSubsets X w))
      (by intro W hW1 hW2; positivity)
  -- combine
  have htotal : (bad.card : ℝ) * (S.card : ℝ) ≤ (∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) :=
    le_trans hsum1 hsum2
  -- now divide
  -- goal: bad.card ≤ #W * (Σ/(#S * #W))  i.e. bad.card·(#S·#W) ≤ #W·Σ?  Use htotal.
  have hmain : (bad.card : ℝ) ≤ (∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) / (S.card : ℝ) := by
    rw [le_div_iff₀ hSpos]
    exact htotal
  calc
    (bad.card : ℝ) ≤ (∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) / (S.card : ℝ) := hmain
    _ = (cardSubsets X w).card * ((∑ A ∈ S, ∑ W ∈ cardSubsets X w, ((chi S W A).card : ℝ)) /
          ((S.card : ℝ) * (cardSubsets X w).card)) := by
      have hs : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
      have hc : ((cardSubsets X w).card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hWposN)
      have hEq2 : ∀ (a b c : ℝ), b ≠ 0 → c ≠ 0 → a / b = c * (a / (b * c)) := by
        intro a b c hb hc
        field_simp [hb, hc]
      exact hEq2 _ _ _ hs hc

end Submission.Sun
