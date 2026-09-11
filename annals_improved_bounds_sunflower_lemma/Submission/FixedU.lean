import Mathlib
import Submission.Deep
import Submission.DeepCore
import Submission.LevelFinal
import Submission.FixedUDefs
import Submission.Case1Count
import Submission.Case2Count
import Submission.Case1Numeric
import Submission.Case2Numeric
import Submission.RaoDev

/-!
# The fixed-U step (Rao's coding lemma, exact-size form)

This file proves `fixed_U_step`, moved here from `Deep.lean` so that this
(long) proof can be developed separately from the definitions in `Deep.lean`.

## Mathematical content

Fix the k-uniform r-spread family `S` over `X` with |S| ≥ r^k.  Fix `U ⊆ X`,
and consider adding a random `v`-subset `V` of `X \ U`.  Rao's lemma says the
average remainder `|χ(·,·)|` shrinks by a constant factor < 1.

Concretely we prove (in the nontrivial case where no member lies in `U`)

  Σ_{V,A} t(A,V) ≤ (5/6)·C(N,v)·Σ_A s(A)

where `s(A) = |χ(A,U)| ≥ 1`, `t(A,V) = |χ(A,U∪V)|`, `N = |X\U|`, by the
"virtual Kraft" method: for suitable real constants a,b with a/b ≤ 5/6 we show

  Σ_{V,A} exp(b·t(A,V) − a·s(A)) ≤ C(N,v)·|S|   (up to tiny slack)

which implies the desired bound by Jensen's inequality (`exp` is convex).

The crucial estimate splits the pairs (V,A) with t ≥ 1 into two cases:
  - case 1:  for the canonical t-subset A* of χ(A,U),  |τ(A*,V∪χ(A,U),s)| ≤ φ,
    where φ := r^k·(ρv/n)^s·(vr/n)^(-t).  Then (V,A) is encoded by the data
    (B0 = V∪χ(A,U), A*, A, Q = V∩χ(A,U)) and the count telescopes:
    # pairs ≤ (#B0)·2^s·φ·2^s.
  - case 2:  |τ(A*,B0,s)| > φ.  Then for fixed A and A* the number of such V is
    ≤ C(N,v)·ρ^(-s)·3^(s-t) (a Markov bound on E|τ|, using spreadness).
Pairs with t = 0 (V covers a member) are negligible.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]


/-- If U contains a member of S then every χ(A,U) is empty: Efix = 0. -/
lemma fix_zero_of_member {S : Finset (Finset α)} {U : Finset α} (hU : ∃ A' ∈ S, A' ⊆ U) :
    Efix S U = 0 := by
  unfold Efix
  have hsum : (∑ A ∈ S, ((chi S U A).card : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    have he : chi S U A = ∅ := (chi_eq_empty_iff (S:=S) (U:=U) (A:=A) hA).2 hU
    simp [he]
  rw [hsum]
  simp

/-- If U contains a member of S then every χ(A,U∪V) is empty: Eext = 0. -/
lemma ext_zero_of_member {S : Finset (Finset α)} {X U : Finset α} {v : ℕ}
    (hU : ∃ A' ∈ S, A' ⊆ U) : Eext S X U v = 0 := by
  unfold Eext
  have h0 : (∑ V ∈ cardSubsets (X \ U) v, ∑ A ∈ S, ((chi S (U ∪ V) A).card : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    apply Finset.sum_eq_zero
    intro A hA
    have he : chi S (U ∪ V) A = ∅ := (chi_eq_empty_iff (S:=S) (U:=U ∪ V) (A:=A) hA).2
      ⟨Classical.choose hU, (Classical.choose_spec hU).1,
        subset_trans (Classical.choose_spec hU).2 (Finset.subset_union_left)⟩
    simp [he]
  rw [h0]
  simp

/-- s(A) ≥ 1 when no member of S lies inside U. -/
lemma chi_card_pos_of_no_member {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S)
    (hU : ¬ ∃ A' ∈ S, A' ⊆ U) : 0 < (chi S U A).card := by
  by_contra hnot
  have h0 : (chi S U A).card = 0 := by omega
  exact hU ((chi_card_zero_iff (S:=S) (U:=U) (A:=A) hA).1 h0)

/-- Efix ≥ 1 when S nonempty and no member lies in U. -/
lemma Efix_ge_one {S : Finset (Finset α)} {U : Finset α} (hSne : S.Nonempty)
    (hU : ¬ ∃ A' ∈ S, A' ⊆ U) : (1 : ℝ) ≤ Efix S U := by
  unfold Efix
  have hpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hsum : (S.card : ℝ) ≤ ∑ A ∈ S, ((chi S U A).card : ℝ) := by
    calc
      (S.card : ℝ) = ∑ A ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ A ∈ S, ((chi S U A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro A hA
        have hc : 1 ≤ (chi S U A).card := chi_card_pos_of_no_member (S:=S) (U:=U) (A:=A) hA hU
        exact_mod_cast hc
  calc
    (1 : ℝ) ≤ (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hpos : 0 < (S.card : ℝ))]
      simpa using hsum
    _ = (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ) := rfl

lemma log_two_ge_69 : (69 : ℝ) / 100 ≤ Real.log 2 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

lemma log_kap_ge_27 : (27 : ℝ) ≤ Real.log (kap : ℝ) := by
  unfold kap
  have h2 := log_two_ge_69
  calc (27 : ℝ) ≤ (40 : ℝ) * (69 / 100 : ℝ) := by norm_num
    _ ≤ (40 : ℝ) * Real.log 2 := by nlinarith [h2]
    _ = Real.log ((2 : ℝ) ^ 40) := (Real.log_pow (2 : ℝ) 40).symm

lemma log_vr_ge_27 {X : Finset α} {v : ℕ} {r : ℝ} (hr1 : 1 ≤ r)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ)) (hXpos : 0 < X.card) :
    (27 : ℝ) ≤ Real.log ((r * (v : ℝ)) / (X.card : ℝ)) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hn0 : 0 < (X.card : ℝ) := by exact_mod_cast hXpos
  have hrv : (kap : ℝ) ≤ (r * (v : ℝ)) / (X.card : ℝ) := by
    have h1 : (kap : ℝ) * (X.card : ℝ) ≤ r * (v : ℝ) := by
      have h1' : (kap * (X.card : ℝ)) / r ≤ (v : ℝ) := by simpa [kap] using hkap
      rw [div_le_iff₀ hr0] at h1'
      nlinarith
    rw [le_div_iff₀ hn0]
    nlinarith
  have hkap0 : 0 < (kap : ℝ) := by unfold kap; positivity
  have hlog := Real.log_le_log hkap0 hrv
  exact le_trans log_kap_ge_27 hlog

/-- natural-log constants for the encoding weight `exp(b·t − a·s)` -/
noncomputable def encA : ℝ := 20
noncomputable def encB : ℝ := 26

theorem fixed_U_step {X : Finset α} {S : Finset (Finset α)} {k : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k) (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    {U : Finset α} {v : ℕ} (hU : U ⊆ X)
    (h8u : 8 * U.card ≤ X.card) (hv : 0 < v)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ))
    (huv2 : U.card + 2 * v ≤ X.card) (huv : U.card + v ≤ X.card)
    (hrbig : 2 ^ 6 ≤ (r * (v : ℝ)) / (X.card : ℝ)) :
    Eext S X U v ≤ c0 * Efix S U := by
  classical
  by_cases hmem : ∃ A' ∈ S, A' ⊆ U
  · have hf : Efix S U = 0 := fix_zero_of_member hmem
    have he : Eext S X U v = 0 := ext_zero_of_member (X := X) (v := v) hmem
    rw [he, hf]
    norm_num
  · have hnm : ¬ ∃ A' ∈ S, A' ⊆ U := hmem
    have hc2sum : (∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card)
        ≤ 2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
      exact case2Sum_le (X := X) (S := S) (U := U) (v := v) (k := k) (r := r)
        huni hU hS h8u hspread hr1 hv (X_card_pos hk hn6) (N_bound_v hU huv) huv hkap
    exact rao_aux (X := X) (S := S) (k := k) (r := r) hk hn6 hS huni hspread hSr hr1 hrn
      (U := U) (v := v) hU h8u hv hkap huv2 huv hrbig hnm hc2sum

end Submission.Sun
