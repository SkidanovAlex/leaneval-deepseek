import Mathlib
import Submission.FixedUDefs
import Submission.Deep
import Submission.DeepCore
import Submission.LevelFinal
import Submission.Case1Numeric
import Submission.Case1Count
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-!
# Development module: the fixed-U step assembly

Mirrors the content that will finally live in `Submission/FixedU.lean`
(above the theorem).  Everything is developed here in isolation and merged
later, so that `FixedU.lean` (imported by `Deep2.lean` etc.) stays intact.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-! ## pairSet membership & the weight function -/

lemma mem_pairSet {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v : ℕ} :
    (V, A) ∈ pairSet X S U v ↔ V ∈ cardSubsets (X \ U) v ∧ A ∈ S := by
  simp [pairSet]

/-- sum over all pairs -/
noncomputable def wbSum (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) : ℝ :=
  ∑ p ∈ pairSet X S U v, wgt S U p.2 p.1

lemma pairSet_card {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v : ℕ} :
    (pairSet X S U v).card = (cardSubsets (X \ U) v).card * S.card := by
  simp [pairSet, Finset.card_product]

/-! A pair's s-value is at most k and at least 1 (in the no-member-in-U case),
and its t-value lies between 1 and s (when t ≥ 1). -/

lemma sVal_le_k {S : Finset (Finset α)} {U A : Finset α} {k : ℕ} (hA : A ∈ S)
    (huni : ∀ A ∈ S, A.card = k) : sVal S U A ≤ k :=
  chi_card_le_k'' (S := S) (U := U) (A := A) hA huni

lemma tVal_le_sVal {S : Finset (Finset α)} {X U V A : Finset α} {v : ℕ} (hA : A ∈ S)
    (hV : V ∈ cardSubsets (X \ U) v) : tVal S U V A ≤ sVal S U A := by
  exact chi_ext_le_fix (S := S) (X := X) (U := U) (V := V) (A := A) (v := v) hA hV

lemma one_le_sVal {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S)
    (hnm : ¬ ∃ A' ∈ S, A' ⊆ U) : 1 ≤ sVal S U A := by
  unfold sVal
  exact s_pos (S := S) (U := U) (A := A) hA hnm

/-- case-1 set (all case-1 pairs, any fiber) -/
noncomputable def case1Set (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) (r : ℝ) (k : ℕ) :
    Finset (Finset α × Finset α) := by
  classical
  exact (pairSet X S U v).filter (fun (V,A) => case1p S X U V A r k v)

/-- case-2 set -/
noncomputable def case2Set (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) (r : ℝ) (k : ℕ) :
    Finset (Finset α × Finset α) := by
  classical
  exact (pairSet X S U v).filter (fun (V,A) => case2p S X U V A r k v)



/-! ## Semantics of case1p / case2p -/

lemma case1p_pos {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ}
    (h : case1p S X U V A r k v) : 0 < tVal S U V A := h.1

/-- case1p = (0 < t ∧ for the fiber (sVal,tVal) the all-C bound holds) -/
lemma case1p_iff {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ} :
    case1p S X U V A r k v ↔
      (0 < tVal S U V A ∧
       ∀ C : Finset α, C ⊆ chi S U A → C.card = tVal S U V A →
         (((tau S U C (V ∪ chi S U A) (sVal S U A)).card : ℝ) ≤
           phiVal r k X v (sVal S U A) (tVal S U V A))) := by
  rfl

/-- for pairs with t ≥ 1, ¬ case1p implies case2p -/
lemma case2p_of_not_case1p {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ}
    (hpos : 0 < tVal S U V A) (h : ¬ case1p S X U V A r k v) :
    case2p S X U V A r k v := by
  rw [case1p_iff] at h
  have hbad : ¬ ∀ C : Finset α, C ⊆ chi S U A → C.card = tVal S U V A →
      (((tau S U C (V ∪ chi S U A) (sVal S U A)).card : ℝ) ≤
        phiVal r k X v (sVal S U A) (tVal S U V A)) := by
    intro hb
    exact h ⟨hpos, hb⟩
  -- classical: negate the ∀ to get the ∃
  by_contra h2
  apply hbad
  intro C hC1 hC2
  -- assume not (bound), use h2
  by_contra hle
  apply h2
  exact ⟨C, hC1, hC2, by linarith⟩

/-- pairs with tVal ≥ 1 split into case1 and case2 -/
lemma case1_or_case2 {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ}
    (hpos : 0 < tVal S U V A) : case1p S X U V A r k v ∨ case2p S X U V A r k v := by
  by_cases hc : case1p S X U V A r k v
  · exact Or.inl hc
  · exact Or.inr (case2p_of_not_case1p (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (r:=r) (k:=k) (v:=v) hpos hc)

/-- case1p and case2p are mutually exclusive -/
lemma case1p_not_case2p {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ}
    (h1 : case1p S X U V A r k v) : ¬ case2p S X U V A r k v := by
  intro h2
  rcases h2 with ⟨C, hCsub, hCcard, hgt⟩
  exact (not_lt_of_ge (h1.2 C hCsub hCcard)) hgt



/-! ## fibre decomposition of the weighted sum -/

/-- weighted case1 contribution of a pair (0 unless case1) -/
noncomputable def c1w (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v : ℕ) : ℝ := by
  classical
  exact if case1p S X U V A r k v then wgt S U V A else 0

/-- weighted case2 contribution of a pair with 0 < t -/
noncomputable def c2w (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v : ℕ) : ℝ := by
  classical
  exact if (case2p S X U V A r k v ∧ 0 < tVal S U V A) then wgt S U V A else 0

/-- indicator that a pair lies in the case1 (s,t)-fibre -/
noncomputable def f1ind (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v s t : ℕ) : ℝ := by
  classical
  exact if sVal S U A = s ∧ tVal S U V A = t ∧ case1p S X U V A r k v then 1 else 0

/-- membership in case1Fiber, re-expressed -/
lemma mem_case1Fiber_iff {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α}
    {v k s t : ℕ} {r : ℝ} :
    (V,A) ∈ case1Fiber X S U v r k s t ↔
      V ∈ cardSubsets (X \ U) v ∧ A ∈ S ∧ sVal S U A = s ∧ tVal S U V A = t ∧
        case1p S X U V A r k v := by
  classical
  simp [case1Fiber, pairSet]
  tauto

/-- a case1 pair has its fibre-index (sVal,tVal) inside idxSet k -/
lemma case1_fiber_idx {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v k : ℕ} {r : ℝ}
    (hV : V ∈ cardSubsets (X \ U) v) (hA : A ∈ S)
    (hc1 : case1p S X U V A r k v)
    (hS : ∀ A ∈ S, A ⊆ X) (hU : U ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) :
    (sVal S U A, tVal S U V A) ∈ idxSet k := by
  have ht1 : 1 ≤ tVal S U V A := case1p_pos (S:=S) hc1
  have hts : tVal S U V A ≤ sVal S U A := tVal_le_sVal (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (v:=v) hA hV
  have hs1 : 1 ≤ sVal S U A := one_le_sVal (S:=S) (U:=U) (A:=A) hA hnm
  have hsk : sVal S U A ≤ k := sVal_le_k (S:=S) (U:=U) (A:=A) hA huni
  change (sVal S U A, tVal S U V A) ∈
    (((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s))
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hs1, hsk⟩
    · rw [Finset.mem_Icc]
      exact ⟨ht1, le_trans hts hsk⟩
  · simpa using hts

/-- a pair satisfying case2p with 0 < t has its fibre index in idxSet -/
lemma case2_fiber_idx {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v k : ℕ} {r : ℝ}
    (hV : V ∈ cardSubsets (X \ U) v) (hA : A ∈ S)
    (hc2 : case2p S X U V A r k v) (htpos : 0 < tVal S U V A)
    (hS : ∀ A ∈ S, A ⊆ X) (hU : U ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) :
    (sVal S U A, tVal S U V A) ∈ idxSet k := by
  have hts : tVal S U V A ≤ sVal S U A := tVal_le_sVal (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (v:=v) hA hV
  have hs1 : 1 ≤ sVal S U A := one_le_sVal (S:=S) (U:=U) (A:=A) hA hnm
  have hsk : sVal S U A ≤ k := sVal_le_k (S:=S) (U:=U) (A:=A) hA huni
  change (sVal S U A, tVal S U V A) ∈
    (((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s))
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hs1, hsk⟩
    · rw [Finset.mem_Icc]
      exact ⟨htpos, le_trans hts hsk⟩
  · simpa using hts

/-- the case1-fibre cardinality equals the sum of fibre indicators over all pairs -/
lemma case1Fiber_card_eq {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k s t : ℕ} {r : ℝ} :
    ((case1Fiber X S U v r k s t).card : ℝ) =
      (cardSubsets (X \ U) v).sum (fun V =>
        S.sum (fun A => f1ind S X U V A r k v s t)) := by
  classical
  calc
    ((case1Fiber X S U v r k s t).card : ℝ)
        = (case1Fiber X S U v r k s t).sum (fun _ : Finset α × Finset α => (1 : ℝ)) := by simp
    _ = (pairSet X S U v).sum (fun p =>
            f1ind S X U p.1 p.2 r k v s t) := by
        rw [case1Fiber]
        simp [f1ind, Finset.sum_filter]
    _ = (cardSubsets (X \ U) v).sum (fun V =>
          S.sum (fun A => f1ind S X U V A r k v s t)) := by
        simp [pairSet, Finset.sum_product]

/-- every element of the case1 (s,t)-fibre is a case1 pair -/
lemma mem_case1Fiber_case1p {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α}
    {v k s t : ℕ} {r : ℝ} (hp : (V,A) ∈ case1Fiber X S U v r k s t) :
    case1p S X U V A r k v := by
  have h := (mem_case1Fiber_iff (X:=X) (S:=S) (U:=U) (V:=V) (A:=A) (v:=v) (k:=k) (s:=s) (t:=t) (r:=r)).1 hp
  exact h.2.2.2.2

/-- the case1 weighted double sum equals the fibre sum -/
lemma case1_wb_eq {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ}
    (hS : ∀ A ∈ S, A ⊆ X) (hU : U ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) :
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v)) =
      ∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card := by
  classical
  have hsum1 : ∀ V ∈ cardSubsets (X \ U) v, ∀ A ∈ S,
      c1w S X U V A r k v =
        ∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2 := by
    intro V hV A hA
    by_cases hc : case1p S X U V A r k v
    · have hj : (sVal S U A, tVal S U V A) ∈ idxSet k :=
        case1_fiber_idx (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (v:=v) (k:=k) (r:=r) hV hA hc hS hU hnm huni
      have hf1 : f1ind S X U V A r k v (sVal S U A) (tVal S U V A) = 1 := by
        rw [f1ind]
        rw [if_pos ⟨rfl, ⟨rfl, hc⟩⟩]
      have hf0 : ∀ b : ℕ × ℕ, b ∈ idxSet k → b ≠ (sVal S U A, tVal S U V A) →
          wfib b * f1ind S X U V A r k v b.1 b.2 = 0 := by
        intro b hb hne
        have hf : f1ind S X U V A r k v b.1 b.2 = 0 := by
          rw [f1ind]
          rw [if_neg (fun h : sVal S U A = b.1 ∧ tVal S U V A = b.2 ∧ case1p S X U V A r k v =>
            hne (by rw [Prod.ext_iff]; exact ⟨h.1.symm, h.2.1.symm⟩))]
        simp [hf]
      have hsingle : (∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2) =
          wfib (sVal S U A, tVal S U V A) * f1ind S X U V A r k v (sVal S U A) (tVal S U V A) := by
        exact Finset.sum_eq_single (s := idxSet k)
          (f := fun j => wfib j * f1ind S X U V A r k v j.1 j.2)
          (sVal S U A, tVal S U V A) hf0 (fun hnot => False.elim (hnot hj))
      calc
        c1w S X U V A r k v = wgt S U V A := by simp [c1w, hc]
        _ = wfib (sVal S U A, tVal S U V A) := wgt_eq_wfib S U V A
        _ = wfib (sVal S U A, tVal S U V A) * f1ind S X U V A r k v (sVal S U A) (tVal S U V A) := by
            rw [hf1]
            ring
        _ = ∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2 := hsingle.symm
    · calc
        c1w S X U V A r k v = 0 := by simp [c1w, hc]
        _ = ∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2 := by
            apply Eq.symm
            apply Finset.sum_eq_zero
            intro j hj
            have hf : f1ind S X U V A r k v j.1 j.2 = 0 := by
              rw [f1ind]
              rw [if_neg (fun h : sVal S U A = j.1 ∧ tVal S U V A = j.2 ∧ case1p S X U V A r k v => hc h.2.2)]
            simp [hf]
  calc
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v))
        = (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
            ∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2)) := by
            apply Finset.sum_congr rfl
            intro V hV
            apply Finset.sum_congr rfl
            intro A hA
            exact hsum1 V hV A hA
    _ = ∑ j ∈ idxSet k, (cardSubsets (X \ U) v).sum (fun V =>
          S.sum (fun A => wfib j * f1ind S X U V A r k v j.1 j.2)) := by
          calc
            (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
                ∑ j ∈ idxSet k, wfib j * f1ind S X U V A r k v j.1 j.2))
                = (cardSubsets (X \ U) v).sum (fun V =>
                    ∑ j ∈ idxSet k, S.sum (fun A => wfib j * f1ind S X U V A r k v j.1 j.2)) := by
                    apply Finset.sum_congr rfl
                    intro V hV
                    exact Finset.sum_comm
            _ = ∑ j ∈ idxSet k, (cardSubsets (X \ U) v).sum (fun V =>
                  S.sum (fun A => wfib j * f1ind S X U V A r k v j.1 j.2)) := by
                  exact Finset.sum_comm
    _ = ∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [case1Fiber_card_eq (X:=X) (S:=S) (U:=U) (v:=v) (k:=k) (s:=j.1) (t:=j.2) (r:=r)]
          have hin : ∀ V, S.sum (fun A => wfib j * f1ind S X U V A r k v j.1 j.2) =
              wfib j * (S.sum (fun A => f1ind S X U V A r k v j.1 j.2)) := by
            intro V
            exact (Finset.mul_sum S (fun A : Finset α => f1ind S X U V A r k v j.1 j.2) (wfib j)).symm
          calc
            (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
                wfib j * f1ind S X U V A r k v j.1 j.2))
                = (cardSubsets (X \ U) v).sum (fun V =>
                    wfib j * S.sum (fun A => f1ind S X U V A r k v j.1 j.2)) := by
                    apply Finset.sum_congr rfl
                    intro V hV
                    exact hin V
            _ = wfib j * ((cardSubsets (X \ U) v).sum (fun V =>
                  S.sum (fun A => f1ind S X U V A r k v j.1 j.2))) := by
                  exact (Finset.mul_sum (cardSubsets (X \ U) v)
                    (fun V => S.sum (fun A => f1ind S X U V A r k v j.1 j.2)) (wfib j)).symm


/-! ## case2 fibre decomposition -/

/-- indicator that a pair lies in the case2 (s,t)-fibre -/
noncomputable def f2ind (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v s t : ℕ) : ℝ := by
  classical
  exact if sVal S U A = s ∧ tVal S U V A = t ∧ case2p S X U V A r k v then 1 else 0

/-- membership in case2Fiber, re-expressed -/
lemma mem_case2Fiber_iff {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α}
    {v k s t : ℕ} {r : ℝ} :
    (V,A) ∈ case2Fiber X S U v r k s t ↔
      V ∈ cardSubsets (X \ U) v ∧ A ∈ S ∧ sVal S U A = s ∧ tVal S U V A = t ∧
        case2p S X U V A r k v := by
  classical
  simp [case2Fiber, pairSet]
  tauto

/-- the case2-fibre cardinality equals the sum of fibre indicators over all pairs -/
lemma case2Fiber_card_eq {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k s t : ℕ} {r : ℝ} :
    ((case2Fiber X S U v r k s t).card : ℝ) =
      (cardSubsets (X \ U) v).sum (fun V =>
        S.sum (fun A => f2ind S X U V A r k v s t)) := by
  classical
  calc
    ((case2Fiber X S U v r k s t).card : ℝ)
        = (case2Fiber X S U v r k s t).sum (fun _ : Finset α × Finset α => (1 : ℝ)) := by simp
    _ = (pairSet X S U v).sum (fun p =>
            f2ind S X U p.1 p.2 r k v s t) := by
        rw [case2Fiber]
        simp [f2ind, Finset.sum_filter]
    _ = (cardSubsets (X \ U) v).sum (fun V =>
          S.sum (fun A => f2ind S X U V A r k v s t)) := by
        simp [pairSet, Finset.sum_product]

/-- the case2 weighted double sum (with 0<t) equals the fibre sum -/
lemma case2_wb_eq {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ}
    (hS : ∀ A ∈ S, A ⊆ X) (hU : U ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) :
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v)) =
      ∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card := by
  classical
  have hsum1 : ∀ V ∈ cardSubsets (X \ U) v, ∀ A ∈ S,
      c2w S X U V A r k v =
        ∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2 := by
    intro V hV A hA
    by_cases hc : case2p S X U V A r k v ∧ 0 < tVal S U V A
    · have hc2 : case2p S X U V A r k v := hc.1
      have htpos : 0 < tVal S U V A := hc.2
      have hj : (sVal S U A, tVal S U V A) ∈ idxSet k :=
        case2_fiber_idx (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (v:=v) (k:=k) (r:=r) hV hA hc2 htpos hS hU hnm huni
      have hf1 : f2ind S X U V A r k v (sVal S U A) (tVal S U V A) = 1 := by
        rw [f2ind]
        rw [if_pos ⟨rfl, ⟨rfl, hc2⟩⟩]
      have hf0 : ∀ b : ℕ × ℕ, b ∈ idxSet k → b ≠ (sVal S U A, tVal S U V A) →
          wfib b * f2ind S X U V A r k v b.1 b.2 = 0 := by
        intro b hb hne
        have hf : f2ind S X U V A r k v b.1 b.2 = 0 := by
          rw [f2ind]
          rw [if_neg (fun h : sVal S U A = b.1 ∧ tVal S U V A = b.2 ∧ case2p S X U V A r k v =>
            hne (by rw [Prod.ext_iff]; exact ⟨h.1.symm, h.2.1.symm⟩))]
        simp [hf]
      have hsingle : (∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2) =
          wfib (sVal S U A, tVal S U V A) * f2ind S X U V A r k v (sVal S U A) (tVal S U V A) := by
        exact Finset.sum_eq_single (s := idxSet k)
          (f := fun j => wfib j * f2ind S X U V A r k v j.1 j.2)
          (sVal S U A, tVal S U V A) hf0 (fun hnot => False.elim (hnot hj))
      calc
        c2w S X U V A r k v = wgt S U V A := by simp [c2w, hc]
        _ = wfib (sVal S U A, tVal S U V A) := wgt_eq_wfib S U V A
        _ = wfib (sVal S U A, tVal S U V A) * f2ind S X U V A r k v (sVal S U A) (tVal S U V A) := by
            rw [hf1]
            ring
        _ = ∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2 := hsingle.symm
    · calc
        c2w S X U V A r k v = 0 := by simp [c2w, hc]
        _ = ∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2 := by
            apply Eq.symm
            apply Finset.sum_eq_zero
            intro j hj
            have hf : f2ind S X U V A r k v j.1 j.2 = 0 := by
              rw [f2ind]
              rw [if_neg (fun h : sVal S U A = j.1 ∧ tVal S U V A = j.2 ∧ case2p S X U V A r k v =>
                hc ⟨h.2.2, by
                  rw [h.2.1]
                  have hj2 : 1 ≤ j.2 := (mem_idxSet_iff.mp hj).2.2.1
                  omega⟩)]
            simp [hf]
  calc
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v))
        = (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
            ∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2)) := by
            apply Finset.sum_congr rfl
            intro V hV
            apply Finset.sum_congr rfl
            intro A hA
            exact hsum1 V hV A hA
    _ = ∑ j ∈ idxSet k, (cardSubsets (X \ U) v).sum (fun V =>
          S.sum (fun A => wfib j * f2ind S X U V A r k v j.1 j.2)) := by
          calc
            (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
                ∑ j ∈ idxSet k, wfib j * f2ind S X U V A r k v j.1 j.2))
                = (cardSubsets (X \ U) v).sum (fun V =>
                    ∑ j ∈ idxSet k, S.sum (fun A => wfib j * f2ind S X U V A r k v j.1 j.2)) := by
                    apply Finset.sum_congr rfl
                    intro V hV
                    exact Finset.sum_comm
            _ = ∑ j ∈ idxSet k, (cardSubsets (X \ U) v).sum (fun V =>
                  S.sum (fun A => wfib j * f2ind S X U V A r k v j.1 j.2)) := by
                  exact Finset.sum_comm
    _ = ∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [case2Fiber_card_eq (X:=X) (S:=S) (U:=U) (v:=v) (k:=k) (s:=j.1) (t:=j.2) (r:=r)]
          have hin : ∀ V, S.sum (fun A => wfib j * f2ind S X U V A r k v j.1 j.2) =
              wfib j * (S.sum (fun A => f2ind S X U V A r k v j.1 j.2)) := by
            intro V
            exact (Finset.mul_sum S (fun A : Finset α => f2ind S X U V A r k v j.1 j.2) (wfib j)).symm
          calc
            (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A =>
                wfib j * f2ind S X U V A r k v j.1 j.2))
                = (cardSubsets (X \ U) v).sum (fun V =>
                    wfib j * S.sum (fun A => f2ind S X U V A r k v j.1 j.2)) := by
                    apply Finset.sum_congr rfl
                    intro V hV
                    exact hin V
            _ = wfib j * ((cardSubsets (X \ U) v).sum (fun V =>
                  S.sum (fun A => f2ind S X U V A r k v j.1 j.2))) := by
                  exact (Finset.mul_sum (cardSubsets (X \ U) v)
                    (fun V => S.sum (fun A => f2ind S X U V A r k v j.1 j.2)) (wfib j)).symm




/-! ## splitting the weighted sum into the three cases -/

/-- zero-t contribution of a pair -/
noncomputable def z0w (S : Finset (Finset α)) (U V A : Finset α) : ℝ := by
  classical
  exact if tVal S U V A = 0 then wgt S U V A else 0

/-- wgt = z0 + case1 + case2 for every pair -/
lemma wgt_eq_split {S : Finset (Finset α)} {X U V A : Finset α} {r : ℝ} {k v : ℕ} :
    wgt S U V A = z0w S U V A + c1w S X U V A r k v + c2w S X U V A r k v := by
  classical
  by_cases hz : tVal S U V A = 0
  · have hc1 : ¬ case1p S X U V A r k v := by
      intro h
      exact (not_lt_of_ge (le_of_eq hz)) (case1p_pos (S:=S) h)
    have hc2 : ¬ (case2p S X U V A r k v ∧ 0 < tVal S U V A) := by
      intro h
      rw [hz] at h
      omega
    have h1 : z0w S U V A = wgt S U V A := by rw [z0w, if_pos hz]
    have h2 : c1w S X U V A r k v = 0 := by rw [c1w, if_neg hc1]
    have h3 : c2w S X U V A r k v = 0 := by rw [c2w, if_neg hc2]
    rw [h1, h2, h3]
    ring
  · have hz' : tVal S U V A ≠ 0 := hz
    have hpos : 0 < tVal S U V A := Nat.pos_of_ne_zero hz'
    by_cases hc : case1p S X U V A r k v
    · have hc2 : ¬ (case2p S X U V A r k v ∧ 0 < tVal S U V A) := by
        intro h2
        exact case1p_not_case2p (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (r:=r) (k:=k) (v:=v) hc h2.1
      have h1 : z0w S U V A = 0 := by rw [z0w, if_neg hz']
      have h2 : c1w S X U V A r k v = wgt S U V A := by rw [c1w, if_pos hc]
      have h3 : c2w S X U V A r k v = 0 := by rw [c2w, if_neg hc2]
      rw [h1, h2, h3]
      ring
    · have hc2 : case2p S X U V A r k v := case2p_of_not_case1p (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (r:=r) (k:=k) (v:=v) hpos hc
      have h1 : z0w S U V A = 0 := by rw [z0w, if_neg hz']
      have h2 : c1w S X U V A r k v = 0 := by rw [c1w, if_neg hc]
      have h3 : c2w S X U V A r k v = wgt S U V A := by rw [c2w, if_pos ⟨hc2, hpos⟩]
      rw [h1, h2, h3]
      ring

/-- wbSum splits as the sum of the three contributions -/
lemma wbSum_split {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ} :
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => wgt S U V A)) =
      (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A)) +
      (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v)) +
      (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v)) := by
  classical
  have hin : ∀ V ∈ cardSubsets (X \ U) v,
      S.sum (fun A => wgt S U V A) = S.sum (fun A => z0w S U V A) +
        S.sum (fun A => c1w S X U V A r k v) + S.sum (fun A => c2w S X U V A r k v) := by
    intro V hV
    calc
      S.sum (fun A => wgt S U V A)
          = S.sum (fun A => z0w S U V A + c1w S X U V A r k v + c2w S X U V A r k v) := by
            apply Finset.sum_congr rfl
            intro A hA
            exact wgt_eq_split (S:=S) (X:=X) (U:=U) (V:=V) (A:=A) (r:=r) (k:=k) (v:=v)
      _ = S.sum (fun A => z0w S U V A) + S.sum (fun A => c1w S X U V A r k v) +
          S.sum (fun A => c2w S X U V A r k v) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => wgt S U V A))
        = (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A) +
            S.sum (fun A => c1w S X U V A r k v) + S.sum (fun A => c2w S X U V A r k v)) := by
            apply Finset.sum_congr rfl
            intro V hV
            exact hin V hV
    _ = (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A)) +
        (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v)) +
        (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- per-pair: zero-t contribution is ≤ exp(-20) -/
lemma z0w_le {S : Finset (Finset α)} {U V A : Finset α} (hA : A ∈ S)
    (hnm : ¬ ∃ A' ∈ S, A' ⊆ U) : z0w S U V A ≤ Real.exp (-20) := by
  classical
  by_cases hz : tVal S U V A = 0
  · have hs1 : 1 ≤ sVal S U A := one_le_sVal (S:=S) (U:=U) (A:=A) hA hnm
    have hs : (1 : ℝ) ≤ (sVal S U A : ℝ) := by exact_mod_cast hs1
    have hw : wgt S U V A = Real.exp (-(20 : ℝ) * (sVal S U A : ℝ)) := by
      rw [wgt, hz]
      congr 1
      ring
    rw [z0w, if_pos hz, hw]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [z0w, if_neg hz]
    positivity

/-- zero-fibre contribution is ≤ C·|S|·exp(-20) -/
lemma z0_sum_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v : ℕ}
    (hS : ∀ A ∈ S, A ⊆ X) (hU : U ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U) :
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A)) ≤
      (cardSubsets (X \ U) v).card * S.card * Real.exp (-20) := by
  classical
  calc
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A))
        ≤ (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => Real.exp (-20))) := by
          apply Finset.sum_le_sum
          intro V hV
          apply Finset.sum_le_sum
          intro A hA
          exact z0w_le (S:=S) (U:=U) (V:=V) (A:=A) hA hnm
    _ = (cardSubsets (X \ U) v).card * S.card * Real.exp (-20) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring




/-! ## the case-1 weighted sum is small -/

/-- the t-sum over Icc 1 k with the condition t ≤ s collapses to Icc 1 s -/
lemma sum_ite_Icc_le_s {s k : ℕ} (hs1 : 1 ≤ s) (hsk : s ≤ k) (f : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0) = ∑ t ∈ Finset.Icc 1 s, f t := by
  classical
  calc
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0)
        = ∑ t ∈ (Finset.Icc 1 k).filter (fun t => t ≤ s), f t := by
          rw [Finset.sum_filter]
    _ = ∑ t ∈ Finset.Icc 1 s, f t := by
          congr 1
          ext t
          constructor
          · intro ht
            have h := Finset.mem_filter.mp ht
            have h1 : 1 ≤ t := (Finset.mem_Icc.mp h.1).1
            exact Finset.mem_Icc.mpr ⟨h1, h.2⟩
          · intro ht
            have h := Finset.mem_Icc.mp ht
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_Icc.mpr ⟨h.1, le_trans h.2 hsk⟩, h.2⟩

/-- a sum over idxSet equals the double sum over s,t -/
lemma sum_idxSet {k : ℕ} (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ idxSet k, f j) = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
  classical
  calc
    (∑ j ∈ idxSet k, f j) = ∑ j ∈ ((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s), f j := by
        rfl
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 k, if t ≤ s then f (s, t) else 0 := by
        rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
          have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
          exact sum_ite_Icc_le_s (s := s) (k := k) hs1 hsk (fun t => f (s, t))




/-! ## the aux theorem (non-trivial case) -/

/-- the weight sum bound used for the nontrivial case; assembles zero + case1 + case2 -/
lemma wb_le_four {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ}
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) (hr1 : 1 ≤ r)
    (hv : 0 < v) (hn : 0 < X.card) (hvn : v ≤ (X \ U).card)
    (hq : Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r) ≤ 1 / 2)
    (hSr : (S.card : ℝ) ≥ r ^ k)
    (hc1 : ∀ s t : ℕ, 1 ≤ t → t ≤ s →
      (((case1Fiber X S U v r k s t).card : ℝ) ≤
        (bigB0 X U v s).card * (4 : ℝ) ^ s * phiVal r k X v s t))
    (hc2sum : (∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card)
      ≤ 2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card) :
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => wgt S U V A))
      ≤ 4 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
  classical
  -- use the split wbSum = z0 + c1 + c2 and the fibre decompositions
  have hsplit := wbSum_split (X := X) (S := S) (U := U) (v := v) (k := k) (r := r)
  -- case1 weighted = fibre sum, bound it by C·r^k (via c1Sum_le)
  have hc1w := case1_wb_eq (X := X) (S := S) (U := U) (v := v) (k := k) (r := r) hS hU hnm huni
  have hc1sum := c1Sum_le (X := X) (S := S) (U := U) (v := v) (k := k) (r := r)
    hU hS hnm huni hr1 hv hn hvn hq hc1
  have hc2w := case2_wb_eq (X := X) (S := S) (U := U) (v := v) (k := k) (r := r) hS hU hnm huni
  have hz0 := z0_sum_le (X := X) (S := S) (U := U) (v := v) hS hU hnm
  have hz0' : (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A)) ≤
      Real.exp (-20) * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
    nlinarith [hz0]
  have hc1' : (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v)) ≤
      (cardSubsets (X \ U) v).card * (S.card : ℝ) := by
    -- = fibre sum ≤ C·r^k ≤ C·|S|
    have h1 : (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v))
        = ∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card := hc1w
    have h2 : (∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card) ≤
        (cardSubsets (X \ U) v).card * (r ^ k) := hc1sum
    have hrk : (cardSubsets (X \ U) v).card * (r ^ k) ≤ (cardSubsets (X \ U) v).card * (S.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hSr (by positivity)
    nlinarith
  have hc2' : (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v)) ≤
      2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
    have h1 : (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v))
        = ∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card := hc2w
    nlinarith
  calc
    (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => wgt S U V A))
        = (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => z0w S U V A)) +
          (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c1w S X U V A r k v)) +
          (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => c2w S X U V A r k v)) := hsplit
    _ ≤ Real.exp (-20) * (S.card : ℝ) * (cardSubsets (X \ U) v).card +
        (cardSubsets (X \ U) v).card * (S.card : ℝ) +
        2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
        nlinarith [hz0', hc1', hc2']
    _ ≤ 4 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
        have hpos : 0 ≤ (S.card : ℝ) * (cardSubsets (X \ U) v).card := by positivity
        have hz : Real.exp (-20) ≤ 1 := by
          calc
            Real.exp (-20) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
            _ = 1 := Real.exp_zero
        nlinarith






/-- Efix ≥ 1 in the no-member case (local copy) -/
lemma efix_ge_one' {S : Finset (Finset α)} {U : Finset α} (hSne : S.Nonempty)
    (hnm : ¬ ∃ A' ∈ S, A' ⊆ U) : (1 : ℝ) ≤ Efix S U := by
  unfold Efix
  have hpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hsum : (S.card : ℝ) ≤ ∑ A ∈ S, ((chi S U A).card : ℝ) := by
    calc
      (S.card : ℝ) = ∑ A ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ A ∈ S, ((chi S U A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro A hA
        have hs : 1 ≤ (chi S U A).card := by
          have hz : (chi S U A).card ≠ 0 := by
            intro h0
            exact hnm ((chi_card_zero_iff (S:=S) (U:=U) (A:=A) hA).1 h0)
          omega
        exact_mod_cast hs
  calc
    (1 : ℝ) ≤ (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hpos : 0 < (S.card : ℝ))]
      simpa using hsum
    _ = (∑ A ∈ S, ((chi S U A).card : ℝ)) / (S.card : ℝ) := rfl

/-- the main inequality in the nontrivial (no member of S inside U) case -/
theorem rao_aux {X : Finset α} {S : Finset (Finset α)} {k : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k) (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    {U : Finset α} {v : ℕ} (hU : U ⊆ X)
    (h8u : 8 * U.card ≤ X.card) (hv : 0 < v)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ))
    (huv2 : U.card + 2 * v ≤ X.card) (huv : U.card + v ≤ X.card)
    (hrbig : 2 ^ 6 ≤ (r * (v : ℝ)) / (X.card : ℝ))
    (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (hc2sum : (∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card)
      ≤ 2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card) :
    Eext S X U v ≤ c0 * Efix S U := by
  classical
  have hCposN : 0 < (cardSubsets (X \ U) v).card := by
    rw [card_cardSubsets]
    exact Nat.choose_pos (N_bound_v (X := X) (U := U) (v := v) hU huv)
  have hCpos : 0 < ((cardSubsets (X \ U) v).card : ℝ) := by exact_mod_cast hCposN
  have hSn : S.Nonempty := S_ne_of_Sr' (k := k) (r := r) (by omega) hr1 hSr
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hSn)
  have hSne0 : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
  have hvn : v ≤ (X \ U).card := N_bound_v (X := X) (U := U) (v := v) hU huv
  have hn : 0 < X.card := X_card_pos (X := X) (k := k) hk hn6
  have hq : Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r) ≤ 1 / 2 :=
    exp26_n_over_rv_half (X := X) (v := v) (r := r) hr1 hv hkap hn
  have hc1 : ∀ s t : ℕ, 1 ≤ t → t ≤ s →
      (((case1Fiber X S U v r k s t).card : ℝ) ≤
        (bigB0 X U v s).card * (4 : ℝ) ^ s * phiVal r k X v s t) := by
    intro s t ht1 hts
    exact case1Fiber_card_le (X := X) (S := S) (U := U) (v := v) (k := k) (s := s) (t := t) (r := r)
      hU hS hnm hr1 ht1 hts
  have hwb := wb_le_four (X := X) (S := S) (U := U) (v := v) (k := k) (r := r)
    hU hS hnm huni hr1 hv hn hvn hq hSr hc1 hc2sum
  let C : ℝ := ((cardSubsets (X \ U) v).card : ℝ)
  let Tsum : ℝ := (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => (tVal S U V A : ℝ)))
  let Ssum : ℝ := S.sum (fun A => (sVal S U A : ℝ))
  have hEext : Eext S X U v = Tsum / (C * (S.card : ℝ)) := by
    unfold Eext
    dsimp [Tsum, C, tVal]
  have hEfix : Efix S U = Ssum / (S.card : ℝ) := by
    unfold Efix
    dsimp [Ssum, sVal]
  let P : Finset (Finset α × Finset α) := (cardSubsets (X \ U) v).product S
  have hPcard : (P.card : ℝ) = C * (S.card : ℝ) := by
    dsimp [P, C]
    rw [Finset.card_product, Nat.cast_mul]
  have hPpos : 0 < P.card := by
    simpa [P, Finset.card_product] using (mul_pos hCposN (Finset.card_pos.mpr hSn))
  have hTsumP : P.sum (fun p : Finset α × Finset α => (tVal S U p.1 p.2 : ℝ)) = Tsum := by
    dsimp [P, Tsum]
    rw [Finset.sum_product]
  have hSsumP : P.sum (fun p : Finset α × Finset α => (sVal S U p.2 : ℝ)) = C * Ssum := by
    dsimp [P, C, Ssum]
    rw [Finset.sum_product]
    have hfun : (fun V : Finset α => S.sum (fun A : Finset α => (sVal S U A : ℝ))) =
        (fun _ : Finset α => (S.sum (fun A : Finset α => (sVal S U A : ℝ)))) := rfl
    rw [hfun]
    rw [sum_const_real]
  have hxsum : P.sum (fun p : Finset α × Finset α =>
      (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ)) =
      (26 : ℝ) * Tsum - (20 : ℝ) * C * Ssum := by
    calc
      P.sum (fun p : Finset α × Finset α =>
          (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ))
          = P.sum (fun p => (26 : ℝ) * (tVal S U p.1 p.2 : ℝ)) -
            P.sum (fun p => (20 : ℝ) * (sVal S U p.2 : ℝ)) := by
              rw [Finset.sum_sub_distrib]
      _ = (26 : ℝ) * Tsum - (20 : ℝ) * C * Ssum := by
            have h1 : P.sum (fun p => (26 : ℝ) * (tVal S U p.1 p.2 : ℝ)) = (26 : ℝ) * Tsum := by
              rw [← Finset.mul_sum]
              rw [hTsumP]
            have h2 : P.sum (fun p => (20 : ℝ) * (sVal S U p.2 : ℝ)) = (20 : ℝ) * (C * Ssum) := by
              rw [← Finset.mul_sum]
              rw [hSsumP]
            rw [h1, h2]
            ring
  have hexpsum : P.sum (fun p : Finset α × Finset α =>
      Real.exp ((26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ))) =
      (cardSubsets (X \ U) v).sum (fun V => S.sum (fun A => wgt S U V A)) := by
    simp [P, Finset.sum_product, wgt]
  have havg := exp_avg_le_sum_div (t := P)
    (x := fun p : Finset α × Finset α =>
      (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ)) hPpos
  have hmean : Real.exp (P.sum (fun p : Finset α × Finset α =>
        (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ)) / (P.card : ℝ)) ≤ 4 := by
    have h2 : P.sum (fun p => Real.exp ((26 : ℝ) * (tVal S U p.1 p.2 : ℝ) -
          (20 : ℝ) * (sVal S U p.2 : ℝ))) / (P.card : ℝ) ≤ 4 := by
      rw [hexpsum, hPcard]
      have hC0 : 0 < C * (S.card : ℝ) := by
        dsimp [C]
        positivity
      rw [div_le_iff₀ hC0]
      dsimp [C] at hwb ⊢
      nlinarith [hwb]
    exact le_trans havg h2
  have hln : P.sum (fun p : Finset α × Finset α =>
        (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ)) /
      (P.card : ℝ) ≤ Real.log 4 := by
    exact (Real.le_log_iff_exp_le (by norm_num : 0 < (4 : ℝ))).mpr hmean
  have hxle : P.sum (fun p : Finset α × Finset α =>
        (26 : ℝ) * (tVal S U p.1 p.2 : ℝ) - (20 : ℝ) * (sVal S U p.2 : ℝ)) ≤
      (P.card : ℝ) * Real.log 4 := by
    have hpos : 0 < (P.card : ℝ) := by exact_mod_cast hPpos
    rw [div_le_iff₀ hpos] at hln
    rw [mul_comm]
    exact hln
  have hmain1 : (26 : ℝ) * Tsum - (20 : ℝ) * C * Ssum ≤ (C * (S.card : ℝ)) * Real.log 4 := by
    rw [← hxsum]
    rw [hPcard] at hxle
    exact hxle
  have hefix1 : (1 : ℝ) ≤ Efix S U := efix_ge_one' (S := S) (U := U) hSn hnm
  have hefixS : (1 : ℝ) ≤ Ssum / (S.card : ℝ) := by
    rw [← hEfix]
    exact hefix1
  have hTstep : Tsum ≤ ((10 : ℝ) / 13) * (C * Ssum) + (C * (S.card : ℝ)) * (Real.log 4 / 26) := by
    have h1 : (26 : ℝ) * Tsum ≤ (20 : ℝ) * C * Ssum + (C * (S.card : ℝ)) * Real.log 4 := by
      nlinarith [hmain1]
    nlinarith
  have hf0 : Real.log 4 / 26 ≤ (5 / 78 : ℝ) := by
    have hl : Real.log 4 ≤ (7 : ℝ) / 5 := log4_le_7_5
    nlinarith
  have hfac : (C * (S.card : ℝ)) * (Real.log 4 / 26) ≤ (5 / 78 : ℝ) * (C * Ssum) := by
    have h1 : Real.log 4 / 26 ≤ (5 / 78 : ℝ) * (Ssum / (S.card : ℝ)) := by
      have hm : (5 / 78 : ℝ) * (1 : ℝ) ≤ (5 / 78 : ℝ) * (Ssum / (S.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hefixS (by norm_num)
      calc
        Real.log 4 / 26 ≤ (5 / 78 : ℝ) * 1 := by nlinarith [hf0]
        _ ≤ (5 / 78 : ℝ) * (Ssum / (S.card : ℝ)) := hm
    have hSnonneg : 0 ≤ (S.card : ℝ) := by positivity
    have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hCnonneg hSnonneg)
    have hEq : (C * (S.card : ℝ)) * ((5 / 78 : ℝ) * (Ssum / (S.card : ℝ))) =
        (5 / 78 : ℝ) * (C * Ssum) := by
      field_simp [hSne0]
    calc
      (C * (S.card : ℝ)) * (Real.log 4 / 26) ≤ (C * (S.card : ℝ)) * ((5 / 78 : ℝ) * (Ssum / (S.card : ℝ))) := by
          nlinarith [h2]
      _ = (5 / 78 : ℝ) * (C * Ssum) := hEq
  have hsum2 : ((10 : ℝ) / 13) * (C * Ssum) + (C * (S.card : ℝ)) * (Real.log 4 / 26) ≤
      (5 / 6 : ℝ) * (C * Ssum) := by
    nlinarith [hfac]
  have hTgoal : Tsum ≤ c0 * (C * Ssum) := by
    dsimp [c0]
    nlinarith [hTstep, hsum2]
  rw [hEext, hEfix]
  have hC0' : 0 < C * (S.card : ℝ) := by
    dsimp [C]
    positivity
  rw [div_le_iff₀ hC0']
  have hEq2 : c0 * (Ssum / (S.card : ℝ)) * (C * (S.card : ℝ)) = c0 * (C * Ssum) := by
    field_simp [hSne0]
  rw [hEq2]
  exact hTgoal

end Submission.Sun

