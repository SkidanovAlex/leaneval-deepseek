import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.FamEst
import Submission.Work.Deep.Nibble.r2_Wfam_defs
import Submission.Work.Deep.Nibble.r2_var_aux
import Submission.Work.Deep.Nibble.r2_comb_count
import Submission.Work.Deep.Nibble.r2_Wfam_count

/-!
# The mean of the per-set waste in the second round of the nibble

This file proves `Work.Deep.Nibble.r2_Wfam_mean`, the first-moment estimate for the
edge-charged waste `badSum 𝓖 ω S = ∑_{e bad} |e ∩ S|` of one round of the wasteful
Rödl nibble on a finite hypergraph `𝓖` in which each edge is kept independently with
probability `p = θ / D`.

The argument is a union bound.  A kept edge `e` is *bad* when some element of
`meetSet 𝓖 e` (a different edge of `𝓖` meeting `e`) is also kept, so

`E[badSum] = ∑_e |e ∩ S| · P(e bad) ≤ ∑_e |e ∩ S| · |meetSet 𝓖 e| · p²`.

The sum `∑_e |e ∩ S| · |meetSet 𝓖 e| ≤ r (1+ε)² D² |S|` is pure double counting under
`r`-uniformity and the degree regularity `hd 𝓖 v = D(1 ± ε)` (`r2_Wfam_count`); with
`p = θ/D` this gives `E[badSum] ≤ r (1+ε)² θ² |S| ≤ 2 r θ² |S|` because `ε ≤ 1/100`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The first moment of the edge-charged waste -/

/-- The charge of the edge `e` in the edge-charged waste: `|e ∩ S|` when `e` is bad, and
`0` otherwise. -/
noncomputable def badCharge (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) (e : 𝓖) : ℝ := by
  classical
  exact if badAt 𝓖 ω e then (((e : Set V) ∩ (S : Set V)).ncard : ℝ) else 0

lemma badCharge_nonneg (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) (e : 𝓖) :
    0 ≤ badCharge 𝓖 ω S e := by
  classical
  unfold badCharge
  by_cases h : badAt 𝓖 ω e <;> simp [h]

lemma badCharge_of_bad {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {S : Finset V} {e : 𝓖}
    (h : badAt 𝓖 ω e) : badCharge 𝓖 ω S e = (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
  classical
  unfold badCharge
  rw [if_pos h]

lemma badCharge_of_not_bad {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {S : Finset V} {e : 𝓖}
    (h : ¬ badAt 𝓖 ω e) : badCharge 𝓖 ω S e = 0 := by
  classical
  unfold badCharge
  rw [if_neg h]

/-- `badSum` as a sum of its charges. -/
lemma badSum_cast (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    ((badSum 𝓖 ω S : ℕ) : ℝ) = ∑ e : 𝓖, badCharge 𝓖 ω S e := by
  classical
  unfold badSum badCharge
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun e _ => by by_cases h : badAt 𝓖 ω e <;> simp [h]

/-- Pointwise, a bad kept edge is charged to the indicators of the pairs of a kept edge and
a kept element of `meetSet 𝓖 e`. -/
lemma badSum_le_sum_indicators (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    ((badSum 𝓖 ω S : ℕ) : ℝ)
      ≤ ∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) *
          ∑ f ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f = true then (1 : ℝ) else 0) := by
  classical
  rw [badSum_cast 𝓖 ω S]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases hb : badAt 𝓖 ω e
  · rw [badCharge_of_bad hb]
    obtain ⟨hwe, f, hfne, hwf, hfint⟩ := hb
    have hfM : f ∈ meetSet 𝓖 e := by
      rw [mem_meetSet]; exact ⟨hfne, hfint⟩
    have h1 : (1 : ℝ)
        ≤ ∑ f' ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f' = true then (1 : ℝ) else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun i _ => ?_) hfM)
      · simp [hwe, hwf]
      · split <;> norm_num
    calc (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
        = (((e : Set V) ∩ (S : Set V)).ncard : ℝ) * 1 := by ring
      _ ≤ (((e : Set V) ∩ (S : Set V)).ncard : ℝ) *
            ∑ f' ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f' = true then (1 : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  · rw [badCharge_of_not_bad hb]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => by split <;> norm_num)

/-- The expectation of the indicator of two coordinates being kept. -/
lemma exp_ind_and (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e f : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).exp
        (fun ω => if ω e = true ∧ ω f = true then (1 : ℝ) else 0)
      = if e = f then p else p * p := by
  classical
  have hfun : (fun ω : 𝓖 → Bool => (if ω e = true ∧ ω f = true then (1 : ℝ) else 0))
      = (fun ω => (if ω e = true then (1 : ℝ) else 0)
          * (if ω f = true then (1 : ℝ) else 0)) := by
    funext ω
    by_cases h1 : ω e = true <;> by_cases h2 : ω f = true <;> simp [h1, h2]
  rw [hfun, exp_ind_mul 𝓖 hp0 hp1 e f]

/-- **The mean of the per-set waste is at most `p²` times the counting sum.** -/
theorem exp_badSum_le (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset V) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
      ≤ p ^ 2 * ∑ e : 𝓖,
          (((e : Set V) ∩ (S : Set V)).ncard : ℝ) * ((meetSet 𝓖 e).card : ℝ) := by
  classical
  set c : 𝓖 → ℝ := fun e => (((e : Set V) ∩ (S : Set V)).ncard : ℝ) with hc
  calc (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
      ≤ (edgeMeasure 𝓖 p hp0 hp1).exp
          (fun ω => ∑ e : 𝓖, c e *
            ∑ f ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f = true then (1 : ℝ) else 0)) :=
        FinProb.exp_mono _ (fun ω => badSum_le_sum_indicators 𝓖 ω S)
    _ = ∑ e : 𝓖, (edgeMeasure 𝓖 p hp0 hp1).exp
          (fun ω => c e *
            ∑ f ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f = true then (1 : ℝ) else 0)) :=
        FinProb.exp_sum _ _
    _ = ∑ e : 𝓖, c e * (edgeMeasure 𝓖 p hp0 hp1).exp
          (fun ω => ∑ f ∈ meetSet 𝓖 e, (if ω e = true ∧ ω f = true then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun e _ => FinProb.exp_mul_left _ (c e) _
    _ = ∑ e : 𝓖, c e * ∑ f ∈ meetSet 𝓖 e, p * p := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [FinProb.exp_sum_finset]
        congr 1
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [exp_ind_and 𝓖 hp0 hp1 e f, if_neg]
        exact fun h => (mem_meetSet.mp hf).1 h.symm
    _ = ∑ e : 𝓖, c e * (((meetSet 𝓖 e).card : ℝ) * (p * p)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = p ^ 2 * ∑ e : 𝓖, c e * ((meetSet 𝓖 e).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring

/-! ## The combinatorial count under the round's hypotheses -/

/-- The `ncard` of the intersection of an edge with a finite set, as the cardinality of a
`Finset`. -/
lemma ncard_inter_eq_card (𝓖 : Set (Set V)) (e : 𝓖) (S : Finset V) :
    ((e : Set V) ∩ (S : Set V)).ncard = (eFin 𝓖 e ∩ S).card := by
  have h : ((e : Set V) ∩ (S : Set V)) = ((eFin 𝓖 e ∩ S : Finset V) : Set V) := by
    ext v
    simp [eFin_mem_iff]
  rw [h, Set.ncard_coe_finset]

/-- Every element of `meetSet 𝓖 e` is an edge through a vertex of `e`; since each vertex of
`e` carries at most `hd 𝓖 w` edges, the count is at most the sum of those degrees. -/
lemma meetSet_card_le_sum_hd (𝓖 : Set (Set V)) (e : 𝓖) :
    (meetSet 𝓖 e).card ≤ ∑ w ∈ eFin 𝓖 e, hd 𝓖 w := by
  classical
  have hsub : meetSet 𝓖 e ⊆ (eFin 𝓖 e).biUnion (fun w => thruF 𝓖 w) := by
    intro f hf
    rw [mem_meetSet] at hf
    obtain ⟨hfne, hfint⟩ := hf
    obtain ⟨w, hwf, hwe⟩ := hfint
    exact Finset.mem_biUnion.mpr ⟨w, by simpa using hwe, by simpa using hwf⟩
  calc (meetSet 𝓖 e).card ≤ ((eFin 𝓖 e).biUnion (fun w => thruF 𝓖 w)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ eFin 𝓖 e, (thruF 𝓖 w).card := Finset.card_biUnion_le
    _ = ∑ w ∈ eFin 𝓖 e, hd 𝓖 w :=
        Finset.sum_congr rfl fun w _ => (hd_eq_card_thruF 𝓖 w).symm

/-- Double counting of the incidences of the family with `S`. -/
lemma sum_ncard_inter_eq_sum_hd (𝓖 : Set (Set V)) (S : Finset V) :
    (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)) = ∑ v ∈ S, (hd 𝓖 v : ℝ) := by
  classical
  have hpt : ∀ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
      = ∑ v ∈ S, (if v ∈ (e : Set V) then (1 : ℝ) else 0) := by
    intro e
    have hfil : eFin 𝓖 e ∩ S = S.filter (fun v => v ∈ (e : Set V)) := by
      ext v
      simp [eFin_mem_iff, and_comm]
    rw [ncard_inter_eq_card, hfil, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hcard : (hd 𝓖 v : ℝ) = ∑ e : 𝓖, (if v ∈ (e : Set V) then (1 : ℝ) else 0) := by
    rw [hd_eq_card_thruF 𝓖 v, thruF, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    simp
  exact (hcard).symm

/-! ## The target estimate -/

theorem r2_Wfam_mean {V : Type*} [Fintype V] [DecidableEq V] {𝓖 : Set (Set V)} {r : ℕ}
    (hr : 2 ≤ r) (huni : Work.Deep.Nibble.HUnif 𝓖 r) {θ ε : ℝ} (hθ0 : 0 < θ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) {D : ℕ} (hD : 8 ≤ D)
    (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hdeg : ∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ))
    (S : Finset V) :
    (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ((Work.Deep.Nibble.badSum 𝓖 ω S : ℕ) : ℝ))
      ≤ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hp2D2 : (θ / (D : ℝ)) ^ 2 * (D : ℝ) ^ 2 = θ ^ 2 := by
    rw [← mul_pow]
    exact congrArg (fun x => x ^ 2) (div_mul_cancel₀ θ hDne)
  have hε2 : (1 + ε) ^ 2 ≤ 2 := by
    have h1 : ε ^ 2 ≤ ε * (1 / 100) := by
      have := mul_le_mul_of_nonneg_left hε1 (le_of_lt hε0)
      nlinarith [this]
    nlinarith [hε0, hε1, h1]
  have hbound := exp_badSum_le 𝓖 hp0 hp1 S
  have hcount := r2_Wfam_count 𝓖 huni (le_of_lt hε0) hdeg S
  calc (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
      ≤ (θ / (D : ℝ)) ^ 2 * ∑ e : 𝓖,
          (((e : Set V) ∩ (S : Set V)).ncard : ℝ) * ((meetSet 𝓖 e).card : ℝ) := hbound
    _ ≤ (θ / (D : ℝ)) ^ 2 * ((r : ℝ) * (1 + ε) ^ 2 * (D : ℝ) ^ 2 * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcount (sq_nonneg _)
    _ = (1 + ε) ^ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) := by
        rw [show (θ / (D : ℝ)) ^ 2 * ((r : ℝ) * (1 + ε) ^ 2 * (D : ℝ) ^ 2 * (S.card : ℝ))
            = ((r : ℝ) * (1 + ε) ^ 2 * (S.card : ℝ)) * ((θ / (D : ℝ)) ^ 2 * (D : ℝ) ^ 2)
            by ring, hp2D2]
        ring
    _ ≤ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) := by
        have hrn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        have hθ2 : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
        have hSc : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        have hprod : (0 : ℝ) ≤ (r : ℝ) * θ ^ 2 * (S.card : ℝ) :=
          mul_nonneg (mul_nonneg hrn hθ2) hSc
        have h1 : (1 + ε) ^ 2 * ((r : ℝ) * θ ^ 2 * (S.card : ℝ))
            ≤ 2 * ((r : ℝ) * θ ^ 2 * (S.card : ℝ)) := mul_le_mul_of_nonneg_right hε2 hprod
        have e1 : (1 + ε) ^ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)
            = (1 + ε) ^ 2 * ((r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by ring
        have e2 : 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)
            = 2 * ((r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by ring
        linarith [h1, e1, e2]

end Work.Deep.Nibble
