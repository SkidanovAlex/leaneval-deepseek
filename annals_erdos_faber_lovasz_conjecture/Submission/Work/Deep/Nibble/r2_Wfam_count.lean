import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_Wfam_defs
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_comb_count

/-!
# The counting bound for the edge-charged waste of the second round

This module proves `Work.Deep.Nibble.r2_Wfam_count`, the pure double-counting
estimate behind the mean of the edge-charged waste `badSum` of one round of the
wasteful Rödl nibble (`Work.Deep.Nibble.r2_Wfam_mean`):

`∑_{e ∈ 𝓖} |e ∩ S| · |meetSet 𝓖 e| ≤ r (1+ε)² D² |S|`

whenever every edge of `𝓖` has `r` vertices (`HUnif 𝓖 r`) and every degree is
within `(1±ε)D` (`hdeg`).

Both factors are bounded by double counting, with no linearity hypothesis
needed:

* `|meetSet 𝓖 e| ≤ ∑_{w ∈ e} hd 𝓖 w` (every edge meeting `e` passes through a
  vertex of `e`), and each degree is at most `D (1+ε)`, so
  `|meetSet 𝓖 e| ≤ r D (1+ε)`;
* `∑_e |e ∩ S| = ∑_{v ∈ S} hd 𝓖 v` (the incidences `(e,v)` with `v ∈ e ∩ S`
  counted by edges resp. by vertices of `S`), and again every degree is at most
  `D (1+ε)`, so `∑_e |e ∩ S| ≤ |S| D (1+ε)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

section Count

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cardinality of a set intersection is the cardinality of the `Finset`
intersection with the edge. -/
private lemma ncard_inter_eq_card (𝓖 : Set (Set V)) (S : Finset V) (e : 𝓖) :
    ((e : Set V) ∩ (S : Set V)).ncard = ((eFin 𝓖 e) ∩ S).card := by
  classical
  have hf : ((e : Set V) ∩ (S : Set V)).Finite := Set.toFinite _
  have hset : hf.toFinset = (eFin 𝓖 e) ∩ S := by
    ext w
    simp [eFin_mem_iff, Finset.mem_inter]
  rw [Set.ncard_eq_toFinset_card _ hf, hset]

/-- An `r`-uniform edge has exactly `r` vertices. -/
private lemma card_eFin_eq (𝓖 : Set (Set V)) {r : ℕ} (huni : HUnif 𝓖 r) (e : 𝓖) :
    (eFin 𝓖 e).card = r := by
  have hf : ((e : Set V)).Finite := Set.toFinite _
  have hset : hf.toFinset = eFin 𝓖 e := by
    ext w; simp [eFin_mem_iff]
  rw [← hset, ← Set.ncard_eq_toFinset_card (e : Set V) hf]
  exact huni (e : Set V) e.2

/-- Every edge meeting `e` passes through a vertex of `e`, so the number of edges
meeting `e` is at most the sum of the degrees over the vertices of `e`. -/
private lemma meetSet_card_le_sum (𝓖 : Set (Set V)) (e : 𝓖) :
    (meetSet 𝓖 e).card ≤ ∑ w ∈ eFin 𝓖 e, hd 𝓖 w := by
  have hsub : meetSet 𝓖 e ⊆ (eFin 𝓖 e).biUnion (fun w => thruF 𝓖 w) := by
    intro f hf
    rw [mem_meetSet] at hf
    obtain ⟨w, hw⟩ := hf.2
    exact Finset.mem_biUnion.mpr
      ⟨w, (eFin_mem_iff (𝓖 := 𝓖)).mpr hw.2, (mem_thruF (𝓖 := 𝓖)).mpr hw.1⟩
  calc (meetSet 𝓖 e).card ≤ ((eFin 𝓖 e).biUnion (fun w => thruF 𝓖 w)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ eFin 𝓖 e, (thruF 𝓖 w).card := Finset.card_biUnion_le
    _ = ∑ w ∈ eFin 𝓖 e, hd 𝓖 w :=
        Finset.sum_congr rfl (fun w _ => (hd_eq_card_thruF 𝓖 w).symm)

/-- Double counting: summing the sizes `|e ∩ S|` over the edges `e` of `𝓖` is the
same as summing the degrees over the vertices of `S`. -/
private lemma sum_eFin_inter_card (𝓖 : Set (Set V)) (S : Finset V) :
    (∑ e : 𝓖, ((eFin 𝓖 e) ∩ S).card) = ∑ v ∈ S, (thruF 𝓖 v).card := by
  have h2 : ∀ e : 𝓖, ((eFin 𝓖 e) ∩ S).card
      = ∑ v ∈ S, (if v ∈ eFin 𝓖 e then (1:ℕ) else 0) := by
    intro e
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones,
      Finset.sum_filter]
  have h3 : ∀ v : V, (thruF 𝓖 v).card
      = ∑ e : 𝓖, (if v ∈ eFin 𝓖 e then (1:ℕ) else 0) := by
    intro v
    rw [thruF, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : v ∈ (e : Set V)
    · rw [if_pos h, if_pos ((eFin_mem_iff (𝓖 := 𝓖)).mpr h)]
    · rw [if_neg h, if_neg (fun hh => h ((eFin_mem_iff (𝓖 := 𝓖)).mp hh))]
  calc (∑ e : 𝓖, ((eFin 𝓖 e) ∩ S).card)
      = ∑ e : 𝓖, ∑ v ∈ S, (if v ∈ eFin 𝓖 e then (1:ℕ) else 0) :=
        Finset.sum_congr rfl (fun e _ => h2 e)
    _ = ∑ v ∈ S, ∑ e : 𝓖, (if v ∈ eFin 𝓖 e then (1:ℕ) else 0) := Finset.sum_comm
    _ = ∑ v ∈ S, (thruF 𝓖 v).card := Finset.sum_congr rfl (fun v _ => (h3 v).symm)

end Count

theorem r2_Wfam_count {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ}
    (huni : Work.Deep.Nibble.HUnif 𝓖 r) {ε : ℝ} (hε : 0 ≤ ε) {D : ℕ}
    (hdeg : ∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ))
    (S : Finset V) :
    (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) *
        ((Work.Deep.Nibble.meetSet 𝓖 e).card : ℝ))
      ≤ (r : ℝ) * (1 + ε) ^ 2 * (D : ℝ) ^ 2 * (S.card : ℝ) := by
  classical
  have hD : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
  have hε1 : (0:ℝ) ≤ 1 + ε := by linarith
  have hle : ∀ v : V, (Work.Deep.Nibble.hd 𝓖 v : ℝ) ≤ (D : ℝ) * (1 + ε) := by
    intro v
    have h := (abs_le.mp (hdeg v)).2
    nlinarith [h]
  have hper : ∀ e : 𝓖,
      ((Work.Deep.Nibble.meetSet 𝓖 e).card : ℝ) ≤ (r : ℝ) * ((D : ℝ) * (1 + ε)) := by
    intro e
    have h1 : ((Work.Deep.Nibble.meetSet 𝓖 e).card : ℝ)
        ≤ ((∑ w ∈ eFin 𝓖 e, hd 𝓖 w : ℕ) : ℝ) := by
      exact_mod_cast meetSet_card_le_sum 𝓖 e
    calc ((Work.Deep.Nibble.meetSet 𝓖 e).card : ℝ)
        ≤ ((∑ w ∈ eFin 𝓖 e, hd 𝓖 w : ℕ) : ℝ) := h1
      _ = ∑ w ∈ eFin 𝓖 e, (hd 𝓖 w : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ w ∈ eFin 𝓖 e, ((D : ℝ) * (1 + ε)) := Finset.sum_le_sum (fun w _ => hle w)
      _ = ((eFin 𝓖 e).card : ℝ) * ((D : ℝ) * (1 + ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (r : ℝ) * ((D : ℝ) * (1 + ε)) := by rw [card_eFin_eq 𝓖 huni e]
  have hfub : (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
      = ∑ v ∈ S, (Work.Deep.Nibble.hd 𝓖 v : ℝ) := by
    have hnat : (∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard) = ∑ v ∈ S, hd 𝓖 v := by
      calc (∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard)
          = ∑ e : 𝓖, ((eFin 𝓖 e) ∩ S).card :=
            Finset.sum_congr rfl (fun e _ => ncard_inter_eq_card 𝓖 S e)
        _ = ∑ v ∈ S, (thruF 𝓖 v).card := sum_eFin_inter_card 𝓖 S
        _ = ∑ v ∈ S, hd 𝓖 v := Finset.sum_congr rfl (fun v _ => (hd_eq_card_thruF 𝓖 v).symm)
    calc (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
        = ((∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard : ℕ) : ℝ) := by rw [Nat.cast_sum]
      _ = ((∑ v ∈ S, hd 𝓖 v : ℕ) : ℝ) := by rw [hnat]
      _ = ∑ v ∈ S, (Work.Deep.Nibble.hd 𝓖 v : ℝ) := Nat.cast_sum _ _
  have hdegS : (∑ v ∈ S, (Work.Deep.Nibble.hd 𝓖 v : ℝ))
      ≤ (S.card : ℝ) * ((D : ℝ) * (1 + ε)) := by
    calc (∑ v ∈ S, (Work.Deep.Nibble.hd 𝓖 v : ℝ)) ≤ ∑ v ∈ S, ((D : ℝ) * (1 + ε)) :=
          Finset.sum_le_sum (fun v _ => hle v)
      _ = (S.card : ℝ) * ((D : ℝ) * (1 + ε)) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
          * ((Work.Deep.Nibble.meetSet 𝓖 e).card : ℝ))
      ≤ ∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) * ((r : ℝ) * ((D : ℝ) * (1 + ε))) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hper e) (Nat.cast_nonneg _))
    _ = ((r : ℝ) * ((D : ℝ) * (1 + ε)))
          * ∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        ring
    _ = ((r : ℝ) * ((D : ℝ) * (1 + ε))) * ∑ v ∈ S, (Work.Deep.Nibble.hd 𝓖 v : ℝ) := by
        rw [hfub]
    _ ≤ ((r : ℝ) * ((D : ℝ) * (1 + ε))) * ((S.card : ℝ) * ((D : ℝ) * (1 + ε))) :=
        mul_le_mul_of_nonneg_left hdegS (by positivity)
    _ = (r : ℝ) * (1 + ε) ^ 2 * (D : ℝ) ^ 2 * (S.card : ℝ) := by ring

end Work.Deep.Nibble
