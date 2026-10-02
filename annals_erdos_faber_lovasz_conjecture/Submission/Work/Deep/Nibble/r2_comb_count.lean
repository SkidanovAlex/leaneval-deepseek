import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup

/-!
# Round 2 of the nibble: the combinatorics of the blocker sets

This file proves `Work.Deep.Nibble.r2_comb_count`, the elementary counting lemma needed for
the second round of the Rödl nibble (`Work.Deep.Nibble.nibble_round2`).

Throughout, `𝓖 : Set (Set V)` is a family of subsets of a finite type `V`, `hd 𝓖 v` is the
degree of the vertex `v`, `HLin 𝓖` says that two distinct edges of `𝓖` meet in at most one
vertex, `HUnif 𝓖 r` says that every edge of `𝓖` has exactly `r` vertices,
`eFin 𝓖 e` is the edge `e` seen as a `Finset V`, and for `v ∈ e`,

`Bset 𝓖 v e = {f ∈ 𝓖 : f ∩ e ≠ ∅, v ∉ f}`

is the set of *blockers* of `e` when the residual degree at `v` is inspected: the edges
meeting `e` which do not contain `v`.

The five assertions of `r2_comb_count` are

1. `∑_v hd 𝓖 v = r · |𝓖|` (double counting: every edge has `r` vertices);
2. `|Bset 𝓖 v e| = ∑_{w ∈ e ∖ {v}} (hd 𝓖 w - 1)`: by linearity a blocker `f` of `e` at `v`
   meets `e` in exactly one vertex `w ≠ v`, and it then runs over all edges through `w`
   except `e` itself (which, moreover, is the only edge through `w` that carries `v`);
3. the upper bound `|Bset 𝓖 v e| ≤ (r-1)(1+ε)D` if all degrees are at most `(1+ε)D`;
4. the lower bound `(r-1)((1-ε)D - 1) ≤ |Bset 𝓖 v e|` if all degrees are at least `(1-ε)D`
   (the `-1` is the edge `e` itself, which has to be removed from each degree);
5. the global sandwich `(1-ε)D·|V| ≤ r·|𝓖| ≤ (1+ε)D·|V|` if all degrees are within `(1±ε)D`.

These are the estimates (2.1) and (2.2) of the round: the free blockers of an edge `e ∋ v`
number `∑_{w ∈ e∖{v}}(hd w - 1) ∈ ((r-1)(D-1))(1 ± O(ε))`, so the conditional law of the
residual degree of an uncovered vertex `v` has mean `D(1-θ/D)^{(r-1)(D-1)}` up to a factor
`1 + O(ε(1 + rθ))`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Classical in
-- The cardinality of a set as the sum of the indicators of its membership predicate.
private lemma ncard_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) :
    s.ncard = ∑ a : α, if a ∈ s then (1 : ℕ) else 0 := by
  classical
  have hs : s.Finite := Set.toFinite s
  have hfinset : hs.toFinset = (Finset.univ : Finset α).filter (fun a => a ∈ s) := by
    ext a; simp
  rw [Set.ncard_eq_toFinset_card s hs, Finset.card_eq_sum_ones, hfinset,
    ← Finset.sum_filter (p := fun a => a ∈ s) (f := fun _ => (1 : ℕ))]

section Combinatorics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the `Finset` version of an edge. -/
private lemma mem_eFin {𝓖 : Set (Set V)} {e : 𝓖} {w : V} :
    w ∈ eFin 𝓖 e ↔ w ∈ (e : Set V) := by
  classical simp [eFin]

/-- The `Finset` version of an edge has the same cardinality as the edge. -/
private lemma card_eFin {𝓖 : Set (Set V)} (e : 𝓖) : (eFin 𝓖 e).card = (e : Set V).ncard := by
  classical
  have hf : ((e : Set V)).Finite := Set.toFinite _
  have hset : hf.toFinset = eFin 𝓖 e := by
    ext w; simp [mem_eFin]
  rw [Set.ncard_eq_toFinset_card ((e : Set V)) hf, hset]

/-- **The sum of the degrees is the number of edges times the edge size** (double counting). -/
private theorem sum_hd_eq_card_mul (𝓖 : Set (Set V)) {r : ℕ} (huni : HUnif 𝓖 r) :
    (∑ v : V, hd 𝓖 v) = r * Nat.card 𝓖 := by
  classical
  have htf : ∀ v : V, thruF 𝓖 v = Finset.univ.filter (fun e : 𝓖 => v ∈ (e : Set V)) := by
    intro v; ext e; simp [thruF]
  have h1 : ∀ v : V, hd 𝓖 v = ∑ e : 𝓖, (if v ∈ (e : Set V) then (1 : ℕ) else 0) := by
    intro v
    rw [hd_eq_card_thruF 𝓖 v, Finset.card_eq_sum_ones, htf v, Finset.sum_filter]
  calc (∑ v : V, hd 𝓖 v)
      = ∑ v : V, ∑ e : 𝓖, (if v ∈ (e : Set V) then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun v _ => h1 v
    _ = ∑ e : 𝓖, ∑ v : V, (if v ∈ (e : Set V) then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ e : 𝓖, (e : Set V).ncard := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (ncard_eq_sum_ite (e : Set V)).symm
    _ = ∑ e : 𝓖, r := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact huni (e : Set V) e.2
    _ = r * Nat.card 𝓖 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card,
          Nat.mul_comm]
        exact congrArg (fun x => r * x) (Nat.cast_id _)

/-- **The exact number of blockers.**  For `v ∈ e` the blockers of `e` at `v` are in bijection
with the pairs `(w, f)` where `w ∈ e ∖ {v}` and `f` is an edge through `w` different from `e`;
linearity makes this a partition, so the cardinality is `∑_{w ∈ e∖{v}} (hd 𝓖 w - 1)`. -/
private theorem bset_card_eq (𝓖 : Set (Set V)) (hlin : HLin 𝓖) {v : V} {e : 𝓖}
    (hve : v ∈ (e : Set V)) :
    (Bset 𝓖 v e).card = ∑ w ∈ (eFin 𝓖 e).erase v, (hd 𝓖 w - 1) := by
  classical
  have hSmem : ∀ w : V, w ∈ (eFin 𝓖 e).erase v ↔ w ≠ v ∧ w ∈ (e : Set V) := by
    intro w; simp only [Finset.mem_erase, mem_eFin]
  have hTmem : ∀ (w : V) (f : 𝓖), f ∈ (thruF 𝓖 w).erase e ↔ f ≠ e ∧ w ∈ (f : Set V) := by
    intro w f; simp only [Finset.mem_erase, mem_thruF]
  have hne' : ∀ {f : 𝓖}, f ≠ e → (f : Set V) ≠ (e : Set V) := fun {f} h hh => h (Subtype.ext hh)
  -- a blocker of `e` at `v` is an edge through a unique vertex of `e ∖ {v}`, other than `e`
  have hEq : Bset 𝓖 v e
      = ((eFin 𝓖 e).erase v).biUnion (fun w => (thruF 𝓖 w).erase e) := by
    ext f
    constructor
    · intro hf
      rw [mem_Bset] at hf
      obtain ⟨⟨w, hw⟩, hvf⟩ := hf
      obtain ⟨hwf, hwe⟩ := hw
      refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
      · rw [hSmem]
        exact ⟨fun hwv => hvf (hwv ▸ hwf), hwe⟩
      · rw [hTmem]
        exact ⟨fun hfe => hvf (hfe.symm ▸ hve), hwf⟩
    · intro hf
      obtain ⟨w, hwS, hwT⟩ := Finset.mem_biUnion.mp hf
      rw [hSmem] at hwS
      rw [hTmem] at hwT
      obtain ⟨hwv, hwe⟩ := hwS
      obtain ⟨hfe, hwf⟩ := hwT
      rw [mem_Bset]
      refine ⟨⟨w, hwf, hwe⟩, fun hvf => ?_⟩
      -- `f ≠ e` and `f ∩ e ∋ w`; if also `v ∈ f` then `f ∩ e ∋ v ≠ w` would not be
      -- subsingleton, so `f = e`, a contradiction
      have hsub : (((f : Set V)) ∩ ((e : Set V))).Subsingleton := hlin f.2 e.2 (hne' hfe)
      exact hwv (hsub ⟨hwf, hwe⟩ ⟨hvf, hve⟩)
  -- the pieces of the partition are pairwise disjoint: a common edge would meet `e` twice
  have hdisj : (↑((eFin 𝓖 e).erase v) : Set V).PairwiseDisjoint
      (fun w => (thruF 𝓖 w).erase e) := by
    intro w₁ hw₁ w₂ hw₂ hne
    change Disjoint ((thruF 𝓖 w₁).erase e) ((thruF 𝓖 w₂).erase e)
    rw [Finset.disjoint_right]
    intro f hf₂ hf₁
    rw [Finset.mem_coe] at hw₁ hw₂
    rw [hSmem] at hw₁ hw₂
    rw [hTmem] at hf₁ hf₂
    have hsub : (((f : Set V)) ∩ ((e : Set V))).Subsingleton := hlin f.2 e.2 (hne' hf₁.1)
    exact hne (hsub ⟨hf₁.2, hw₁.2⟩ ⟨hf₂.2, hw₂.2⟩)
  rw [hEq, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [hSmem] at hw
  -- the edges through `w` other than `e` are exactly `hd 𝓖 w - 1` in number
  rw [Finset.card_erase_of_mem ((mem_thruF 𝓖).mpr hw.2), hd_eq_card_thruF 𝓖 w]

/-- **Upper bound for the blockers**, from an upper bound on the degrees. -/
private theorem bset_card_upper (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖)
    (huni : HUnif 𝓖 r) {v : V} {e : 𝓖} (hve : v ∈ (e : Set V)) {ε D : ℝ} (hε : 0 ≤ ε)
    (hdeg : ∀ w : V, (hd 𝓖 w : ℝ) ≤ (1 + ε) * D) :
    ((Bset 𝓖 v e).card : ℝ) ≤ ((r : ℝ) - 1) * ((1 + ε) * D) := by
  have hcard_e : (eFin 𝓖 e).card = r := by
    rw [card_eFin]; exact huni (e : Set V) e.2
  have hScard : ((eFin 𝓖 e).erase v).card = r - 1 := by
    rw [Finset.card_erase_of_mem (mem_eFin.mpr hve), hcard_e]
  have hcast : ((Bset 𝓖 v e).card : ℝ)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w - 1 : ℕ) : ℝ) := by
    rw [bset_card_eq 𝓖 hlin hve, Nat.cast_sum]
  calc ((Bset 𝓖 v e).card : ℝ)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w - 1 : ℕ) : ℝ) := hcast
    _ ≤ ∑ w ∈ (eFin 𝓖 e).erase v, (hd 𝓖 w : ℝ) :=
        Finset.sum_le_sum fun w _ => Nat.cast_le.mpr (Nat.sub_le _ _)
    _ ≤ ∑ w ∈ (eFin 𝓖 e).erase v, ((1 + ε) * D) :=
        Finset.sum_le_sum fun w _ => hdeg w
    _ = ((r : ℝ) - 1) * ((1 + ε) * D) := by
        rw [Finset.sum_const, hScard, nsmul_eq_mul, Nat.cast_pred (show 0 < r by omega)]

/-- **Lower bound for the blockers**, from a lower bound on the degrees. -/
private theorem bset_card_lower (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖)
    (huni : HUnif 𝓖 r) {v : V} {e : 𝓖} (hve : v ∈ (e : Set V)) {ε D : ℝ} (hε : 0 ≤ ε)
    (hdeg : ∀ w : V, (1 - ε) * D ≤ (hd 𝓖 w : ℝ)) :
    ((r : ℝ) - 1) * ((1 - ε) * D - 1) ≤ ((Bset 𝓖 v e).card : ℝ) := by
  have hcard_e : (eFin 𝓖 e).card = r := by
    rw [card_eFin]; exact huni (e : Set V) e.2
  have hScard : ((eFin 𝓖 e).erase v).card = r - 1 := by
    rw [Finset.card_erase_of_mem (mem_eFin.mpr hve), hcard_e]
  have hcast : ((Bset 𝓖 v e).card : ℝ)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w - 1 : ℕ) : ℝ) := by
    rw [bset_card_eq 𝓖 hlin hve, Nat.cast_sum]
  rw [hcast]
  calc ((r : ℝ) - 1) * ((1 - ε) * D - 1)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((1 - ε) * D - 1) := by
        rw [Finset.sum_const, hScard, nsmul_eq_mul, Nat.cast_pred (show 0 < r by omega)]
    _ ≤ ∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w - 1 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_erase] at hw
        -- `w ∈ e`, so `e` itself is an edge through `w` and `hd 𝓖 w ≥ 1`
        have h1 : 1 ≤ hd 𝓖 w := by
          rw [hd_eq_card_thruF 𝓖 w]
          have : (0:ℕ) < (thruF 𝓖 w).card :=
            Finset.card_pos.mpr ⟨e, (mem_thruF 𝓖).mpr (mem_eFin.mp hw.2)⟩
          omega
        rw [Nat.cast_pred (show 0 < hd 𝓖 w by omega)]
        linarith [hdeg w]

/-- **The global degree sandwich.**  Degrees within `(1±ε)D` force `r|𝓖| = ∑_v hd 𝓖 v` to
lie between `(1-ε)D|V|` and `(1+ε)D|V|`. -/
private theorem sum_hd_sandwich (𝓖 : Set (Set V)) {r : ℕ} (huni : HUnif 𝓖 r) :
    ∀ ε D : ℝ, 0 ≤ ε →
      (∀ v : V, (1 - ε) * D ≤ (hd 𝓖 v : ℝ)) →
      (∀ v : V, (hd 𝓖 v : ℝ) ≤ (1 + ε) * D) →
      (1 - ε) * D * (Fintype.card V : ℝ) ≤ (r : ℝ) * (Nat.card 𝓖 : ℝ)
      ∧ (r : ℝ) * (Nat.card 𝓖 : ℝ) ≤ (1 + ε) * D * (Fintype.card V : ℝ) := by
  intro ε D hε hlo hhi
  have hsum := sum_hd_eq_card_mul 𝓖 huni
  have hcast : (∑ v : V, (hd 𝓖 v : ℝ)) = (r : ℝ) * (Nat.card 𝓖 : ℝ) := by
    rw [← Nat.cast_sum, hsum, Nat.cast_mul]
  constructor
  · calc (1 - ε) * D * (Fintype.card V : ℝ)
        = ∑ v : V, ((1 - ε) * D) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ ∑ v : V, (hd 𝓖 v : ℝ) := Finset.sum_le_sum fun v _ => hlo v
      _ = (r : ℝ) * (Nat.card 𝓖 : ℝ) := hcast
  · calc (r : ℝ) * (Nat.card 𝓖 : ℝ)
        = ∑ v : V, (hd 𝓖 v : ℝ) := hcast.symm
      _ ≤ ∑ v : V, ((1 + ε) * D) := Finset.sum_le_sum fun v _ => hhi v
      _ = (1 + ε) * D * (Fintype.card V : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring

end Combinatorics

theorem r2_comb_count {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ}
    (hr : 1 ≤ r) (hlin : Work.Deep.Nibble.HLin 𝓖) (huni : Work.Deep.Nibble.HUnif 𝓖 r) :
    (∑ v : V, Work.Deep.Nibble.hd 𝓖 v) = r * Nat.card 𝓖
  ∧ (∀ (v : V) (e : 𝓖), v ∈ (e : Set V) →
      (Work.Deep.Nibble.Bset 𝓖 v e).card = ∑ w ∈ (Work.Deep.Nibble.eFin 𝓖 e).erase v, (Work.Deep.Nibble.hd 𝓖 w - 1))
  ∧ (∀ (v : V) (e : 𝓖), v ∈ (e : Set V) → ∀ ε D : ℝ, 0 ≤ ε →
      (∀ w : V, (Work.Deep.Nibble.hd 𝓖 w : ℝ) ≤ (1 + ε) * D) →
      ((Work.Deep.Nibble.Bset 𝓖 v e).card : ℝ) ≤ ((r : ℝ) - 1) * ((1 + ε) * D))
  ∧ (∀ (v : V) (e : 𝓖), v ∈ (e : Set V) → ∀ ε D : ℝ, 0 ≤ ε →
      (∀ w : V, (1 - ε) * D ≤ (Work.Deep.Nibble.hd 𝓖 w : ℝ)) →
      ((r : ℝ) - 1) * ((1 - ε) * D - 1) ≤ ((Work.Deep.Nibble.Bset 𝓖 v e).card : ℝ))
  ∧ (∀ ε D : ℝ, 0 ≤ ε →
      (∀ v : V, (1 - ε) * D ≤ (Work.Deep.Nibble.hd 𝓖 v : ℝ)) →
      (∀ v : V, (Work.Deep.Nibble.hd 𝓖 v : ℝ) ≤ (1 + ε) * D) →
      (1 - ε) * D * (Fintype.card V : ℝ) ≤ (r : ℝ) * (Nat.card 𝓖 : ℝ)
      ∧ (r : ℝ) * (Nat.card 𝓖 : ℝ) ≤ (1 + ε) * D * (Fintype.card V : ℝ)) := by
  refine ⟨sum_hd_eq_card_mul 𝓖 huni, ?_, ?_, ?_, ?_⟩
  · intro v e hve
    exact bset_card_eq 𝓖 hlin hve
  · intro v e hve ε D hε hdeg
    exact bset_card_upper 𝓖 hr hlin huni hve hε hdeg
  · intro v e hve ε D hε hdeg
    exact bset_card_lower 𝓖 hr hlin huni hve hε hdeg
  · intro ε D hε hlo hhi
    exact sum_hd_sandwich 𝓖 huni ε D hε hlo hhi

end Work.Deep.Nibble
