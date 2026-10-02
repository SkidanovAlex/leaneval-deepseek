import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Prob.Colouring.card_weighted_dev_le

/-!
# A balanced `K`-fold partition of the edges of a multi-hypergraph

This file proves `Work.Deep.Nibble.exists_edgePartition`: the edges of a multi-hypergraph
`𝓜` on `Fin n` can be split into `K` parts so that every part has, at every vertex `w`,
degree within a `δ`-fraction of the average `d_𝓜(w)/K`.

The proof is the probabilistic method.  We colour every "item" — every proper edge, and
every copy of every singleton edge — independently and uniformly with one of the `K` parts,
and let `part i` consist of the items receiving colour `i`.  For a fixed part `i` and vertex
`w`, the degree of `part i` at `w` is a sum of independent Bernoulli(`1/K`) variables, one
for each item through `w`; the two-sided weighted Chernoff bound
(`Work.Deep.Prob.Colouring.card_weighted_dev_le`) bounds the number of colourings on which
this degree deviates by more than `δ d_𝓜(w)/K` from its mean `d_𝓜(w)/K` by
`K ^ #items * 2 * exp (-3 δ ^ 2 (1-β)D / (8K))`.  Summing over the `nK` pairs `(w, i)` and
using the hypothesis on the union bound, fewer than `K ^ #items` colourings are bad, so a
good one exists.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The items to be coloured -/

/-- The index type of the items to be coloured: one slot for each set of vertices (the slot
is "used" only when the set is a proper edge of `𝓜`) together with one slot for each copy of
each singleton edge. -/
abbrev Item (𝓜 : MultiHypergraph n) : Type := Set (Fin n) ⊕ (Σ w : Fin n, Fin (𝓜.singles w))

/-- The items "through" the vertex `w`: the slots of the proper edges containing `w`, and the
slots of the singleton copies at `w`. -/
def isThrough (𝓜 : MultiHypergraph n) (w : Fin n) (r : Item 𝓜) : Prop :=
  (∃ e : Set (Fin n), r = Sum.inl e ∧ e ∈ 𝓜.edges ∧ w ∈ e) ∨
    (∃ j : Fin (𝓜.singles w), r = Sum.inr ⟨w, j⟩)

/-- The indicator of the items through `w`, as a real weight. -/
noncomputable def throughW (𝓜 : MultiHypergraph n) (w : Fin n) (r : Item 𝓜) : ℝ :=
  if isThrough 𝓜 w r then 1 else 0

/-- The `i`-th part of the partition induced by a colouring `c` of the items. -/
def partOf (𝓜 : MultiHypergraph n) {K : ℕ} (c : Item 𝓜 → Fin K) (i : Fin K) :
    MultiHypergraph n where
  edges := {e | e ∈ 𝓜.edges ∧ c (Sum.inl e) = i}
  singles := fun w =>
    ((Finset.univ : Finset (Fin (𝓜.singles w))).filter (fun j => c (Sum.inr ⟨w, j⟩) = i)).card

/-! ## The items through a vertex -/

lemma isThrough_inl (𝓜 : MultiHypergraph n) (w : Fin n) (e : Set (Fin n)) :
    isThrough 𝓜 w (Sum.inl e) ↔ e ∈ 𝓜.edges ∧ w ∈ e := by
  constructor
  · rintro (⟨e', he', he, hw⟩ | ⟨j, h⟩)
    · rw [Sum.inl.injEq] at he'
      rw [he']
      exact ⟨he, hw⟩
    · exact absurd h (by simp)
  · rintro ⟨he, hw⟩
    exact Or.inl ⟨e, rfl, he, hw⟩

lemma isThrough_inr (𝓜 : MultiHypergraph n) (w : Fin n)
    (s : Σ w' : Fin n, Fin (𝓜.singles w')) :
    isThrough 𝓜 w (Sum.inr s) ↔ s.1 = w := by
  constructor
  · rintro (⟨e, he, -, -⟩ | ⟨j, h⟩)
    · exact absurd he (by simp)
    · have h' : s = ⟨w, j⟩ := Sum.inr.inj h
      rw [h']
  · intro h
    obtain ⟨w', j⟩ := s
    simp only at h
    subst h
    exact Or.inr ⟨j, rfl⟩

/-- A sum over the sigma type of single copies, restricted to the copies at `w`. -/
lemma sum_sigma_ite (𝓜 : MultiHypergraph n) (w : Fin n)
    (f : (w' : Fin n) → Fin (𝓜.singles w') → ℝ) :
    (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'), (if s.1 = w then f s.1 s.2 else 0))
      = ∑ j : Fin (𝓜.singles w), f w j := by
  rw [Fintype.sum_sigma]
  have hinner : ∀ w' : Fin n,
      (∑ j : Fin (𝓜.singles w'), (if (⟨w', j⟩ : Σ w' : Fin n, Fin (𝓜.singles w')).1 = w
          then f w' j else 0))
        = (if w' = w then ∑ j : Fin (𝓜.singles w'), f w' j else 0) := by
    intro w'
    by_cases h : w' = w
    · rw [if_pos h]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_pos h]
    · rw [if_neg h, Finset.sum_eq_zero]
      intro j _
      rw [if_neg]
      intro hc
      exact h hc
  rw [Finset.sum_congr rfl (fun w' _ => hinner w'), Finset.sum_ite_eq']
  simp

lemma sum_sigma_through (𝓜 : MultiHypergraph n) (w : Fin n) {K : ℕ}
    (c : Item 𝓜 → Fin K) (i : Fin K) :
    (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'),
        (if isThrough 𝓜 w (Sum.inr s) ∧ c (Sum.inr s) = i then (1 : ℝ) else 0))
      = (∑ j : Fin (𝓜.singles w),
        (if c (Sum.inr (⟨w, j⟩ : Σ w' : Fin n, Fin (𝓜.singles w'))) = i then (1 : ℝ)
          else 0)) := by
  trans (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'),
      (if s.1 = w then (if c (Sum.inr s) = i then (1 : ℝ) else 0) else 0))
  · apply Finset.sum_congr rfl
    intro s _
    by_cases h : s.1 = w
    · rw [if_pos h]
      by_cases hc : c (Sum.inr s) = i
      · rw [if_pos hc, if_pos ⟨(isThrough_inr 𝓜 w s).mpr h, hc⟩]
      · rw [if_neg hc, if_neg (fun hh => hc hh.2)]
    · rw [if_neg h, if_neg (fun hh => h ((isThrough_inr 𝓜 w s).mp hh.1))]
  · exact sum_sigma_ite 𝓜 w (fun w' j => if c (Sum.inr ⟨w', j⟩) = i then (1 : ℝ) else 0)

lemma sum_inl_through (𝓜 : MultiHypergraph n) (w : Fin n) {K : ℕ}
    (c : Item 𝓜 → Fin K) (i : Fin K) :
    (∑ e : Set (Fin n),
        (if isThrough 𝓜 w (Sum.inl e) ∧ c (Sum.inl e) = i then (1 : ℝ) else 0))
      = (∑ e : Set (Fin n),
        (if (e ∈ 𝓜.edges ∧ c (Sum.inl e) = i) ∧ w ∈ e then (1 : ℝ) else 0)) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : (e ∈ 𝓜.edges ∧ c (Sum.inl e) = i) ∧ w ∈ e
  · rw [if_pos h, if_pos (by rw [isThrough_inl]; tauto)]
  · rw [if_neg h, if_neg (by rw [isThrough_inl]; tauto)]

/-- The degree in a family of edges, as a filtered cardinality. -/
lemma hdeg_bridge (R : Set (Set (Fin n))) (w : Fin n) :
    MultiHypergraph.hdeg R w =
      (Finset.univ.filter (fun e : Set (Fin n) => e ∈ R ∧ w ∈ e)).card := by
  rw [MultiHypergraph.hdeg, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-! ## The degree of a part -/

/-- The degree of `partOf 𝓜 c i` at `w` is the number of items through `w` receiving the
colour `i`. -/
lemma deg_partOf_card (𝓜 : MultiHypergraph n) {K : ℕ} (c : Item 𝓜 → Fin K) (i : Fin K)
    (w : Fin n) :
    (partOf 𝓜 c i).deg w
      = (Finset.univ.filter (fun r : Item 𝓜 => isThrough 𝓜 w r ∧ c r = i)).card := by
  rw [MultiHypergraph.deg_def]
  have hA : MultiHypergraph.hdeg (partOf 𝓜 c i).edges w
      = (Finset.univ.filter (fun e : Set (Fin n) =>
          (e ∈ 𝓜.edges ∧ c (Sum.inl e) = i) ∧ w ∈ e)).card := by
    rw [hdeg_bridge]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro e _
    rw [partOf, Set.mem_ofPred_eq]
  rw [hA]
  have hcast : ((((Finset.univ.filter (fun e : Set (Fin n) =>
        (e ∈ 𝓜.edges ∧ c (Sum.inl e) = i) ∧ w ∈ e)).card
      + (Finset.univ.filter (fun j : Fin (𝓜.singles w) =>
          c (Sum.inr ⟨w, j⟩) = i)).card) : ℕ) : ℝ)
      = ((Finset.univ.filter (fun r : Item 𝓜 => isThrough 𝓜 w r ∧ c r = i)).card : ℝ) := by
    push_cast
    rw [← Finset.sum_boole (fun e : Set (Fin n) =>
          (e ∈ 𝓜.edges ∧ c (Sum.inl e) = i) ∧ w ∈ e) Finset.univ,
      ← Finset.sum_boole (fun j : Fin (𝓜.singles w) => c (Sum.inr ⟨w, j⟩) = i) Finset.univ,
      ← Finset.sum_boole (fun r : Item 𝓜 => isThrough 𝓜 w r ∧ c r = i) Finset.univ,
      Fintype.sum_sum_type]
    rw [← sum_inl_through 𝓜 w c i, ← sum_sigma_through 𝓜 w c i]
  exact_mod_cast hcast

/-- The total weight of the items through `w` is the degree of `w`. -/
lemma through_sum (𝓜 : MultiHypergraph n) (w : Fin n) :
    (∑ r : Item 𝓜, throughW 𝓜 w r) = (𝓜.deg w : ℝ) := by
  rw [show (∑ r : Item 𝓜, throughW 𝓜 w r)
      = (∑ e : Set (Fin n), (if isThrough 𝓜 w (Sum.inl e) then (1 : ℝ) else 0))
        + (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'),
            (if isThrough 𝓜 w (Sum.inr s) then (1 : ℝ) else 0)) by
      rw [Fintype.sum_sum_type]
      rfl]
  rw [show (∑ e : Set (Fin n), (if isThrough 𝓜 w (Sum.inl e) then (1 : ℝ) else 0))
      = (∑ e : Set (Fin n), (if e ∈ 𝓜.edges ∧ w ∈ e then (1 : ℝ) else 0)) from
      Finset.sum_congr rfl (fun e _ => by
        by_cases h : e ∈ 𝓜.edges ∧ w ∈ e
        · rw [if_pos h, if_pos ((isThrough_inl 𝓜 w e).mpr h)]
        · rw [if_neg h, if_neg (fun hc => h ((isThrough_inl 𝓜 w e).mp hc))])]
  rw [show (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'),
        (if isThrough 𝓜 w (Sum.inr s) then (1 : ℝ) else 0))
      = (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'), (if s.1 = w then (1 : ℝ) else 0)) from
      Finset.sum_congr rfl (fun s _ => by
        by_cases h : s.1 = w
        · rw [if_pos h, if_pos ((isThrough_inr 𝓜 w s).mpr h)]
        · rw [if_neg h, if_neg (fun hc => h ((isThrough_inr 𝓜 w s).mp hc))])]
  rw [show (∑ s : Σ w' : Fin n, Fin (𝓜.singles w'), (if s.1 = w then (1 : ℝ) else 0))
      = (𝓜.singles w : ℝ) from by
      rw [sum_sigma_ite 𝓜 w (fun _ _ => (1 : ℝ))]
      simp]
  rw [Finset.sum_boole, ← hdeg_bridge 𝓜.edges w, MultiHypergraph.deg_def]
  push_cast
  ring

/-- The degree of `partOf 𝓜 c i` at `w`, as the weighted sum of indicators used in the
Chernoff bound. -/
lemma deg_partOf_eq_sum (𝓜 : MultiHypergraph n) {K : ℕ} (c : Item 𝓜 → Fin K) (i : Fin K)
    (w : Fin n) :
    ((partOf 𝓜 c i).deg w : ℝ)
      = ∑ r : Item 𝓜, (if c r = i then throughW 𝓜 w r else 0) := by
  rw [deg_partOf_card]
  rw [← Finset.sum_boole (fun r : Item 𝓜 => isThrough 𝓜 w r ∧ c r = i) Finset.univ]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : isThrough 𝓜 w r ∧ c r = i
  · rw [if_pos h, throughW, if_pos h.1, if_pos h.2]
  · rw [if_neg h]
    by_cases h1 : c r = i
    · rw [throughW, if_pos h1, if_neg (fun hs => h ⟨hs, h1⟩)]
    · rw [if_neg h1]

/-- The degrees of the parts sum to the degree of `𝓜` at every vertex. -/
lemma deg_sum_partOf (𝓜 : MultiHypergraph n) {K : ℕ} (c : Item 𝓜 → Fin K) (w : Fin n) :
    (∑ i : Fin K, (partOf 𝓜 c i).deg w) = 𝓜.deg w := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => deg_partOf_eq_sum 𝓜 c i w), Finset.sum_comm]
  trans (∑ r : Item 𝓜, throughW 𝓜 w r)
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_ite_eq]
    simp
  · exact through_sum 𝓜 w

/-- The `K`-fold partition of the edges of `𝓜` induced by a colouring of the items. -/
def partitionOf (𝓜 : MultiHypergraph n) {K : ℕ} (c : Item 𝓜 → Fin K) : EdgePartition 𝓜 K where
  part i := partOf 𝓜 c i
  le i := ⟨fun _ he => he.1, fun w => by
    show ((Finset.univ : Finset (Fin (𝓜.singles w))).filter
        (fun j => c (Sum.inr ⟨w, j⟩) = i)).card ≤ 𝓜.singles w
    calc ((Finset.univ : Finset (Fin (𝓜.singles w))).filter
          (fun j => c (Sum.inr ⟨w, j⟩) = i)).card
        ≤ (Finset.univ : Finset (Fin (𝓜.singles w))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 𝓜.singles w := by simp⟩
  edges_cover e he := ⟨c (Sum.inl e), ⟨he, rfl⟩, fun i hi => hi.2.symm⟩
  deg_sum w := deg_sum_partOf 𝓜 c w

/-! ## The counting inequality

The counting inequality used below is `Work.Deep.Prob.Colouring.card_weighted_dev_le`,
proved in `Submission/Work/Deep/Prob/Colouring/card_weighted_dev_le.lean` (imported above):
colouring a finite set independently and uniformly with `K` colours, the number of colourings
whose `i`-coloured weight deviates from its mean by at least `τ` is at most
`K ^ #ι * 2 * exp (-(τ ^ 2) / (2 * C * (mean + τ / 3)))`. -/

/-! ## The arithmetic of the exponent -/

lemma exp_arg_le {m D δ β K : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hm0 : 0 ≤ m)
    (hm : (1 - β) * D ≤ m) :
    3 * δ ^ 2 * ((1 - β) * D) / (8 * K)
      ≤ (δ * (m / K)) ^ 2 / (2 * 1 * (m / K + (δ * (m / K)) / 3)) := by
  rw [show (2 : ℝ) * 1 * (m / K + (δ * (m / K)) / 3)
      = 2 * (m / K + (δ * (m / K)) / 3) by ring]
  rcases eq_or_lt_of_le hm0 with h | hpos
  · subst h
    have hnum : 3 * δ ^ 2 * ((1 - β) * D) ≤ 0 := by
      have : (1 - β) * D ≤ 0 := by simpa using hm
      nlinarith [sq_nonneg δ]
    rw [show (δ * (0 / K)) ^ 2 / (2 * (0 / K + (δ * (0 / K)) / 3)) = 0 by norm_num]
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  · have hA : (δ * (m / K)) ^ 2 / (2 * (m / K + (δ * (m / K)) / 3))
        = 3 * δ ^ 2 * m / (2 * K * (δ + 3)) := by
      field_simp
      ring
    rw [hA]
    have hδ3 : (0 : ℝ) < δ + 3 := by linarith
    have hkey : (1 - β) * D * (δ + 3) ≤ 4 * m := by
      have h1 : (1 - β) * D * (δ + 3) ≤ m * (δ + 3) :=
        mul_le_mul_of_nonneg_right hm (by linarith)
      have h2 : m * (δ + 3) ≤ m * 4 := mul_le_mul_of_nonneg_left (by linarith) hm0
      linarith
    have h1 : (0 : ℝ) < 8 * K := by positivity
    have h2 : (0 : ℝ) < 2 * K * (δ + 3) := by positivity
    rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
    have h4 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 6 * δ ^ 2 * K)
    nlinarith [h4]

/-! ## The main theorem -/

theorem exists_edgePartition {n : ℕ} (𝓜 : ErdosFaberLovaszConjecture.MultiHypergraph n)
    {K : ℕ} (hK : 2 ≤ K)
    {β D δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hβ : β ≤ 1 / 2)
    (hdeg : ∀ w : Fin n, |((𝓜.deg w : ℝ)) - D| ≤ β * D)
    (hbound : 2 * ((n : ℝ) * (K : ℝ)) *
      Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ))) < 1) :
    ∃ P : ErdosFaberLovaszConjecture.EdgePartition 𝓜 K, ∀ i w,
      |(((P.part i).deg w : ℝ)) - (𝓜.deg w : ℝ) / (K : ℝ)| ≤
        δ * ((𝓜.deg w : ℝ) / (K : ℝ)) := by
  classical
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  -- The family of bad colourings, one per pair `(part, vertex)`.
  set badF : Fin K × Fin n → Finset (Item 𝓜 → Fin K) := fun p =>
    Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
      δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
        |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
          - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|) with hbadF
  -- Each `badF p` has at most `K ^ #items * 2 exp (-3δ²(1-β)D/(8K))` colourings.
  have hper : ∀ p : Fin K × Fin n, ((badF p).card : ℝ)
      ≤ (K : ℝ) ^ (Fintype.card (Item 𝓜)) *
          (2 * Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ)))) := by
    rintro ⟨i, w⟩
    have hm : (1 - β) * D ≤ (𝓜.deg w : ℝ) := by
      have h := hdeg w
      rw [abs_le] at h
      linarith [h.1]
    have hdw : (0 : ℝ) ≤ (𝓜.deg w : ℝ) := Nat.cast_nonneg _
    have hcle := Work.Deep.Prob.Colouring.card_weighted_dev_le (ι := Item 𝓜) hK (throughW 𝓜 w)
      (fun r => by rw [throughW]; split_ifs <;> norm_num)
      (C := 1) (by norm_num) (fun r => by rw [throughW]; split_ifs <;> norm_num)
      i (τ := δ * ((𝓜.deg w : ℝ) / (K : ℝ))) (by positivity)
    refine le_trans hcle ?_
    rw [through_sum 𝓜 w]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact exp_arg_le hKpos hδ0 hδ1 hdw hm
  -- Union bound.
  have hBad : ((Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
      ∃ p : Fin K × Fin n,
        δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
          |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
            - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|)).card : ℝ)
      < (K : ℝ) ^ (Fintype.card (Item 𝓜)) := by
    have hsub : (Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
          ∃ p : Fin K × Fin n,
            δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
              |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
                - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|))
        ⊆ Finset.univ.biUnion badF := by
      intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨-, p, hp⟩ := hc
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_univ p, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hp⟩⟩
    have hbound' : ((n : ℝ) * (K : ℝ)) *
        (2 * Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ)))) < 1 := by
      have h := hbound
      ring_nf at h ⊢
      linarith [h]
    have hpow : (0 : ℝ) < (K : ℝ) ^ (Fintype.card (Item 𝓜)) := by positivity
    calc ((Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
              ∃ p : Fin K × Fin n,
                δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
                  |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
                    - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|)).card : ℝ)
        ≤ ((Finset.univ.biUnion badF).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((∑ p : Fin K × Fin n, (badF p).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ p : Fin K × Fin n, ((badF p).card : ℝ) := by push_cast; ring
      _ ≤ ∑ _p : Fin K × Fin n,
            ((K : ℝ) ^ (Fintype.card (Item 𝓜)) *
              (2 * Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ))))) :=
          Finset.sum_le_sum (fun p _ => hper p)
      _ = ((K : ℝ) * (n : ℝ)) *
            ((K : ℝ) ^ (Fintype.card (Item 𝓜)) *
              (2 * Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ))))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ = (((n : ℝ) * (K : ℝ)) *
              (2 * Real.exp (-(3 * δ ^ 2 * ((1 - β) * D)) / (8 * (K : ℝ))))) *
            (K : ℝ) ^ (Fintype.card (Item 𝓜)) := by ring
      _ < 1 * (K : ℝ) ^ (Fintype.card (Item 𝓜)) :=
          mul_lt_mul_of_pos_right hbound' hpow
      _ = (K : ℝ) ^ (Fintype.card (Item 𝓜)) := by ring
  -- A good colouring exists.
  have hssub : (Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
      ∃ p : Fin K × Fin n,
        δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
          |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
            - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|)) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro huniv
    have hcard : ((Finset.univ.filter (fun c : Item 𝓜 → Fin K =>
        ∃ p : Fin K × Fin n,
          δ * ((𝓜.deg p.2 : ℝ) / (K : ℝ)) ≤
            |(∑ r : Item 𝓜, (if c r = p.1 then throughW 𝓜 p.2 r else 0))
              - (∑ r : Item 𝓜, throughW 𝓜 p.2 r) / (K : ℝ)|)).card : ℝ)
        = (K : ℝ) ^ (Fintype.card (Item 𝓜)) := by
      rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      push_cast
      ring
    linarith [hBad, hcard]
  obtain ⟨c, -, hc⟩ := Finset.exists_of_ssubset hssub
  refine ⟨partitionOf 𝓜 c, fun i w => ?_⟩
  have hgood : ¬ (δ * ((𝓜.deg w : ℝ) / (K : ℝ)) ≤
      |(∑ r : Item 𝓜, (if c r = i then throughW 𝓜 w r else 0))
        - (∑ r : Item 𝓜, throughW 𝓜 w r) / (K : ℝ)|) := by
    intro hcon
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨(i, w), hcon⟩⟩)
  have hlt := not_le.mp hgood
  rw [← deg_partOf_eq_sum 𝓜 c i w, through_sum 𝓜 w] at hlt
  show |(((partOf 𝓜 c i).deg w : ℝ)) - (𝓜.deg w : ℝ) / (K : ℝ)| ≤
    δ * ((𝓜.deg w : ℝ) / (K : ℝ))
  exact le_of_lt hlt

end

end Work.Deep.Nibble
