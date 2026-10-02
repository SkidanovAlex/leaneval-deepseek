import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# Lower `(p,ε)`-regular graphs are robust expanders

This module proves `Work.Deep.GKO.robustExpander_lowerReg`: a graph on `n` vertices which is
lower `(p,ε)`-regular in the sense of `Work.Deep.GKO.LowerReg` is a robust `(ε,τ)`-expander
(`Work.Deep.GKO.RobustExpander`), provided

* `2ε ≤ τ` (so that the two sides of the regularity are disjoint enough), and
* `ε < (p - ε)(τ - ε)`, and
* `1 ≤ (τ - ε - ε/(p-ε))n`, which is the room needed to make the two roundings
  `⌈εn⌉` and `⌈εn/(p-ε)⌉` fit inside `S`.

The argument is the one of the paper: if some `S` with `τn ≤ |S| ≤ (1-τ)n` had
`ε`-robust neighbourhood smaller than `|S| + εn`, then `T = V ∖ N_ε(S)` (the vertices with
fewer than `εn` neighbours in `S`) has more than `(τ-ε)n` elements.  Choosing `B ⊆ T` with
`|B| = ⌈εn⌉` and `A ⊆ S ∖ B` with `|A| = ⌈εn/(p-ε)⌉` (both possible by the room hypothesis),
`A` and `B` are disjoint sets of size at least `εn`, so lower regularity gives
`(p-ε)|A||B| ≤ e(A,B)`, while every vertex of `B` has fewer than `εn` neighbours in `S ⊇ A`,
so `e(A,B) < εn|B|`; hence `(p-ε)|A| < εn`, contradicting `|A| ≥ εn/(p-ε)`.

The remaining case `p - ε > 1` is impossible: lower regularity then forbids two disjoint sets
of size `≥ εn` (their edge count is bounded by `|A||B|` above), and if no such pair exists then
`2⌈εn⌉ > n`, which combined with `ε ≤ τ/2 ≤ 1/4` forces `n = 1`, where no `S` satisfies
`τn ≤ |S| ≤ (1-τ)n`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Classical

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Counting lemmas for `crossEdges` -/

/-- `e_G(A,B) = ∑_{b ∈ B} |N(b) ∩ A|`. -/
private theorem crossEdges_eq_sum (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges G A B = ∑ b ∈ B, (A.filter (fun a => G.Adj a b)).card := by
  classical
  have h1 : crossEdges G A B =
      ((A ×ˢ B).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card := rfl
  rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  show (∑ x ∈ A, if G.Adj x b then 1 else 0) = (A.filter (fun a => G.Adj a b)).card
  rw [Finset.card_filter]

/-- `e_G(A,B) ≤ |A| · |B|`. -/
private theorem crossEdges_le_card_mul_card (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges G A B ≤ A.card * B.card := by
  classical
  have h1 : crossEdges G A B =
      ((A ×ˢ B).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card := rfl
  rw [h1]
  calc ((A ×ˢ B).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card
      ≤ (A ×ˢ B).card := Finset.card_filter_le _ _
    _ = A.card * B.card := Finset.card_product A B

/-- A vertex outside the `ε`-robust neighbourhood of `S` has fewer than `εn` neighbours in
`S`. -/
private theorem card_filter_adj_lt_of_notMem_robustNbrs (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {ε : ℝ} {b : Fin n} (hb : b ∉ robustNbrs G ε S) :
    ((S.filter (fun a => G.Adj a b)).card : ℝ) < ε * (n : ℝ) := by
  classical
  have hset : G.neighborSet b ∩ (S : Set (Fin n)) =
      ((S.filter (fun a => G.Adj a b) : Finset (Fin n)) : Set (Fin n)) := by
    ext x
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Finset.mem_filter, Finset.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (SimpleGraph.adj_comm G b x).mp h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(SimpleGraph.adj_comm G b x).mpr h1, h2⟩
  have hncard : ((G.neighborSet b ∩ (S : Set (Fin n))).ncard : ℝ) < ε * (n : ℝ) := by
    rw [robustNbrs] at hb
    simp only [Set.mem_ofPred_eq] at hb
    exact not_le.mp hb
  rw [← Set.ncard_coe_finset, ← hset]
  exact hncard

/-! ## Rounding lemmas -/

/-- If `x + y + 1 ≤ k` then the two roundings `⌈x⌉` and `⌈y⌉` fit inside `k`. -/
private theorem ceil_add_ceil_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ}
    (h : x + y + 1 ≤ (k : ℝ)) : ⌈x⌉₊ + ⌈y⌉₊ ≤ k := by
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  have h3 : ((⌈x⌉₊ + ⌈y⌉₊ : ℕ) : ℝ) < (k : ℝ) + 1 := by push_cast; linarith
  by_contra hcon
  have h4 : k + 1 ≤ ⌈x⌉₊ + ⌈y⌉₊ := by omega
  have h5 : ((k + 1 : ℕ) : ℝ) ≤ ((⌈x⌉₊ + ⌈y⌉₊ : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith

/-- The complement of a vertex set, as a `Finset`, has card `n - |R|`. -/
private theorem card_compl_filter (R : Set (Fin n)) :
    (Finset.univ.filter (fun x => x ∉ R)).card = Nat.card (Fin n) - R.ncard := by
  classical
  have hcoe : ((Finset.univ.filter (fun x => x ∉ R) : Finset (Fin n)) : Set (Fin n)) = Rᶜ := by
    ext x; simp
  have h1 : ((Finset.univ.filter (fun x => x ∉ R) : Finset (Fin n)) : Set (Fin n)).ncard
      = (Finset.univ.filter (fun x => x ∉ R)).card := Set.ncard_coe_finset _
  rw [hcoe, Set.ncard_compl] at h1
  rw [← h1]

/-- A subset of `Fin n` has at most `n` elements. -/
private theorem ncard_le_card (R : Set (Fin n)) : R.ncard ≤ n := by
  have h := Set.ncard_le_ncard (Set.subset_univ R)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-! ## The main theorem -/

end

noncomputable section

/-- A lower `(p,ε)`-regular graph is a robust `(ε,τ)`-expander, provided `2ε ≤ τ`, `ε < (p-ε)(τ-ε)` and there is enough room for the rounding, `1 ≤ (τ - ε - ε/(p-ε)) * n`.

Let `S` satisfy `τn ≤ |S| ≤ (1-τ)n` and let `V∖R` be the complement of the `ε`-robust neighbourhood of `S`; suppose `|R| < |S| + εn`, so `|V∖R| > (τ-ε)n ≥ εn`.  Choose `B ⊆ V∖R` with `⌈εn⌉ ≤ |B|` and then `A ⊆ S ∖ B` with `|A| ≥ εn/(p-ε)` (possible because `|S| - ⌈εn⌉ ≥ τn - εn - 1 ≥ εn/(p-ε)` by the room hypothesis and `|S| ≥ τn`).  Then `A` and `B` are disjoint, `|A|,|B| ≥ εn`, so lower regularity gives `(p-ε)|A||B| ≤ e(A,B)`, while every `b ∈ B ⊆ V∖R` has fewer than `εn` neighbours in `S ⊇ A`, so `e(A,B) < εn|B|`; hence `(p-ε)|A| < εn`, i.e. `|A| < εn/(p-ε)`, a contradiction.

The room hypothesis is needed: without it the statement is false (e.g. `n = 2`, `G = K₂`, `p = 1`, `ε = 1/5`, `τ = 1/2`). -/
theorem robustExpander_lowerReg {n : ℕ} (G : SimpleGraph (Fin n)) {p ε τ : ℝ}
    (hlr : Work.Deep.GKO.LowerReg G p ε) (hε : 0 < ε) (hτ : 0 < τ) (hετ : 2 * ε ≤ τ)
    (hkey : ε < (p - ε) * (τ - ε))
    (hn : 1 ≤ (τ - ε - ε / (p - ε)) * (n : ℝ)) :
    Work.Deep.GKO.RobustExpander G ε τ := by
  classical
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hn
    norm_num at hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnnneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
  have hτε : 0 < τ - ε := by linarith
  have hpε : 0 < p - ε := by
    by_contra h
    have h' : p - ε ≤ 0 := not_lt.mp h
    have h2 : (p - ε) * (τ - ε) ≤ 0 := by
      nlinarith [mul_nonneg (neg_nonneg.mpr h') hτε.le]
    linarith
  rcases le_or_gt (p - ε) 1 with hpe | hpe
  · -- ===== main case: `p - ε ≤ 1` =====
    intro S hS1 hS2
    by_contra hcon
    have hRlt : ((robustNbrs G ε S).ncard : ℝ) < (S.card : ℝ) + ε * (n : ℝ) := not_le.mp hcon
    set RF : Finset (Fin n) := Finset.univ.filter (fun x => x ∉ robustNbrs G ε S) with hRF
    have hRFcard : RF.card = n - (robustNbrs G ε S).ncard := by
      rw [hRF, card_compl_filter, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hRnle : (robustNbrs G ε S).ncard ≤ n := ncard_le_card _
    have hRFcard' : (RF.card : ℝ) = (n : ℝ) - ((robustNbrs G ε S).ncard : ℝ) := by
      rw [hRFcard, Nat.cast_sub hRnle]
    have hRFbig : (τ - ε) * (n : ℝ) < (RF.card : ℝ) := by
      have h1 : τ * (n : ℝ) ≤ (n : ℝ) - (S.card : ℝ) := by linarith [hS2]
      rw [hRFcard']; linarith
    have hRFε : ε * (n : ℝ) ≤ (RF.card : ℝ) := by
      have h1 : ε * (n : ℝ) ≤ (τ - ε) * (n : ℝ) := by nlinarith [hετ, hnnneg]
      linarith
    have hk_le : ⌈ε * (n : ℝ)⌉₊ ≤ RF.card := Nat.ceil_le.mpr hRFε
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hk_le
    have hBε : ε * (n : ℝ) ≤ (B.card : ℝ) := by
      rw [hBcard]; exact Nat.le_ceil _
    have hkpos : 0 < ⌈ε * (n : ℝ)⌉₊ := Nat.ceil_pos.mpr (mul_pos hε hnpos)
    have hBne : B.Nonempty := by rw [← Finset.card_pos, hBcard]; exact hkpos
    have hBpos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard]; exact_mod_cast hkpos
    -- the room hypothesis, rewritten
    have hroom : ε * (n : ℝ) / (p - ε) + ε * (n : ℝ) + 1 ≤ τ * (n : ℝ) := by
      have h := hn
      have hx : (τ - ε - ε / (p - ε)) * (n : ℝ)
          = τ * (n : ℝ) - ε * (n : ℝ) - ε * (n : ℝ) / (p - ε) := by ring
      rw [hx] at h
      linarith
    have hAroom : ⌈ε * (n : ℝ) / (p - ε)⌉₊ + ⌈ε * (n : ℝ)⌉₊ ≤ S.card :=
      ceil_add_ceil_le (by positivity) (by positivity) (by linarith [hroom, hS1])
    have hSBcard : ⌈ε * (n : ℝ) / (p - ε)⌉₊ ≤ (S \ B).card := by
      have h1 : (S \ B).card = S.card - (B ∩ S).card := Finset.card_sdiff
      have h2 : (B ∩ S).card ≤ B.card := Finset.card_le_card Finset.inter_subset_left
      omega
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hSBcard
    have hAS : A ⊆ S := fun a ha => (Finset.mem_sdiff.mp (hAsub ha)).1
    have hAdisj : Disjoint A B := Finset.disjoint_of_subset_left hAsub Finset.sdiff_disjoint
    have hAε : ε * (n : ℝ) ≤ (A.card : ℝ) := by
      rw [hAcard]
      have h1 : ε * (n : ℝ) ≤ ε * (n : ℝ) / (p - ε) := by
        rw [le_div_iff₀ hpε]
        nlinarith [mul_nonneg (mul_pos hε hnpos).le (sub_nonneg.mpr hpe)]
      have h2 : ε * (n : ℝ) / (p - ε) ≤ (⌈ε * (n : ℝ) / (p - ε)⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    have hlow : (p - ε) * (A.card : ℝ) * (B.card : ℝ) ≤ (crossEdges G A B : ℝ) :=
      hlr A B hAdisj hAε hBε
    have hbnd : ∀ b ∈ B, ((S.filter (fun a => G.Adj a b)).card : ℝ) < ε * (n : ℝ) := by
      intro b hb
      refine card_filter_adj_lt_of_notMem_robustNbrs G S ?_
      have hb' : b ∈ Finset.univ.filter (fun x => x ∉ robustNbrs G ε S) := by
        rw [← hRF]; exact hBsub hb
      simpa using hb'
    have hup : (crossEdges G A B : ℝ) < ε * (n : ℝ) * (B.card : ℝ) := by
      have hsum1 : crossEdges G A B ≤ ∑ b ∈ B, (S.filter (fun a => G.Adj a b)).card := by
        rw [crossEdges_eq_sum]
        exact Finset.sum_le_sum
          (fun b _ => Finset.card_le_card (Finset.filter_subset_filter _ hAS))
      have h3 : (∑ b ∈ B, ((S.filter (fun a => G.Adj a b)).card : ℝ))
          < ∑ b ∈ B, (ε * (n : ℝ)) :=
        Finset.sum_lt_sum_of_nonempty hBne (fun b hb => hbnd b hb)
      have h4 : (∑ b ∈ B, (ε * (n : ℝ))) = (B.card : ℝ) * (ε * (n : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      calc (crossEdges G A B : ℝ)
          ≤ ((∑ b ∈ B, (S.filter (fun a => G.Adj a b)).card : ℕ) : ℝ) := by
            exact_mod_cast hsum1
        _ = ∑ b ∈ B, ((S.filter (fun a => G.Adj a b)).card : ℝ) := by push_cast; ring
        _ < ∑ b ∈ B, (ε * (n : ℝ)) := h3
        _ = (B.card : ℝ) * (ε * (n : ℝ)) := h4
        _ = ε * (n : ℝ) * (B.card : ℝ) := by ring
    have hkey2 : (p - ε) * (A.card : ℝ) < ε * (n : ℝ) := by
      have h1 : (p - ε) * (A.card : ℝ) * (B.card : ℝ) < ε * (n : ℝ) * (B.card : ℝ) :=
        lt_of_le_of_lt hlow hup
      exact lt_of_mul_lt_mul_right h1 hBpos.le
    have hAge : ε * (n : ℝ) ≤ (p - ε) * (A.card : ℝ) := by
      have h1 : ε * (n : ℝ) / (p - ε) ≤ (A.card : ℝ) := by
        rw [hAcard]; exact Nat.le_ceil _
      have h2 : (p - ε) * (ε * (n : ℝ) / (p - ε)) = ε * (n : ℝ) := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hpε)
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 hpε.le
    linarith
  · -- ===== case `1 < p - ε` =====
    rcases Nat.lt_or_ge n (2 * ⌈ε * (n : ℝ)⌉₊) with h2k | h2k
    · -- `n < 2⌈εn⌉`: no `S` can exist
      intro S hS1 hS2
      have hτhalf : τ ≤ 1 / 2 := by nlinarith [hS1, hS2, hnpos]
      have hεq : ε ≤ 1 / 4 := by nlinarith [hετ, hτhalf]
      have h2k' : n + 1 ≤ 2 * ⌈ε * (n : ℝ)⌉₊ := by omega
      have hceil : (⌈ε * (n : ℝ)⌉₊ : ℝ) < ε * (n : ℝ) + 1 :=
        Nat.ceil_lt_add_one (mul_pos hε hnpos).le
      have hbig : (n : ℝ) - 1 < 2 * (ε * (n : ℝ)) := by
        have hc : ((n + 1 : ℕ) : ℝ) ≤ ((2 * ⌈ε * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast h2k'
        push_cast at hc
        linarith
      have hsmall2 : 2 * (ε * (n : ℝ)) ≤ (n : ℝ) / 2 := by nlinarith [hεq, hnpos]
      have hnlt : n < 2 := by
        have : (n : ℝ) < 2 := by linarith
        exact_mod_cast this
      have hn1' : n = 1 := by omega
      subst hn1'
      have hSle1 : S.card ≤ 1 := by
        have h := Finset.card_le_univ S
        rwa [Fintype.card_fin] at h
      norm_num at hS1 hS2
      have hSpos : (0 : ℝ) < (S.card : ℝ) := by linarith
      have hSge1 : 1 ≤ S.card := by
        have : 0 < S.card := by exact_mod_cast hSpos
        omega
      have hSle1' : (S.card : ℝ) ≤ 1 := by exact_mod_cast hSle1
      have hSge1' : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hSge1
      linarith
    · -- `2⌈εn⌉ ≤ n`: lower regularity forbids two disjoint sets of size `≥ εn`
      have hk_le_n : ⌈ε * (n : ℝ)⌉₊ ≤ n := by omega
      have hkpos : 0 < ⌈ε * (n : ℝ)⌉₊ := Nat.ceil_pos.mpr (mul_pos hε hnpos)
      obtain ⟨A₀, hA₀sub, hA₀card⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := ⌈ε * (n : ℝ)⌉₊)
        (by rw [Finset.card_univ, Fintype.card_fin]; exact hk_le_n)
      have hroom' : ⌈ε * (n : ℝ)⌉₊ ≤ ((Finset.univ : Finset (Fin n)) \ A₀).card := by
        have h1 : ((Finset.univ : Finset (Fin n)) \ A₀).card = n - ⌈ε * (n : ℝ)⌉₊ := by
          rw [Finset.card_sdiff, Finset.inter_univ, hA₀card, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨B₀, hB₀sub, hB₀card⟩ := Finset.exists_subset_card_eq hroom'
      have hdisj : Disjoint A₀ B₀ :=
        (Finset.disjoint_of_subset_left hB₀sub Finset.sdiff_disjoint).symm
      have hA₀ε : ε * (n : ℝ) ≤ (A₀.card : ℝ) := by rw [hA₀card]; exact Nat.le_ceil _
      have hB₀ε : ε * (n : ℝ) ≤ (B₀.card : ℝ) := by rw [hB₀card]; exact Nat.le_ceil _
      have hA₀pos : (0 : ℝ) < (A₀.card : ℝ) := by rw [hA₀card]; exact_mod_cast hkpos
      have hB₀pos : (0 : ℝ) < (B₀.card : ℝ) := by rw [hB₀card]; exact_mod_cast hkpos
      have hcontra : p - ε ≤ 1 := by
        have h1 := hlr A₀ B₀ hdisj hA₀ε hB₀ε
        have h2 : (crossEdges G A₀ B₀ : ℝ) ≤ (A₀.card : ℝ) * (B₀.card : ℝ) := by
          exact_mod_cast crossEdges_le_card_mul_card G A₀ B₀
        have hpos : 0 < (A₀.card : ℝ) * (B₀.card : ℝ) := mul_pos hA₀pos hB₀pos
        nlinarith [h1, h2, hpos]
      exact absurd hcontra (not_le.mpr hpe)

end

end Work.Deep.GKO
