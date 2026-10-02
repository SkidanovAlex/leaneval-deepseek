import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# `δ(G) ≥ pn/2` for a lower `(p,ε)`-regular, near-regular graph

This module proves `Work.Deep.GKO.minDeg_ge_of_lowerReg`: for a graph `G` on `n` vertices
which is lower `(p,ε)`-regular (`LowerReg G p ε`) and whose degrees differ from the maximum
degree by at most `νn`, with `3ε + ν ≤ p/2` and `εn ≥ 1`, `ε ≤ 1/3`, `ε ≤ p ≤ 1`, the
minimum degree satisfies `δ(G) ≥ pn/2`.

The proof combines the maximum-degree bound `Δ(G) ≥ (p - 3ε)n` (proved here as
`maxDeg_ge_of_lowerReg_aux`, the graph-language form of
`ErdosFaberLovaszConjecture.maxDegree_ge_of_selfLowerRegular` from `Submission/EFL/OptCol.lean`)
with the near-regularity hypothesis `Δ - d(v) ≤ νn` at a vertex `v` realising the minimum
degree (such a vertex exists because `ℕ` is well-ordered and `n ≥ 1`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Elementary degree bounds -/

/-- Every degree is at most the maximum degree. -/
theorem card_neighborSet_le_maxDeg (G : SimpleGraph (Fin n)) (v : Fin n) :
    Nat.card (G.neighborSet v) ≤ maxDeg G := by
  rw [maxDeg]
  exact Finset.le_sup (s := Finset.univ) (f := fun v => Nat.card (G.neighborSet v))
    (Finset.mem_univ v)

/-- The number of edges between `A` and `B` is at most the sum of the degrees over `A`:
each edge of `G` between `A` and `B` is counted in the degree of its endpoint in `A`. -/
theorem crossEdges_le_sum_card_neighborSet (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges G A B ≤ ∑ a ∈ A, Nat.card (G.neighborSet a) := by
  classical
  have h1 : crossEdges G A B = ∑ a ∈ A, (B.filter (fun b => G.Adj a b)).card := by
    unfold crossEdges
    rw [show (A.product B : Finset (Fin n × Fin n)) = A ×ˢ B from rfl]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.1) (t := A)]
    swap
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp', hpa⟩ := hp
      rw [Finset.mem_filter, Finset.mem_product] at hp'
      obtain ⟨⟨hpA, hpB⟩, hpP⟩ := hp'
      rw [hpa] at hpP
      rw [Finset.mem_filter]
      exact ⟨hpB, hpP⟩
    · intro p hp q hq hpq
      rw [Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) hpq
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨(a, b), by
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨ha, hb.1⟩, hb.2⟩, rfl⟩, rfl⟩
  rw [h1]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun b hb => ?_) (Set.toFinite _)
  rw [Finset.mem_coe, Finset.mem_filter] at hb
  exact (SimpleGraph.mem_neighborSet G a b).mpr hb.2

/-! ## The maximum-degree bound -/

/-- **Lower regularity gives `Δ ≥ (p - 3ε)n`.**  Graph-language form of
`ErdosFaberLovaszConjecture.maxDegree_ge_of_selfLowerRegular` (which is also the statement of
the companion lemma `Work.Deep.GKO.maxDeg_ge_of_lowerReg`).

The argument splits off a set `V₁` of `⌈εn⌉` vertices and uses lower regularity between `V₁`
and its complement `V₂`: `e(V₁,V₂) ≥ (p-ε)|V₁||V₂| ≥ (p-ε)(1-2ε)n|V₁|`, while
`e(V₁,V₂) ≤ |V₁|Δ`.  Dividing by `|V₁| > 0` and using `2ε² ≥ 0` gives the claim. -/
theorem maxDeg_ge_of_lowerReg_aux {n : ℕ} (G : SimpleGraph (Fin n)) {p ε : ℝ}
    (hlr : LowerReg G p ε) (hεn : 1 ≤ ε * (n : ℝ)) (hε1 : ε ≤ 1 / 3)
    (hεp : ε ≤ p) (hp1 : p ≤ 1) (hn : 1 ≤ n) :
    (p - 3 * ε) * (n : ℝ) ≤ (maxDeg G : ℝ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hεn0 : (0 : ℝ) < ε * n := lt_of_lt_of_le zero_lt_one hεn
  have hfloor : ⌈ε * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith [hε1, hnR])
  obtain ⟨V₁, -, hV₁card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := ⌈ε * (n : ℝ)⌉₊)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hfloor)
  set V₂ : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ V₁ with hV₂
  have hdisj : Disjoint V₁ V₂ := by
    rw [hV₂, Finset.disjoint_left]
    intro v hv1 hv2
    exact (Finset.mem_sdiff.mp hv2).2 hv1
  have hV₁ge : ε * (n : ℝ) ≤ (V₁.card : ℝ) := by
    rw [hV₁card]; exact_mod_cast Nat.le_ceil (ε * (n : ℝ))
  have hceil_lt : ((⌈ε * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤ ε * (n : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt hεn0)
    linarith
  have hV₂card : (V₂.card : ℝ) = (n : ℝ) - ((⌈ε * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h1 : V₂.card = n - ⌈ε * (n : ℝ)⌉₊ := by
      rw [hV₂, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        hV₁card]
    rw [h1, Nat.cast_sub hfloor]
  have hV₂ge : ε * (n : ℝ) ≤ (V₂.card : ℝ) := by
    rw [hV₂card]
    have h3 : (2 : ℝ) * (ε * n) + 1 ≤ (n : ℝ) := by nlinarith [hε1, hεn, hnR]
    linarith
  have hlrA := hlr V₁ V₂ hdisj hV₁ge hV₂ge
  have hsum := crossEdges_le_sum_card_neighborSet G V₁ V₂
  have hbound : (crossEdges G V₁ V₂ : ℝ) ≤ (V₁.card : ℝ) * (maxDeg G : ℝ) := by
    have h4 : (∑ v ∈ V₁, Nat.card (G.neighborSet v)) ≤ V₁.card * maxDeg G :=
      calc (∑ v ∈ V₁, Nat.card (G.neighborSet v)) ≤ ∑ _v ∈ V₁, maxDeg G :=
            Finset.sum_le_sum (fun v _ => card_neighborSet_le_maxDeg G v)
        _ = V₁.card * maxDeg G := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have h5 : (crossEdges G V₁ V₂ : ℝ) ≤
        ((∑ v ∈ V₁, Nat.card (G.neighborSet v) : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have h6 : ((∑ v ∈ V₁, Nat.card (G.neighborSet v) : ℕ) : ℝ) ≤
        (V₁.card : ℝ) * (maxDeg G : ℝ) := by
      exact_mod_cast h4
    linarith
  have hV₁pos : (0 : ℝ) < (V₁.card : ℝ) := lt_of_lt_of_le hεn0 hV₁ge
  have hΔ : (p - ε) * (V₂.card : ℝ) ≤ (maxDeg G : ℝ) := by
    have h6a : (V₁.card : ℝ) * ((p - ε) * (V₂.card : ℝ)) =
        (p - ε) * (V₁.card : ℝ) * (V₂.card : ℝ) := by ring
    have h6 : (V₁.card : ℝ) * ((p - ε) * (V₂.card : ℝ)) ≤
        (V₁.card : ℝ) * (maxDeg G : ℝ) := by
      rw [h6a]; exact le_trans hlrA hbound
    exact le_of_mul_le_mul_left h6 hV₁pos
  have hpε : 0 ≤ p - ε := by linarith
  have hV₂big : (1 - 2 * ε) * (n : ℝ) ≤ (V₂.card : ℝ) := by
    rw [hV₂card]
    linarith [hceil_lt, hεn]
  have h7 : (p - ε) * ((1 - 2 * ε) * (n : ℝ)) ≤ (p - ε) * (V₂.card : ℝ) :=
    mul_le_mul_of_nonneg_left hV₂big hpε
  have h8 : (p - 3 * ε) * (n : ℝ) ≤ (p - ε) * ((1 - 2 * ε) * (n : ℝ)) := by
    have h9 : 0 ≤ ε * (n : ℝ) := le_of_lt hεn0
    have hε0 : 0 ≤ ε := by nlinarith [h9, hnR]
    have hkey : 0 ≤ (n : ℝ) * (2 * ε * (1 - p + ε)) :=
      mul_nonneg (Nat.cast_nonneg n)
        (mul_nonneg (by linarith) (by linarith))
    nlinarith [hkey]
  exact le_trans h8 (le_trans h7 hΔ)

/-! ## The minimum-degree bound -/

/-- Lower `(p,ε)`-regularity plus near-regularity gives `δ ≥ pn/2`: combine `Δ ≥ (p-3ε)n` (from `Work.Deep.GKO.maxDeg_ge_of_lowerReg`) with `Δ - d(v) ≤ νn` and `3ε + ν ≤ p/2`.  This is the minimum degree bound `δ ≥ pn/2` used to run the forest-removal argument. -/
theorem minDeg_ge_of_lowerReg {n : ℕ} (G : SimpleGraph (Fin n)) {p ε ν : ℝ}
    (hlr : Work.Deep.GKO.LowerReg G p ε) (hεn : 1 ≤ ε * (n : ℝ)) (hε1 : ε ≤ 1 / 3)
    (hεp : ε ≤ p) (hp1 : p ≤ 1) (hn : 1 ≤ n)
    (hdev : ∀ v : Fin n,
      ((Work.Deep.GKO.maxDeg G : ℝ) - (Nat.card (G.neighborSet v) : ℝ)) ≤ ν * (n : ℝ))
    (hsmall : 3 * ε + ν ≤ p / 2) :
    (p / 2) * (n : ℝ) ≤ (Work.Deep.GKO.minDeg G : ℝ) := by
  classical
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hΔ : (p - 3 * ε) * (n : ℝ) ≤ (maxDeg G : ℝ) :=
    maxDeg_ge_of_lowerReg_aux G hlr hεn hε1 hεp hp1 hn
  -- every vertex degree is at least `pn/2`
  have hdeg : ∀ v : Fin n, (p / 2) * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
    intro v
    have h1 := hdev v
    have h2 : p / 2 ≤ (p - 3 * ε) - ν := by linarith
    have h3 : (p / 2) * (n : ℝ) ≤ ((p - 3 * ε) - ν) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h2 hnR
    have h4 : ((p - 3 * ε) - ν) * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
      have h5 : ((p - 3 * ε) - ν) * (n : ℝ) = (p - 3 * ε) * (n : ℝ) - ν * (n : ℝ) := by ring
      linarith [hΔ, h1, h5]
    linarith
  -- `n ≥ 1` makes the range of the degree function nonempty, and `minDeg G` is attained
  have hne : (Set.range (fun v : Fin n => Nat.card (G.neighborSet v))).Nonempty :=
    Set.range_nonempty_iff_nonempty.mpr ⟨⟨0, hn⟩⟩
  obtain ⟨v₀, hv₀⟩ := Nat.sInf_mem hne
  have hv₀' : minDeg G = Nat.card (G.neighborSet v₀) := hv₀.symm
  rw [hv₀']
  exact hdeg v₀

end

end Work.Deep.GKO
