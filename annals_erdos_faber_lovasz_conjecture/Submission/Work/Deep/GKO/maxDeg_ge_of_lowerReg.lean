import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

namespace Work.Deep.GKO

/-! ## Two counting lemmas for the graph-side degree bounds

`crossEdges G A B` counts the pairs `(a,b) ∈ A × B` with `G.Adj a b`, and every such
pair contributes one to the degree of `a`; summing over `a ∈ A` therefore bounds the
number of edges between `A` and `B` by the sum of the degrees of `A`.  Both lemmas
below are the graph-language counterparts of `edgeCount_le_sum_degAt_left` and
`degAt_le_maxDegree` of `Submission/EFL/OptCol.lean`. -/

/-- The number of edges between `A` and `B` is at most the sum of the degrees over `A`. -/
private theorem crossEdges_le_sum_deg {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges G A B ≤ ∑ v ∈ A, Nat.card (G.neighborSet v) := by
  classical
  have key : crossEdges G A B ≤ ∑ a ∈ A, (B.filter (fun b => G.Adj a b)).card := by
    unfold crossEdges
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.1) (t := A)]
    swap
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1).1
    refine Finset.sum_le_sum (fun a _ => ?_)
    refine Finset.card_le_card_of_injOn (fun p : Fin n × Fin n => p.2) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Finset.mem_filter] at hp1
      obtain ⟨hpAB, hadj⟩ := hp1
      obtain ⟨-, hpB⟩ := Finset.mem_product.mp hpAB
      simp only [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hpB, hp2 ▸ hadj⟩
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) hpq
  refine le_trans key ?_
  refine Finset.sum_le_sum (fun a _ => ?_)
  have hcard : (G.neighborFinset a).card = Nat.card (G.neighborSet a) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree,
      Nat.card_eq_fintype_card]
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro b hb
  rw [Finset.mem_filter] at hb
  rw [SimpleGraph.mem_neighborFinset]
  exact hb.2

/-- Every degree is at most the maximum degree. -/
private theorem deg_le_maxDeg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Nat.card (G.neighborSet v) ≤ maxDeg G := by
  classical
  unfold maxDeg
  exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
    (f := fun v => Nat.card (G.neighborSet v)) (Finset.mem_univ v)

/-- Lower `(p,ε)`-regularity gives a lower bound for the maximum degree: `Δ ≥ (p-3ε)n`.  This is the graph-language analogue of `ErdosFaberLovaszConjecture.maxDegree_ge_of_selfLowerRegular` in `Submission/EFL/OptCol.lean` (which is already proved and can be copied); the argument splits off a set `V₁` of `⌈εn⌉` vertices and uses regularity between `V₁` and its complement. -/
theorem maxDeg_ge_of_lowerReg {n : ℕ} (G : SimpleGraph (Fin n)) {p ε : ℝ}
    (hlr : Work.Deep.GKO.LowerReg G p ε) (hεn : 1 ≤ ε * (n : ℝ)) (hε1 : ε ≤ 1 / 3)
    (hεp : ε ≤ p) (hp1 : p ≤ 1) (hn : 1 ≤ n) :
    (p - 3 * ε) * (n : ℝ) ≤ (Work.Deep.GKO.maxDeg G : ℝ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hεn0 : (0 : ℝ) < ε * (n : ℝ) := lt_of_lt_of_le zero_lt_one hεn
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
  have hsum : crossEdges G V₁ V₂ ≤ ∑ v ∈ V₁, Nat.card (G.neighborSet v) :=
    crossEdges_le_sum_deg G V₁ V₂
  have hbound : (crossEdges G V₁ V₂ : ℝ) ≤ (V₁.card : ℝ) * (maxDeg G : ℝ) := by
    have h3 : ((∑ v ∈ V₁, Nat.card (G.neighborSet v) : ℕ) : ℝ) ≤
        (V₁.card : ℝ) * (maxDeg G : ℝ) := by
      have h4 : (∑ v ∈ V₁, Nat.card (G.neighborSet v)) ≤ V₁.card * maxDeg G := by
        calc (∑ v ∈ V₁, Nat.card (G.neighborSet v)) ≤ ∑ _v ∈ V₁, maxDeg G :=
              Finset.sum_le_sum (fun v _ => deg_le_maxDeg G v)
          _ = V₁.card * maxDeg G := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      exact_mod_cast h4
    have h5 : (crossEdges G V₁ V₂ : ℝ) ≤
        ((∑ v ∈ V₁, Nat.card (G.neighborSet v) : ℕ) : ℝ) := by
      exact_mod_cast hsum
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

end Work.Deep.GKO
