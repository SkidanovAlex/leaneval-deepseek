import Mathlib
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting many fibre balls inside the level set of `P'`

If every `y ∈ Y` comes with a "good ball" `B y` inside the fibre `{x : P x = y}` which has at
least `t / d` elements and on which `p ^ L` divides the derivative `P'`, then the balls `B y`
(`y ∈ Y`) are pairwise disjoint (they lie in distinct fibres) and are all contained in the level
set `G = {x : p ^ L ∣ P'(x)}`.  Hence

  `|Y| * (t / d) ≤ |G|`.

Only the combinatorial content is proved here: the existence of the balls is the hypothesis
`hgood`; `hY` and `ht` merely record the situation in which the lemma is applied.
-/

namespace Work.KMTPlan.A6.ConcAux2

theorem card_le_of_good_balls {p k L : ℕ} [Fact p.Prime] {t : ℝ} (ht : 0 < t) (d : ℕ) (Q : Polynomial ℤ) (Y : Finset (ZMod (p ^ k))) (hY : ∀ y ∈ Y, t ≤ (Work.Analysis.Concentration.polyFiberCard Q (p ^ k) y : ℝ)) (hgood : ∀ y : ZMod (p ^ k), y ∈ Y → ∃ B : Finset (ZMod (p ^ k)), B ⊆ (Finset.univ.filter (fun x : ZMod (p ^ k) => Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y)) ∧ t / (d : ℝ) ≤ (B.card : ℝ) ∧ ∀ x ∈ B, (p : ℤ) ^ L ∣ (Polynomial.derivative Q).eval (x.val : ℤ)) : (Y.card : ℝ) * (t / (d : ℝ)) ≤ ((Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ L ∣ (Polynomial.derivative Q).eval (x.val : ℤ))).card : ℝ) := by
  classical
  -- the level set of the derivative
  set G : Finset (ZMod (p ^ k)) :=
    Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ L ∣ (Polynomial.derivative Q).eval (x.val : ℤ)) with hG
  -- choose the good ball attached to each `y ∈ Y`, and extend it by `∅` off `Y`
  choose B hB using hgood
  set B' : ZMod (p ^ k) → Finset (ZMod (p ^ k)) := fun y => if hy : y ∈ Y then B y hy else ∅ with hB'
  have hB'eq : ∀ y (hy : y ∈ Y), B' y = B y hy := by
    intro y hy
    simp only [hB']
    exact dif_pos hy
  -- each ball lies in the fibre of its index
  have hBsub : ∀ y (hy : y ∈ Y), B' y ⊆
      Finset.univ.filter (fun x : ZMod (p ^ k) => Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y) := by
    intro y hy
    rw [hB'eq y hy]
    exact (hB y hy).1
  -- ... and has at least `t / d` elements
  have hBcard : ∀ y (hy : y ∈ Y), t / (d : ℝ) ≤ ((B' y).card : ℝ) := by
    intro y hy
    rw [hB'eq y hy]
    exact (hB y hy).2.1
  -- ... and consists of points at which `p ^ L` divides `P'`
  have hBdvd : ∀ y (hy : y ∈ Y) x, x ∈ B' y →
      (p : ℤ) ^ L ∣ (Polynomial.derivative Q).eval (x.val : ℤ) := by
    intro y hy x hx
    rw [hB'eq y hy] at hx
    exact (hB y hy).2.2 x hx
  have hBsubG : ∀ y (hy : y ∈ Y), B' y ⊆ G := by
    intro y hy x hx
    rw [hG]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBdvd y hy x hx⟩
  -- balls with distinct indices lie in distinct fibres, hence are disjoint
  have hdisj : (↑Y : Set (ZMod (p ^ k))).PairwiseDisjoint B' := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi j hj hne
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter] at hx
    have h1 : Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = i :=
      (Finset.mem_filter.mp (hBsub i hi hx.1)).2
    have h2 : Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = j :=
      (Finset.mem_filter.mp (hBsub j hj hx.2)).2
    exact h1.symm.trans h2
  have hcard : (Y.biUnion B').card = ∑ y ∈ Y, (B' y).card := Finset.card_biUnion hdisj
  have hle_nat : (∑ y ∈ Y, (B' y).card) ≤ G.card := by
    rw [← hcard]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hBsubG)
  calc (Y.card : ℝ) * (t / (d : ℝ)) = ∑ _y ∈ Y, t / (d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ Y, ((B' y).card : ℝ) := Finset.sum_le_sum (fun y hy => hBcard y hy)
    _ = ((∑ y ∈ Y, (B' y).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (G.card : ℝ) := by exact_mod_cast hle_nat

end Work.KMTPlan.A6.ConcAux2
