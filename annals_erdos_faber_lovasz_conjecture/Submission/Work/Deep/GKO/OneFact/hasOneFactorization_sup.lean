import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.RegVocab

/-!
# Gluing two 1-factorizations

`hasOneFactorization_sup` (proved): the edge-disjoint union of a graph with a `k`-factorization and
one with an `l`-factorization has a `(k+l)`-factorization.  Extracted from the retired N5 file
(`OneFact/oneFactLowerReg_of_approxHam.lean`) so that the elementary N5
(`OneFact/oneFactLowerReg_elementary.lean`) can glue its two factorizations without importing
`KOInputs`/`robustExpander_lowerReg`.  The degree bookkeeping lemmas below are used by the same
assembly.
-/

namespace Work.Deep.GKO.OneFact

noncomputable section

lemma rpow_two_thirds_le_div {n : ℕ} {C : ℝ} (hC : 0 < C) (hn : C ^ 3 ≤ (n : ℝ)) :
    ((n : ℝ)) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) / C := by
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (pow_pos hC 3) hn
  have h3 : (C ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = C := by
    rw [show (C ^ 3 : ℝ) = C ^ (3:ℝ) from (Real.rpow_natCast C 3).symm]
    rw [← Real.rpow_mul hC.le]
    norm_num
  have h1 : C ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 := Real.rpow_le_rpow (le_of_lt (pow_pos hC 3)) hn (by norm_num : (0:ℝ) ≤ 1/3)
    linarith [h2, h3.le, h3.ge]
  have h4 : (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3) = (n : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
  rw [le_div_iff₀ hC]
  calc (n : ℝ) ^ ((2:ℝ)/3) * C ≤ (n : ℝ) ^ ((2:ℝ)/3) * (n : ℝ) ^ ((1:ℝ)/3) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hn0) _)
    _ = (n : ℝ) := h4

/-- One-factorizations of two edge-disjoint spanning subgraphs glue: the `k` perfect
matchings of `A` and the `l` perfect matchings of `B` are `k + l` perfect matchings of
`A ⊔ B` (a perfect matching of `A` is a perfect matching of any supergraph). -/
theorem hasOneFactorization_sup {n : ℕ} {A B : SimpleGraph (Fin n)} {k l : ℕ}
    (hdisj : Disjoint A.edgeSet B.edgeSet) (hA : HasOneFactorization A k)
    (hB : HasOneFactorization B l) : HasOneFactorization (A ⊔ B) (k + l) := by
  classical
  obtain ⟨MA, hMA1, hMA2, hMA3⟩ := hA
  obtain ⟨MB, hMB1, hMB2, hMB3⟩ := hB
  refine ⟨fun i => Sum.elim MA MB ((finSumFinEquiv (m := k) (n := l)).symm i), ?_, ?_, ?_⟩
  · intro i
    rcases h : (finSumFinEquiv (m := k) (n := l)).symm i with j | j
    · simp only [h, Sum.elim_inl]
      exact ⟨le_trans (hMA1 j).1 le_sup_left, (hMA1 j).2⟩
    · simp only [h, Sum.elim_inr]
      exact ⟨le_trans (hMB1 j).1 le_sup_right, (hMB1 j).2⟩
  · intro i i' hii
    have hne : (finSumFinEquiv (m := k) (n := l)).symm i ≠
        (finSumFinEquiv (m := k) (n := l)).symm i' :=
      fun h => hii ((finSumFinEquiv (m := k) (n := l)).symm.injective h)
    rcases hi : (finSumFinEquiv (m := k) (n := l)).symm i with j | j <;>
      rcases hi' : (finSumFinEquiv (m := k) (n := l)).symm i' with j' | j'
    · have hj : j ≠ j' := fun h => hne (by rw [hi, hi', h])
      simp only [hi, hi', Sum.elim_inl]
      exact hMA2 j j' hj
    · simp only [hi, hi', Sum.elim_inl, Sum.elim_inr]
      exact Disjoint.mono (SimpleGraph.edgeSet_mono (hMA1 j).1)
        (SimpleGraph.edgeSet_mono (hMB1 j').1) hdisj
    · simp only [hi, hi', Sum.elim_inr, Sum.elim_inl]
      exact Disjoint.mono (SimpleGraph.edgeSet_mono (hMB1 j).1)
        (SimpleGraph.edgeSet_mono (hMA1 j').1) hdisj.symm
    · have hj : j ≠ j' := fun h => hne (by rw [hi, hi', h])
      simp only [hi, hi', Sum.elim_inr]
      exact hMB2 j j' hj
  · intro e he
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at he
    rcases he with he | he
    · obtain ⟨j, hj⟩ := hMA3 e he
      exact ⟨(finSumFinEquiv (m := k) (n := l)) (Sum.inl j), by simp [Sum.elim_inl, hj]⟩
    · obtain ⟨j, hj⟩ := hMB3 e he
      exact ⟨(finSumFinEquiv (m := k) (n := l)) (Sum.inr j), by simp [Sum.elim_inr, hj]⟩

/-- Degree additivity for two edge-disjoint graphs. -/
lemma card_neighborSet_sup_of_disjoint {n : ℕ} {A B : SimpleGraph (Fin n)}
    (h : Disjoint A.edgeSet B.edgeSet) (v : Fin n) :
    Nat.card ((A ⊔ B).neighborSet v)
      = Nat.card (A.neighborSet v) + Nat.card (B.neighborSet v) := by
  have hset : (A ⊔ B).neighborSet v = A.neighborSet v ∪ B.neighborSet v := by
    ext x; simp [SimpleGraph.mem_neighborSet]
  have hdisj : Disjoint (A.neighborSet v) (B.neighborSet v) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact (Set.disjoint_left.mp h)
      ((SimpleGraph.mem_edgeSet (G := A) (v := v) (w := x)).mpr hxA)
      ((SimpleGraph.mem_edgeSet (G := B) (v := v) (w := x)).mpr hxB)
  rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hdisj (Set.toFinite _)]

/-- Monotonicity of the degree under subgraphs. -/
lemma card_neighborSet_le_of_le {n : ℕ} {A B : SimpleGraph (Fin n)} (h : A ≤ B) (v : Fin n) :
    Nat.card (A.neighborSet v) ≤ Nat.card (B.neighborSet v) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun x hx => h hx)

/-- `Nat.sqrt` is dominated by the real square root. -/
lemma nat_sqrt_cast_le_sqrt (m : ℕ) : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
  have hm : (((Nat.sqrt m : ℕ) : ℝ)) ^ 2 ≤ (m : ℝ) := by
    have h := Nat.sqrt_le' m
    push_cast
    exact_mod_cast h
  have h2 := Real.sqrt_le_sqrt hm
  rwa [Real.sqrt_sq (by positivity)] at h2
end

end Work.Deep.GKO.OneFact
