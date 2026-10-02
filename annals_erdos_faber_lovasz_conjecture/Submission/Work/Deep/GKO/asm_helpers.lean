import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.maxDeg_ge_of_lowerReg
import Submission.Work.Deep.GKO.lowerReg_of_delete
import Submission.Work.Deep.GKO.exists_spanningLinearForest

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Classical

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Monotonicity of lower regularity in the error parameter -/

theorem LowerReg_mono_eps {G : SimpleGraph (Fin n)} {p ε ε' : ℝ}
    (h : LowerReg G p ε) (hεε' : ε ≤ ε') : LowerReg G p ε' := by
  intro A B hdisj hA hB
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hA' : ε * (n : ℝ) ≤ (A.card : ℝ) := le_trans (mul_le_mul_of_nonneg_right hεε' hn) hA
  have hB' : ε * (n : ℝ) ≤ (B.card : ℝ) := le_trans (mul_le_mul_of_nonneg_right hεε' hn) hB
  have h1 := h A B hdisj hA' hB'
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have h2 : (p - ε') * (A.card : ℝ) * (B.card : ℝ) ≤
      (p - ε) * (A.card : ℝ) * (B.card : ℝ) := by
    have hAB : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := mul_nonneg hA0 hB0
    have hle : p - ε' ≤ p - ε := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle hAB
    nlinarith [hmul]
  exact le_trans h2 h1

/-! ## Degree bookkeeping for spanning linear forests -/

theorem spanningLinearForest_degree_eq {F : SimpleGraph (Fin n)} {L : Finset (Fin n)}
    (hF : IsSpanningLinearForestWithLeaves F L) (v : Fin n) :
    Nat.card (F.neighborSet v) = if v ∈ L then 1 else 2 := by
  have h₁ : Nat.card (F.neighborSet v) = 1 ↔ v ∈ L := hF.2.2.2 v
  have h₂ : Nat.card (F.neighborSet v) ≤ 2 := hF.2.2.1 v
  have h₃ : 1 ≤ Nat.card (F.neighborSet v) := hF.2.1 v
  by_cases hv : v ∈ L
  · rw [if_pos hv]; exact h₁.mpr hv
  · rw [if_neg hv]
    have hne : Nat.card (F.neighborSet v) ≠ 1 := fun h => hv (h₁.mp h)
    omega

theorem isLinearForest_of_spanning {F : SimpleGraph (Fin n)} {L : Finset (Fin n)}
    (hF : IsSpanningLinearForestWithLeaves F L) : IsLinearForest F :=
  ⟨hF.1, fun v => hF.2.2.1 v⟩

/-! ## The degree of `G \ H` -/

theorem card_neighborSet_sdiff (G H : SimpleGraph (Fin n)) (h : H ≤ G) (v : Fin n) :
    Nat.card ((G \ H).neighborSet v) = Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) := by
  have hsub : H.neighborSet v ⊆ G.neighborSet v := fun w hw => h hw
  have hset : (G \ H).neighborSet v = G.neighborSet v \ H.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_sdiff, SimpleGraph.sdiff_adj]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff hsub]
  simp only [Nat.card_coe_set_eq]

/-! ## Adjacency in a finite supremum -/

theorem finset_sup_adj {ι : Type*} (s : Finset ι) (F : ι → SimpleGraph (Fin n)) (v w : Fin n) :
    (s.sup F).Adj v w ↔ ∃ i ∈ s, (F i).Adj v w := by
  classical
  rw [Finset.sup_eq_iSup]
  simp only [SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i, his, hi⟩; exact ⟨i, his, hi⟩
  · rintro ⟨i, his, hi⟩; exact ⟨i, his, hi⟩

theorem ncard_neighborSet_finset_sup_sum {ι : Type*} (s : Finset ι)
    (F : ι → SimpleGraph (Fin n)) (v : Fin n)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet) :
    ((s.sup F).neighborSet v).ncard = ∑ i ∈ s, ((F i).neighborSet v).ncard := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hdisj_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet :=
      fun i hi j hj hij =>
        hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hdisj_at : ∀ i ∈ t, Disjoint (F a).edgeSet (F i).edgeSet :=
      fun i hi =>
        hdisj a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
    have hdj : Disjoint ((F a).neighborSet v) ((t.sup F).neighborSet v) := by
      rw [Set.disjoint_left]
      intro w hwa hwt
      have h2 : (F a).Adj v w := hwa
      have h3 : (t.sup F).Adj v w := hwt
      rw [finset_sup_adj] at h3
      obtain ⟨i, hi, h3'⟩ := h3
      have he1 : s(v, w) ∈ (F a).edgeSet := (SimpleGraph.mem_edgeSet _).mpr h2
      have he2 : s(v, w) ∈ (F i).edgeSet := (SimpleGraph.mem_edgeSet _).mpr h3'
      exact (Set.disjoint_left.mp (hdisj_at i hi)) he1 he2
    rw [Finset.sup_insert, SimpleGraph.neighborSet_sup,
      Set.ncard_union_eq hdj (Set.toFinite _) (Set.toFinite _), ih hdisj_t,
      Finset.sum_insert ha]

theorem card_neighborSet_sup_eq_sum {k : ℕ} (F : Fin k → SimpleGraph (Fin n)) (v : Fin n)
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet) :
    Nat.card (((Finset.univ : Finset (Fin k)).sup F).neighborSet v) =
      ∑ i : Fin k, Nat.card ((F i).neighborSet v) := by
  simp only [Nat.card_coe_set_eq]
  exact ncard_neighborSet_finset_sup_sum Finset.univ F v
    (fun i _ j _ hij => hdisj i j hij)

/-! ## The number of vertices covered by a matching -/

theorem matching_covered_card {M : SimpleGraph (Fin n)} [DecidableRel M.Adj]
    (hM : IsMatching' M) :
    (Finset.univ.filter (fun v => ∃ w, M.Adj v w)).card = 2 * Nat.card M.edgeSet := by
  classical
  have hkey : ∀ v : Fin n, (if (∃ w, M.Adj v w) then 1 else 0) = Nat.card (M.neighborSet v) := by
    intro v
    by_cases h : ∃ w, M.Adj v w
    · rw [if_pos h]
      obtain ⟨w, hw⟩ := h
      have hset : M.neighborSet v = {w} := by
        ext x
        simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
        exact ⟨fun hx => hM v x w hx hw, fun hx => hx ▸ hw⟩
      rw [hset, Nat.card_coe_set_eq, Set.ncard_singleton]
    · rw [if_neg h]
      have hset : M.neighborSet v = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false, SimpleGraph.mem_neighborSet]
        exact fun hx => h ⟨x, hx⟩
      rw [hset, Nat.card_coe_set_eq, Set.ncard_empty]
  rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun v _ => hkey v)]
  have hdeg : ∀ v : Fin n, Nat.card (M.neighborSet v) = M.degree v := by
    intro v
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  rw [Finset.sum_congr rfl (fun v _ => hdeg v), SimpleGraph.sum_degrees_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]

end

end Work.Deep.GKO

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Small counting lemmas -/

theorem natCard_subtype_filter_eq {k : ℕ} (P : Fin k → Prop) [DecidablePred P] :
    Nat.card {i : Fin k // P i} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_ite_mem_eq {k : ℕ} (L : Fin k → Finset (Fin n)) (v : Fin n) :
    (∑ j : Fin k, (if v ∈ L j then 1 else 2)) =
      2 * k - (Finset.univ.filter (fun j : Fin k => v ∈ L j)).card := by
  classical
  have hc : (∑ j : Fin k, (if v ∈ L j then 1 else 0))
      = (Finset.univ.filter (fun j : Fin k => v ∈ L j)).card := by
    rw [Finset.sum_boole]; simp
  have hsum : (∑ j : Fin k, (if v ∈ L j then 1 else 2))
      + (∑ j : Fin k, (if v ∈ L j then 1 else 0)) = 2 * k := by
    rw [← Finset.sum_add_distrib]
    have h2 : (∑ j : Fin k, ((if v ∈ L j then 1 else 2) + (if v ∈ L j then 1 else 0)))
        = ∑ _j : Fin k, 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : v ∈ L j <;> simp [h]
    rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [hc] at hsum
  exact Nat.eq_sub_of_add_eq hsum

/-! ## Evenness of the total deficiency -/

theorem even_two_mul_sub (N Δ E : ℕ) (hN : Even N) : Even (N * Δ - 2 * E) := by
  obtain ⟨m, hm⟩ := hN
  refine ⟨m * Δ - E, ?_⟩
  have h2 : N * Δ = 2 * (m * Δ) := by rw [hm]; ring
  rw [h2, show (m * Δ - E) + (m * Δ - E) = 2 * (m * Δ - E) from (two_mul _).symm,
    Nat.mul_sub_left_distrib]

theorem even_sum_deficiency (G : SimpleGraph (Fin n)) (hn : Even n) :
    Even (∑ v : Fin n, (maxDeg G - Nat.card (G.neighborSet v))) := by
  classical
  have hle : ∀ v : Fin n, Nat.card (G.neighborSet v) ≤ maxDeg G := fun v =>
    Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
      (f := fun u => Nat.card (G.neighborSet u)) (Finset.mem_univ v)
  have hadd : (∑ v : Fin n, (maxDeg G - Nat.card (G.neighborSet v)))
      + (∑ v : Fin n, Nat.card (G.neighborSet v)) = ∑ _v : Fin n, maxDeg G := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => Nat.sub_add_cancel (hle v))
  have h3 : (∑ _v : Fin n, maxDeg G) = n * maxDeg G := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h4 : (∑ v : Fin n, Nat.card (G.neighborSet v)) = 2 * Nat.card G.edgeSet := by
    have hdeg : ∀ v : Fin n, Nat.card (G.neighborSet v) = G.degree v := fun v => by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    rw [Finset.sum_congr rfl (fun v _ => hdeg v), SimpleGraph.sum_degrees_eq_twice_card_edges,
      SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hle2 : 2 * Nat.card G.edgeSet ≤ n * maxDeg G := by
    rw [← h4, ← h3]
    exact Finset.sum_le_sum (fun v _ => hle v)
  have hA : (∑ v : Fin n, (maxDeg G - Nat.card (G.neighborSet v)))
      = n * maxDeg G - 2 * Nat.card G.edgeSet := by
    rw [h3, h4] at hadd
    exact Nat.eq_sub_of_add_eq hadd
  rw [hA]
  exact even_two_mul_sub n (maxDeg G) (Nat.card G.edgeSet) hn

/-! ## Hakimi's condition at every vertex -/

theorem hakimi_condition_of_minDegree (G : SimpleGraph (Fin n)) {w : Fin n}
    (hw : ∀ v : Fin n, Nat.card (G.neighborSet w) ≤ Nat.card (G.neighborSet v))
    (h : maxDeg G - Nat.card (G.neighborSet w) ≤
      ∑ v ∈ Finset.univ.erase w, (maxDeg G - Nat.card (G.neighborSet v))) :
    ∀ v : Fin n, maxDeg G - Nat.card (G.neighborSet v) ≤
      ∑ u ∈ Finset.univ.erase v, (maxDeg G - Nat.card (G.neighborSet u)) := by
  classical
  intro v
  have hvw : maxDeg G - Nat.card (G.neighborSet v) ≤ maxDeg G - Nat.card (G.neighborSet w) :=
    Nat.sub_le_sub_left (hw v) (maxDeg G)
  set S : ℕ := ∑ u : Fin n, (maxDeg G - Nat.card (G.neighborSet u)) with hS
  have hew : (∑ u ∈ Finset.univ.erase w, (maxDeg G - Nat.card (G.neighborSet u)))
      + (maxDeg G - Nat.card (G.neighborSet w)) = S :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ w)
  have hev : (∑ u ∈ Finset.univ.erase v, (maxDeg G - Nat.card (G.neighborSet u)))
      + (maxDeg G - Nat.card (G.neighborSet v)) = S :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ v)
  have hfw : (∑ u ∈ Finset.univ.erase w, (maxDeg G - Nat.card (G.neighborSet u)))
      = S - (maxDeg G - Nat.card (G.neighborSet w)) := Nat.eq_sub_of_add_eq hew
  have hfv : (∑ u ∈ Finset.univ.erase v, (maxDeg G - Nat.card (G.neighborSet u)))
      = S - (maxDeg G - Nat.card (G.neighborSet v)) := Nat.eq_sub_of_add_eq hev
  rw [hfw] at h
  rw [hfv]
  exact le_trans (le_trans hvw h) (Nat.sub_le_sub_left hvw S)

/-! ## Combining matching decompositions of edge-disjoint graphs -/

theorem hasMatchingDecomposition_sup_of_disjoint {H₁ H₂ : SimpleGraph (Fin n)} {k₁ k₂ : ℕ}
    (hdisj : Disjoint H₁.edgeSet H₂.edgeSet)
    (h₁ : HasMatchingDecomposition H₁ k₁) (h₂ : HasMatchingDecomposition H₂ k₂) :
    HasMatchingDecomposition (H₁ ⊔ H₂) (k₁ + k₂) := by
  classical
  obtain ⟨M₁, hm₁, hle₁, hd₁, hc₁⟩ := h₁
  obtain ⟨M₂, hm₂, hle₂, hd₂, hc₂⟩ := h₂
  let M : Fin (k₁ + k₂) → SimpleGraph (Fin n) := Fin.addCases M₁ M₂
  have hMl : ∀ i : Fin k₁, M (Fin.castAdd k₂ i) = M₁ i := fun i => Fin.addCases_left i
  have hMr : ∀ j : Fin k₂, M (Fin.natAdd k₁ j) = M₂ j := fun j => Fin.addCases_right j
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.addCases (fun a => by rw [hMl a]; exact hm₁ a)
      (fun b => by rw [hMr b]; exact hm₂ b) i
  · intro i
    exact Fin.addCases (fun a => by rw [hMl a]; exact le_trans (hle₁ a) le_sup_left)
      (fun b => by rw [hMr b]; exact le_trans (hle₂ b) le_sup_right) i
  · intro i j hij
    revert hij
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro hij
      revert hij
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j
      · intro hij
        rw [hMl a, hMl a']
        exact hd₁ a a' (fun h => hij (by rw [h]))
      · intro hij
        rw [hMl a, hMr b']
        exact Disjoint.mono (SimpleGraph.edgeSet_mono (hle₁ a))
          (SimpleGraph.edgeSet_mono (hle₂ b')) hdisj
    · intro hij
      revert hij
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j
      · intro hij
        rw [hMr b, hMl a']
        exact Disjoint.mono (SimpleGraph.edgeSet_mono (hle₂ b))
          (SimpleGraph.edgeSet_mono (hle₁ a')) hdisj.symm
      · intro hij
        rw [hMr b, hMr b']
        exact hd₂ b b' (fun h => hij (by rw [h]))
  · intro e he
    rw [SimpleGraph.edgeSet_sup] at he
    rcases he with he | he
    · obtain ⟨i, hi⟩ := hc₁ e he
      exact ⟨Fin.castAdd k₂ i, by rw [hMl i]; exact hi⟩
    · obtain ⟨j, hj⟩ := hc₂ e he
      exact ⟨Fin.natAdd k₁ j, by rw [hMr j]; exact hj⟩


/-! ## The degree of a neighbourhood difference -/

theorem nat_sub_cast_le (a b : ℕ) : ((a - b : ℕ) : ℝ) ≥ (a : ℝ) - (b : ℝ) := by
  rcases le_or_gt b a with h | h
  · rw [Nat.cast_sub h]
  · have : (a - b : ℕ) = 0 := Nat.sub_eq_zero_of_le (le_of_lt h)
    rw [this]; push_cast
    have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
    linarith

theorem disjoint_sdiff_right {α : Type*} (A B : Set α) : Disjoint A (B \ A) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false]
  tauto

theorem disjoint_sdiff_left {α : Type*} (A B : Set α) : Disjoint (A \ B) B := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false]
  tauto

theorem le_card_neighborSet_sdiff (G H : SimpleGraph (Fin n)) (v : Fin n) :
    Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) ≤ Nat.card ((G \ H).neighborSet v) := by
  have hset : (G \ H).neighborSet v = G.neighborSet v \ H.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_sdiff, SimpleGraph.sdiff_adj]
  rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have h1 : G.neighborSet v ⊆ (G.neighborSet v \ H.neighborSet v) ∪ H.neighborSet v := by
    intro w hw
    by_cases h : w ∈ H.neighborSet v
    · exact Or.inr h
    · exact Or.inl ⟨hw, h⟩
  have h2 : (G.neighborSet v).ncard
      ≤ ((G.neighborSet v \ H.neighborSet v) ∪ H.neighborSet v).ncard :=
    Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((G.neighborSet v \ H.neighborSet v) ∪ H.neighborSet v).ncard
      = (G.neighborSet v \ H.neighborSet v).ncard + (H.neighborSet v).ncard :=
    Set.ncard_union_eq (disjoint_sdiff_left _ _) (Set.toFinite _) (Set.toFinite _)
  omega

/-! ## The minimum degree bound -/

theorem minDeg_le_degree (G : SimpleGraph (Fin n)) (v : Fin n) :
    (minDeg G : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  have h : minDeg G ≤ Nat.card (G.neighborSet v) :=
    Nat.sInf_le (Set.mem_range_self v)
  exact_mod_cast h

theorem le_minDeg (G : SimpleGraph (Fin n)) {a : ℝ} (hn : 0 < n)
    (h : ∀ v : Fin n, a ≤ (Nat.card (G.neighborSet v) : ℝ)) : a ≤ (minDeg G : ℝ) := by
  obtain ⟨v₀, hv₀⟩ := Nat.sInf_mem
    (Set.range_nonempty_iff_nonempty.mpr ⟨⟨0, hn⟩⟩ : (Set.range
      (fun v : Fin n => Nat.card (G.neighborSet v))).Nonempty)
  have hv₀' : minDeg G = Nat.card (G.neighborSet v₀) := hv₀.symm
  rw [hv₀']
  exact h v₀

/-! ## Degrees in a finite supremum -/

theorem card_neighborSet_finset_sup_le_sum {ι : Type*} (s : Finset ι)
    (F : ι → SimpleGraph (Fin n)) (v : Fin n) :
    ((s.sup F).neighborSet v).ncard ≤ ∑ i ∈ s, ((F i).neighborSet v).ncard := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty, SimpleGraph.neighborSet_bot, Set.ncard_empty, Finset.sum_empty]
  | insert a t ha ih =>
    rw [Finset.sup_insert, SimpleGraph.neighborSet_sup, Finset.sum_insert ha]
    calc ((F a).neighborSet v ∪ (t.sup F).neighborSet v).ncard
        ≤ ((F a).neighborSet v).ncard + ((t.sup F).neighborSet v).ncard :=
          Set.ncard_union_le _ _
      _ ≤ ((F a).neighborSet v).ncard + ∑ i ∈ t, ((F i).neighborSet v).ncard :=
          Nat.add_le_add_left ih _

theorem card_neighborSet_sup_range_le (F : ℕ → SimpleGraph (Fin n)) (i : ℕ) (v : Fin n)
    (hdeg : ∀ j ∈ Finset.range i, Nat.card ((F j).neighborSet v) ≤ 2) :
    Nat.card (((Finset.range i).sup F).neighborSet v) ≤ 2 * i := by
  rw [Nat.card_coe_set_eq]
  refine le_trans (card_neighborSet_finset_sup_le_sum (Finset.range i) F v) ?_
  calc ∑ j ∈ Finset.range i, ((F j).neighborSet v).ncard
      ≤ ∑ _j ∈ Finset.range i, 2 := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [← Nat.card_coe_set_eq]
        exact hdeg j hj
    _ = 2 * i := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-! ## Edge-disjointness of the successively removed forests -/

theorem disjoint_edgeSet_of_le_sdiff {G : SimpleGraph (Fin n)} {F : ℕ → SimpleGraph (Fin n)} {i : ℕ}
    (hF : ∀ j < i, F j ≤ G \ (Finset.range j).sup F) :
    ∀ a < i, ∀ b < i, a ≠ b → Disjoint (F a).edgeSet (F b).edgeSet := by
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with h | h
  · have hd : Disjoint ((Finset.range b).sup F).edgeSet (G \ (Finset.range b).sup F).edgeSet := by
      rw [SimpleGraph.edgeSet_sdiff]
      exact disjoint_sdiff_right _ _
    refine Disjoint.mono (SimpleGraph.edgeSet_mono
        (Finset.le_sup (f := F) (Finset.mem_range.mpr h)))
      (SimpleGraph.edgeSet_mono (hF b hb)) hd
  · have hd : Disjoint ((Finset.range a).sup F).edgeSet (G \ (Finset.range a).sup F).edgeSet := by
      rw [SimpleGraph.edgeSet_sdiff]
      exact disjoint_sdiff_right _ _
    exact (Disjoint.mono (SimpleGraph.edgeSet_mono
        (Finset.le_sup (f := F) (Finset.mem_range.mpr h)))
      (SimpleGraph.edgeSet_mono (hF a ha)) hd).symm

/-! ## The iterative construction of the edge-disjoint spanning linear forests -/

theorem exists_forests_aux (G : SimpleGraph (Fin n)) {p ε ε₀ α : ℝ} (k : ℕ)
    (L : ℕ → Finset (Fin n))
    (hn : 0 < n) (hlr : LowerReg G p ε₀) (hε₀ : 0 < ε₀)
    (hdegrade : max (2 * ε₀) (2 * Real.sqrt (2 * (k : ℝ) / (n : ℝ))) ≤ ε)
    (hα : 0 < α) (hα1 : α ≤ 1 / 10)
    (hεα : ε ≤ α / 100) (hεp : ε ≤ p / 100) (hεn : 1 ≤ ε * (n : ℝ))
    (hdeg : α * (n : ℝ) + 2 * (k : ℝ) ≤ (minDeg G : ℝ))
    (hLeven : ∀ j < k, Even (L j).card) (hL2 : ∀ j < k, 2 ≤ (L j).card)
    (hL : ∀ j < k, ((L j).card : ℝ) ≤ 2 * α * (n : ℝ) / 5) :
    ∃ F : ℕ → SimpleGraph (Fin n),
      (∀ j < k, IsSpanningLinearForestWithLeaves (F j) (L j)) ∧
      (∀ j < k, F j ≤ G \ (Finset.range j).sup F) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have key : ∀ i ≤ k, ∃ F : ℕ → SimpleGraph (Fin n),
      (∀ j < i, IsSpanningLinearForestWithLeaves (F j) (L j)) ∧
      (∀ j < i, F j ≤ G \ (Finset.range j).sup F) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨fun _ => ⊥, by simp, by simp⟩
    | succ i ih =>
      intro hik
      have hik' : i ≤ k := le_trans (Nat.le_succ i) hik
      obtain ⟨F, hF1, hF2⟩ := ih hik'
      have hik'' : i < k := by omega
      set H : SimpleGraph (Fin n) := (Finset.range i).sup F with hH
      -- degree bound for H
      have hHdeg : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ 2 * i := by
        intro v
        refine card_neighborSet_sup_range_le F i v (fun j hj => ?_)
        exact (hF1 j (Finset.mem_range.mp hj)).2.2.1 v
      -- lower regularity of G \ H
      have hη : (0 : ℝ) ≤ 2 * (i : ℝ) / (n : ℝ) := by positivity
      have hHbd : ∀ v : Fin n,
          (Nat.card (H.neighborSet v) : ℝ) ≤ (2 * (i : ℝ) / (n : ℝ)) * (n : ℝ) := by
        intro v
        have h1 : (Nat.card (H.neighborSet v) : ℝ) ≤ 2 * (i : ℝ) := by
          have := hHdeg v
          push_cast
          exact_mod_cast this
        have h2 : (2 * (i : ℝ) / (n : ℝ)) * (n : ℝ) = 2 * (i : ℝ) := by
          rw [div_mul_cancel₀]; exact ne_of_gt hnpos
        linarith [h1, h2.le, h2.ge]
      have hlrH := lowerReg_of_delete G H hlr hη hHbd
      have hdegrade_i : max (2 * ε₀) (2 * Real.sqrt (2 * (i : ℝ) / (n : ℝ))) ≤ ε := by
        have h1 : 2 * ε₀ ≤ ε := le_trans (le_max_left _ _) hdegrade
        have h2 : 2 * Real.sqrt (2 * (i : ℝ) / (n : ℝ))
            ≤ 2 * Real.sqrt (2 * (k : ℝ) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.sqrt_le_sqrt
          have h2i : (2 : ℝ) * i ≤ 2 * k := by
            have : 2 * i ≤ 2 * k := by omega
            exact_mod_cast this
          rw [div_le_div_iff_of_pos_right hnpos]
          exact h2i
        have h3 : 2 * Real.sqrt (2 * (k : ℝ) / (n : ℝ)) ≤ ε := le_trans (le_max_right _ _) hdegrade
        exact max_le h1 (le_trans h2 h3)
      have hlrH' : LowerReg (G \ H) p ε := LowerReg_mono_eps hlrH hdegrade_i
      -- minimum degree of G \ H
      have hdegH : α * (n : ℝ) ≤ (minDeg (G \ H) : ℝ) := by
        refine le_minDeg _ hn (fun v => ?_)
        have h1 : Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v)
            ≤ Nat.card ((G \ H).neighborSet v) := le_card_neighborSet_sdiff G H v
        have h2 : (Nat.card (G.neighborSet v) : ℝ) ≥ α * (n : ℝ) + 2 * (k : ℝ) := by
          have := minDeg_le_degree G v
          linarith [hdeg, this]
        have h3 : (Nat.card (H.neighborSet v) : ℝ) ≤ 2 * (i : ℝ) := by
          have := hHdeg v
          push_cast
          exact_mod_cast this
        have h4 : ((2 * (k : ℝ)) : ℝ) ≥ 2 * (i : ℝ) := by
          have : 2 * i ≤ 2 * k := by omega
          exact_mod_cast this
        have h5 : ((Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) : ℕ) : ℝ)
            ≥ (Nat.card (G.neighborSet v) : ℝ) - (Nat.card (H.neighborSet v) : ℝ) :=
          nat_sub_cast_le _ _
        have h6 : (Nat.card ((G \ H).neighborSet v) : ℝ)
            ≥ ((Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) : ℕ) : ℝ) := by
          exact_mod_cast h1
        linarith
      obtain ⟨Fnew, hFnew_le, hFnew⟩ := exists_spanningLinearForest (G \ H) hlrH' hα hα1 hεα hεp
        hεn hdegH (L i) (hLeven i hik'') (hL2 i hik'') (hL i hik'')
      let F' : ℕ → SimpleGraph (Fin n) := fun j => if j = i then Fnew else F j
      have hF'i : F' i = Fnew := if_pos rfl
      have hF'j : ∀ j, j ≠ i → F' j = F j := fun j hj => if_neg hj
      have hsup' : ∀ j ≤ i, (Finset.range j).sup F' = (Finset.range j).sup F := by
        intro j hj
        refine Finset.sup_congr rfl (fun l hl => ?_)
        rw [Finset.mem_range] at hl
        exact hF'j l (by omega)
      refine ⟨F', ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · rw [hji, hF'i]; exact hFnew
        · rw [hF'j j hji]; exact hF1 j (by omega)
      · intro j hj
        have hji : j ≤ i := by omega
        rw [hsup' j hji]
        by_cases hje : j = i
        · rw [hje, hF'i, ← hH]
          exact hFnew_le
        · rw [hF'j j hje]
          exact hF2 j (by omega)
  exact key k le_rfl


/-! ## The edge-disjoint spanning linear forests, indexed by `Fin k` -/

theorem exists_edgeDisjoint_spanningLinearForests (G : SimpleGraph (Fin n))
    {p ε ε₀ α : ℝ} {k : ℕ} (L : Fin k → Finset (Fin n))
    (hn : 0 < n) (hlr : LowerReg G p ε₀) (hε₀ : 0 < ε₀)
    (hdegrade : max (2 * ε₀) (2 * Real.sqrt (2 * (k : ℝ) / (n : ℝ))) ≤ ε)
    (hα : 0 < α) (hα1 : α ≤ 1 / 10)
    (hεα : ε ≤ α / 100) (hεp : ε ≤ p / 100) (hεn : 1 ≤ ε * (n : ℝ))
    (hdeg : α * (n : ℝ) + 2 * (k : ℝ) ≤ (minDeg G : ℝ))
    (hLeven : ∀ i, Even (L i).card) (hL2 : ∀ i, 2 ≤ (L i).card)
    (hL : ∀ i, ((L i).card : ℝ) ≤ 2 * α * (n : ℝ) / 5) :
    ∃ F : Fin k → SimpleGraph (Fin n),
      (∀ i, IsSpanningLinearForestWithLeaves (F i) (L i)) ∧
      (∀ i, F i ≤ G \ (Finset.univ.filter (fun j : Fin k => j < i)).sup F) := by
  classical
  let L' : ℕ → Finset (Fin n) := fun j => if h : j < k then L ⟨j, h⟩ else ∅
  have hL' : ∀ j (hj : j < k), L' j = L ⟨j, hj⟩ := fun j hj => dif_pos hj
  obtain ⟨Fseq, hF1, hF2⟩ := exists_forests_aux G k L' hn hlr hε₀ hdegrade hα hα1 hεα hεp hεn hdeg
    (fun j hj => by rw [hL' j hj]; exact hLeven ⟨j, hj⟩)
    (fun j hj => by rw [hL' j hj]; exact hL2 ⟨j, hj⟩)
    (fun j hj => by rw [hL' j hj]; exact hL ⟨j, hj⟩)
  refine ⟨fun i => Fseq (i : ℕ), ?_, ?_⟩
  · intro i
    have h := hF1 (i : ℕ) i.isLt
    rw [hL' (i : ℕ) i.isLt] at h
    exact h
  · intro i
    have himg : (Finset.univ.filter (fun j : Fin k => j < i)).image Fin.val
        = Finset.range (i : ℕ) := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro ha
        exact ⟨⟨a, lt_trans ha i.isLt⟩, ha, rfl⟩
    have hsup : ((Finset.univ.filter (fun j : Fin k => j < i)).sup
          (fun j : Fin k => Fseq (j : ℕ)))
        = (Finset.range (i : ℕ)).sup Fseq := by
      rw [← himg, Finset.sup_image]
      rfl
    rw [hsup]
    exact hF2 (i : ℕ) i.isLt


theorem sdiff_le' {G H : SimpleGraph (Fin n)} : G \ H ≤ G :=
  fun u v huv => ((SimpleGraph.sdiff_adj G H u v).mp huv).1

theorem sdiff_sup_self' {G H : SimpleGraph (Fin n)} (h : H ≤ G) : H ⊔ (G \ H) = G := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨h, sdiff_le'⟩
  · intro u v huv
    simp only [SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    by_cases h2 : H.Adj u v
    · exact Or.inl h2
    · exact Or.inr ⟨huv, h2⟩

theorem eventually_ge_const (T : ℝ) : ∀ᶠ k : ℕ in Filter.atTop, T ≤ (k : ℝ) :=
  Filter.eventually_atTop.mpr ⟨⌈T⌉₊ + 1, fun k hk => le_trans (Nat.le_ceil T) (by
    have : ⌈T⌉₊ ≤ k := by omega
    exact_mod_cast this)⟩

end

end Work.Deep.GKO
