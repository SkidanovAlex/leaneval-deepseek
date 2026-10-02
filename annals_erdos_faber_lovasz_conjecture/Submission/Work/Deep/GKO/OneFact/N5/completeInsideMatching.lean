import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.StepTools
import Submission.Work.Deep.GKO.OneFact.N5.stepPathAux
import Submission.Work.Deep.GKO.OneFact.N5.exists_dumpSet
import Submission.Work.Deep.GKO.OneFact.N5.even_card_uncov
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.RegVocab

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO.OneFact.N5

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Deleting the edges inside a mate-closed vertex set -/

/-- `N` with every edge whose two ends lie in `D` deleted. -/
def delInside (N : SimpleGraph (Fin n)) (D : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := N.Adj x y ∧ x ∉ D ∧ y ∉ D
  symm := Std.Symm.mk (fun x y h => ⟨(N.adj_comm x y).mp h.1, h.2.2, h.2.1⟩)
  loopless := Std.Irrefl.mk (fun x h => N.loopless.1 x h.1)

theorem delInside_adj {N : SimpleGraph (Fin n)} {D : Finset (Fin n)} {x y : Fin n} :
    (delInside N D).Adj x y ↔ N.Adj x y ∧ x ∉ D ∧ y ∉ D := Iff.rfl

theorem delInside_le (N : SimpleGraph (Fin n)) (D : Finset (Fin n)) : delInside N D ≤ N :=
  fun x y h => h.1

theorem isMatching'_delInside {N : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hN : Work.Deep.GKO.IsMatching' N) : Work.Deep.GKO.IsMatching' (delInside N D) :=
  fun v w w' h h' => hN v w w' h.1 h'.1

/-- If `D` is closed under `N`-mates, then so is its complement. -/
theorem nmate_notMem {N : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hD : ∀ x ∈ D, ∀ y, N.Adj x y → y ∈ D) {x y : Fin n} (hx : x ∉ D) (h : N.Adj x y) :
    y ∉ D := fun hy => hx (hD y hy x ((N.adj_comm x y).mp h))

theorem mem_uncov_delInside {N : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hD : ∀ x ∈ D, ∀ y, N.Adj x y → y ∈ D) (x : Fin n) :
    x ∈ uncov (delInside N D) ↔ x ∈ uncov N ∨ x ∈ D := by
  rw [mem_uncov_iff, mem_uncov_iff]
  constructor
  · intro h
    by_cases hx : x ∈ D
    · exact Or.inr hx
    · refine Or.inl fun y hy => ?_
      by_cases hyD : y ∈ D
      · exact absurd (hD y hyD x ((N.adj_comm x y).mp hy)) hx
      · exact h y ⟨hy, hx, hyD⟩
  · rintro (h | hx) y ⟨hy, hxD, -⟩
    · exact h y hy
    · exact absurd hx hxD

theorem delInside_agree {N : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hD : ∀ x ∈ D, ∀ y, N.Adj x y → y ∈ D) {x : Fin n} (hx : x ∉ D) (y : Fin n) :
    (delInside N D).Adj x y ↔ N.Adj x y := by
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, hx, nmate_notMem hD hx h⟩

/-! ## Enumerating a finset -/

/-- The `i`-th element of a finset of cardinality `a`. -/
noncomputable def enumOf (s : Finset (Fin n)) (a : ℕ) (h : s.card = a) : Fin a ≃ ↥s :=
  (finCongr h).symm.trans (Finset.equivFin s).symm

theorem enumOf_mem (s : Finset (Fin n)) (a : ℕ) (h : s.card = a) (i : Fin a) :
    (enumOf s a h i : Fin n) ∈ s := (enumOf s a h i).2

theorem enumOf_surjective (s : Finset (Fin n)) (a : ℕ) (h : s.card = a) {x : Fin n}
    (hx : x ∈ s) : ∃ i : Fin a, (enumOf s a h i : Fin n) = x :=
  ⟨(enumOf s a h).symm ⟨x, hx⟩, by simp⟩

theorem enumOf_injective (s : Finset (Fin n)) (a : ℕ) (h : s.card = a) :
    Function.Injective fun i : Fin a => (enumOf s a h i : Fin n) :=
  fun i j hij => (enumOf s a h).injective (Subtype.ext hij)

/-! ## The flip sequence -/

/-- The sequence of matchings obtained from `M₀` by flipping the paths of a family one by one. -/
noncomputable def flipSeq {n a : ℕ} {N K : SimpleGraph (Fin n)} {F U' : Finset (Fin n)}
    {φ ψ : Fin a → Fin n} {γ : Fin a → Fin 6 → Fin n} (fam : PathFam N K F U' φ ψ a γ)
    (M₀ : SimpleGraph (Fin n)) : ℕ → SimpleGraph (Fin n) :=
  fun k => Nat.rec M₀ (fun j prev =>
    if hj : j < a then ((fam.good ⟨j, hj⟩ hj).toStepPath).flip prev else prev) k

theorem flipSeq_zero {n a : ℕ} {N K : SimpleGraph (Fin n)} {F U' : Finset (Fin n)}
    {φ ψ : Fin a → Fin n} {γ : Fin a → Fin 6 → Fin n} (fam : PathFam N K F U' φ ψ a γ)
    (M₀ : SimpleGraph (Fin n)) : flipSeq fam M₀ 0 = M₀ := rfl

theorem flipSeq_succ {n a : ℕ} {N K : SimpleGraph (Fin n)} {F U' : Finset (Fin n)}
    {φ ψ : Fin a → Fin n} {γ : Fin a → Fin 6 → Fin n} (fam : PathFam N K F U' φ ψ a γ)
    (M₀ : SimpleGraph (Fin n)) {k : ℕ} (hk : k < a) :
    flipSeq fam M₀ (k + 1)
      = ((fam.good ⟨k, hk⟩ hk).toStepPath).flip (flipSeq fam M₀ k) := by
  show (if hj : k < a then ((fam.good ⟨k, hj⟩ hj).toStepPath).flip (flipSeq fam M₀ k)
    else flipSeq fam M₀ k) = _
  rw [dif_pos hk]

/-! ## Vertex sets of a path family -/

theorem usedV_eq_union {N K : SimpleGraph (Fin n)} {F U' : Finset (Fin n)} {a : ℕ}
    (γ : Fin a → Fin 6 → Fin n) (φ ψ : Fin a → Fin n) (k : ℕ)
    (hgood : ∀ i, i.val < k → Good N K F U' φ ψ γ i) (x : Fin n) :
    x ∈ usedV γ k ↔ x ∈ pairsAbove φ ψ k ∨ x ∈ usedW γ k := by
  rw [mem_usedV, mem_pairsAbove, mem_usedW]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [mem_vset] at hx
    rcases hx with h | h | h | h | h | h
    · exact Or.inl ⟨i, hi, Or.inl (by rw [h, (hgood i hi).zero])⟩
    · exact Or.inr ⟨i, hi, Or.inl h⟩
    · exact Or.inr ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inl ⟨i, hi, Or.inr (by rw [h, (hgood i hi).five])⟩
  · rintro (⟨i, hi, h | h⟩ | ⟨i, hi, h | h | h | h⟩)
    · exact ⟨i, hi, mem_vset.mpr (Or.inl (by rw [h, (hgood i hi).zero]))⟩
    · exact ⟨i, hi, mem_vset.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        rw [h, (hgood i hi).five]))))))⟩
    · exact ⟨i, hi, mem_vset.mpr (Or.inr (Or.inl h))⟩
    · exact ⟨i, hi, mem_vset.mpr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨i, hi, mem_vset.mpr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact ⟨i, hi, mem_vset.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩

theorem mem_usedV_succ {a : ℕ} (γ : Fin a → Fin 6 → Fin n) {k : ℕ} (hk : k < a) {x : Fin n} :
    x ∈ usedV γ (k + 1) ↔ x ∈ usedV γ k ∨ x ∈ vset γ ⟨k, hk⟩ := by
  rw [mem_usedV, mem_usedV]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · exact Or.inl ⟨i, hlt, hx⟩
    · have hik : i = ⟨k, hk⟩ := Fin.ext heq
      rw [hik] at hx
      exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), hx⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩

theorem mem_pairsAbove_succ {a : ℕ} (φ ψ : Fin a → Fin n) {k : ℕ} (hk : k < a) {x : Fin n} :
    x ∈ pairsAbove φ ψ (k + 1) ↔ x ∈ pairsAbove φ ψ k ∨ x = φ ⟨k, hk⟩ ∨ x = ψ ⟨k, hk⟩ := by
  rw [mem_pairsAbove, mem_pairsAbove]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · exact Or.inl ⟨i, hlt, h⟩
    · rw [show i = ⟨k, hk⟩ from Fin.ext heq] at h
      exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h | h)
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), h⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inl h⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inr h⟩

theorem mem_usedW_succ {a : ℕ} (γ : Fin a → Fin 6 → Fin n) {k : ℕ} (hk : k < a) {x : Fin n} :
    x ∈ usedW γ (k + 1) ↔ x ∈ usedW γ k
      ∨ x = γ ⟨k, hk⟩ 1 ∨ x = γ ⟨k, hk⟩ 2 ∨ x = γ ⟨k, hk⟩ 3 ∨ x = γ ⟨k, hk⟩ 4 := by
  rw [mem_usedW, mem_usedW]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · exact Or.inl ⟨i, hlt, h⟩
    · rw [show i = ⟨k, hk⟩ from Fin.ext heq] at h
      exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h | h | h | h)
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), h⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inl h⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inr (Or.inl h)⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inr (Or.inr (Or.inr h))⟩

/-! ## The main theorem -/

theorem completeInsideMatching {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (N K : SimpleGraph (Fin n)) (hN : Work.Deep.GKO.IsMatching' N)
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hKbip : ∀ u v, K.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (F : Finset (Fin n)) {q ε : ℝ} {s D : ℕ} (hq : 0 < q) (hε : 0 < ε)
    (hlr : Work.Deep.GKO.BipLowerReg K A B q ε)
    (hU : (Work.Deep.GKO.OneFact.N5.uncov N).card ≤ s)
    (hdeg : ∀ v, D ≤ Work.Deep.GKO.degIn K v (Finset.univ \ F))
    (hroom : ε * (n : ℝ) + ((2 * F.card + 14 * s : ℕ) : ℝ) < (D : ℝ)) :
    ∃ P : SimpleGraph (Fin n), Work.Deep.GKO.IsPerfectMatching' (N ⊔ K) P ∧
      (∀ v ∈ F, v ∉ Work.Deep.GKO.OneFact.N5.uncov N → ¬ Work.Deep.GKO.OneFact.N5.Rematched N P v) ∧
      (({v : Fin n | v ∉ Work.Deep.GKO.OneFact.N5.uncov N ∧
        Work.Deep.GKO.OneFact.N5.Rematched N P v} : Set (Fin n)).ncard ≤
        5 * (Work.Deep.GKO.OneFact.N5.uncov N).card)
:= by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨⊥, ⟨fun x y h => h.elim, fun v => Fin.elim0 v⟩, fun v _ _ => Fin.elim0 v, ?_⟩
    have : ({v : Fin 0 | ¬v ∈ uncov N ∧ Rematched N ⊥ v} : Set (Fin 0)) = ∅ := by
      ext v; exact Fin.elim0 v
    rw [this]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    set U : Finset (Fin n) := uncov N with hUdef
    set AA : ℕ := (U ∩ A).card with hAA
    set BB : ℕ := (U ∩ B).card with hBB
    set a : ℕ := max AA BB with ha
    have hUeq : U = (U ∩ A) ∪ (U ∩ B) := by
      ext x
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (by rw [hcov]; exact Finset.mem_univ x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
        · exact hx
        · exact hx
    have hUdisj : Disjoint (U ∩ A) (U ∩ B) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact Finset.disjoint_left.mp hAB (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
    have hUcard : U.card = AA + BB := by
      rw [hUeq, Finset.card_union_of_disjoint hUdisj, hAA, hBB]
    have heven : Even U.card := by
      rw [hUdef]; exact even_card_uncov A B hAB hcov hcard N hN hNin
    have hAA_le : AA ≤ s := by
      rw [hAA]
      exact le_trans (Finset.card_le_card (Finset.inter_subset_left)) hU
    have hBB_le : BB ≤ s := by
      rw [hBB]
      exact le_trans (Finset.card_le_card (Finset.inter_subset_left)) hU
    have ha_le : a ≤ s := by
      rw [ha]; exact max_le hAA_le hBB_le
    obtain ⟨v₀⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    have hdeg_le_B : Work.Deep.GKO.degIn K v₀ (Finset.univ \ F) ≤ B.card := by
      rcases Finset.mem_union.mp (by rw [hcov]; exact Finset.mem_univ v₀) with hv | hv
      · exact Finset.card_le_card fun x hx => by
          rw [Work.Deep.GKO.mem_nbrFinset] at hx
          rcases hKbip v₀ x hx.2 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · exact absurd h (Finset.disjoint_left.mp hAB hv)
      · have hA : Work.Deep.GKO.degIn K v₀ (Finset.univ \ F) ≤ A.card :=
          Finset.card_le_card fun x hx => by
            rw [Work.Deep.GKO.mem_nbrFinset] at hx
            rcases hKbip v₀ x hx.2 with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd h (Finset.disjoint_left.mp hAB.symm hv)
            · exact h
        rwa [hcard] at hA
    have hdeg_le_A : Work.Deep.GKO.degIn K v₀ (Finset.univ \ F) ≤ A.card := by
      rcases Finset.mem_union.mp (by rw [hcov]; exact Finset.mem_univ v₀) with hv | hv
      · have hB : Work.Deep.GKO.degIn K v₀ (Finset.univ \ F) ≤ B.card :=
          Finset.card_le_card fun x hx => by
            rw [Work.Deep.GKO.mem_nbrFinset] at hx
            rcases hKbip v₀ x hx.2 with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · exact absurd h (Finset.disjoint_left.mp hAB hv)
        rwa [← hcard] at hB
      · exact Finset.card_le_card fun x hx => by
          rw [Work.Deep.GKO.mem_nbrFinset] at hx
          rcases hKbip v₀ x hx.2 with ⟨h, -⟩ | ⟨-, h⟩
          · exact absurd h (Finset.disjoint_left.mp hAB.symm hv)
          · exact h
    have hbigB : AA + 2 * F.card ≤ B.card := by
      have h1 : ((AA + 2 * F.card : ℕ) : ℝ) < (B.card : ℝ) := by
        have h2 : ((AA + 2 * F.card : ℕ) : ℝ) ≤ (s : ℝ) + 2 * (F.card : ℝ) := by
          have h := Nat.add_le_add_right hAA_le (2 * F.card)
          exact_mod_cast h
        have h3 : (s : ℝ) + 2 * (F.card : ℝ)
            ≤ ε * (n : ℝ) + ((2 * F.card + 14 * s : ℕ) : ℝ) := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hε0 : (0 : ℝ) < ε := hε
          push_cast
          nlinarith [hε0.le, hn0]
        have h4 : (D : ℝ) ≤ (B.card : ℝ) := by
          exact_mod_cast le_trans (hdeg v₀) hdeg_le_B
        linarith [hroom, h2, h3]
      exact_mod_cast le_of_lt h1
    have hbigA : BB + 2 * F.card ≤ A.card := by
      have h1 : ((BB + 2 * F.card : ℕ) : ℝ) < (A.card : ℝ) := by
        have h2 : ((BB + 2 * F.card : ℕ) : ℝ) ≤ (s : ℝ) + 2 * (F.card : ℝ) := by
          have h := Nat.add_le_add_right hBB_le (2 * F.card)
          exact_mod_cast h
        have h3 : (s : ℝ) + 2 * (F.card : ℝ)
            ≤ ε * (n : ℝ) + ((2 * F.card + 14 * s : ℕ) : ℝ) := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hε0 : (0 : ℝ) < ε := hε
          push_cast
          nlinarith [hε0.le, hn0]
        have h4 : (D : ℝ) ≤ (A.card : ℝ) := by
          exact_mod_cast le_trans (hdeg v₀) hdeg_le_A
        linarith [hroom, h2, h3]
      exact_mod_cast le_of_lt h1
    -- the shared construction
    have hmain : ∀ Dd : Finset (Fin n), ((U ∪ Dd) ∩ A).card = a → ((U ∪ Dd) ∩ B).card = a →
        Disjoint Dd F → Disjoint Dd U → (∀ x ∈ Dd, ∀ y, N.Adj x y → y ∈ Dd) →
        Dd.card + 4 * a ≤ 5 * U.card →
        ∃ P : SimpleGraph (Fin n), Work.Deep.GKO.IsPerfectMatching' (N ⊔ K) P ∧
          (∀ v ∈ F, v ∉ U → ¬ Rematched N P v) ∧
          (({v : Fin n | v ∉ U ∧ Rematched N P v} : Set (Fin n)).ncard ≤ 5 * U.card) := by
      intro Dd hcardA hcardB hDF hDU hDclosed hDcount
      set U' : Finset (Fin n) := U ∪ Dd with hU'def
      have hUmem : ∀ x, x ∈ U' ↔ x ∈ U ∨ x ∈ Dd := fun x => Finset.mem_union
      have hUsub : U ⊆ U' := fun x hx => Finset.mem_union_left _ hx
      have hDsubU' : Dd ⊆ U' := fun x hx => Finset.mem_union_right _ hx
      have hU'closed : ∀ x y, N.Adj x y → (x ∈ U' ↔ y ∈ U') := by
        intro x y hxy
        constructor
        · intro hx
          rcases (hUmem x).mp hx with hxU | hxD
          · exact absurd hxy (((mem_uncov_iff N x).mp (by rw [← hUdef]; exact hxU)) y)
          · exact (hUmem y).mpr (Or.inr (hDclosed x hxD y hxy))
        · intro hy
          rcases (hUmem y).mp hy with hyU | hyD
          · exact absurd ((N.adj_comm x y).mp hxy)
              (((mem_uncov_iff N y).mp (by rw [← hUdef]; exact hyU)) x)
          · exact (hUmem x).mpr (Or.inr (hDclosed y hyD x ((N.adj_comm x y).mp hxy)))
      have hcover : ∀ x, x ∉ U' → ∃ y, N.Adj x y := by
        intro x hx
        refine (not_mem_uncov_iff N x).mp ?_
        rw [← hUdef]
        intro hxU
        exact hx ((hUmem x).mpr (Or.inl hxU))
      set φ : Fin a → Fin n := fun i => (enumOf (U' ∩ A) a hcardA i : Fin n) with hφdef
      set ψ : Fin a → Fin n := fun i => (enumOf (U' ∩ B) a hcardB i : Fin n) with hψdef
      have hφA : ∀ i, φ i ∈ A := by
        intro i; rw [hφdef]
        exact (Finset.mem_inter.mp (enumOf_mem (U' ∩ A) a hcardA i)).2
      have hφU' : ∀ i, φ i ∈ U' := by
        intro i; rw [hφdef]
        exact (Finset.mem_inter.mp (enumOf_mem (U' ∩ A) a hcardA i)).1
      have hψB : ∀ i, ψ i ∈ B := by
        intro i; rw [hψdef]
        exact (Finset.mem_inter.mp (enumOf_mem (U' ∩ B) a hcardB i)).2
      have hψU' : ∀ i, ψ i ∈ U' := by
        intro i; rw [hψdef]
        exact (Finset.mem_inter.mp (enumOf_mem (U' ∩ B) a hcardB i)).1
      have hφinj : Function.Injective φ := by
        intro i j h; rw [hφdef] at h; exact enumOf_injective (U' ∩ A) a hcardA h
      have hψinj : Function.Injective ψ := by
        intro i j h; rw [hψdef] at h; exact enumOf_injective (U' ∩ B) a hcardB h
      have hne : ∀ i : Fin a, φ i ≠ ψ i := fun i h =>
        Finset.disjoint_left.mp hAB (hφA i) (h ▸ hψB i)
      have hpairsU' : pairsAbove φ ψ a = U' := by
        ext x
        rw [mem_pairsAbove]
        constructor
        · rintro ⟨i, -, h | h⟩
          · rw [h]; exact hφU' i
          · rw [h]; exact hψU' i
        · intro hx
          rcases Finset.mem_union.mp (by rw [hcov]; exact Finset.mem_univ x) with h | h
          · obtain ⟨i, hi⟩ := enumOf_surjective (U' ∩ A) a hcardA
              (Finset.mem_inter.mpr ⟨hx, h⟩)
            exact ⟨i, i.isLt, Or.inl hi.symm⟩
          · obtain ⟨i, hi⟩ := enumOf_surjective (U' ∩ B) a hcardB
              (Finset.mem_inter.mpr ⟨hx, h⟩)
            exact ⟨i, i.isLt, Or.inr hi.symm⟩
      have hstep_room : ∀ (γ : Fin a → Fin 6 → Fin n) {k : ℕ}, k < a →
          ε * (n : ℝ) + ((2 * a + 2 * (usedW γ k).card + F.card : ℕ) : ℝ) < (D : ℝ) := by
        intro γ k hk
        have h1 : (usedW γ k).card ≤ 4 * k := usedW_card γ k
        have h2 : 8 * k ≤ 8 * a := Nat.mul_le_mul_left 8 (le_of_lt hk)
        have h3 : 8 * a ≤ 8 * s := Nat.mul_le_mul_left 8 ha_le
        have h4 : 2 * a + 2 * (usedW γ k).card + F.card ≤ 2 * s + 8 * s + F.card := by omega
        have h5 : 2 * s + 8 * s + F.card ≤ 2 * F.card + 14 * s := by omega
        have hcast : ((2 * a + 2 * (usedW γ k).card + F.card : ℕ) : ℝ)
            ≤ ((2 * F.card + 14 * s : ℕ) : ℝ) := by exact_mod_cast h4.trans h5
        have hroom' : ε * (n : ℝ) + ((2 * F.card + 14 * s : ℕ) : ℝ) < (D : ℝ) := hroom
        linarith
      -- (A) building the paths
      have hbuild : ∀ k, k ≤ a → ∃ γ : Fin a → Fin 6 → Fin n, PathFam N K F U' φ ψ k γ := by
        intro k
        induction k with
        | zero =>
          intro _
          refine ⟨fun i _ => φ i, ⟨fun i hi => absurd hi (Nat.not_lt_zero i.val),
            fun i i' j j' hi => absurd hi (Nat.not_lt_zero i.val)⟩⟩
        | succ k ih =>
          intro hk
          have hka : k < a := hk
          obtain ⟨γ, hγ⟩ := ih (Nat.le_of_succ_le hk)
          obtain ⟨v, hv_inj, hv0, hv5, hvK01, hvN12, hvK23, hvN34, hvK45,
            hv1, hv2, hv3, hv4⟩ :=
            exists_stepPath_aux A B U' F (usedW γ k) N K hAB hN hNin hKbip hU'closed hcover
              (hφA ⟨k, hka⟩) (hψB ⟨k, hka⟩) (hφU' ⟨k, hka⟩) (hψU' ⟨k, hka⟩)
              (hne ⟨k, hka⟩) hq hε hlr hdeg (le_of_eq hcardA) (le_of_eq hcardB)
              (hstep_room γ hka)
          have hvW : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → v j ∉ usedW γ k := by
            intro j hj hj'
            fin_cases j
            · exact absurd rfl hj
            · exact hv1.2.2
            · exact hv2.2.2
            · exact hv3.2.2
            · exact hv4.2.2
            · exact absurd rfl hj'
          have hWin : ∀ (i : Fin a), i.val < k → ∀ j : Fin 6, j ≠ 0 → j ≠ 5 →
              γ i j ∈ usedW γ k := by
            intro i hi j hj hj'
            rw [mem_usedW]
            fin_cases j
            · exact absurd rfl hj
            · exact ⟨i, hi, Or.inl rfl⟩
            · exact ⟨i, hi, Or.inr (Or.inl rfl)⟩
            · exact ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
            · exact ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩
            · exact absurd rfl hj'
          refine ⟨Function.update γ ⟨k, hka⟩ v, ?_, ?_⟩
          · intro i hi
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
            · have hne' : i ≠ ⟨k, hka⟩ := by
                intro hh; rw [hh] at hlt; exact absurd hlt (Nat.lt_irrefl k)
              have hgood := hγ.good i hlt
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa only [Function.update_of_ne hne'] using hgood.inj
              · simpa only [Function.update_of_ne hne'] using hgood.zero
              · simpa only [Function.update_of_ne hne'] using hgood.five
              · simpa only [Function.update_of_ne hne'] using hgood.K01
              · simpa only [Function.update_of_ne hne'] using hgood.N12
              · simpa only [Function.update_of_ne hne'] using hgood.K23
              · simpa only [Function.update_of_ne hne'] using hgood.N34
              · simpa only [Function.update_of_ne hne'] using hgood.K45
              · intro j hj hj'
                simpa only [Function.update_of_ne hne'] using hgood.avoid j hj hj'
            · have hik : i = ⟨k, hka⟩ := Fin.ext heq
              subst hik
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa only [Function.update_self] using hv_inj
              · simpa only [Function.update_self] using hv0
              · simpa only [Function.update_self] using hv5
              · simpa only [Function.update_self] using hvK01
              · simpa only [Function.update_self] using hvN12
              · simpa only [Function.update_self] using hvK23
              · simpa only [Function.update_self] using hvN34
              · simpa only [Function.update_self] using hvK45
              · intro j hj hj'
                refine ⟨?_, ?_⟩
                · simpa only [Function.update_self] using (show v j ∉ F from by
                    fin_cases j
                    · exact absurd rfl hj
                    · exact hv1.1
                    · exact hv2.1
                    · exact hv3.1
                    · exact hv4.1
                    · exact absurd rfl hj')
                · simpa only [Function.update_self] using (show v j ∉ U' from by
                    fin_cases j
                    · exact absurd rfl hj
                    · exact hv1.2.1
                    · exact hv2.2.1
                    · exact hv3.2.1
                    · exact hv4.2.1
                    · exact absurd rfl hj')
          · intro i i' j j' hi hi' hj0 hj5 hj0' hj5' heq
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq_i
            · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt' | heq_i'
              · have hii : i ≠ ⟨k, hka⟩ := by
                  intro hh; rw [hh] at hlt; exact absurd hlt (Nat.lt_irrefl k)
                have hii' : i' ≠ ⟨k, hka⟩ := by
                  intro hh; rw [hh] at hlt'; exact absurd hlt' (Nat.lt_irrefl k)
                refine hγ.disj i i' j j' hlt hlt' hj0 hj5 hj0' hj5' ?_
                simpa only [Function.update_of_ne hii, Function.update_of_ne hii'] using heq
              · have hik' : i' = ⟨k, hka⟩ := Fin.ext heq_i'
                subst hik'
                have hii : i ≠ ⟨k, hka⟩ := by
                  intro hh; rw [hh] at hlt; exact absurd hlt (Nat.lt_irrefl k)
                have h1 : γ i j = v j' := by
                  have h2 := heq
                  rwa [Function.update_of_ne hii, Function.update_self] at h2
                exact absurd (h1 ▸ hWin i hlt j hj0 hj5) (hvW j' hj0' hj5')
            · have hik : i = ⟨k, hka⟩ := Fin.ext heq_i
              subst hik
              rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt' | heq_i'
              · have hii' : i' ≠ ⟨k, hka⟩ := by
                  intro hh; rw [hh] at hlt'; exact absurd hlt' (Nat.lt_irrefl k)
                have h1 : v j = γ i' j' := by
                  have h2 := heq
                  rwa [Function.update_self, Function.update_of_ne hii'] at h2
                exact absurd (h1 ▸ hWin i' hlt' j' hj0' hj5') (hvW j hj0 hj5)
              · exact (Fin.ext heq_i').symm
      obtain ⟨γ, hγ⟩ := hbuild a le_rfl
      -- (B) the flip sequence
      set P₀ : SimpleGraph (Fin n) := delInside N Dd with hP₀def
      have hP₀match : Work.Deep.GKO.IsMatching' P₀ := by
        rw [hP₀def]; exact isMatching'_delInside hN
      have hP₀le : P₀ ≤ N ⊔ K := by
        rw [hP₀def]
        intro x y h
        exact (SimpleGraph.sup_adj N K x y).mpr (Or.inl (delInside_le N Dd h))
      have hseq : ∀ k ≤ a, Work.Deep.GKO.IsMatching' (flipSeq hγ P₀ k) ∧
          (flipSeq hγ P₀ k ≤ N ⊔ K) ∧
          (∀ x, x ∉ Dd → x ∉ usedV γ k → ∀ y, (flipSeq hγ P₀ k).Adj x y ↔ N.Adj x y) ∧
          (∀ x, x ∈ uncov (flipSeq hγ P₀ k) ↔ x ∈ U' ∧ x ∉ pairsAbove φ ψ k) := by
        intro k
        induction k with
        | zero =>
          intro _
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [flipSeq_zero]; exact hP₀match
          · rw [flipSeq_zero]; exact hP₀le
          · intro x hxD _ y
            rw [flipSeq_zero, hP₀def]
            exact delInside_agree hDclosed hxD y
          · intro x
            rw [flipSeq_zero, hP₀def, mem_uncov_delInside hDclosed, ← hUdef, hU'def,
              Finset.mem_union]
            constructor
            · intro h
              exact ⟨h, by
                rw [mem_pairsAbove]
                rintro ⟨i, hi, -⟩
                exact absurd hi (Nat.not_lt_zero i.val)⟩
            · rintro ⟨h, -⟩
              exact h
        | succ k ih =>
          intro hk
          have hka : k < a := hk
          obtain ⟨ihmatch, ihle, ihagree, ihuncov⟩ := ih (Nat.le_of_succ_le hk)
          have hgk : Good N K F U' φ ψ γ ⟨k, hka⟩ := hγ.good ⟨k, hka⟩ hka
          have hflip : flipSeq hγ P₀ (k + 1)
              = (hgk.toStepPath).flip (flipSeq hγ P₀ k) := flipSeq_succ hγ P₀ hka
          -- the vertices of the `k`-th path avoid `Dd` and the already used set
          have hvD : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → γ ⟨k, hka⟩ j ∉ Dd := fun j hj hj5 h =>
            (hgk.avoid j hj hj5).2 (hDsubU' h)
          have hvV : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → γ ⟨k, hka⟩ j ∉ usedV γ k := by
            intro j hj hj5 hmem
            rw [usedV_eq_union γ φ ψ k (fun i _ => hγ.good i i.isLt)] at hmem
            rcases hmem with hmem | hmem
            · rw [mem_pairsAbove] at hmem
              obtain ⟨i, hi0, h | h⟩ := hmem
              · exact (hgk.avoid j hj hj5).2 (by rw [h]; exact hφU' i)
              · exact (hgk.avoid j hj hj5).2 (by rw [h]; exact hψU' i)
            · rw [mem_usedW] at hmem
              obtain ⟨i, hi, h | h | h | h⟩ := hmem
              · exact absurd (show i.val < k from hi)
                  (by rw [hγ.disj i ⟨k, hka⟩ 1 j i.isLt hka (by decide) (by decide) hj hj5 h.symm]
                      at hi; exact absurd hi (Nat.lt_irrefl k))
              · exact absurd (show i.val < k from hi)
                  (by rw [hγ.disj i ⟨k, hka⟩ 2 j i.isLt hka (by decide) (by decide) hj hj5 h.symm]
                      at hi; exact absurd hi (Nat.lt_irrefl k))
              · exact absurd (show i.val < k from hi)
                  (by rw [hγ.disj i ⟨k, hka⟩ 3 j i.isLt hka (by decide) (by decide) hj hj5 h.symm]
                      at hi; exact absurd hi (Nat.lt_irrefl k))
              · exact absurd (show i.val < k from hi)
                  (by rw [hγ.disj i ⟨k, hka⟩ 4 j i.isLt hka (by decide) (by decide) hj hj5 h.symm]
                      at hi; exact absurd hi (Nat.lt_irrefl k))
          have h12 : (flipSeq hγ P₀ k).Adj (γ ⟨k, hka⟩ 1) (γ ⟨k, hka⟩ 2) :=
            (ihagree _ (hvD 1 (by decide) (by decide)) (hvV 1 (by decide) (by decide)) _).mpr hgk.N12
          have h34 : (flipSeq hγ P₀ k).Adj (γ ⟨k, hka⟩ 3) (γ ⟨k, hka⟩ 4) :=
            (ihagree _ (hvD 3 (by decide) (by decide)) (hvV 3 (by decide) (by decide)) _).mpr hgk.N34
          have hno0 : ∀ y, ¬ (flipSeq hγ P₀ k).Adj (γ ⟨k, hka⟩ 0) y := by
            intro y hy
            have hunc : γ ⟨k, hka⟩ 0 ∈ uncov (flipSeq hγ P₀ k) := by
              rw [ihuncov]
              refine ⟨by rw [hgk.zero]; exact hφU' ⟨k, hka⟩, ?_⟩
              rw [mem_pairsAbove]
              rintro ⟨i, hi, h | h⟩
              · refine absurd (show i = ⟨k, hka⟩ from hφinj (by rw [← h, hgk.zero])) ?_
                intro hh
                exact absurd hi (by rw [hh]; exact Nat.lt_irrefl k)
              · exact absurd (by rw [← hgk.zero, h]; exact hψB i)
                  (Finset.disjoint_left.mp hAB (hφA ⟨k, hka⟩))
            exact (mem_uncov_iff _ _).mp hunc y hy
          have hno5 : ∀ y, ¬ (flipSeq hγ P₀ k).Adj (γ ⟨k, hka⟩ 5) y := by
            intro y hy
            have hunc : γ ⟨k, hka⟩ 5 ∈ uncov (flipSeq hγ P₀ k) := by
              rw [ihuncov]
              refine ⟨by rw [hgk.five]; exact hψU' ⟨k, hka⟩, ?_⟩
              rw [mem_pairsAbove]
              rintro ⟨i, hi, h | h⟩
              · exact absurd (by rw [← h, hgk.five]; exact hψB ⟨k, hka⟩)
                  (Finset.disjoint_left.mp hAB (hφA i))
              · refine absurd (show i = ⟨k, hka⟩ from hψinj (by rw [← h, hgk.five])) ?_
                intro hh
                exact absurd hi (by rw [hh]; exact Nat.lt_irrefl k)
            exact (mem_uncov_iff _ _).mp hunc y hy
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hflip]
            exact hgk.toStepPath.flip_matching ihmatch h12 h34 hno0 hno5
          · rw [hflip]
            exact hgk.toStepPath.flip_le ihle
          · intro x hxD hxV y
            rw [hflip]
            have hxv : x ∉ vset γ ⟨k, hka⟩ := fun hc =>
              hxV ((mem_usedV_succ γ hka).mpr (Or.inr hc))
            have hxu : x ∉ usedV γ k := fun hc =>
              hxV ((mem_usedV_succ γ hka).mpr (Or.inl hc))
            rw [hgk.toStepPath.flip_agree (by
              simpa [StepPath.sverts, vset, Good.toStepPath] using hxv) y]
            exact ihagree x hxD hxu y
          · intro x
            rw [hflip, StepPath.mem_uncov_flip, ihuncov]
            have hsverts : (hgk.toStepPath).sverts = vset γ ⟨k, hka⟩ := by
              simp [StepPath.sverts, vset, Good.toStepPath]
            rw [hsverts]
            constructor
            · rintro ⟨⟨hxU', hxP⟩, hxV⟩
              refine ⟨hxU', fun hp => ?_⟩
              rw [mem_pairsAbove_succ φ ψ hka] at hp
              rcases hp with hp | hp | hp
              · exact hxP hp
              · exact hxV (by rw [mem_vset]; exact Or.inl (by rw [hp, hgk.zero]))
              · exact hxV (by rw [mem_vset]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
                  rw [hp, hgk.five]))))))
            · rintro ⟨hxU', hxP⟩
              refine ⟨⟨hxU', fun hp => hxP ((mem_pairsAbove_succ φ ψ hka).mpr (Or.inl hp))⟩,
                fun hxV => ?_⟩
              rw [mem_vset] at hxV
              rcases hxV with h | h | h | h | h | h
              · exact hxP ((mem_pairsAbove_succ φ ψ hka).mpr
                  (Or.inr (Or.inl (by rw [h, hgk.zero]))))
              · exact (hgk.avoid 1 (by decide) (by decide)).2 (by rw [← h]; exact hxU')
              · exact (hgk.avoid 2 (by decide) (by decide)).2 (by rw [← h]; exact hxU')
              · exact (hgk.avoid 3 (by decide) (by decide)).2 (by rw [← h]; exact hxU')
              · exact (hgk.avoid 4 (by decide) (by decide)).2 (by rw [← h]; exact hxU')
              · exact hxP ((mem_pairsAbove_succ φ ψ hka).mpr
                  (Or.inr (Or.inr (by rw [h, hgk.five]))))
      -- (C) the final matching
      obtain ⟨hmatch, hle, hagree, huncov⟩ := hseq a le_rfl
      have husedV : ∀ x, x ∈ usedV γ a ↔ x ∈ U' ∨ x ∈ usedW γ a := by
        intro x
        rw [usedV_eq_union γ φ ψ a (fun i _ => hγ.good i i.isLt), hpairsU']
      refine ⟨flipSeq hγ P₀ a, ⟨hle, ?_⟩, ?_, ?_⟩
      · intro v
        have hv : v ∉ uncov (flipSeq hγ P₀ a) := by
          rw [huncov]
          rintro ⟨h1, h2⟩
          exact h2 (by rw [hpairsU']; exact h1)
        obtain ⟨w, hw⟩ := (not_mem_uncov_iff (flipSeq hγ P₀ a) v).mp hv
        exact ⟨w, hw, fun w' hw' => hmatch v w' w hw' hw⟩
      · intro v hvF hvU
        have hvD : v ∉ Dd := fun h => (Finset.disjoint_left.mp hDF h) hvF
        have hvW : v ∉ usedW γ a := by
          rw [mem_usedW]
          rintro ⟨i, hi, h | h | h | h⟩
          · exact (hγ.good i hi).avoid 1 (by decide) (by decide) |>.1 (by rw [← h]; exact hvF)
          · exact (hγ.good i hi).avoid 2 (by decide) (by decide) |>.1 (by rw [← h]; exact hvF)
          · exact (hγ.good i hi).avoid 3 (by decide) (by decide) |>.1 (by rw [← h]; exact hvF)
          · exact (hγ.good i hi).avoid 4 (by decide) (by decide) |>.1 (by rw [← h]; exact hvF)
        have hvU' : v ∉ U' := by
          intro h
          rcases (Finset.mem_union.mp h) with h' | h'
          · exact hvU h'
          · exact hvD h'
        have hvV : v ∉ usedV γ a := fun h => (husedV v).mp h |>.elim hvU' hvW
        intro hrem
        obtain ⟨w, hw, hw'⟩ := hrem
        exact hw' ((hagree v hvD hvV w).mp hw)
      · have hsub : ({v : Fin n | v ∉ U ∧ Rematched N (flipSeq hγ P₀ a) v} : Set (Fin n))
            ⊆ ((Dd ∪ usedW γ a : Finset (Fin n)) : Set (Fin n)) := by
          intro v hv
          rw [Finset.mem_coe, Finset.mem_union]
          by_contra hcon
          rw [not_or] at hcon
          obtain ⟨hvD, hvW⟩ := hcon
          have hvU' : v ∉ U' := by
            intro h
            rcases (Finset.mem_union.mp h) with h' | h'
            · exact hv.1 h'
            · exact hvD h'
          have hvV : v ∉ usedV γ a := fun h => ((husedV v).mp h).elim hvU' hvW
          obtain ⟨w, hw, hw'⟩ := hv.2
          exact hw' ((hagree v hvD hvV w).mp hw)
        refine le_trans (Set.ncard_le_ncard hsub) ?_
        rw [Set.ncard_coe_finset]
        have h1 : (Dd ∪ usedW γ a).card ≤ Dd.card + (usedW γ a).card := Finset.card_union_le _ _
        have h2 : (usedW γ a).card ≤ 4 * a := usedW_card γ a
        omega
    -- the two orientations of the dumping
    by_cases hle : BB ≤ AA
    · have heven' : Even (AA - BB) := by
        obtain ⟨m, hm⟩ := heven
        rw [hUcard] at hm
        refine ⟨m - BB, ?_⟩
        omega
      have h2d : 2 * ((AA - BB) / 2) = AA - BB := Nat.two_mul_div_two_of_even heven'
      obtain ⟨D, hDsub, hDcard2, hDF, hDU, -, hDclosed⟩ :=
        exists_dumpSet A B hAB hcov N hN hNin F (d := (AA - BB) / 2)
          (by show 2 * ((AA - BB) / 2) = (uncov N ∩ A).card - (uncov N ∩ B).card
              rw [← hUdef, ← hAA, ← hBB]
              exact h2d)
          (by show (uncov N ∩ A).card + 2 * F.card ≤ B.card
              rw [← hUdef, ← hAA]
              exact hbigB)
      have hDU' : Disjoint D U := hDU
      refine hmain D ?_ ?_ hDF hDU' hDclosed ?_
      · have hsub : (U ∪ D) ∩ A = U ∩ A := by
          ext x
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ⟨hx | hx, hxA⟩
            · exact ⟨hx, hxA⟩
            · exact absurd (hDsub hx) (Finset.disjoint_left.mp hAB hxA)
          · rintro ⟨hx, hxA⟩
            exact ⟨Or.inl hx, hxA⟩
        rw [hsub, ← hAA, ha]
        exact (max_eq_left hle).symm
      · have hsub : (U ∪ D) ∩ B = (U ∩ B) ∪ D := by
          ext x
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ⟨hx | hx, hxB⟩
            · exact Or.inl ⟨hx, hxB⟩
            · exact Or.inr hx
          · rintro (⟨hx, hxB⟩ | hx)
            · exact ⟨Or.inl hx, hxB⟩
            · exact ⟨Or.inr hx, hDsub hx⟩
        have hdisj : Disjoint (U ∩ B) D := by
          rw [Finset.disjoint_left]
          intro x hx hxD
          exact (Finset.disjoint_left.mp hDU hxD) (Finset.mem_inter.mp hx).1
        rw [hsub, Finset.card_union_of_disjoint hdisj, ← hBB, hDcard2, h2d, ha]
        omega
      · rw [hDcard2, h2d, ha, hUcard]
        omega
    · have hlt : AA < BB := not_le.mp hle
      have heven' : Even (BB - AA) := by
        obtain ⟨m, hm⟩ := heven
        rw [hUcard] at hm
        refine ⟨m - AA, ?_⟩
        omega
      have h2d : 2 * ((BB - AA) / 2) = BB - AA := Nat.two_mul_div_two_of_even heven'
      obtain ⟨D, hDsub, hDcard2, hDF, hDU, -, hDclosed⟩ :=
        exists_dumpSet B A hAB.symm (by rw [Finset.union_comm]; exact hcov) N hN
          (fun u v h => (hNin u v h).elim Or.inr Or.inl) F (d := (BB - AA) / 2)
          (by show 2 * ((BB - AA) / 2) = (uncov N ∩ B).card - (uncov N ∩ A).card
              rw [← hUdef, ← hAA, ← hBB]
              exact h2d)
          (by show (uncov N ∩ B).card + 2 * F.card ≤ A.card
              rw [← hUdef, ← hBB]
              exact hbigA)
      have hDU' : Disjoint D U := hDU
      refine hmain D ?_ ?_ hDF hDU' hDclosed ?_
      · have hsub : (U ∪ D) ∩ A = (U ∩ A) ∪ D := by
          ext x
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ⟨hx | hx, hxA⟩
            · exact Or.inl ⟨hx, hxA⟩
            · exact Or.inr hx
          · rintro (⟨hx, hxA⟩ | hx)
            · exact ⟨Or.inl hx, hxA⟩
            · exact ⟨Or.inr hx, hDsub hx⟩
        have hdisj : Disjoint (U ∩ A) D := by
          rw [Finset.disjoint_left]
          intro x hx hxD
          exact (Finset.disjoint_left.mp hDU hxD) (Finset.mem_inter.mp hx).1
        rw [hsub, Finset.card_union_of_disjoint hdisj, ← hAA, hDcard2, h2d, ha]
        omega
      · have hsub : (U ∪ D) ∩ B = U ∩ B := by
          ext x
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ⟨hx | hx, hxB⟩
            · exact ⟨hx, hxB⟩
            · exact absurd (hDsub hx) (Finset.disjoint_left.mp hAB.symm hxB)
          · rintro ⟨hx, hxB⟩
            exact ⟨Or.inl hx, hxB⟩
        rw [hsub, ← hBB, ha]
        exact (max_eq_right hlt.le).symm
      · rw [hDcard2, h2d, ha, hUcard]
        omega

end

end Work.Deep.GKO.OneFact.N5
