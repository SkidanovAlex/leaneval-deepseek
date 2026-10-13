/-
  WilE5 / Cells — the flat leaves of the cell-wise fibrewise stratification recursion are pairwise
  disjoint.

  This file proves `Work.WilE5.Cells.leafDisj`, the disjointness clause of the assembly: for the
  recursion started at a *single* sign cell `C` (`cellSemi X C` is the `SemiPf` set with the one
  disjunct `C`), two flat leaves `flatSemiPfP (cellSemi X C) Ml NΦ σ` and
  `flatSemiPfP (cellSemi X C) Ml NΦ τ` of states at levels `≤ q` are *equal* as soon as they meet.

  The mathematical content is that the sets `Z_σ = (stSemiPf X σ).set` of the recursion form a tree
  of partitions:

  * a state's set is the disjoint union of its flat leaf and the sets of its children
    (`stSemiPf_subset_flatSemiPf_union_children` for the covering, `child_disjoint_flat` and
    `children_disjoint` for the disjointness);
  * consequently two states at the same level have disjoint sets unless they are equal
    (`levelP_pairwise_disjoint`), and the set of a strict descendant avoids the ancestor's flat
    leaf (`descP_disjoint_flat`);
  * the recursion is started once per face pattern, and two different face patterns give disjoint
    initial states (`root_eq_of_mem`, `rootInj_cellSemi`).

  These facts give the statement: if two flat leaves meet at a point, the two states sit at the
  same level (otherwise the point is both in the flat leaf of one state and in the set of a strict
  descendant of the other), and at the same level they must be equal (otherwise their sets are
  disjoint).

  NOTE. `levelP` is defined for every level and the argument above never uses `k ≤ q`: the
  conclusion holds for all `k`, `k'`; the hypothesis `k, k' ∈ Finset.range (q + 1)` of the frozen
  statement is simply not needed.
-/
import Mathlib
import Submission.Work.WilE5.Cells
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.child_subset_parent
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid
import Submission.Work.WilE5.Operators.opMono_step
import Submission.Work.WilE5.Cells.testLt_trichotomy
import Submission.Work.WilE5.Cells.children_disjoint
import Submission.Work.WilE5.Cells.child_disjoint_flat
import Submission.Work.WilE5.Cells.root_eq_of_mem

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Classical
namespace Work.WilE5.Cells
open WilkiesDesign WilkiesDesign.E

/-! ## §0. The local ingredients proved by colleagues

`testLt_trichotomy`, `children_disjoint`, `child_disjoint_flat` and `root_eq_of_mem` are imported
above. -/

/-! ## §1. The descendants of a state under a test-order profile -/

/-- The `n`-fold descendants of a state under the test-order profile `Ml`: the `0`-fold
descendants are the state itself, and the `(n+1)`-fold descendants are the children of the
`n`-fold ones. -/
noncomputable def descP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) : ℕ → List (St p q X.r)
  | 0 => [σ]
  | (k + 1) => (descP X Ml NΦ σ k).flatMap fun τ => childrenP X.c Ml NΦ τ

theorem descP_zero {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r) :
    descP X Ml NΦ σ 0 = [σ] := rfl

theorem descP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r)
    (k : ℕ) :
    descP X Ml NΦ σ (k + 1) =
      (descP X Ml NΦ σ k).flatMap fun τ => childrenP X.c Ml NΦ τ := rfl

theorem mem_descP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r)
    (k : ℕ) {τ : St p q X.r} :
    τ ∈ descP X Ml NΦ σ (k + 1) ↔
      ∃ σ' ∈ descP X Ml NΦ σ k, τ ∈ childrenP X.c Ml NΦ σ' := by
  rw [descP_succ, List.mem_flatMap]

/-- The states at depth `k` of the recursion with profile `Ml` are the `k`-fold descendants of
the initial states. -/
theorem levelP_eq_flatMap_descP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (k : ℕ) :
    levelP X Ml NΦ k = (initStates X).flatMap fun σ => descP X Ml NΦ σ k := by
  induction k with
  | zero => simp [levelP_zero, descP_zero]
  | succ k ih =>
    rw [levelP_succ, ih, List.flatMap_assoc]
    rfl

/-- Splitting levels: the states at level `k + n` are the `n`-fold descendants of the states at
level `k`. -/
theorem levelP_add_descP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (k n : ℕ) :
    levelP X Ml NΦ (k + n) = (levelP X Ml NΦ k).flatMap fun σ => descP X Ml NΦ σ n := by
  induction n with
  | zero => simp [descP_zero]
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 from rfl, levelP_succ, ih, List.flatMap_assoc]
    rfl

/-! ## §2. Membership in the children and in the descendants -/

/-- The children of a state under a profile, spelled out. -/
theorem mem_childrenP_iff {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) {τ : St p q X.r} :
    τ ∈ childrenP X.c Ml NΦ σ ↔ ∃ t ∈ testL q (Ml σ.B.length) NΦ, ∃ s : Bool,
      τ = childSt X.c (Ml σ.B.length) NΦ σ t s := by
  rw [show childrenP X.c Ml NΦ σ =
      (testL q (Ml σ.B.length) NΦ).flatMap
        (fun t => [childSt X.c (Ml σ.B.length) NΦ σ t false,
          childSt X.c (Ml σ.B.length) NΦ σ t true]) from rfl, List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨t, ht, false, rfl⟩
    · exact ⟨t, ht, true, rfl⟩
  · rintro ⟨t, ht, s, rfl⟩
    refine ⟨t, ht, ?_⟩
    cases s <;> simp

/-- A child of a state has its set inside the state's set. -/
theorem childP_subset_parent {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    {σ τ : St p q X.r} (h : τ ∈ childrenP X.c Ml NΦ σ) :
    (stSemiPf X τ).set ⊆ (stSemiPf X σ).set := by
  rw [mem_childrenP_iff] at h
  obtain ⟨t, ht, s, rfl⟩ := h
  exact Strat.child_subset_parent X (Ml σ.B.length) NΦ σ t s

/-- The set of a descendant is contained in the set of the ancestor. -/
theorem stSemiPf_subset_of_mem_descP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (n : ℕ) {σ τ : St p q X.r} (h : τ ∈ descP X Ml NΦ σ n) :
    (stSemiPf X τ).set ⊆ (stSemiPf X σ).set := by
  induction n generalizing τ with
  | zero =>
    rw [descP_zero, List.mem_singleton] at h
    rw [h]
  | succ n ih =>
    rw [mem_descP_succ] at h
    obtain ⟨σ', hσ', hτ⟩ := h
    exact subset_trans (childP_subset_parent X Ml NΦ hτ) (ih hσ')

/-- The flat leaf of a state is contained in its set. -/
theorem flatSemiPfP_subset_stSemiPf {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) : (flatSemiPfP X Ml NΦ σ).set ⊆ (stSemiPf X σ).set := by
  intro x hx
  rw [flatSemiPfP_eq] at hx
  exact semiPfAnd_set_subset (semiPfAnd X (stCond σ))
    (Basic.eqsOf (flatEqs X.c (Ml σ.B.length) NΦ σ)) hx

/-! ## §3. Disjointness of the children of one state -/

/-- Two distinct children of the same state have disjoint sets. -/
theorem childrenP_disjoint {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    {σ σ₁ σ₂ : St p q X.r} (h₁ : σ₁ ∈ childrenP X.c Ml NΦ σ)
    (h₂ : σ₂ ∈ childrenP X.c Ml NΦ σ) (hne : σ₁ ≠ σ₂) :
    Disjoint (stSemiPf X σ₁).set (stSemiPf X σ₂).set := by
  rw [mem_childrenP_iff] at h₁ h₂
  obtain ⟨t, ht, s, rfl⟩ := h₁
  obtain ⟨t', ht', s', rfl⟩ := h₂
  by_cases htt : t = t'
  · subst htt
    by_cases hss : s = s'
    · rw [hss] at hne
      exact absurd rfl hne
    · exact children_disjoint X (Ml σ.B.length) NΦ σ ht ht' (Or.inr hss)
        (fun hc => absurd rfl hc)
  · refine children_disjoint X (Ml σ.B.length) NΦ σ ht ht' (Or.inl htt) ?_
    intro _
    by_cases h1 : testLt t t' = true
    · exact Or.inl h1
    · refine Or.inr (by_contra fun h2 => ?_)
      exact htt (testLt_trichotomy (Bool.eq_false_of_not_eq_true h1)
        (Bool.eq_false_of_not_eq_true h2))

/-! ## §4. The tree structure of the recursion -/

/-- The initial states are injective on points: no two distinct initial states share a point. -/
def RootInj {p q : ℕ} (X : SemiPf (p + q)) : Prop :=
  ∀ ⦃σ τ : St p q X.r⦄, σ ∈ initStates X → τ ∈ initStates X →
    ((stSemiPf X σ).set ∩ (stSemiPf X τ).set).Nonempty → σ = τ

/-- For the recursion started at a single sign cell, the initial states are injective on points:
the recursion is started once per face pattern, and a point determines its face pattern. -/
theorem rootInj_cellSemi {p q : ℕ} (X : SemiPf (p + q)) (C : Basic (p + q) X.r) :
    RootInj (cellSemi X C) := by
  intro σ τ hσ hτ hne
  obtain ⟨z, hzσ, hzτ⟩ := hne
  obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates (cellSemi X C) hσ
  obtain ⟨A', hA', Fy', ε', rfl⟩ := exists_of_mem_initStates (cellSemi X C) hτ
  have hAeq : A = C := by
    have h := hA
    rw [show (cellSemi X C).basics = [C] from rfl] at h
    exact List.mem_singleton.mp h
  have hA'eq : A' = C := by
    have h := hA'
    rw [show (cellSemi X C).basics = [C] from rfl] at h
    exact List.mem_singleton.mp h
  rw [hAeq] at hzσ
  rw [hA'eq] at hzτ
  rw [hAeq, hA'eq]
  exact root_eq_of_mem (cellSemi X C) C Fy Fy' ε ε' hzσ hzτ

/-- Two distinct states of the same level have disjoint sets. -/
theorem levelP_pairwise_disjoint {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (hroot : RootInj X) :
    ∀ n, ∀ σ ∈ levelP X Ml NΦ n, ∀ τ ∈ levelP X Ml NΦ n, σ ≠ τ →
      Disjoint (stSemiPf X σ).set (stSemiPf X τ).set := by
  intro n
  induction n with
  | zero =>
    intro σ hσ τ hτ hne
    rw [levelP_zero] at hσ hτ
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact hne (hroot hσ hτ ⟨x, hx, hx'⟩)
  | succ n ih =>
    intro σ hσ τ hτ hne
    rw [mem_levelP_succ] at hσ hτ
    obtain ⟨σ', hσ', hσc⟩ := hσ
    obtain ⟨τ', hτ', hτc⟩ := hτ
    by_cases h : σ' = τ'
    · subst h
      exact childrenP_disjoint X Ml NΦ hσc hτc hne
    · exact Disjoint.mono (childP_subset_parent X Ml NΦ hσc)
        (childP_subset_parent X Ml NΦ hτc) (ih σ' hσ' τ' hτ' h)

/-- A child of a descendant of `σ` has its set disjoint from the flat leaf of `σ`. -/
theorem descP_children_disjoint_flat {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    ∀ n (σ' : St p q X.r), σ' ∈ descP X Ml NΦ σ n → ∀ (τ : St p q X.r),
      τ ∈ childrenP X.c Ml NΦ σ' → Disjoint (stSemiPf X τ).set (flatSemiPfP X Ml NΦ σ).set := by
  intro n
  induction n with
  | zero =>
    intro σ' hσ' τ hτ
    rw [descP_zero, List.mem_singleton] at hσ'
    rw [hσ'] at hτ
    rw [mem_childrenP_iff] at hτ
    obtain ⟨t, ht, s, rfl⟩ := hτ
    rw [flatSemiPfP_eq]
    exact child_disjoint_flat X (Ml σ.B.length) NΦ σ ht
  | succ n ih =>
    intro σ' hσ' τ hτ
    rw [mem_descP_succ] at hσ'
    obtain ⟨σ'', hσ'', hσ'c⟩ := hσ'
    exact Disjoint.mono_left (childP_subset_parent X Ml NΦ hτ) (ih σ'' hσ'' σ' hσ'c)

/-- The set of a strict descendant of `σ` is disjoint from the flat leaf of `σ`. -/
theorem descP_disjoint_flat {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    ∀ n, 1 ≤ n → ∀ τ ∈ descP X Ml NΦ σ n,
      Disjoint (stSemiPf X τ).set (flatSemiPfP X Ml NΦ σ).set := by
  intro n hn τ hτ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [mem_descP_succ] at hτ
  obtain ⟨σ', hσ', hτc⟩ := hτ
  exact descP_children_disjoint_flat X Ml NΦ σ m σ' hσ' τ hτc

/-! ## §5. The main argument -/

/-- Two flat leaves at *different* levels cannot meet. -/
theorem leafDisj_aux {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q))
    (C : WilkiesDesign.E.Basic (p + q) X.r) (Ml : ℕ → ℕ) (NΦ : ℕ) {k k' : ℕ} (hklt : k < k')
    {σ : Work.WilE5.St p q X.r} (hσ : σ ∈ Work.WilE5.levelP (Work.WilE5.cellSemi X C) Ml NΦ k)
    {τ : Work.WilE5.St p q X.r} (hτ : τ ∈ Work.WilE5.levelP (Work.WilE5.cellSemi X C) Ml NΦ k')
    (hne : ((Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ σ).set ∩
      (Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ τ).set).Nonempty) : False := by
  obtain ⟨z, hzσ, hzτ⟩ := hne
  have hzσ' : z ∈ (stSemiPf (cellSemi X C) σ).set :=
    flatSemiPfP_subset_stSemiPf (cellSemi X C) Ml NΦ σ hzσ
  have hzτ' : z ∈ (stSemiPf (cellSemi X C) τ).set :=
    flatSemiPfP_subset_stSemiPf (cellSemi X C) Ml NΦ τ hzτ
  have hk' : k' = k + (k' - k) := by omega
  rw [hk', levelP_add_descP] at hτ
  obtain ⟨σ₀, hσ₀, hτd⟩ := List.mem_flatMap.mp hτ
  have hzσ₀ : z ∈ (stSemiPf (cellSemi X C) σ₀).set :=
    stSemiPf_subset_of_mem_descP (cellSemi X C) Ml NΦ (k' - k) hτd hzτ'
  by_cases heq : σ = σ₀
  · subst heq
    have hd := descP_disjoint_flat (cellSemi X C) Ml NΦ σ (k' - k)
      (Nat.sub_pos_of_lt hklt) τ hτd
    exact Set.disjoint_left.mp hd hzτ' hzσ
  · have hd := levelP_pairwise_disjoint (cellSemi X C) Ml NΦ (rootInj_cellSemi X C) k
      σ hσ σ₀ hσ₀ heq
    exact Set.disjoint_left.mp hd hzσ' hzσ₀

theorem leafDisj {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (C : WilkiesDesign.E.Basic (p + q) X.r)
    (Ml : ℕ → ℕ) (NΦ : ℕ) :
    ∀ k ∈ Finset.range (q + 1), ∀ k' ∈ Finset.range (q + 1),
      ∀ σ ∈ Work.WilE5.levelP (Work.WilE5.cellSemi X C) Ml NΦ k,
      ∀ τ ∈ Work.WilE5.levelP (Work.WilE5.cellSemi X C) Ml NΦ k',
      ((Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ σ).set ∩
        (Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ τ).set).Nonempty →
      (Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ σ).set =
        (Work.WilE5.flatSemiPfP (Work.WilE5.cellSemi X C) Ml NΦ τ).set := by
  intro k _ k' _ σ hσ τ hτ hne
  rcases lt_trichotomy k k' with h | h | h
  · exact (leafDisj_aux X C Ml NΦ h hσ hτ hne).elim
  · subst h
    by_cases heq : σ = τ
    · rw [heq]
    · exfalso
      obtain ⟨z, hzσ, hzτ⟩ := hne
      have hzσ' : z ∈ (stSemiPf (cellSemi X C) σ).set :=
        flatSemiPfP_subset_stSemiPf (cellSemi X C) Ml NΦ σ hzσ
      have hzτ' : z ∈ (stSemiPf (cellSemi X C) τ).set :=
        flatSemiPfP_subset_stSemiPf (cellSemi X C) Ml NΦ τ hzτ
      have hd := levelP_pairwise_disjoint (cellSemi X C) Ml NΦ (rootInj_cellSemi X C) k
        σ hσ τ hτ heq
      exact Set.disjoint_left.mp hd hzσ' hzτ'
  · obtain ⟨z, hzσ, hzτ⟩ := hne
    exact (leafDisj_aux X C Ml NΦ h hτ hσ ⟨z, hzτ, hzσ⟩).elim

end Work.WilE5.Cells
