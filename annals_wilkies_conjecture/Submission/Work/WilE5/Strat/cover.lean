import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.InitCover
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid
import Submission.Work.WilE5.Strat.child_subset_parent

set_option autoImplicit false

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §1. The `k`-fold descendants of a state

`desc X M NΦ σ k` is the list of states obtained from `σ` by `k` applications of the children
map.  The recursion is "push the children map in from the left", which makes the level of the
global recursion `level X M NΦ k` the flat map of `desc · k` over the initial states, and makes
`desc` monotone under descent (if `τ` is a child of `σ` then the `k`-fold descendants of `τ`
are among the `(k+1)`-fold descendants of `σ`). -/

/-- The `k`-fold children of a state. -/
noncomputable def desc {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    ℕ → List (St p q X.r)
  | 0 => [σ]
  | (k + 1) => (desc X M NΦ σ k).flatMap fun τ => children X.c M NΦ τ

theorem desc_zero {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    desc X M NΦ σ 0 = [σ] := rfl

theorem desc_succ {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) (k : ℕ) :
    desc X M NΦ σ (k + 1)
      = (desc X M NΦ σ k).flatMap (fun τ => children X.c M NΦ τ) := rfl

/-- The states at depth `k` are exactly the `k`-fold descendants of the initial states. -/
theorem level_eq_flatMap_desc {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (k : ℕ) :
    level X M NΦ k = (initStates X).flatMap (fun σ => desc X M NΦ σ k) := by
  induction k with
  | zero => simp [level, desc_zero]
  | succ k ih =>
    show (level X M NΦ k).flatMap (fun σ => children X.c M NΦ σ)
      = (initStates X).flatMap (fun σ => desc X M NΦ σ (k + 1))
    have h1 : (initStates X).flatMap (fun σ => desc X M NΦ σ (k + 1))
        = (initStates X).flatMap (fun σ => (desc X M NΦ σ k).flatMap
            (fun τ => children X.c M NΦ τ)) := by simp only [desc_succ]
    rw [h1, ← List.flatMap_assoc, ← ih]

/-- A descendant of a child of `σ` is a descendant of `σ` at the next level. -/
theorem desc_child_subset {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ τ : St p q X.r)
    (h : τ ∈ children X.c M NΦ σ) (k : ℕ) :
    ∀ ρ ∈ desc X M NΦ τ k, ρ ∈ desc X M NΦ σ (k + 1) := by
  induction k with
  | zero =>
    intro ρ hρ
    rw [desc_zero, List.mem_singleton] at hρ
    subst hρ
    rw [desc_succ, desc_zero, List.flatMap_singleton]
    exact h
  | succ k ih =>
    intro ρ hρ
    rw [desc_succ, List.mem_flatMap] at hρ
    obtain ⟨ρ', hρ', hρρ'⟩ := hρ
    rw [desc_succ, List.mem_flatMap]
    exact ⟨ρ', ih ρ' hρ', hρρ'⟩

/-! ## §2. The pivots of a child: distinctness and increment

A child appends `t.l` to the parent's pivot list.  The appended direction is *new* whenever the
test is valid and belongs to `testL` (validity kills all the old pivot directions, `testL`
requires `t.m t.l ≠ 0`), and a valid test is exactly what a *nonempty* child gives. -/

theorem pivDirs_length {p q r : ℕ} (σ : St p q r) : (pivDirs σ.B).length = σ.B.length :=
  List.length_map _

theorem childSt_pivDirs {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    pivDirs (childSt X.c M NΦ σ t s).B = pivDirs σ.B ++ [t.l] := by
  simp [pivDirs, childSt, childB]

theorem childSt_B_length {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    (childSt X.c M NΦ σ t s).B.length = σ.B.length + 1 := by
  simp [childSt, childB]

/-- The peeled direction of a valid test of `testL` is not one of the state's pivots. -/
theorem notMem_pivDirs_of_valid_testL {p q r : ℕ} (σ : St p q r) (M NΦ : ℕ) (t : Test q)
    (ht : t ∈ testL q M NΦ) (hv : valid σ t) : t.l ∉ pivDirs σ.B := by
  intro h
  rw [pivDirs, List.mem_map] at h
  obtain ⟨x, hx, hx2⟩ := h
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hx
  have hv' : t.m (σ.B.get a).2 = 0 := hv.2 a
  rw [ha] at hv'
  rw [show x.2 = t.l from hx2] at hv'
  exact (mem_testL_iff t).mp ht |>.2.2 hv'

/-- A state with `q` pairwise distinct pivots has every direction among its pivots, hence admits
no valid test of `testL`. -/
theorem mem_pivDirs_of_nodup_length {p q r : ℕ} (σ : St p q r) (hnd : (pivDirs σ.B).Nodup)
    (h : σ.B.length = q) (l : Fin q) : l ∈ pivDirs σ.B := by
  have hcard : (pivDirs σ.B).toFinset.card = Fintype.card (Fin q) := by
    rw [List.toFinset_card_of_nodup hnd, pivDirs_length, h]
    simp
  have huniv : (pivDirs σ.B).toFinset = Finset.univ := Finset.eq_univ_of_card _ hcard
  rw [← List.mem_toFinset, huniv]
  exact Finset.mem_univ l

/-- Distinctness of the pivots is preserved by the recursion. -/
theorem nodup_pivDirs_childSt {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) (ht : t ∈ testL q M NΦ) (hv : valid σ t)
    (hnd : (pivDirs σ.B).Nodup) :
    (pivDirs (childSt X.c M NΦ σ t s).B).Nodup := by
  rw [childSt_pivDirs, ← List.concat_eq_append, List.nodup_concat]
  exact ⟨notMem_pivDirs_of_valid_testL σ M NΦ t ht hv, hnd⟩

/-! ## §3. The flatness invariant `σ.Φ ⊆ σ.Ξ`

This is the invariant that supplies the hypothesis `hΦ` of the partition statement: every flatness
source of a state is one of the state's accumulated vanishing conditions, hence vanishes at every
point of the state's set.  It holds at the initial states (`Φ = Ξ = A.eqs`) and is preserved
because a child has `Φ' = σ.Φ ++ Ξ'` and `Ξ' = childΞ'`. -/

/-- The invariant: every flatness source of the state is one of its accumulated conditions. -/
def PhiInXi {p q r : ℕ} (σ : St p q r) : Prop := ∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ

/-- The invariant gives the `hΦ` hypothesis of the partition statement. -/
theorem PhiInXi_holds {p q : ℕ} (X : SemiPf (p + q)) {σ : St p q X.r} (h : PhiInXi σ) :
    ∀ ψ ∈ σ.Φ, ∀ w ∈ (stSemiPf X σ).set, eaEval X.c ψ w = 0 := by
  intro ψ hψ w hw
  have h1 : ψ ∈ (stCond σ).eqs := by
    have h2 := h ψ hψ
    simp only [stCond, List.mem_append]
    exact Or.inr h2
  rw [stSemiPf, semiPfAnd_set] at hw
  exact hw.2.1 ψ h1

/-- The invariant passes to children. -/
theorem PhiInXi_child {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) {σ : St p q X.r}
    (t : Test q) (s : Bool) (h : PhiInXi σ) : PhiInXi (childSt X.c M NΦ σ t s) := by
  intro ψ hψ
  simp only [childSt, List.mem_append] at hψ ⊢
  rcases hψ with hψ | hψ
  · exact List.mem_append_left _ (List.mem_append_left _ (h ψ hψ))
  · exact hψ

/-- The invariant holds at the initial states. -/
theorem PhiInXi_initSt {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r)
    (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) : PhiInXi (initSt X A Fy ε) :=
  fun _ h => h

/-- The pivots of an initial state are pairwise distinct (they are a sublist of the fibre
directions, listed once each). -/
theorem initSt_pivDirs_nodup {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r)
    (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) :
    (pivDirs (initSt X A Fy ε).B).Nodup := by
  rw [pivDirs, initSt, List.map_map]
  exact List.Nodup.map Subtype.val_injective (Finset.nodup_toList Fy.attach)

/-- The initial system of a state has at most `q` equations. -/
theorem initSt_B_length {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r)
    (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) :
    (initSt X A Fy ε).B.length ≤ q := by
  have h : (initSt X A Fy ε).B.length = Fy.card := by simp [initSt]
  rw [h]
  exact le_trans (Finset.card_le_univ Fy) (le_of_eq (Fintype.card_fin q))

/-! ## §4. Nonempty children come from valid tests -/

/-- A child at a test of `testL` is one of the state's children. -/
theorem mem_children_of_mem_testL {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) (ht : t ∈ testL q M NΦ) :
    childSt X.c M NΦ σ t s ∈ children X.c M NΦ σ := by
  refine List.mem_flatMap.mpr ⟨t, ht, ?_⟩
  cases s <;> simp

/-- A nonempty child arises only from a valid test: an invalid test has `opVal = 0`, which
contradicts the sign condition carried by every child. -/
theorem valid_of_mem_child {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) {z : Fin (p + q) → ℝ}
    (hz : z ∈ (stSemiPf X (childSt X.c M NΦ σ t s)).set) : valid σ t := by
  by_contra h
  have h0 : opVal X.c σ t = 0 := opVal_eq_zero_of_not_valid X.c σ t h
  have hz0 : eaEval X.c (opVal X.c σ t) z = 0 := by rw [h0]; simp [eaEval]
  rw [stSemiPf_child_set_eq] at hz
  have hsign := hz.2.2.2.2
  rw [hz0] at hsign
  cases s
  · simp only [Bool.false_eq_true, if_false] at hsign
    exact absurd hsign (lt_irrefl 0)
  · simp only [if_true] at hsign
    exact absurd hsign (lt_irrefl 0)

/-! ## §5. The descent: a state's set is covered by the flat leaves of its descendants

Induction on the budget `n ≥ q - |B|`.  Each nonempty child adds a new distinct pivot, so
`q - |B|` strictly decreases; at budget `0` (that is, `|B| = q`) no test is valid and the
partition puts every point of the state's set in its flat leaf. -/

theorem desc_cover {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) :
    ∀ n : ℕ, ∀ σ : St p q X.r, q - σ.B.length ≤ n → (pivDirs σ.B).Nodup → PhiInXi σ →
      (stSemiPf X σ).set ⊆ ⋃ k ∈ Finset.range (n + 1),
        ⋃ τ ∈ desc X M NΦ σ k, (flatSemiPf X M NΦ τ).set := by
  intro n
  induction n with
  | zero =>
    intro σ hb hnd hΦΞ z hz
    have hlen : σ.B.length = q := by
      have h1 : (pivDirs σ.B).length ≤ Fintype.card (Fin q) := List.Nodup.length_le_card hnd
      rw [pivDirs_length, Fintype.card_fin] at h1
      omega
    rcases stSemiPf_subset_flatSemiPf_union_children X M NΦ σ (PhiInXi_holds X hΦΞ) hz with
      hfl | ⟨t, ht, s, hzs⟩
    · refine Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨σ, by rw [desc_zero]; exact List.mem_singleton.mpr rfl, hfl⟩
    · exfalso
      have hv : valid σ t := valid_of_mem_child X M NΦ σ t s hzs
      exact notMem_pivDirs_of_valid_testL σ M NΦ t ht hv
        (mem_pivDirs_of_nodup_length σ hnd hlen t.l)
  | succ n ih =>
    intro σ hb hnd hΦΞ z hz
    rcases stSemiPf_subset_flatSemiPf_union_children X M NΦ σ (PhiInXi_holds X hΦΞ) hz with
      hfl | ⟨t, ht, s, hzs⟩
    · refine Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨σ, by rw [desc_zero]; exact List.mem_singleton.mpr rfl, hfl⟩
    · have hv : valid σ t := valid_of_mem_child X M NΦ σ t s hzs
      have hnd' : (pivDirs (childSt X.c M NΦ σ t s).B).Nodup :=
        nodup_pivDirs_childSt X M NΦ σ t s ht hv hnd
      have hb' : q - (childSt X.c M NΦ σ t s).B.length ≤ n := by
        rw [childSt_B_length]; omega
      have hΦΞ' : PhiInXi (childSt X.c M NΦ σ t s) := PhiInXi_child X M NΦ t s hΦΞ
      have hchild := ih (childSt X.c M NΦ σ t s) hb' hnd' hΦΞ' hzs
      rw [Set.mem_iUnion₂] at hchild
      obtain ⟨k, hk, hchild⟩ := hchild
      rw [Set.mem_iUnion₂] at hchild
      obtain ⟨ρ, hρ, hzρ⟩ := hchild
      refine Set.mem_iUnion₂.mpr ⟨k + 1,
        Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega), ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨ρ, desc_child_subset X M NΦ σ _
        (mem_children_of_mem_testL X M NΦ σ t s ht) k ρ hρ, hzρ⟩

/-- The flat leaves of the recursion cover `X`.  This is the level induction of the covering step:
(i) at level zero use `Work.WilE5.Strat.exists_initSt_mem`; (ii) for the recursion step use the
partition `Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children` (a state's set is covered by
its flat leaf and its children's sets — its hypothesis `hΦ` is an invariant of the construction:
weaker than needed, `∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ` suffices, because the state's conditions all vanish on its
set, and it is preserved since `Φ' = σ.Φ ++ childΞ'` while `childΞ' ⊆ (stCond ·).eqs`); (iii) for
termination note that a nonempty child arises only from a *valid* test
(`Work.WilE5.Strat.opVal_eq_zero_of_not_valid`: an invalid test's child has an empty set), and that
the peeled direction of a valid test is not one of the parent's pivots (the test's multi-index
vanishes in all pivot directions and is nonzero in the peeled one), so along any chain of nonempty
states the pivots stay pairwise distinct and increase, and there are at most `q` of them.

Suggested formalisation: define `desc X M NΦ σ : ℕ → List (Work.WilE5.St p q X.r)` (the `n`-fold
children of `σ`), prove `level X M NΦ k = (initStates X).flatMap (desc X M NΦ · k)` by induction on
`k`, and then prove by induction on the budget that for every state `σ` whose pivots are pairwise
distinct, `(stSemiPf X σ).set` is contained in
`⋃ k ∈ Finset.range (q - σ.B.length + 1), ⋃ τ ∈ desc X M NΦ σ k, (flatSemiPf X M NΦ τ).set`,
combining the partition with the induction hypothesis for each child (and the emptiness of the
children of invalid tests). -/
theorem cover {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Mtest NΦ : ℕ) :
    X.set ⊆ ⋃ k ∈ Finset.range (q + 1),
      ⋃ σ ∈ Work.WilE5.level X Mtest NΦ k, (Work.WilE5.flatSemiPf X Mtest NΦ σ).set := by
  intro z hz
  obtain ⟨σ, hσmem, -, -, -, -, -, hzσ⟩ := exists_initSt_mem X hz
  obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates X hσmem
  have hnd : (pivDirs (initSt X A Fy ε).B).Nodup := initSt_pivDirs_nodup X A Fy ε
  have hΦΞ : PhiInXi (initSt X A Fy ε) := PhiInXi_initSt X A Fy ε
  have hble : q - (initSt X A Fy ε).B.length ≤ q := Nat.sub_le _ _
  have hcov := desc_cover X Mtest NΦ q (initSt X A Fy ε) hble hnd hΦΞ hzσ
  rw [Set.mem_iUnion₂] at hcov
  obtain ⟨k, hk, hcov⟩ := hcov
  rw [Set.mem_iUnion₂] at hcov
  obtain ⟨τ, hτ, hzτ⟩ := hcov
  refine Set.mem_iUnion₂.mpr ⟨k, hk, Set.mem_iUnion₂.mpr ⟨τ, ?_, hzτ⟩⟩
  rw [level_eq_flatMap_desc]
  exact List.mem_flatMap.mpr ⟨initSt X A Fy ε, initSt_mem_initStates X A hA Fy ε, hτ⟩

end Work.WilE5.Strat
