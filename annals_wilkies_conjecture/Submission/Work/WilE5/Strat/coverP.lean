/-
  WilE5 / Strat — the *profile* covering statement.

  `SysL.levelP X Ml NΦ` is the fibrewise stratification recursion with a test-order *profile*
  `Ml : ℕ → ℕ`: the children of a state `σ` are computed from the test list
  `testL q (Ml σ.B.length) NΦ`, i.e. with the order bound of the state's *own* level.  The profile
  is what makes the a-priori bounds of the assembly work: the degrees of a state grow with its
  level, so no single global test bound can satisfy the `hMu` hypothesis of the flat-leaf
  correctness (`flatLeafGoodP`) — see the discussion in `Profile.lean`.

  This file proves that the profile recursion still covers `X` by flat leaves at levels `≤ q`:

      X.set ⊆ ⋃ k ∈ range (q+1), ⋃ σ ∈ levelP X Ml NΦ k, (flatSemiPfP X Ml NΦ σ).set.

  The argument is the level induction of `Strat/cover.lean`, carried out for the profile.  At a
  state `σ` the partition `stSemiPf_subset_flatSemiPf_union_children` is applied with the bound
  `M := Ml σ.B.length` (which is exactly the profile order of that state):

  * either the point `z` lies in the state's flat leaf — done at depth `0`;
  * or `z` lies in a profile child; then the flatness invariant `PhiInXi` (`σ.Φ ⊆ σ.Ξ`, whence
    every flatness source vanishes on the state's set) descends to the child, the child's test is
    *valid* (`valid_of_mem_child`: an invalid test's child has empty set), so its peeled direction
    is a new pivot (`notMem_pivDirs_of_valid_testL`), so the pivots of the child are again pairwise
    distinct — and increase by one.  Since all pivots live in `Fin q`, at budget `0` the state has
    `q` distinct pivots, every direction is a pivot (`mem_pivDirs_of_nodup_length`), no test of the
    list is valid, and the partition puts the whole state into its flat leaf.

  The recursion bookkeeping (the `k`-fold profile descendants `descP` and its relation to
  `levelP`) is in `Strat/DescP.lean`, `Strat/levelP_eq_flatMap_descP.lean` and
  `Strat/descP_child_subset.lean`.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Profile
import Submission.Work.WilE5.Strat.InitCover
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid
import Submission.Work.WilE5.Strat.child_subset_parent
import Submission.Work.WilE5.Strat.DescP
import Submission.Work.WilE5.Strat.cover
import Submission.Work.WilE5.Strat.levelP_eq_flatMap_descP
import Submission.Work.WilE5.Strat.descP_child_subset

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-- A profile child of a state is one of the state's profile children (the children of a state
are enumerated by the tests of its own profile order `Ml σ.B.length` and the two signs). -/
theorem mem_childrenP_of_mem_testLP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) (t : Test q) (s : Bool) (ht : t ∈ testLP Ml NΦ σ) :
    childStP X.c Ml NΦ σ t s ∈ childrenP X.c Ml NΦ σ := by
  refine List.mem_flatMap.mpr ⟨t, ht, ?_⟩
  cases s <;> simp

/-- The partition at a state of the *profile* recursion: with the profile order of the state's own
level, a point of the state's set lies in the state's flat leaf or in one of its profile children.
This is `stSemiPf_subset_flatSemiPf_union_children` with the bound `M := Ml σ.B.length`, which is
exactly what `childrenP`/`flatSemiPfP` use at `σ`. -/
theorem stSemiPf_subset_flatSemiPfP_union_childrenP {p q : ℕ} (X : SemiPf (p + q))
    (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r)
    (hΦ : ∀ ψ ∈ σ.Φ, ∀ w ∈ (stSemiPf X σ).set, eaEval X.c ψ w = 0)
    {z : Fin (p + q) → ℝ} (hz : z ∈ (stSemiPf X σ).set) :
    z ∈ (flatSemiPfP X Ml NΦ σ).set ∨
      ∃ t ∈ testLP Ml NΦ σ, ∃ s : Bool,
        z ∈ (stSemiPf X (childStP X.c Ml NΦ σ t s)).set :=
  stSemiPf_subset_flatSemiPf_union_children X (Ml σ.B.length) NΦ σ hΦ hz

/-- **Covering from a state.**  If `σ` has pairwise distinct pivots and the flatness invariant
`PhiInXi`, and its level plus the budget `n` reaches `q`, then the state's set is covered by the
flat leaves of its `k`-fold profile descendants, `k ≤ n`.

The proof is an induction on the budget `n`.  At budget `0` (that is `|B| ≥ q`, hence `|B| = q`)
every fibre direction is a pivot, so no test of the list is valid and the partition puts the whole
state into its flat leaf.  At a positive budget the partition either stops in the flat leaf
(depth `0`) or descends to a profile child: the child's test is valid (its set contains the point),
whence its peeled direction is a fresh pivot and the invariants survive; the child's budget is one
less, and a descendant of the child is a descendant of the state at the next depth. -/
theorem descP_cover {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    ∀ n : ℕ, ∀ σ : St p q X.r, σ.B.length + n ≥ q → (pivDirs σ.B).Nodup → PhiInXi σ →
      (stSemiPf X σ).set ⊆ ⋃ k ∈ Finset.range (n + 1),
        ⋃ τ ∈ descP X Ml NΦ σ k, (flatSemiPfP X Ml NΦ τ).set := by
  intro n
  induction n with
  | zero =>
    intro σ hb hnd hΦΞ z hz
    -- `|B| = q`: every fibre direction is a pivot, so no test of the list is valid
    have hle : (pivDirs σ.B).length ≤ Fintype.card (Fin q) := List.Nodup.length_le_card hnd
    rw [pivDirs_length, Fintype.card_fin] at hle
    have hlen : σ.B.length = q := by omega
    rcases stSemiPf_subset_flatSemiPfP_union_childrenP X Ml NΦ σ (PhiInXi_holds X hΦΞ) hz with
      hfl | ⟨t, ht, s, hzs⟩
    · exact Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega),
        Set.mem_iUnion₂.mpr ⟨σ, by rw [descP_zero]; exact List.mem_singleton.mpr rfl, hfl⟩⟩
    · exfalso
      have hv : valid σ t := valid_of_mem_child X (Ml σ.B.length) NΦ σ t s hzs
      exact notMem_pivDirs_of_valid_testL σ (Ml σ.B.length) NΦ t ht hv
        (mem_pivDirs_of_nodup_length σ hnd hlen t.l)
  | succ n ih =>
    intro σ hb hnd hΦΞ z hz
    rcases stSemiPf_subset_flatSemiPfP_union_childrenP X Ml NΦ σ (PhiInXi_holds X hΦΞ) hz with
      hfl | ⟨t, ht, s, hzs⟩
    · exact Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega),
        Set.mem_iUnion₂.mpr ⟨σ, by rw [descP_zero]; exact List.mem_singleton.mpr rfl, hfl⟩⟩
    · -- descend to the profile child, which again satisfies all the invariants
      have hv : valid σ t := valid_of_mem_child X (Ml σ.B.length) NΦ σ t s hzs
      have hnd' : (pivDirs (childStP X.c Ml NΦ σ t s).B).Nodup :=
        nodup_pivDirs_childSt X (Ml σ.B.length) NΦ σ t s ht hv hnd
      have hb' : (childStP X.c Ml NΦ σ t s).B.length + n ≥ q := by
        rw [childStP_level X.c Ml NΦ σ t s]
        omega
      have hΦΞ' : PhiInXi (childStP X.c Ml NΦ σ t s) :=
        PhiInXi_child X (Ml σ.B.length) NΦ t s hΦΞ
      have hchild := ih (childStP X.c Ml NΦ σ t s) hb' hnd' hΦΞ' hzs
      rw [Set.mem_iUnion₂] at hchild
      obtain ⟨k, hk, hchild⟩ := hchild
      rw [Set.mem_iUnion₂] at hchild
      obtain ⟨ρ, hρ, hzρ⟩ := hchild
      refine Set.mem_iUnion₂.mpr ⟨k + 1,
        Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega),
        Set.mem_iUnion₂.mpr ⟨ρ, ?_, hzρ⟩⟩
      exact descP_child_subset X Ml NΦ σ _ (mem_childrenP_of_mem_testLP X Ml NΦ σ t s ht) k ρ hρ

/-- **The profile covering statement.**  The flat leaves of the profile recursion at levels `≤ q`
cover `X`.  Start with an initial state containing the point (`exists_initSt_mem`); it has pairwise
distinct pivots (`initSt_pivDirs_nodup`, the face pattern is a `Finset`) and satisfies the flatness
invariant (`PhiInXi_initSt`).  `descP_cover` then covers it by flat leaves of its descendants,
which are exactly the states at the corresponding level of `levelP`
(`levelP_eq_flatMap_descP`). -/
theorem coverP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    X.set ⊆ ⋃ k ∈ Finset.range (q + 1),
      ⋃ σ ∈ Work.WilE5.levelP X Ml NΦ k, (Work.WilE5.flatSemiPfP X Ml NΦ σ).set := by
  intro z hz
  obtain ⟨σ, hσmem, -, -, -, -, -, hzσ⟩ := exists_initSt_mem X hz
  obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates X hσmem
  have hnd : (pivDirs (initSt X A Fy ε).B).Nodup := initSt_pivDirs_nodup X A Fy ε
  have hΦΞ : PhiInXi (initSt X A Fy ε) := PhiInXi_initSt X A Fy ε
  have hble : (initSt X A Fy ε).B.length + q ≥ q := Nat.le_add_left q _
  have hcov := descP_cover X Ml NΦ q (initSt X A Fy ε) hble hnd hΦΞ hzσ
  rw [Set.mem_iUnion₂] at hcov
  obtain ⟨k, hk, hcov⟩ := hcov
  rw [Set.mem_iUnion₂] at hcov
  obtain ⟨τ, hτ, hzτ⟩ := hcov
  refine Set.mem_iUnion₂.mpr ⟨k, hk, Set.mem_iUnion₂.mpr ⟨τ, ?_, hzτ⟩⟩
  rw [levelP_eq_flatMap_descP]
  exact List.mem_flatMap.mpr ⟨initSt X A Fy ε, initSt_mem_initStates X A hA Fy ε, hτ⟩

end Work.WilE5.Strat
