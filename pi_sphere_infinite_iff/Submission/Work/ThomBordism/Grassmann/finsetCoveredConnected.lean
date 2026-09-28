import Mathlib
import Submission.Work.ThomBordism.Grassmann.twoSetConnected

/-!
# The finite-cover Mayer–Vietoris (van Kampen) connectivity theorem

`finsetCoveredConnected`: if `T` is a finite family of open sets whose every nonempty finite
intersection is nonempty, and for every nonempty `S ⊆ T` the space `⋂ i ∈ S, U i` has trivial
`π_j` for all `j < k - |S|`, then the union `⋃ i ∈ T, U i` has trivial `π_j` for all `j < k - 1`.

The proof is an induction on the finite index set.  The induction step splits `T` as
`insert a s` and applies the two-set theorem `Work.ThomBordism.Grassmann.twoSetConnected` (proved
in the sibling module) to the open pieces `W = ⋃ i ∈ s, U i` and `V = U a` inside the subspace
`↥(W ∪ V)`; the hypotheses are transported along the canonical homeomorphisms
`↥{z : ↥(W ∪ V) | z ∈ W} ≃ₜ ↥W` (`subSubHomeo`).  The intersection hypothesis for the two-set
step is supplied by a second application of the induction hypothesis, to the family
`fun i => U i ∩ U a`.  The case `k = 2`, where the two-set theorem is not available, is the
path-connectedness statement `subsingleton_piZero_union`.
-/

set_option linter.style.haveILetI false

namespace Work.ThomBordism.Grassmann

open scoped Topology

/-- **Transport of the triviality of a homotopy group along a homeomorphism**, for all `j`
(including `j = 0`, where the statement is about path components). -/
theorem subsingleton_homotopyGroup_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {a : A} {b : B} (hab : e a = b) (j : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin j) B b)) : Subsingleton (HomotopyGroup (Fin j) A a) := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    exact Work.ThomBordism.TwoSet.subsingleton_piZero_of_homeomorph e hab h
  · haveI : Nonempty (Fin j) := ⟨⟨0, hpos⟩⟩
    exact Work.ThomBordism.TwoSet.subsingleton_of_homeomorph e hab (Fin j) h

/-- Transport of a statement about the subtype of a set along an equality of sets. -/
theorem subsingleton_of_set_eq {X : Type*} [TopologicalSpace X] {A B : Set X} (h : A = B) {j : ℕ}
    (hB : ∀ y : ↥B, Subsingleton (HomotopyGroup (Fin j) ↥B y)) :
    ∀ x : ↥A, Subsingleton (HomotopyGroup (Fin j) ↥A x) := h ▸ hB

/-- The canonical homeomorphism `↥{z : ↥Z // z ∈ W} ≃ₜ ↥W` for `W ⊆ Z`. -/
def subSubHomeo {X : Type*} [TopologicalSpace X] {Z W : Set X} (h : W ⊆ Z) :
    {z : ↥Z // (z : X) ∈ W} ≃ₜ ↥W where
  toFun z := ⟨z.1.1, z.2⟩
  invFun w := ⟨⟨w.1, h w.2⟩, w.2⟩
  left_inv z := by ext; rfl
  right_inv w := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A finite union of open sets is open. -/
theorem isOpen_biUnion_finset {ι : Type*} {X : Type*} [TopologicalSpace X] {U : ι → Set X}
    {s : Finset ι} (h : ∀ i, IsOpen (U i)) : IsOpen (⋃ i ∈ s, U i) := by
  rw [show (⋃ i ∈ s, U i) = ⋃ i : ι, ⋃ (_ : i ∈ s), U i from rfl]
  exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => h i))

/-- `⋂ i ∈ s, (U i ∩ B) = (⋂ i ∈ s, U i) ∩ B` for nonempty `s`. -/
theorem biInter_inter_const {X : Type*} {ι : Type*} [DecidableEq ι] (U : ι → Set X)
    {s : Finset ι} (hs : s.Nonempty) (B : Set X) :
    (⋂ i ∈ s, (U i ∩ B)) = (⋂ i ∈ s, U i) ∩ B := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => (h i hi).1, (h (Classical.choose hs) (Classical.choose_spec hs)).2⟩
  · rintro ⟨h1, h2⟩ i hi
    exact ⟨h1 i hi, h2⟩

/-- `⋃ i ∈ s, (U i ∩ B) = (⋃ i ∈ s, U i) ∩ B`. -/
theorem biUnion_inter_const {X : Type*} {ι : Type*} [DecidableEq ι] (U : ι → Set X)
    (s : Finset ι) (B : Set X) : (⋃ i ∈ s, (U i ∩ B)) = (⋃ i ∈ s, U i) ∩ B := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨⟨i, hi, h1⟩, h2⟩
  · rintro ⟨⟨i, hi, h1⟩, h2⟩
    exact ⟨i, hi, h1, h2⟩

/-- **`π₀`-triviality implies path connectedness** (for a nonempty set). -/
theorem isPathConnected_of_subsingleton_piZero {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : ∀ u : ↥S, Subsingleton (HomotopyGroup (Fin 0) ↥S u)) (hne : S.Nonempty) :
    IsPathConnected S := by
  obtain ⟨w, hw⟩ := hne
  have hZ : Subsingleton (ZerothHomotopy ↥S) :=
    @Equiv.subsingleton _ _ (HomotopyGroup.pi0EquivZerothHomotopy (x := (⟨w, hw⟩ : ↥S))).symm
      (h ⟨w, hw⟩)
  refine ⟨w, hw, fun y hy => (joinedIn_iff_joined hw hy).mpr ?_⟩
  exact Quotient.exact (Subsingleton.elim (ZerothHomotopy.mk (⟨w, hw⟩ : ↥S))
    (ZerothHomotopy.mk (⟨y, hy⟩ : ↥S)))

/-- **A union of two path-connected sets with nonempty intersection is path connected.** -/
theorem subsingleton_piZero_union {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : ∀ u : ↥U, Subsingleton (HomotopyGroup (Fin 0) ↥U u))
    (hV : ∀ v : ↥V, Subsingleton (HomotopyGroup (Fin 0) ↥V v))
    (hne : (U ∩ V).Nonempty) (x : ↥(U ∪ V)) :
    Subsingleton (HomotopyGroup (Fin 0) ↥(U ∪ V) x) := by
  have hUne : U.Nonempty := Set.Nonempty.mono Set.inter_subset_left hne
  have hVne : V.Nonempty := Set.Nonempty.mono Set.inter_subset_right hne
  have hUn : IsPathConnected (U ∪ V) :=
    IsPathConnected.union (isPathConnected_of_subsingleton_piZero hU hUne)
      (isPathConnected_of_subsingleton_piZero hV hVne) hne
  have hne' : (U ∪ V).Nonempty := Set.Nonempty.mono Set.subset_union_left hUne
  have hpc : PathConnectedSpace ↥(U ∪ V) :=
    PathConnectedSpace.mk ((Set.nonempty_coe_sort).mpr hne')
      (fun a b => (joinedIn_iff_joined a.2 b.2).mp (IsPathConnected.joinedIn hUn a.1 a.2 b.1 b.2))
  exact @Equiv.subsingleton _ _ (HomotopyGroup.pi0EquivZerothHomotopy (x := x))
    (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2

/-- **The two-set (Mayer–Vietoris) step**, for subsets of an ambient space: if `W`, `V` are open,
`W ∩ V ≠ ∅`, `π_j` of `W` and of `V` is trivial for `j < k - 1`, and `π_j(W ∩ V)` is trivial for
`j < k - 2`, then `π_j(W ∪ V)` is trivial for `j < k - 1`. -/
theorem twoSetStep {X : Type*} [TopologicalSpace X] {W V : Set X}
    (hW : IsOpen W) (hV : IsOpen V) (hne : (W ∩ V).Nonempty)
    (k : ℕ) (hk : 2 ≤ k)
    (hWk : ∀ j, j < k - 1 → ∀ x : ↥W, Subsingleton (HomotopyGroup (Fin j) ↥W x))
    (hVk : ∀ j, j < k - 1 → ∀ x : ↥V, Subsingleton (HomotopyGroup (Fin j) ↥V x))
    (hWVk : ∀ j, j < k - 2 → ∀ x : ↥(W ∩ V), Subsingleton (HomotopyGroup (Fin j) ↥(W ∩ V) x)) :
    ∀ j, j < k - 1 → ∀ x : ↥(W ∪ V), Subsingleton (HomotopyGroup (Fin j) ↥(W ∪ V) x) := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    intro j hj x
    have hj0 : j = 0 := by omega
    subst hj0
    exact subsingleton_piZero_union (fun u => hWk 0 (by omega) u) (fun v => hVk 0 (by omega) v)
      hne x
  · have hWopen : IsOpen {z : ↥(W ∪ V) | (z : X) ∈ W} :=
      continuous_subtype_val.isOpen_preimage W hW
    have hVopen : IsOpen {z : ↥(W ∪ V) | (z : X) ∈ V} :=
      continuous_subtype_val.isOpen_preimage V hV
    have hcov : {z : ↥(W ∪ V) | (z : X) ∈ W} ∪ {z : ↥(W ∪ V) | (z : X) ∈ V} = Set.univ := by
      refine Set.eq_univ_of_forall (fun z => ?_)
      rcases z.2 with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz
    have hne' : ({z : ↥(W ∪ V) | (z : X) ∈ W} ∩ {z : ↥(W ∪ V) | (z : X) ∈ V}).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨⟨z, Or.inl hz.1⟩, hz.1, hz.2⟩
    refine Work.ThomBordism.Grassmann.twoSetConnected hWopen hVopen hcov hne' (k - 1) (by omega)
      ?_ ?_ ?_
    · intro j hj x
      exact subsingleton_homotopyGroup_of_homeomorph
        (subSubHomeo (Z := W ∪ V) (W := W) Set.subset_union_left) rfl j
        (hWk j (by omega) (subSubHomeo (Z := W ∪ V) (W := W) Set.subset_union_left x))
    · intro j hj x
      exact subsingleton_homotopyGroup_of_homeomorph
        (subSubHomeo (Z := W ∪ V) (W := V) Set.subset_union_right) rfl j
        (hVk j (by omega) (subSubHomeo (Z := W ∪ V) (W := V) Set.subset_union_right x))
    · intro j hj
      have hj' : j < k - 2 := by omega
      have hset : ({z : ↥(W ∪ V) | (z : X) ∈ W} ∩ {z : ↥(W ∪ V) | (z : X) ∈ V})
          = {z : ↥(W ∪ V) | (z : X) ∈ W ∩ V} := by
        ext z; exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
      exact subsingleton_of_set_eq (j := j) hset (fun y => subsingleton_homotopyGroup_of_homeomorph
        (subSubHomeo (Z := W ∪ V) (W := W ∩ V) (fun z hz => Or.inl hz.1)) rfl j
        (hWVk j hj' (subSubHomeo (Z := W ∪ V) (W := W ∩ V) (fun z hz => Or.inl hz.1) y)))

theorem finsetCoveredConnected {X : Type*} [TopologicalSpace X] {ι : Type*} [DecidableEq ι]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (T : Finset ι) (hT : T.Nonempty) (k : ℕ)
    (hk : 1 ≤ k)
    (hne : ∀ S : Finset ι, S.Nonempty → S ⊆ T → (⋂ i ∈ S, U i).Nonempty)
    (hcon : ∀ S : Finset ι, S.Nonempty → S ⊆ T → ∀ j, j < k - S.card →
      ∀ x : ↥(⋂ i ∈ S, U i), Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ S, U i) x)) :
    ∀ j, j < k - 1 → ∀ x : ↥(⋃ i ∈ T, U i),
      Subsingleton (HomotopyGroup (Fin j) ↥(⋃ i ∈ T, U i) x) := by
  classical
  -- the statement, uniformly in the family of open sets, by induction on the finite index set
  have H : ∀ T : Finset ι, ∀ (V : ι → Set X), (∀ i, IsOpen (V i)) → ∀ k, 1 ≤ k →
      (∀ S : Finset ι, S.Nonempty → S ⊆ T → (⋂ i ∈ S, V i).Nonempty) →
      (∀ S : Finset ι, S.Nonempty → S ⊆ T → ∀ j, j < k - S.card →
        ∀ x : ↥(⋂ i ∈ S, V i), Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ S, V i) x)) →
      T.Nonempty → ∀ j, j < k - 1 → ∀ x : ↥(⋃ i ∈ T, V i),
        Subsingleton (HomotopyGroup (Fin j) ↥(⋃ i ∈ T, V i) x) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro V hVopen k hk hne' hcon' hT
      exact (Finset.not_nonempty_empty hT).elim
    | insert a s ha ih =>
      intro V hVopen k hk hne' hcon' hT
      rcases Finset.eq_empty_or_nonempty s with hse | hsne
      · -- the index set is the singleton `{a}`
        subst hse
        intro j hj
        refine subsingleton_of_set_eq (j := j)
          (by simp : (⋃ i ∈ insert a (∅ : Finset ι), V i) = V a) ?_
        exact subsingleton_of_set_eq (j := j)
          (by simp : (V a) = (⋂ i ∈ ({a} : Finset ι), V i))
          (hcon' {a} (Finset.singleton_nonempty a) (by simp) j
            (by rw [Finset.card_singleton]; exact hj))
      · by_cases hk2 : 2 ≤ k
        · have hWopen : IsOpen (⋃ i ∈ s, V i) := isOpen_biUnion_finset (fun i => hVopen i)
          have hpair : ((⋃ i ∈ s, V i) ∩ V a).Nonempty := by
            obtain ⟨z, hz⟩ := hne' (insert a s) hT (fun _ hx => hx)
            rw [Finset.set_biInter_insert] at hz
            obtain ⟨hz1, hz2⟩ := hz
            obtain ⟨i₀, hi₀⟩ := hsne
            refine ⟨z, ?_, hz1⟩
            exact Set.mem_iUnion.mpr ⟨i₀, Set.mem_iUnion.mpr ⟨hi₀, (by
              have hz2' : ∀ i, i ∈ s → z ∈ V i := by simpa only [Set.mem_iInter] using hz2
              exact hz2' i₀ hi₀ : z ∈ V i₀)⟩⟩
          -- the induction hypothesis, at parameter `k`, for the smaller index set `s`
          have hWk : ∀ j, j < k - 1 → ∀ x : ↥(⋃ i ∈ s, V i),
              Subsingleton (HomotopyGroup (Fin j) ↥(⋃ i ∈ s, V i) x) :=
            ih V hVopen k hk (fun S hS hST => hne' S hS (hST.trans (Finset.subset_insert a s)))
              (fun S hS hST => hcon' S hS (hST.trans (Finset.subset_insert a s))) hsne
          -- the single piece `V a`
          have hVk : ∀ j, j < k - 1 → ∀ x : ↥(V a),
              Subsingleton (HomotopyGroup (Fin j) ↥(V a) x) := by
            intro j hj
            exact subsingleton_of_set_eq (j := j)
              (by simp : (V a) = (⋂ i ∈ ({a} : Finset ι), V i))
              (hcon' {a} (Finset.singleton_nonempty a) (by simp) j
                (by rw [Finset.card_singleton]; exact hj))
          -- the intersection `(⋃ i ∈ s, V i) ∩ V a`, by induction at parameter `k - 1`
          have hWVk : ∀ j, j < k - 2 → ∀ x : ↥((⋃ i ∈ s, V i) ∩ V a),
              Subsingleton (HomotopyGroup (Fin j) ↥((⋃ i ∈ s, V i) ∩ V a) x) := by
            have hconIn : ∀ S : Finset ι, S.Nonempty → S ⊆ s → ∀ j, j < (k - 1) - S.card →
                ∀ x : ↥(⋂ i ∈ S, (V i ∩ V a)),
                  Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ S, (V i ∩ V a)) x) := by
              intro S hS hST j hj
              have hj' : j < k - (insert a S).card := by
                rw [Finset.card_insert_of_notMem (fun hmem => ha (hST hmem))]
                omega
              have hset : (⋂ i ∈ S, (V i ∩ V a)) = ⋂ i ∈ insert a S, V i := by
                rw [Finset.set_biInter_insert]
                exact (biInter_inter_const V hS (V a)).trans (Set.inter_comm _ _)
              exact subsingleton_of_set_eq (j := j) hset
                (hcon' (insert a S) ⟨a, Finset.mem_insert_self a S⟩
                  (Finset.insert_subset_insert a hST) j hj')
            have hneIn : ∀ S : Finset ι, S.Nonempty → S ⊆ s →
                (⋂ i ∈ S, (V i ∩ V a)).Nonempty := by
              intro S hS hST
              have hset : (⋂ i ∈ S, (V i ∩ V a)) = ⋂ i ∈ insert a S, V i := by
                rw [Finset.set_biInter_insert]
                exact (biInter_inter_const V hS (V a)).trans (Set.inter_comm _ _)
              have h := hne' (insert a S) ⟨a, Finset.mem_insert_self a S⟩
                (Finset.insert_subset_insert a hST)
              rwa [← hset] at h
            have ihIn := ih (fun i => V i ∩ V a) (fun i => (hVopen i).inter (hVopen a))
              (k - 1) (by omega) hneIn hconIn hsne
            intro j hj
            have hset : (⋃ i ∈ s, (V i ∩ V a)) = (⋃ i ∈ s, V i) ∩ V a :=
              biUnion_inter_const V s (V a)
            exact subsingleton_of_set_eq (j := j) hset.symm (ihIn j (by omega))
          -- the two-set step
          intro j hj
          exact subsingleton_of_set_eq (j := j)
            (by rw [Finset.set_biUnion_insert, Set.union_comm] :
              (⋃ i ∈ insert a s, V i) = (⋃ i ∈ s, V i) ∪ V a)
            (twoSetStep hWopen (hVopen a) hpair k hk2 hWk hVk hWVk j hj)
        · -- `k = 1`: the conclusion is vacuous
          intro j hj x
          exfalso
          omega
  exact H T U hopen k hk hne hcon hT

end Work.ThomBordism.Grassmann
