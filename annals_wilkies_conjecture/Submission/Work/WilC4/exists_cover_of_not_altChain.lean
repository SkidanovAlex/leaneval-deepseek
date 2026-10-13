/-
  WilC4/exists_cover_of_not_altChain

  `¬ AltChain N A` for a set `A ⊆ ℝ` means that `A` contains no chain of `N + 1` points
  separated by points outside `A`, i.e. that `A` has at most `N` order connected components.
  This file shows that `A` is then a finite union of at most `N` order convex (= preconnected)
  subsets of `A`.

  The proof is an induction on `N`.  Peeling off the order connected component
  `D = ordConnectedComponent A a` of a chosen point `a ∈ A`, one shows
  `¬ AltChain k (A \ D)` from `¬ AltChain (k+1) A`, and concludes by the induction hypothesis.
  The key point is that if `A \ D` contained `k+1` points separated by points of `A \ D`, then
  inserting the point `a` (which lies in a different component) into the sorted sequence would
  produce a chain of `k + 2` points of `A` separated by points outside `A`; the insertion is
  realised by enumerating `{a} ∪ range y` increasingly with `Finset.orderEmbOfFin`.
-/
import Mathlib
import Submission.Work.WilC4.UnifDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Interval
namespace Work.WilC4

/-! ## The "gap" form of `¬ AltChain`

`¬ AltChain N A` is equivalent to: any `N + 1` points of `A` have two consecutive members whose
whole open interval lies in `A`.  (No monotonicity of the points is needed: a pair whose points
are not increasing has an empty — hence admissible — open interval.) -/

theorem not_altChain_iff {A : Set ℝ} {N : ℕ} :
    ¬ AltChain N A ↔
      ∀ x : Fin (N + 1) → ℝ, (∀ j, x j ∈ A) →
        ∃ j : Fin N, ∀ z, x (Fin.castSucc j) < z → z < x (Fin.succ j) → z ∈ A := by
  constructor
  · intro h x hx
    by_contra hc
    push_neg at hc
    exact h ⟨x, fun j => Classical.choose (hc j), hx, fun j => by
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hc j)
      exact ⟨h3, h1, h2⟩⟩
  · rintro h ⟨x, y, hx, hy⟩
    obtain ⟨j, hj⟩ := h x hx
    exact (hy j).1 (hj (y j) (hy j).2.1 (hy j).2.2)

/-! ## Two elementary lemmas about order connected components -/

/-- If `y` lies in the order connected component of `a` in `A` and the interval `[[x, y]]` is
contained in `A`, then `x` lies in that component too. -/
lemma mem_ordConnectedComponent_of_mem_of_uIcc_subset {A : Set ℝ} {a x y : ℝ}
    (hy : y ∈ Set.ordConnectedComponent A a) (hxy : Set.uIcc x y ⊆ A) :
    x ∈ Set.ordConnectedComponent A a := by
  rw [Set.mem_ordConnectedComponent] at hy ⊢
  exact (Set.uIcc_subset_uIcc_union_uIcc (a := a) (b := y) (c := x)).trans
    (Set.union_subset hy (by rw [Set.uIcc_comm]; exact hxy))

/-- A closed interval whose endpoints lie in `A` and whose interior lies in `A` is contained
in `A`. -/
lemma Icc_subset_of_mem_of_Ioo {A : Set ℝ} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A)
    (h : ∀ z, x < z → z < y → z ∈ A) : Set.Icc x y ⊆ A := by
  intro z hz
  rcases lt_trichotomy z x with h1 | h1 | h1
  · exact absurd hz.1 (not_le.mpr h1)
  · rw [h1]; exact hx
  · rcases lt_trichotomy z y with h2 | h2 | h2
    · exact h z h1 h2
    · rw [h2]; exact hy
    · exact absurd hz.2 (not_le.mpr h2)

/-! ## The cover -/

theorem exists_cover_aux : ∀ N : ℕ, ∀ A : Set ℝ, ¬ AltChain N A →
    ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, I.OrdConnected) ∧
      A = ⋃₀ (s : Set (Set ℝ)) := by
  intro N
  induction N with
  | zero =>
    intro A hA
    have hAe : A = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp fun hne => hA (altChain_zero_iff.mpr hne)
    exact ⟨∅, by simp, by simp, by simp [hAe]⟩
  | succ k ih =>
    intro A hA
    by_cases hAe : A = ∅
    · exact ⟨∅, by simp, by simp, by simp [hAe]⟩
    · obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hAe
      have hDsub : Set.ordConnectedComponent A a ⊆ A := Set.ordConnectedComponent_subset
      have hk : ¬ AltChain k (A \ Set.ordConnectedComponent A a) := by
        rw [not_altChain_iff]
        intro y hy
        by_cases hmono : StrictMono y
        · -- `y` is strictly increasing: insert `a` into its range, sorted
          have hyinj : Function.Injective y := hmono.injective
          have hay : a ∉ Finset.univ.image y := by
            rw [Finset.mem_image]
            rintro ⟨m, -, hm⟩
            have hmD : y m ∈ Set.ordConnectedComponent A a := by
              rw [hm]; exact Set.self_mem_ordConnectedComponent.mpr ha
            exact (hy m).2 hmD
          have hcardY : (Finset.univ.image y).card = k + 1 := by
            rw [Finset.card_image_of_injective _ hyinj, Finset.card_univ, Fintype.card_fin]
          set F : Finset ℝ := insert a (Finset.univ.image y) with hF
          have hcardF : F.card = k + 2 := by
            rw [hF, Finset.card_insert_of_notMem hay, hcardY]
          set u : Fin (k + 2) ↪o ℝ := F.orderEmbOfFin hcardF with hu
          have hublock : ∀ i : Fin (k + 2), u i = a ∨ ∃ m : Fin (k + 1), u i = y m := by
            intro i
            have hm : u i ∈ F := by rw [hu]; exact Finset.orderEmbOfFin_mem F hcardF i
            rw [hF, Finset.mem_insert, Finset.mem_image] at hm
            rcases hm with h | ⟨m, -, hm⟩
            · exact Or.inl h
            · exact Or.inr ⟨m, hm.symm⟩
          have huA : ∀ i, u i ∈ A := by
            intro i
            rcases hublock i with h | ⟨m, hm⟩
            · rw [h]; exact ha
            · rw [hm]; exact (hy m).1
          obtain ⟨j, hj⟩ := (not_altChain_iff.mp hA) u huA
          have hjj : u (Fin.castSucc j) < u (Fin.succ j) :=
            u.strictMono (Fin.castSucc_lt_succ (i := j))
          by_cases hja : u (Fin.castSucc j) = a
          · -- the left member of the gap is `a`
            obtain ⟨p, hp⟩ : ∃ m : Fin (k + 1), u (Fin.succ j) = y m := by
              rcases hublock (Fin.succ j) with h | h
              · rw [h] at hjj
                rw [hja] at hjj
                exact absurd hjj (lt_irrefl a)
              · exact h
            have hap : a < y p := by rw [← hja, ← hp]; exact hjj
            have hpD : y p ∈ Set.ordConnectedComponent A a :=
              mem_ordConnectedComponent_of_mem_of_uIcc_subset
                (Set.self_mem_ordConnectedComponent.mpr ha) (by
                  rw [Set.uIcc_comm, Set.uIcc_of_le (le_of_lt hap), ← hp]
                  exact Icc_subset_of_mem_of_Ioo ha (huA (Fin.succ j))
                    fun z h1 h2 => hj z (by rw [hja]; exact h1) h2)
            exact absurd hpD (hy p).2
          · by_cases hja' : u (Fin.succ j) = a
            · -- the right member of the gap is `a`
              obtain ⟨p, hp⟩ : ∃ m : Fin (k + 1), u (Fin.castSucc j) = y m := by
                rcases hublock (Fin.castSucc j) with h | h
                · exact absurd h hja
                · exact h
              have hpa : y p < a := by rw [← hp, ← hja']; exact hjj
              have hpD : y p ∈ Set.ordConnectedComponent A a :=
                mem_ordConnectedComponent_of_mem_of_uIcc_subset
                  (Set.self_mem_ordConnectedComponent.mpr ha) (by
                    rw [Set.uIcc_of_le (le_of_lt hpa), ← hp, ← hja']
                    exact Icc_subset_of_mem_of_Ioo (huA (Fin.castSucc j)) (huA (Fin.succ j))
                      fun z h1 h2 => hj z h1 h2)
              exact absurd hpD (hy p).2
            · -- neither member of the gap is `a`: they are two consecutive points of `y`
              obtain ⟨p, hp⟩ : ∃ m : Fin (k + 1), u (Fin.castSucc j) = y m := by
                rcases hublock (Fin.castSucc j) with h | h
                · exact absurd h hja
                · exact h
              obtain ⟨q, hq⟩ : ∃ m : Fin (k + 1), u (Fin.succ j) = y m := by
                rcases hublock (Fin.succ j) with h | h
                · exact absurd h hja'
                · exact h
              have hpq_lt : p.val < q.val := by
                have h1 : y p < y q := by rw [← hp, ← hq]; exact hjj
                exact Fin.lt_iff_val_lt_val.mp (hmono.lt_iff_lt.mp h1)
              have hq_le : q.val ≤ p.val + 1 := by
                by_contra hc
                rw [not_le] at hc
                have hp'k : p.val + 1 < k + 1 := by omega
                let p' : Fin (k + 1) := ⟨p.val + 1, hp'k⟩
                have hpp' : p < p' := by rw [Fin.lt_iff_val_lt_val]; simp [p']
                have hp'q : p' < q := by
                  rw [Fin.lt_iff_val_lt_val]; simp only [p']; omega
                have hp'F : y p' ∈ F := by
                  rw [hF, Finset.mem_insert]
                  exact Or.inr (Finset.mem_image.mpr ⟨p', Finset.mem_univ _, rfl⟩)
                have hp'range : y p' ∈ Set.range u := by
                  rw [hu, Finset.range_orderEmbOfFin]; exact hp'F
                obtain ⟨l, hl⟩ := Set.mem_range.mp hp'range
                have hl1 : Fin.castSucc j < l :=
                  u.lt_iff_lt.mp (by rw [hp, hl]; exact hmono hpp')
                have hl2 : l < Fin.succ j :=
                  u.lt_iff_lt.mp (by rw [hl, hq]; exact hmono hp'q)
                have h1 : (Fin.castSucc j).val < l.val := Fin.lt_iff_val_lt_val.mp hl1
                have h2 : l.val < (Fin.succ j).val := Fin.lt_iff_val_lt_val.mp hl2
                rw [Fin.coe_castSucc] at h1
                rw [Fin.val_succ] at h2
                omega
              have hpq : q.val = p.val + 1 := by omega
              have hpk : p.val < k := by omega
              let m : Fin k := ⟨p.val, hpk⟩
              have hcm : Fin.castSucc m = p := Fin.ext rfl
              have hsm : Fin.succ m = q := by
                apply Fin.ext
                rw [Fin.val_succ]
                show (p.val + 1) = q.val
                omega
              refine ⟨m, fun z hz1 hz2 => ?_⟩
              have hcy : y (Fin.castSucc m) = u (Fin.castSucc j) := by rw [hcm, ← hp]
              have hsy : y (Fin.succ m) = u (Fin.succ j) := by rw [hsm, ← hq]
              have hz1' : u (Fin.castSucc j) < z := by rw [← hcy]; exact hz1
              have hz2' : z < u (Fin.succ j) := by rw [← hsy]; exact hz2
              have hzA : z ∈ A := hj z hz1' hz2'
              refine ⟨hzA, fun hzD => (hy (Fin.castSucc m)).2 ?_⟩
              have huIcc : Set.uIcc (y (Fin.castSucc m)) z ⊆ A := by
                rw [hcy, Set.uIcc_of_le (le_of_lt hz1')]
                exact Icc_subset_of_mem_of_Ioo (huA (Fin.castSucc j)) hzA
                  fun w h1 h2 => hj w h1 (lt_trans h2 hz2')
              exact mem_ordConnectedComponent_of_mem_of_uIcc_subset hzD huIcc
        · -- `y` is not increasing: two consecutive points are not increasing, so their gap is empty
          rw [Fin.strictMono_iff_lt_succ] at hmono
          push_neg at hmono
          obtain ⟨i, hi⟩ := hmono
          exact ⟨i, fun z h1 h2 =>
            absurd (lt_trans h1 (lt_of_lt_of_le h2 hi)) (lt_irrefl _)⟩
      obtain ⟨s, hcard, hord, hunion⟩ := ih (A \ Set.ordConnectedComponent A a) hk
      refine ⟨insert (Set.ordConnectedComponent A a) s, ?_, ?_, ?_⟩
      · calc (insert (Set.ordConnectedComponent A a) s).card
            ≤ s.card + 1 := Finset.card_insert_le _ _
          _ ≤ k + 1 := by omega
      · intro I hI
        rw [Finset.mem_insert] at hI
        rcases hI with rfl | hI
        · exact inferInstance
        · exact hord I hI
      · rw [Finset.coe_insert, Set.sUnion_insert, ← hunion]
        exact (Set.union_sdiff_cancel hDsub).symm

/-- `¬ AltChain N A` for `A ⊆ ℝ` implies that `A` is a union of at most `N` preconnected
(order convex) subsets. -/
theorem exists_cover_of_not_altChain {A : Set ℝ} {N : ℕ} (h : ¬ AltChain N A) :
    ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      A = ⋃₀ (s : Set (Set ℝ)) := by
  obtain ⟨s, hcard, hord, hunion⟩ := exists_cover_aux N A h
  exact ⟨s, hcard, fun I hI => Set.OrdConnected.isPreconnected (hord I hI), hunion⟩

end Work.WilC4
