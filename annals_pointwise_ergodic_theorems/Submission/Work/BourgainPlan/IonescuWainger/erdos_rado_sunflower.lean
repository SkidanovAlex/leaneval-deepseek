import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# The Erdős–Rado sunflower lemma

A *sunflower* (in the sense of `TaoDefs.IsSunflower`) is a family of sets sharing a common core
`A₀ ⊆ A i` whose petals `A i \ A₀` are pairwise disjoint.  The **Erdős–Rado sunflower lemma**
states that for every cardinality bound `k` and every required number `r` of petals there is a
threshold `M` such that every family of at least `M` sets of size at most `k` contains `r`
distinct members forming a sunflower.

We prove the quantitative form, following the classical induction of Erdős–Rado 1960:

* `E k r = k! · (r-1)^k` is a bound for families all of whose members have *exactly* `k`
  elements (`exact_bound`), proved by induction on `k` using the maximal pairwise-disjoint
  subfamily and the pigeonhole/`link`-`shadow` argument;
* for families whose members have size at most `k` one sums the exact bounds over the
  cardinality layers (`atmost_bound`);
* the stated theorem is the contrapositive of the latter.

The supporting definitions (`HasSunflower`, `PairwiseDisj`, `link`, `shadow`,
`disjointFamilies`) and the elementary lemmas about them are laid out below.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.BourgainPlan.IonescuWainger

variable {α : Type*} [DecidableEq α]

/-- A finite family `T` of finite sets **contains an `r`-sunflower** if there are `r` *distinct*
members of `T` forming a sunflower. -/
def HasSunflower (r : ℕ) (T : Finset (Finset α)) : Prop :=
  ∃ A : Fin r → Finset α, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A

/-- A family `W` of sets is **pairwise disjoint** if any two distinct members are disjoint. -/
def PairwiseDisj (W : Finset (Finset α)) : Prop :=
  ∀ A ∈ W, ∀ B ∈ W, A ≠ B → Disjoint A B

/-- The **link** of a family `T` at a point `x`: the members of `T` containing `x`. -/
def link (T : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  T.filter (fun A => x ∈ A)

/-- The **shadow** of a family `T` at a point `x`: the link at `x` with `x` removed. -/
def shadow (T : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (link T x).image (fun A => A.erase x)

/-- The family of all pairwise disjoint subfamilies of `T`.  Its elements of maximum
cardinality are exactly the maximal pairwise disjoint subfamilies of `T` (for the purposes
of the sunflower argument). -/
noncomputable def disjointFamilies (T : Finset (Finset α)) : Finset (Finset (Finset α)) := by
  classical
  exact T.powerset.filter (fun W => PairwiseDisj W)

/-- Membership in `disjointFamilies`: pairwise disjoint subfamilies of `T`. -/
theorem mem_disjointFamilies {T W : Finset (Finset α)} :
    W ∈ disjointFamilies T ↔ W ⊆ T ∧ PairwiseDisj W := by
  classical
  rw [disjointFamilies, mem_filter, mem_powerset]

/-- The Erdős–Rado bound for families of `k`-element sets: `k! · (r-1)^k`.

It is defined by the recursion `E 0 r = 1`, `E (k+1) r = (k+1)·(r-1)·E k r`, so that the
inductive step of the sunflower lemma is a clean rewriting; equivalently it is `k!(r-1)^k`. -/
def E : ℕ → ℕ → ℕ
  | 0, _ => 1
  | (k+1), r => (k+1) * (r-1) * E k r

/-- A family is a sunflower (petals pairwise disjoint over a common core) iff its pairwise
intersections are all equal to a single set contained in every member.  This `∩`-form is the
convenient one for lifting a sunflower through the `insert x ·` map. -/
theorem isSunflower_iff_inter {r : ℕ} (A : Fin r → Finset α) :
    IsSunflower A ↔ ∃ K : Finset α, (∀ i, K ⊆ A i) ∧ ∀ i j : Fin r, i ≠ j → A i ∩ A j = K := by
  constructor
  · rintro ⟨A₀, hsub, hdisj⟩
    refine ⟨A₀, hsub, fun i j hij => ?_⟩
    ext x
    constructor
    · intro hx
      rw [mem_inter] at hx
      by_contra hxA
      exact (disjoint_left.mp (hdisj i j hij))
        (mem_sdiff.mpr ⟨hx.1, hxA⟩) (mem_sdiff.mpr ⟨hx.2, hxA⟩)
    · intro hx; exact mem_inter.mpr ⟨hsub i hx, hsub j hx⟩
  · rintro ⟨K, hsub, hinter⟩
    exact ⟨K, hsub, fun i j hij => by
      rw [disjoint_left]
      intro x hxi hxj
      rw [mem_sdiff] at hxi hxj
      have hx : x ∈ A i ∩ A j := mem_inter.mpr ⟨hxi.1, hxj.1⟩
      rw [hinter i j hij] at hx
      exact hxj.2 hx⟩

/-- Sunflowers are monotone in the family: enlarging `T` preserves `HasSunflower`. -/
theorem HasSunflower_mono {r : ℕ} {S T : Finset (Finset α)}
    (hST : S ⊆ T) (h : HasSunflower r S) : HasSunflower r T := by
  obtain ⟨A, hA, hinj, hsun⟩ := h
  exact ⟨A, fun i => hST (hA i), hinj, hsun⟩

/-- **The link/shadow lifting lemma.**  If the shadow of `T` at `x` contains an `r`-sunflower,
then so does `T` itself: add `x` back to each of the `r` petals. -/
theorem hasSunflower_of_shadow (T : Finset (Finset α)) (x : α) {r : ℕ}
    (h : HasSunflower r (shadow T x)) : HasSunflower r T := by
  obtain ⟨A, hA, hinj, hsun⟩ := h
  have hxA : ∀ i, x ∉ A i := by
    intro i
    obtain ⟨C, hC, hCA⟩ := mem_image.mp (hA i)
    rw [← hCA]; exact notMem_erase x C
  refine ⟨fun i => insert x (A i), ?_, ?_, ?_⟩
  · intro i
    show insert x (A i) ∈ T
    obtain ⟨C, hC, hCA⟩ := mem_image.mp (hA i)
    have hxC : x ∈ C := (mem_filter.mp hC).2
    have hCT : C ∈ T := (mem_filter.mp hC).1
    rw [← hCA, insert_erase hxC]; exact hCT
  · intro i j hij
    change insert x (A i) = insert x (A j) at hij
    have h2 : (insert x (A i)).erase x = (insert x (A j)).erase x := by rw [hij]
    rw [erase_insert (hxA i), erase_insert (hxA j)] at h2
    exact hinj h2
  · rw [isSunflower_iff_inter] at hsun ⊢
    obtain ⟨K, hKsub, hKint⟩ := hsun
    refine ⟨insert x K, ?_, ?_⟩
    · intro i y hy
      rw [mem_insert] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (hKsub i hy)
    · intro i j hij
      rw [← insert_inter_distrib, hKint i j hij]

/-- A pairwise disjoint family of at least `r` sets contains an `r`-sunflower (with empty
core). -/
theorem hasSunflower_of_pairwiseDisj {r : ℕ} {W : Finset (Finset α)}
    (h : PairwiseDisj W) (hr : r ≤ W.card) : HasSunflower r W := by
  classical
  obtain ⟨t, htW, htcard⟩ := exists_subset_card_eq hr
  set φ := t.equivFinOfCardEq htcard with hφ
  set A : Fin r → Finset α := fun i => ((φ.symm i : ↥t) : Finset α) with hAdef
  have hAt : ∀ i, A i ∈ t := fun i => ((φ.symm i : ↥t)).2
  have hinj : Function.Injective A := by
    intro i j hij
    have h1 : (φ.symm i : ↥t) = (φ.symm j : ↥t) := Subtype.ext hij
    exact φ.symm.injective h1
  have hsf : IsSunflower A := by
    refine ⟨∅, fun i => empty_subset _, fun i j hij => ?_⟩
    rw [sdiff_empty, sdiff_empty]
    exact h (A i) (htW (hAt i)) (A j) (htW (hAt j)) (fun hc => hij (hinj hc))
  exact ⟨A, fun i => htW (hAt i), hinj, hsf⟩

/-- **Erdős–Rado, exact cardinality.**  A family of *exactly* `k`-element sets with no
`r`-sunflower has at most `E k r` members.  Induction on `k`: take a pairwise disjoint
subfamily of maximum cardinality; every member meets its union, which has at most `k(r-1)`
points, so some link has strictly more than `E (k-1) r` points by pigeonhole, and its shadow
(an `E (k-1) r`-bounded family of `(k-1)`-element sets) lifts to a sunflower by
`hasSunflower_of_shadow`. -/
theorem exact_bound (k r : ℕ) : ∀ (T : Finset (Finset α)),
    (∀ A ∈ T, A.card = k) → ¬ HasSunflower r T → T.card ≤ E k r := by
  induction k with
  | zero =>
    intro T hsize hno
    have hsub : T ⊆ ({∅} : Finset (Finset α)) := by
      intro A hA
      have h0 : A = ∅ := card_eq_zero.mp (hsize A hA)
      simp [h0]
    calc T.card ≤ ({∅} : Finset (Finset α)).card := card_le_card hsub
      _ = 1 := by simp
      _ = E 0 r := by simp [E]
  | succ k ih =>
    intro T hsize hno
    classical
    have hPne : (disjointFamilies T).Nonempty :=
      ⟨∅, by rw [mem_disjointFamilies]; exact ⟨empty_subset _, fun A hA => (notMem_empty A hA).elim⟩⟩
    obtain ⟨W, hWmem, hWmax⟩ := exists_max_image (disjointFamilies T) (fun W => W.card) hPne
    have hWT : W ⊆ T := (mem_disjointFamilies.mp hWmem).1
    have hWdisj : PairwiseDisj W := (mem_disjointFamilies.mp hWmem).2
    -- a maximal pairwise disjoint subfamily has at most `r-1` members, else `W` is an `r`-sunflower
    have hWle : W.card ≤ r - 1 := by
      have hnot : ¬ r ≤ W.card :=
        fun hrle => hno (HasSunflower_mono hWT (hasSunflower_of_pairwiseDisj hWdisj hrle))
      omega
    -- its union `U` has at most `(k+1)(r-1)` points
    have hUcard : (W.biUnion (fun B => B)).card ≤ (Nat.succ k) * (r-1) := by
      have h1 : (W.biUnion (fun B => B)).card ≤ ∑ B ∈ W, B.card := card_biUnion_le
      have h2 : ∑ B ∈ W, B.card = ∑ B ∈ W, (Nat.succ k) := by
        apply sum_congr rfl; intro B hB; exact hsize B (hWT hB)
      have h3 : ∑ B ∈ W, (Nat.succ k) = W.card * (Nat.succ k) := by
        rw [sum_const, smul_eq_mul]
      calc (W.biUnion (fun B => B)).card ≤ ∑ B ∈ W, B.card := h1
        _ = ∑ B ∈ W, (Nat.succ k) := h2
        _ = W.card * (Nat.succ k) := h3
        _ ≤ (r-1) * (Nat.succ k) := Nat.mul_le_mul_right _ hWle
        _ = (Nat.succ k) * (r-1) := by ring
    -- every member of `T` meets `U`, by maximality of `W`
    have hmeet : ∀ A ∈ T, (A ∩ (W.biUnion (fun B => B))).Nonempty := by
      intro A hA
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      have hdisj : ∀ B ∈ W, Disjoint A B := by
        intro B hB
        rw [disjoint_left]
        intro y hyA hyB
        have hBU : B ⊆ W.biUnion (fun B => B) := fun x hx => mem_biUnion.mpr ⟨B, hB, hx⟩
        have : y ∈ A ∩ (W.biUnion (fun B => B)) := mem_inter.mpr ⟨hyA, hBU hyB⟩
        rw [hcon] at this
        exact notMem_empty y this
      by_cases hAW : A ∈ W
      · have hAU : A ⊆ W.biUnion (fun B => B) := fun x hx => mem_biUnion.mpr ⟨A, hAW, hx⟩
        have hAnon : A.Nonempty := by rw [← card_pos]; have := hsize A hA; omega
        obtain ⟨x, hx⟩ := hAnon
        have : x ∈ A ∩ (W.biUnion (fun B => B)) := mem_inter.mpr ⟨hx, hAU hx⟩
        rw [hcon] at this
        exact notMem_empty x this
      · -- otherwise `W ∪ {A}` is a larger pairwise disjoint subfamily, contradicting maximality
        have hInsP : insert A W ∈ disjointFamilies T := by
          rw [mem_disjointFamilies]
          refine ⟨?_, ?_⟩
          · intro B hB
            rw [mem_insert] at hB
            rcases hB with rfl | hBW
            · exact hA
            · exact hWT hBW
          · intro B hB C hC hBC
            rw [mem_insert] at hB hC
            rcases hB with rfl | hBW <;> rcases hC with rfl | hCW
            · exact absurd rfl hBC
            · exact hdisj C hCW
            · exact (hdisj B hBW).symm
            · exact hWdisj B hBW C hCW hBC
        have hlt : W.card < (insert A W).card := by
          rw [card_insert_of_notMem hAW]; omega
        have := hWmax (insert A W) hInsP
        omega
    -- each link is bounded by the induction hypothesis via its shadow
    have hlink : ∀ x ∈ W.biUnion (fun B => B), (link T x).card ≤ E k r := by
      intro x hxU
      have hsh : (shadow T x).card = (link T x).card := by
        rw [shadow, card_image_of_injOn]
        intro A hA B hB hAB
        change A.erase x = B.erase x at hAB
        have hxA : x ∈ A := (mem_filter.mp hA).2
        have hxB : x ∈ B := (mem_filter.mp hB).2
        have h2 : insert x (A.erase x) = insert x (B.erase x) := by rw [hAB]
        rwa [insert_erase hxA, insert_erase hxB] at h2
      have hshsize : ∀ A ∈ shadow T x, A.card = k := by
        intro A hA
        obtain ⟨C, hC, hCA⟩ := mem_image.mp hA
        have hxC : x ∈ C := (mem_filter.mp hC).2
        have hCT : C ∈ T := (mem_filter.mp hC).1
        rw [← hCA, card_erase_of_mem hxC, hsize C hCT]
        omega
      have hshno : ¬ HasSunflower r (shadow T x) := fun hsf => hno (hasSunflower_of_shadow T x hsf)
      have := ih (shadow T x) hshsize hshno
      rwa [hsh] at this
    -- `T` is covered by the links over `U`
    have hTcard : T.card ≤ ∑ x ∈ W.biUnion (fun B => B), (link T x).card := by
      have hsub : T ⊆ (W.biUnion (fun B => B)).biUnion (fun x => link T x) := by
        intro A hA
        obtain ⟨x, hx⟩ := hmeet A hA
        obtain ⟨hxA, hxU⟩ := mem_inter.mp hx
        exact mem_biUnion.mpr ⟨x, hxU, by rw [link, mem_filter]; exact ⟨hA, hxA⟩⟩
      calc T.card ≤ ((W.biUnion (fun B => B)).biUnion (fun x => link T x)).card := card_le_card hsub
        _ ≤ ∑ x ∈ W.biUnion (fun B => B), (link T x).card := card_biUnion_le
    calc T.card ≤ ∑ x ∈ W.biUnion (fun B => B), (link T x).card := hTcard
      _ ≤ ∑ x ∈ W.biUnion (fun B => B), E k r := sum_le_sum hlink
      _ = (W.biUnion (fun B => B)).card * E k r := by rw [sum_const, smul_eq_mul]
      _ ≤ ((Nat.succ k) * (r-1)) * E k r := Nat.mul_le_mul_right _ hUcard
      _ = E (Nat.succ k) r := by simp [E]

/-- **Erdős–Rado, bounded cardinality.**  A family of sets of size at most `k` with no
`r`-sunflower has at most `∑_{j ≤ k} E j r` members: split by cardinality layer and apply
`exact_bound` to each layer. -/
theorem atmost_bound (k r : ℕ) : ∀ (T : Finset (Finset α)),
    (∀ A ∈ T, A.card ≤ k) → ¬ HasSunflower r T →
    T.card ≤ ∑ j ∈ Finset.range (k+1), E j r := by
  intro T hsize hno
  classical
  have hmaps : Set.MapsTo (fun A : Finset α => A.card) ↑T ↑(Finset.range (k+1)) := by
    intro A hA
    simp only [Finset.mem_coe, mem_range]
    have := hsize A hA; omega
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_le_sum
  intro j hj
  rw [mem_range] at hj
  have hcards : ∀ A ∈ T.filter (fun A => A.card = j), A.card = j :=
    fun A hA => (mem_filter.mp hA).2
  have hnosub : ¬ HasSunflower r (T.filter (fun A => A.card = j)) :=
    fun hsf => hno (HasSunflower_mono (filter_subset _ _) hsf)
  exact exact_bound j r _ hcards hnosub

/-- **Erdős–Rado sunflower lemma.**  For every `k` and `r` there is a threshold `M` such that
every family of at least `M` sets of cardinality at most `k` contains `r` distinct members
forming a sunflower. -/
theorem erdos_rado_sunflower (k r : ℕ) :
    ∃ M : ℕ, ∀ {α : Type*} [DecidableEq α] (T : Finset (Finset α)),
      (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset α, (∀ i, A i ∈ T) ∧ Function.Injective A ∧
        IsSunflower A := by
  refine ⟨(∑ j ∈ Finset.range (k+1), E j r) + 1, ?_⟩
  intro α _ T hsize hM
  by_contra hno
  have := atmost_bound k r T hsize hno
  omega

end Work.BourgainPlan.IonescuWainger
