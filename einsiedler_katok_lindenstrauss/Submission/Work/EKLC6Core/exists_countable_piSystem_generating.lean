import Mathlib

namespace Work.EKLC6Core

open Set MeasureTheory

/-- **A countable generating π-system.**  (Corrected form: the previous version of this declaration
wrongly concluded `generateFrom (Set.range S) = ⊤`; `⊤ : MeasurableSpace X` is the *discrete*
σ-algebra, so that is impossible for countable `S` on an uncountable space.  The ambient σ-algebra
must be named.)

On a standard Borel space, there is a countable family of measurable sets which is a π-system
(closed under binary intersections), contains the whole space, and generates the ambient σ-algebra.

Proof sketch: use `countablyGenerated_of_standardBorel` together with
`MeasurableSpace.natGeneratingSequence`, giving `b : ℕ → Set X` with
`generateFrom (range b) = mX` and each `b n` measurable.  Enumerate the countable type
`{s : Finset ℕ}` with a surjection `e : ℕ → Finset ℕ` and set `S k := ⋂ n ∈ e k, b n`.  Then
`S i ∩ S j = S k` for `e k = e i ∪ e j`, `S k = univ` for `e k = ∅` (take `k` with `e k = ∅`,
e.g. any `k` with `e k = ∅`), and `b n = S k` for `e k = {n}`; hence
`generateFrom (range S) = generateFrom (range b) = mX`. -/
theorem exists_countable_piSystem_generating {X : Type*} [mX : MeasurableSpace X]
    [StandardBorelSpace X] :
    ∃ S : ℕ → Set X,
      (∀ n, @MeasurableSet X mX (S n)) ∧
      (∀ i j : ℕ, ∃ k, S i ∩ S j = S k) ∧
      (∃ k, S k = Set.univ) ∧
      @MeasurableSpace.generateFrom X (Set.range S) = mX := by
  classical
  -- A distinguished countable generating sequence of measurable sets.
  let b : ℕ → Set X := MeasurableSpace.natGeneratingSequence X
  have hbgen : @MeasurableSpace.generateFrom X (Set.range b) = mX :=
    MeasurableSpace.generateFrom_natGeneratingSequence X
  have hbmeas : ∀ n, @MeasurableSet X mX (b n) := fun n =>
    MeasurableSpace.measurableSet_natGeneratingSequence n
  -- The countable π-system of finite intersections of the `b n`.
  let C : Set (Set X) := Set.range (fun t : Finset ℕ => t.inf b)
  have hCmeas : ∀ s ∈ C, @MeasurableSet X mX s := by
    rintro s ⟨t, rfl⟩
    dsimp only
    rw [Finset.inf_eq_iInf]
    exact MeasurableSet.biInter t.countable_toSet (fun n _ => hbmeas n)
  have hCgen : @MeasurableSpace.generateFrom X C = mX := by
    have h1 : @MeasurableSpace.generateFrom X C
        ≤ @MeasurableSpace.generateFrom X (Set.range b) := by
      apply MeasurableSpace.generateFrom_le
      rintro s ⟨t, rfl⟩
      dsimp only
      rw [Finset.inf_eq_iInf]
      exact MeasurableSet.biInter t.countable_toSet (fun n _ =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n))
    have h2 : @MeasurableSpace.generateFrom X (Set.range b)
        ≤ @MeasurableSpace.generateFrom X C := by
      apply MeasurableSpace.generateFrom_mono
      rintro s ⟨n, rfl⟩
      exact ⟨{n}, by dsimp only; rw [Finset.inf_singleton]⟩
    rw [← hbgen]
    exact le_antisymm h1 h2
  have hCne : C.Nonempty := ⟨Set.univ, ⟨∅, by dsimp only; rw [Finset.inf_empty]; rfl⟩⟩
  have hCcount : C.Countable := Set.countable_range _
  -- Reindex the countable π-system as a sequence.
  obtain ⟨S, hS⟩ := Set.Countable.exists_eq_range hCcount hCne
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hCmeas (S n) (by rw [hS]; exact Set.mem_range_self n)
  · intro i j
    have hi : S i ∈ C := by rw [hS]; exact Set.mem_range_self i
    have hj : S j ∈ C := by rw [hS]; exact Set.mem_range_self j
    obtain ⟨t1, ht1⟩ := hi
    obtain ⟨t2, ht2⟩ := hj
    have ht1' : t1.inf b = S i := ht1
    have ht2' : t2.inf b = S j := ht2
    have hmem : (t1 ∪ t2).inf b ∈ C := ⟨t1 ∪ t2, rfl⟩
    have hrange : (t1 ∪ t2).inf b ∈ Set.range S := by rw [← hS]; exact hmem
    obtain ⟨k, hk⟩ := hrange
    refine ⟨k, ?_⟩
    rw [hk, Finset.inf_union, ht1', ht2']
    simp only [Set.inf_eq_inter]
  · have hu : (Set.univ : Set X) ∈ C := ⟨∅, by dsimp only; rw [Finset.inf_empty]; rfl⟩
    have hrange : (Set.univ : Set X) ∈ Set.range S := by rw [← hS]; exact hu
    obtain ⟨k, hk⟩ := hrange
    exact ⟨k, hk⟩
  · rw [← hS]; exact hCgen

end Work.EKLC6Core
