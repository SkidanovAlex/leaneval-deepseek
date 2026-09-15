import Mathlib
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le

namespace Commons.NumberTheory.Sieve

/-- The `PrimeData m` with exactly one active index are exactly `({j},∅)`, `(∅,{j})` and
`({j},{j})` for `j : Fin m`.  Consequently the sum of any `ℂ`-valued function over them splits into
those three sums.

(`PrimeData m` is the structure with fields `X X' : Finset (Fin m)` and `0 = (∅,∅)`.)

Proof sketch: show
`Finset.univ.filter (fun σ => (σ.X ∪ σ.X').card = 1)`
` = Finset.univ.image (fun j : Fin m => (⟨{j}, ∅⟩ : PrimeData m))`
`   ∪ Finset.univ.image (fun j : Fin m => (⟨∅, {j}⟩ : PrimeData m))`
`   ∪ Finset.univ.image (fun j : Fin m => (⟨{j}, {j}⟩ : PrimeData m))`
by extensionality (`Finset.ext` + `Finset.mem_filter`/`Finset.mem_union`/`Finset.mem_image`,
`Finset.card_eq_one`) — if `X ∪ X' = {j}` then `X, X' ⊆ {j}` and at least one of them is nonempty.
Then apply `Finset.sum_union` twice with `Finset.disjoint_left` (the three images are pairwise
disjoint) and `Finset.sum_image` with injectivity of `j ↦ ⟨{j}, ∅⟩` etc. -/
theorem sum_filter_card_one (m : ℕ) (F : PrimeData m → ℂ) :
    ∑ σ ∈ Finset.univ.filter (fun σ => (σ.X ∪ σ.X').card = 1), F σ
      = (∑ j : Fin m, F ⟨{j}, ∅⟩) + (∑ j : Fin m, F ⟨∅, {j}⟩)
        + (∑ j : Fin m, F ⟨{j}, {j}⟩) := by
  classical
  set S1 : Finset (PrimeData m) :=
    Finset.univ.image (fun j : Fin m => (⟨{j}, ∅⟩ : PrimeData m)) with hS1
  set S2 : Finset (PrimeData m) :=
    Finset.univ.image (fun j : Fin m => (⟨∅, {j}⟩ : PrimeData m)) with hS2
  set S3 : Finset (PrimeData m) :=
    Finset.univ.image (fun j : Fin m => (⟨{j}, {j}⟩ : PrimeData m)) with hS3
  have hset : Finset.univ.filter (fun σ : PrimeData m => (σ.X ∪ σ.X').card = 1)
      = (S1 ∪ S2) ∪ S3 := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hS1, hS2, hS3,
      Finset.mem_image]
    constructor
    · intro h
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
      have hX : σ.X ⊆ {j} := by
        intro x hx
        have hmem : x ∈ σ.X ∪ σ.X' := Finset.mem_union_left _ hx
        rwa [hj] at hmem
      have hX' : σ.X' ⊆ {j} := by
        intro x hx
        have hmem : x ∈ σ.X ∪ σ.X' := Finset.mem_union_right _ hx
        rwa [hj] at hmem
      rcases Finset.subset_singleton_iff.mp hX with hX0 | hXj
      · have hX's : σ.X' = {j} := by
          have h' := hj
          rw [hX0, Finset.empty_union] at h'
          exact h'
        refine Or.inl (Or.inr ⟨j, ?_⟩)
        rw [show σ = ⟨σ.X, σ.X'⟩ from rfl, PrimeData.mk.injEq]
        exact ⟨hX0.symm, hX's.symm⟩
      · rcases Finset.subset_singleton_iff.mp hX' with hX'0 | hX'j
        · refine Or.inl (Or.inl ⟨j, ?_⟩)
          rw [show σ = ⟨σ.X, σ.X'⟩ from rfl, PrimeData.mk.injEq]
          exact ⟨hXj.symm, hX'0.symm⟩
        · refine Or.inr ⟨j, ?_⟩
          rw [show σ = ⟨σ.X, σ.X'⟩ from rfl, PrimeData.mk.injEq]
          exact ⟨hXj.symm, hX'j.symm⟩
    · intro h
      rcases h with h12 | h3
      · rcases h12 with h1 | h2
        · obtain ⟨j, hj⟩ := h1
          have h1' : {j} = σ.X := by simpa using congrArg (fun τ : PrimeData m => τ.X) hj
          have h2' : (∅ : Finset (Fin m)) = σ.X' := by
            simpa using congrArg (fun τ : PrimeData m => τ.X') hj
          rw [← h1', ← h2']; simp
        · obtain ⟨j, hj⟩ := h2
          have h1' : (∅ : Finset (Fin m)) = σ.X := by
            simpa using congrArg (fun τ : PrimeData m => τ.X) hj
          have h2' : {j} = σ.X' := by
            simpa using congrArg (fun τ : PrimeData m => τ.X') hj
          rw [← h1', ← h2']; simp
      · obtain ⟨j, hj⟩ := h3
        have h1' : {j} = σ.X := by simpa using congrArg (fun τ : PrimeData m => τ.X) hj
        have h2' : {j} = σ.X' := by simpa using congrArg (fun τ : PrimeData m => τ.X') hj
        rw [← h1', ← h2']; simp
  rw [hset]
  have hd32 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro x hx12 hx3
    rw [Finset.mem_union] at hx12
    rw [hS3, Finset.mem_image] at hx3
    obtain ⟨k, -, hk⟩ := hx3
    rcases hx12 with hx1 | hx2
    · rw [hS1, Finset.mem_image] at hx1
      obtain ⟨j, -, hj⟩ := hx1
      rw [← hj] at hk
      have hX' : (∅ : Finset (Fin m)) = {k} := by
        simpa using congrArg (fun τ : PrimeData m => τ.X') hk
      exact Finset.singleton_ne_empty k hX'.symm
    · rw [hS2, Finset.mem_image] at hx2
      obtain ⟨j, -, hj⟩ := hx2
      rw [← hj] at hk
      have hX : (∅ : Finset (Fin m)) = {k} := by
        simpa using congrArg (fun τ : PrimeData m => τ.X) hk
      exact Finset.singleton_ne_empty k hX.symm
  have hd21 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS1, Finset.mem_image] at hx1
    rw [hS2, Finset.mem_image] at hx2
    obtain ⟨j, -, hj⟩ := hx1
    obtain ⟨k, -, hk⟩ := hx2
    rw [← hj] at hk
    have hX : (∅ : Finset (Fin m)) = {k} := by
      simpa using congrArg (fun τ : PrimeData m => τ.X) hk
    exact Finset.singleton_ne_empty k hX.symm
  rw [Finset.sum_union hd32, Finset.sum_union hd21]
  have hS1sum : S1.sum F = ∑ j : Fin m, F (⟨{j}, ∅⟩ : PrimeData m) := by
    have hinj : Set.InjOn (fun j : Fin m => (⟨{j}, ∅⟩ : PrimeData m))
        (↑(Finset.univ : Finset (Fin m))) := by
      intro x _ y _ hxy
      have hX : ({x} : Finset (Fin m)) = {y} := by simpa using congrArg (fun τ : PrimeData m => τ.X) hxy
      exact Finset.singleton_inj.mp hX
    simpa using Finset.sum_image (s := (Finset.univ : Finset (Fin m)))
      (g := fun j : Fin m => (⟨{j}, ∅⟩ : PrimeData m)) (f := F) hinj
  have hS2sum : S2.sum F = ∑ j : Fin m, F (⟨∅, {j}⟩ : PrimeData m) := by
    have hinj : Set.InjOn (fun j : Fin m => (⟨∅, {j}⟩ : PrimeData m))
        (↑(Finset.univ : Finset (Fin m))) := by
      intro x _ y _ hxy
      have hX' : ({x} : Finset (Fin m)) = {y} := by simpa using congrArg (fun τ : PrimeData m => τ.X') hxy
      exact Finset.singleton_inj.mp hX'
    simpa using Finset.sum_image (s := (Finset.univ : Finset (Fin m)))
      (g := fun j : Fin m => (⟨∅, {j}⟩ : PrimeData m)) (f := F) hinj
  have hS3sum : S3.sum F = ∑ j : Fin m, F (⟨{j}, {j}⟩ : PrimeData m) := by
    have hinj : Set.InjOn (fun j : Fin m => (⟨{j}, {j}⟩ : PrimeData m))
        (↑(Finset.univ : Finset (Fin m))) := by
      intro x _ y _ hxy
      have hX : ({x} : Finset (Fin m)) = {y} := by simpa using congrArg (fun τ : PrimeData m => τ.X) hxy
      exact Finset.singleton_inj.mp hX
    simpa using Finset.sum_image (s := (Finset.univ : Finset (Fin m)))
      (g := fun j : Fin m => (⟨{j}, {j}⟩ : PrimeData m)) (f := F) hinj
  rw [hS1sum, hS2sum, hS3sum]

end Commons.NumberTheory.Sieve
