import Mathlib
import Submission.Work.Drive.Surf.Model

namespace Work.Surf

open scoped Topology

/-- The parity of a sum of an odd number of odd naturals is the parity of the number of summands.
Used as the arithmetic step of `chordMeetAll_parity`. -/
lemma odd_sum_iff_odd_card {ι : Type*} [Fintype ι] (f : ι → ℕ) (hf : ∀ i, Odd (f i)) :
    Odd (∑ i, f i) ↔ Odd (Fintype.card ι) := by
  have h1 : (∑ i : ι, f i) % 2 = (Fintype.card ι) % 2 := by
    rw [Finset.sum_nat_mod]
    rw [Finset.sum_congr rfl (fun i _ => Nat.odd_iff.mp (hf i))]
    simp
  rw [Nat.odd_iff, Nat.odd_iff, h1]

/-- **The family form of the mod-2 intersection number of two chord systems.**

This is pure bookkeeping: `chordMeetAll A B` is the disjoint union of the blocks
`chordMeetBlock A B i j` (`Work.Drive.chordMeetBlock_disjoint`, `Work.Drive.chordMeetAll_subset_iUnion`,
already proved in `Submission/Work/Drive/Surf/Model.lean`), and each block is in bijection with
`chordMeet (A i) (B j)` via `((i,s),(j,t)) ↦ (s,t)`.  Hence

`(chordMeetAll A B).ncard = ∑ i, ∑ j, (chordMeet (A i) (B j)).ncard`,

and since each summand is odd by `hodd` — which also rules out the infinite case, because `Set.ncard`
of an infinite set is `0` — a sum of `Fintype.card ι * Fintype.card κ` odd naturals has the parity of
`Fintype.card ι * Fintype.card κ`.  Useful lemmas: `Set.ncard_image_of_injective`,
`Set.ncard_eq_toFinset_card`, `Odd.add_odd`, `Even.add_odd`, `Finset.card_univ`. -/
theorem chordMeetAll_parity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hodd : ∀ i j, Odd (Work.Drive.chordMeet (A i) (B j)).ncard) :
    Odd (Work.Drive.chordMeetAll A B).ncard ↔ Odd (Fintype.card ι * Fintype.card κ) := by
  classical
  -- Each block is a copy of the corresponding `chordMeet`, under the injection `(s,t) ↦ ((i,s),(j,t))`.
  have hkey : ∀ i j, (Work.Drive.chordMeetBlock A B i j).ncard =
        (Work.Drive.chordMeet (A i) (B j)).ncard
      ∧ (Work.Drive.chordMeetBlock A B i j).Finite := by
    intro i j
    have hinj : Function.Injective (fun q : ℝ × ℝ => ((i, q.1), (j, q.2)) :
        ℝ × ℝ → (ι × ℝ) × (κ × ℝ)) := by
      intro a b h
      exact Prod.ext (by simpa using congrArg Prod.fst h) (by simpa using congrArg Prod.snd h)
    have himg : (fun q : ℝ × ℝ => ((i, q.1), (j, q.2))) '' (Work.Drive.chordMeet (A i) (B j))
        = Work.Drive.chordMeetBlock A B i j := by
      ext q
      constructor
      · rintro ⟨q', hq', rfl⟩
        exact ⟨rfl, rfl, hq'.1, hq'.2.1, hq'.2.2⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨(q.1.2, q.2.2), ⟨h3, h4, h5⟩,
          Prod.ext (Prod.ext h1.symm rfl) (Prod.ext h2.symm rfl)⟩
    -- `hodd` rules out the infinite case, since `Set.ncard` of an infinite set is `0`.
    have hfinChord : (Work.Drive.chordMeet (A i) (B j)).Finite := by
      by_contra h
      have hinf : (Work.Drive.chordMeet (A i) (B j)).Infinite := Set.not_finite.mp h
      have h := hodd i j
      rw [Set.Infinite.ncard hinf] at h
      exact Nat.not_odd_zero h
    refine ⟨?_, ?_⟩
    · rw [← himg, Set.ncard_image_of_injective _ hinj]
    · rw [← himg]
      exact hfinChord.image _
  -- The blocks are the pairwise disjoint pieces of `chordMeetAll`.
  let s : ι × κ → Set ((ι × ℝ) × (κ × ℝ)) := fun p => Work.Drive.chordMeetBlock A B p.1 p.2
  have hunion : Work.Drive.chordMeetAll A B = ⋃ p, s p := by
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Work.Drive.chordMeetAll_subset_iUnion A B hq)
      obtain ⟨j, hij⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨(i, j), hij⟩
    · intro q hq
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hq
      exact Work.Drive.chordMeetBlock_subset A B p.1 p.2 hp
  have hun := Set.ncard_iUnion_of_finite (s := s) (fun p => (hkey p.1 p.2).2) (by
    intro p q hpq
    exact Work.Drive.chordMeetBlock_disjoint A B (fun h => hpq (by simpa using h)))
  have hncard : (Work.Drive.chordMeetAll A B).ncard =
      ∑ p : ι × κ, (Work.Drive.chordMeet (A p.1) (B p.2)).ncard := by
    rw [hunion, hun, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl (fun p _ => (hkey p.1 p.2).1)
  rw [hncard, ← Fintype.card_prod]
  exact odd_sum_iff_odd_card (fun p : ι × κ => (Work.Drive.chordMeet (A p.1) (B p.2)).ncard)
    (fun p => hodd p.1 p.2)

end Work.Surf
