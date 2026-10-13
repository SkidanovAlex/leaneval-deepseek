import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs

namespace Work.DSCOH.Norm.ReadFib

open Work.DSCOH.Norm

set_option linter.unusedSectionVars false

/-! ## Auxiliary order-embedding API for `Finset.orderEmbOfFin` -/

section OrderEmbAux

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- The index of `c` in the increasing enumeration `s.orderEmbOfFin h` is the number of elements
of `s` strictly below `c`, whenever `c` is in the range. -/
lemma card_filter_lt_of_orderEmbOfFin_eq {s : Finset α} {k : ℕ} (h : s.card = k) {i : Fin k}
    {c : α} (hc : s.orderEmbOfFin h i = c) :
    (s.filter (fun v => v < c)).card = (i : ℕ) := by
  have himg : s.filter (fun v => v < c)
      = (Finset.univ.filter (fun j : Fin k => j < i)).image (s.orderEmbOfFin h) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, hvc⟩
      obtain ⟨j, hj⟩ := Set.mem_range.mp (show v ∈ Set.range (s.orderEmbOfFin h) from by
        rw [Finset.range_orderEmbOfFin]; exact hv)
      refine ⟨j, ?_, hj⟩
      rw [← hj, ← hc] at hvc
      exact (s.orderEmbOfFin h).lt_iff_lt.mp hvc
    · rintro ⟨j, hji, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s h j,
        by rw [← hc]; exact (s.orderEmbOfFin h).lt_iff_lt.mpr hji⟩
  rw [himg, Finset.card_image_of_injective _ (s.orderEmbOfFin h).injective]
  exact filter_card_lt i

/-- Membership in the image of `s.orderEmbOfFin h` is described exactly by the count of the
elements of `s` below the value. -/
lemma orderEmbOfFin_apply_eq_iff {s : Finset α} {k : ℕ} (h : s.card = k) (i : Fin k) (c : α) :
    s.orderEmbOfFin h i = c ↔ c ∈ s ∧ (i : ℕ) = (s.filter (fun v => v < c)).card := by
  constructor
  · intro hc
    exact ⟨hc ▸ Finset.orderEmbOfFin_mem s h i, (card_filter_lt_of_orderEmbOfFin_eq h hc).symm⟩
  · rintro ⟨hcs, hcard⟩
    obtain ⟨j, hj⟩ := Set.mem_range.mp (show c ∈ Set.range (s.orderEmbOfFin h) from by
      rw [Finset.range_orderEmbOfFin]; exact hcs)
    have hji : j = i := Fin.ext (by
      have := card_filter_lt_of_orderEmbOfFin_eq h hj
      omega)
    rw [← hji]
    exact hj

end OrderEmbAux

/-! ## The `read` index map -/

section ReadAux

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- Membership in `headVal x a`: the values read by the head of `readA`. -/
lemma mem_headVal_iff {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (c : Fin (k+1)) :
    c ∈ headVal x a ↔ ∃ j : Fin (k+1), (j:ℕ) < (a:ℕ) ∧ Tuple.sort x j = c := by
  rw [headVal, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hjc⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2, hjc⟩
  · rintro ⟨j, hj, hjc⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hjc⟩

/-- The values of the tail embedding, described by the order-embedding API. -/
lemma tailEmb_eq_iff {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1))
    (i : Fin ((k+1) - (a:ℕ))) (c : Fin (k+1)) :
    tailEmb x a i = c ↔ c ∈ (headVal x a)ᶜ ∧
      (i:ℕ) = ((headVal x a)ᶜ.filter (fun v => v < c)).card := by
  rw [tailEmb]
  exact orderEmbOfFin_apply_eq_iff (compl_card x a) i c

/-- Every element of the complement of the head is in the range of the tail embedding. -/
lemma exists_tailEmb_of_mem_compl {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1))
    {c : Fin (k+1)} (hc : c ∈ (headVal x a)ᶜ) :
    ∃ i : Fin ((k+1) - (a:ℕ)), tailEmb x a i = c := by
  have hmem : c ∈ Set.range (tailEmb x a) := by
    rw [tailEmb, Finset.range_orderEmbOfFin]
    simpa using hc
  exact Set.mem_range.mp hmem

/-- The tail embedding reads the `a`-th smallest value at the second position `pos2A`. -/
lemma tailEmb_rankA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    tailEmb x a ⟨rankA x a, by have := rankA_lt x a; rw [compl_card] at this; exact this⟩
      = Tuple.sort x a := by
  rw [tailEmb]
  exact (orderEmbOfFin_apply_eq_iff (compl_card x a) _ _).mpr
    ⟨sortA_mem_compl x a, rfl⟩

/-- The value read at `pos2A` is `Tuple.sort x a`. -/
lemma readA_pos2A {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    readA x a (pos2A x a) = Tuple.sort x a := by
  have hgt : ¬ (((pos2A x a : Fin (k+2)) : ℕ) ≤ (a:ℕ)) := by
    show ¬ ((a:ℕ) + 1 + rankA x a ≤ (a:ℕ))
    omega
  rw [readA_tail x a hgt]
  have hidx : (⟨((pos2A x a : Fin (k+2)) : ℕ) - 1 - (a:ℕ),
        by have := (pos2A x a).isLt; omega⟩ : Fin ((k+1) - (a:ℕ)))
      = ⟨rankA x a, by have := rankA_lt x a; rw [compl_card] at this; exact this⟩ := by
    apply Fin.ext
    show ((pos2A x a : Fin (k+2)) : ℕ) - 1 - (a:ℕ) = rankA x a
    have hval : ((pos2A x a : Fin (k+2)) : ℕ) = (a:ℕ) + 1 + rankA x a := rfl
    rw [hval]
    omega
  rw [hidx]
  exact tailEmb_rankA x a

end ReadAux

/-- The fibre structure of the "read" index map of the sorting homotopy of Stacks 20.23.6:
`readA x a : Fin (k+2) → Fin (k+1)` is the index map of the `a`-th "read" of the tuple
`x : Fin (k+1) → ι` (the `p`-th entry of the read is `x (readA x a p)`).  It is a surjection
whose only double point is the `a`-th smallest value `Tuple.sort x a`, taken at the two
positions `a` and `pos2A x a`, and every other value has a unique preimage. -/
theorem readAFiber {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ} (x : Fin (k+1) → ι)
    (a : Fin (k+1)) :
    (∀ b : Fin (k+2), Work.DSCOH.Norm.readA x a b = Tuple.sort x a ↔
        b = Fin.castSucc a ∨ b = Work.DSCOH.Norm.pos2A x a) ∧
    (∀ c : Fin (k+1), c ≠ Tuple.sort x a → ∃! b : Fin (k+2), Work.DSCOH.Norm.readA x a b = c) := by
  constructor
  · intro b
    by_cases hle : (b:ℕ) ≤ (a:ℕ)
    · rw [readA_head x a hle]
      have hb_iff : (Tuple.sort x ⟨(b:ℕ), by have := b.isLt; omega⟩ = Tuple.sort x a)
          ↔ (b:ℕ) = (a:ℕ) := by
        constructor
        · intro h; exact congrArg Fin.val ((Tuple.sort x).injective h)
        · intro h; exact congrArg (Tuple.sort x) (Fin.ext h)
      rw [hb_iff]
      constructor
      · intro h; left; exact Fin.ext h
      · rintro (h | h)
        · exact congrArg Fin.val h
        · exfalso
          have hb2 : (b:ℕ) = (a:ℕ) + 1 + rankA x a := by rw [h]; rfl
          omega
    · have hgt : (a:ℕ) < (b:ℕ) := by omega
      constructor
      · intro h
        rw [readA_tail x a hle] at h
        have hi := (tailEmb_eq_iff x a ⟨(b:ℕ) - 1 - (a:ℕ),
          by have := b.isLt; omega⟩ (Tuple.sort x a)).mp h
        have hcard : (b:ℕ) - 1 - (a:ℕ) = rankA x a := by
          rw [rankA]; exact hi.2
        right
        apply Fin.ext
        show (b:ℕ) = (a:ℕ) + 1 + rankA x a
        omega
      · rintro (h | h)
        · exfalso
          have : (b:ℕ) = (a:ℕ) := congrArg Fin.val h
          omega
        · subst h; exact readA_pos2A x a
  · intro c hc_ne
    by_cases hcH : c ∈ headVal x a
    · obtain ⟨j, hjlt, hjσ⟩ := (mem_headVal_iff x a c).mp hcH
      refine ⟨⟨(j:ℕ), by have := j.isLt; omega⟩, ?_, ?_⟩
      · show readA x a (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (k+2)) = c
        rw [readA_head x a (by show (j:ℕ) ≤ (a:ℕ); omega), ← hjσ]
      · intro b hb
        by_cases hble : (b:ℕ) ≤ (a:ℕ)
        · rw [readA_head x a hble] at hb
          have : (⟨(b:ℕ), by have := b.isLt; omega⟩ : Fin (k+1)) = j :=
            (Tuple.sort x).injective (hb.trans hjσ.symm)
          exact Fin.ext (by simpa using congrArg Fin.val this)
        · rw [readA_tail x a hble] at hb
          rw [← hb] at hcH
          exact absurd hcH (tailEmb_mem x a _)
    · have hcT : c ∈ (headVal x a)ᶜ := Finset.mem_compl.mpr hcH
      obtain ⟨t, ht⟩ := exists_tailEmb_of_mem_compl x a hcT
      refine ⟨⟨(a:ℕ) + 1 + (t:ℕ), by have := t.isLt; omega⟩, ?_, ?_⟩
      · show readA x a (⟨(a:ℕ) + 1 + (t:ℕ), by have := t.isLt; omega⟩ : Fin (k+2)) = c
        rw [readA_tail x a (by show ¬ ((a:ℕ) + 1 + (t:ℕ) ≤ (a:ℕ)); omega)]
        have hidx : (⟨(a:ℕ) + 1 + (t:ℕ) - 1 - (a:ℕ),
            by have := t.isLt; omega⟩ : Fin ((k+1) - (a:ℕ))) = t := by
          apply Fin.ext
          show (a:ℕ) + 1 + (t:ℕ) - 1 - (a:ℕ) = (t:ℕ)
          omega
        rw [hidx]
        exact ht
      · intro b hb
        by_cases hble : (b:ℕ) ≤ (a:ℕ)
        · rw [readA_head x a hble] at hb
          rcases lt_or_eq_of_le hble with hlt | heq
          · exact absurd ((mem_headVal_iff x a c).mpr
              ⟨⟨(b:ℕ), by have := b.isLt; omega⟩, hlt, hb⟩) hcH
          · refine absurd ?_ hc_ne
            rw [← hb]
            exact congrArg (Tuple.sort x) (Fin.ext (by simpa using heq))
        · rw [readA_tail x a hble] at hb
          have hi : (⟨(b:ℕ) - 1 - (a:ℕ),
              by have := b.isLt; omega⟩ : Fin ((k+1)-(a:ℕ))) = t :=
            (tailEmb x a).injective (hb.trans ht.symm)
          apply Fin.ext
          have hv : (b:ℕ) - 1 - (a:ℕ) = (t:ℕ) := congrArg Fin.val hi
          show (b:ℕ) = (a:ℕ) + 1 + (t:ℕ)
          omega

end Work.DSCOH.Norm.ReadFib
