import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs

/-!
# `frameSum 0 = masterSum`

The frame sum at the singleton index `i = 0` is the master sum.

The frame sum runs over pairs `fg = (f, g)` of triples `f, g : Fin 3 → Fin H` satisfying the
*uniqueness* condition at the index `0`: the shift `shift6 fg 0` occurs exactly once among the six
shifts.  Reindexing `fg ↦ (aOf fg, bOf fg)` identifies these pairs with the pairs
`(a, b) ∈ [1,H]^3 × [1,H]^3` for which `a 0` does not occur among `a 1, a 2, b 0, b 1, b 2`; on
this set the uniqueness condition is exactly `NotInB a b ∧ a 0 ≠ a 1 ∧ a 0 ≠ a 2`, and the weight
`sqrtGcdW m 0 (shift6 fg) * frameW d g fg` becomes the master weight `wtAB m a b` cut down by
`DLd d a b ∧ g ∣ contAB a b` -- i.e. exactly the summand of `masterSum`.

The auxiliary facts used are `aOf_mem_box3`/`bOf_mem_box3` (the reindexing lands in the box),
`exists_pair_of_mem_box3`/`eq_of_aOf_bOf_eq` (it is a bijection), `frameUniq_iff_zero` (the
uniqueness predicate matches `condAB`'s "singleton" part) and `sqrtGcdW_zero_shift6` (the weights
agree).
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.frame_count_prov_aux

open Work.LinnikBurgess

/-- Membership in the box `[1,H]^3`. -/
lemma mem_box3 {H : ℕ} {a : Fin 3 → ℕ} :
    a ∈ box3 H ↔ ∀ l : Fin 3, 1 ≤ a l ∧ a l ≤ H := by
  rw [box3, Fintype.mem_piFinset]
  exact forall_congr' (fun l => Finset.mem_Icc)

/-- The entries of `aOf fg` lie in `[1,H]`. -/
lemma aOf_mem_box3 {H : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : aOf fg ∈ box3 H := by
  rw [mem_box3]
  intro l
  refine ⟨?_, ?_⟩
  · simp only [aOf]; omega
  · simp only [aOf]; exact Nat.succ_le_of_lt (fg.1 l).isLt

/-- The entries of `bOf fg` lie in `[1,H]`. -/
lemma bOf_mem_box3 {H : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : bOf fg ∈ box3 H := by
  rw [mem_box3]
  intro l
  refine ⟨?_, ?_⟩
  · simp only [bOf]; omega
  · simp only [bOf]; exact Nat.succ_le_of_lt (fg.2 l).isLt

/-- The map `fg ↦ (aOf fg, bOf fg)` is injective. -/
lemma eq_of_aOf_bOf_eq {H : ℕ} {fg₁ fg₂ : (Fin 3 → Fin H) × (Fin 3 → Fin H)}
    (h1 : aOf fg₁ = aOf fg₂) (h2 : bOf fg₁ = bOf fg₂) : fg₁ = fg₂ := by
  have hf : fg₁.1 = fg₂.1 := by
    funext l
    have h := congrFun h1 l
    simp only [aOf] at h
    exact Fin.ext (by omega)
  have hg : fg₁.2 = fg₂.2 := by
    funext l
    have h := congrFun h2 l
    simp only [bOf] at h
    exact Fin.ext (by omega)
  exact Prod.ext hf hg

/-- Every pair of triples in the box is the image of a pair of `Fin H`-triples under
`fg ↦ (aOf fg, bOf fg)`. -/
lemma exists_pair_of_mem_box3 {H : ℕ} {a b : Fin 3 → ℕ}
    (ha : a ∈ box3 H) (hb : b ∈ box3 H) :
    ∃ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H), aOf fg = a ∧ bOf fg = b := by
  rw [mem_box3] at ha hb
  refine ⟨(fun l => ⟨a l - 1, ?_⟩, fun l => ⟨b l - 1, ?_⟩), ?_, ?_⟩
  · exact lt_of_lt_of_le
      (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one (ha l).1) Nat.one_pos) (ha l).2
  · exact lt_of_lt_of_le
      (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one (hb l).1) Nat.one_pos) (hb l).2
  · funext l
    simp only [aOf]
    exact Nat.sub_add_cancel (ha l).1
  · funext l
    simp only [bOf]
    exact Nat.sub_add_cancel (hb l).1

/-- Uniqueness of the shift at position `0` is exactly the "singleton" part of `condAB`. -/
lemma frameUniq_iff_zero {H : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    (∀ i' : Fin 6, i' ≠ 0 → shift6 fg 0 ≠ shift6 fg i')
      ↔ (NotInB (aOf fg) (bOf fg) ∧ (aOf fg) 0 ≠ (aOf fg) 1 ∧ (aOf fg) 0 ≠ (aOf fg) 2) := by
  constructor
  · intro h
    refine ⟨fun l => ?_, ?_, ?_⟩
    · fin_cases l
      · simpa [aOf, bOf, shift6] using h 3 (by decide)
      · simpa [aOf, bOf, shift6] using h 4 (by decide)
      · simpa [aOf, bOf, shift6] using h 5 (by decide)
    · simpa [aOf, bOf, shift6] using h 1 (by decide)
    · simpa [aOf, bOf, shift6] using h 2 (by decide)
  · rintro ⟨h1, h2, h3⟩ i' hi'
    fin_cases i'
    · exact absurd rfl hi'
    · simpa [aOf, bOf, shift6] using h2
    · simpa [aOf, bOf, shift6] using h3
    · simpa [aOf, bOf, shift6] using h1 0
    · simpa [aOf, bOf, shift6] using h1 1
    · simpa [aOf, bOf, shift6] using h1 2

/-- The weight `sqrtGcdW m 0 (shift6 fg)` is the master weight `wtAB m (aOf fg) (bOf fg)`. -/
lemma sqrtGcdW_zero_shift6 {H m : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    sqrtGcdW m 0 (shift6 fg) = wtAB m (aOf fg) (bOf fg) := by
  obtain ⟨f, g⟩ := fg
  set F : Fin 6 → ℝ := fun l =>
    Real.sqrt ((Nat.gcd m ((shift6 (f, g) 0 : ℤ) - (shift6 (f, g) l : ℤ)).natAbs : ℕ) : ℝ)
    with hF
  have hprod : (∏ l ∈ Finset.univ.erase (0 : Fin 6), F l) = sqrtGcdW m 0 (shift6 (f, g)) := by
    rw [sqrtGcdW]
  rw [← hprod]
  have hset : Finset.univ.erase (0 : Fin 6) = ({1,2,3,4,5} : Finset (Fin 6)) := by decide
  rw [hset]
  rw [show ({1,2,3,4,5} : Finset (Fin 6))
        = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 ∅)))) from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_empty]
  have e1 : F 1 = wg m (aOf (f, g) 0) (aOf (f, g) 1) := by simp [hF, wg, del, shift6, aOf]
  have e2 : F 2 = wg m (aOf (f, g) 0) (aOf (f, g) 2) := by simp [hF, wg, del, shift6, aOf]
  have e3 : F 3 = wg m (aOf (f, g) 0) (bOf (f, g) 0) := by simp [hF, wg, del, shift6, aOf, bOf]
  have e4 : F 4 = wg m (aOf (f, g) 0) (bOf (f, g) 1) := by simp [hF, wg, del, shift6, aOf, bOf]
  have e5 : F 5 = wg m (aOf (f, g) 0) (bOf (f, g) 2) := by simp [hF, wg, del, shift6, aOf, bOf]
  rw [e1, e2, e3, e4, e5, wtAB]
  ring

/-- `masterSum` as a single sum over pairs in the box. -/
lemma masterSum_eq_sum_prod (H m d g : ℕ) :
    masterSum H m d g
      = ∑ p ∈ box3 H ×ˢ box3 H,
          (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0) := by
  rw [masterSum]
  exact (Finset.sum_product (box3 H) (box3 H)
    (fun p : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0)).symm

theorem frameSum_eq_masterSum (H m d g : ℕ) :
    frameSum H m d g 0 = masterSum H m d g := by
  classical
  rw [masterSum_eq_sum_prod]
  -- The summand of the frame sum, once uniqueness holds, is the master summand.
  have hAbody : ∀ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
      (∀ i' : Fin 6, i' ≠ 0 → shift6 fg 0 ≠ shift6 fg i') →
      sqrtGcdW m 0 (shift6 fg) * frameW d g fg
        = (if condAB d g (aOf fg) (bOf fg) then wtAB m (aOf fg) (bOf fg) else 0) := by
    intro fg huniq
    have huniqQ := (frameUniq_iff_zero fg).mp huniq
    rw [frameW, sqrtGcdW_zero_shift6]
    by_cases hD : DLd d (aOf fg) (bOf fg) ∧ g ∣ contAB (aOf fg) (bOf fg)
    · rw [if_pos hD, if_pos]
      · ring
      · unfold condAB
        exact ⟨huniqQ.1, huniqQ.2.1, huniqQ.2.2, hD.1, hD.2⟩
    · rw [if_neg hD, if_neg]
      · ring
      · intro hc
        exact hD ⟨hc.2.2.2.1, hc.2.2.2.2⟩
  -- Reindex the frame sum by `fg ↦ (aOf fg, bOf fg)`.
  have hA : frameSum H m d g 0
      = ∑ p ∈ (box3 H ×ˢ box3 H).filter
          (fun p => NotInB p.1 p.2 ∧ p.1 0 ≠ p.1 1 ∧ p.1 0 ≠ p.1 2),
        (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0) := by
    unfold frameSum
    refine Finset.sum_bij (fun fg _ => (aOf fg, bOf fg)) ?_ ?_ ?_ ?_
    · intro fg hfg
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨aOf_mem_box3 fg, bOf_mem_box3 fg⟩,
        (frameUniq_iff_zero fg).mp (Finset.mem_filter.mp hfg).2⟩
    · intro fg₁ _ fg₂ _ heq
      have heq' : (aOf fg₁, bOf fg₁) = (aOf fg₂, bOf fg₂) := heq
      exact eq_of_aOf_bOf_eq (congrArg Prod.fst heq') (congrArg Prod.snd heq')
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨fg, h1, h2⟩ := exists_pair_of_mem_box3 hp.1.1 hp.1.2
      refine ⟨fg, ?_, ?_⟩
      · rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        show ∀ i' : Fin 6, i' ≠ 0 → shift6 fg 0 ≠ shift6 fg i'
        rw [frameUniq_iff_zero, h1, h2]
        exact hp.2
      · show (aOf fg, bOf fg) = p
        rw [h1, h2]
    · intro fg hfg
      rw [Finset.mem_filter] at hfg
      exact hAbody fg hfg.2
  rw [hA]
  -- Pairs failing the singleton condition contribute nothing, so the filter can be dropped.
  have hBbody : ∀ p : (Fin 3 → ℕ) × (Fin 3 → ℕ),
      (if NotInB p.1 p.2 ∧ p.1 0 ≠ p.1 1 ∧ p.1 0 ≠ p.1 2
        then (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0) else 0)
      = (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0) := by
    intro p
    by_cases hQ : NotInB p.1 p.2 ∧ p.1 0 ≠ p.1 1 ∧ p.1 0 ≠ p.1 2
    · rw [if_pos hQ]
    · rw [if_neg hQ, if_neg]
      intro hc
      exact hQ ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hB : (∑ p ∈ (box3 H ×ˢ box3 H).filter
          (fun p => NotInB p.1 p.2 ∧ p.1 0 ≠ p.1 1 ∧ p.1 0 ≠ p.1 2),
        (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0))
      = ∑ p ∈ box3 H ×ˢ box3 H,
        (if condAB d g p.1 p.2 then wtAB m p.1 p.2 else 0) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p _ => hBbody p)
  rw [hB]

end Work.LinnikBurgess.frame_count_prov_aux
