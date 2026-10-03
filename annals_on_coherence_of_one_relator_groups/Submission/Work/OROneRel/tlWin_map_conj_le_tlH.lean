import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.band_halves_inter
import Submission.Work.OROneRel.tlWin_pq_eq_tlH

/-!
# The window subgroups `tlWin m` are closed under conjugation by the low deck element

For the two-letter band of `tlW p q` (window `[0, p*q]`), the *gauge-free* window subgroup
`tlWin p q m` is the closure of the set of words of weight `0` whose decorated walk stays in the
window `[0,m]`.  This file proves that conjugating any such subgroup by the low deck element
`τ = tlLowTau p q` lands inside the band vertex `tlH p q Wt`:

  `(tlWin p q m).map (MulAut.conj τ) ≤ tlH p q Wt`   whenever `m + 1 ≤ p*q`.

The point is the walk bookkeeping.  `τ` is a word of weight `1` whose walk runs from level `0` to
level `1` inside the band (`tlLowTau_walk`), so conjugating a word `L` of weight `0` whose walk
stays in `[0,m]` by `τ` shifts its walk to `[1, m+1] ⊆ [0, p*q]` (`decor_winE_shift`), and reading
`τ⁻¹` back from level `1` returns to level `0` inside the band (`decor_invRev`).  Hence the
concatenation

  `wordOf τ ++ L ++ invRev (wordOf τ)`

is a closed walk of weight `0` inside the whole band, i.e. spells an element of `tlWin p q (p*q)`,
which is the band vertex `tlH` (`tlWin_pq_eq_tlH`).
-/

namespace Work.OROneRel

/-- **The generating set of the window subgroup `tlWin p q m`**: the elements of `F₂` spelled by a
word of weight `0` whose decorated walk (for the weight `tlW p q`, started at level `0`) stays in
the window `[0,m]`.  This is literally the set whose closure is `tlWin p q m`. -/
def tlWinGen (p q : ℕ) (m : ℤ) : Set (FreeGroup (Fin 2)) :=
  {x | ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = x ∧ lsig (tlW p q) L = 0 ∧
    ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m}

/-- The window subgroup `tlWin p q m` is the closure of its generating set `tlWinGen p q m`. -/
theorem tlWin_eq_closure_tlWinGen (p q : ℕ) (m : ℤ) :
    tlWin p q m = Subgroup.closure (tlWinGen p q m) :=
  rfl

/-- **The generator-level statement.**  Conjugating an element of `tlWinGen p q m` by the low deck
element `τ` lands in the whole window subgroup `tlWin p q (p*q)`.  Indeed `τ x τ⁻¹` is spelled by
`wordOf τ ++ L ++ invRev (wordOf τ)`, whose decorated walk is the walk of `τ` (level `0` to `1`,
inside the band), the walk of `L` shifted up by one (levels `[1, m+1] ⊆ [0, p*q]`) and the reversed
walk of `τ` read back from level `1` (levels `[0, p*q]`). -/
theorem tlWinGen_conj_mem_tlWin (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {m : ℤ} (hm : m + 1 ≤ (p : ℤ) * (q : ℤ))
    {x : FreeGroup (Fin 2)} (hx : x ∈ tlWinGen p q m) :
    tlLowTau p q hp hq hcop * x * (tlLowTau p q hp hq hcop)⁻¹
      ∈ tlWin p q ((p : ℤ) * (q : ℤ)) := by
  obtain ⟨L, hmk, hlsig, hwalk⟩ := hx
  have hlsigT : lsig (tlW p q) (wordOf (tlLowTau p q hp hq hcop)) = 1 := by
    rw [lsig_wordOf, tlLowTau_cohom]
    rfl
  have hmkW : FreeGroup.mk (wordOf (tlLowTau p q hp hq hcop) ++ L ++
      FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)))
      = tlLowTau p q hp hq hcop * x * (tlLowTau p q hp hq hcop)⁻¹ := by
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mk_wordOf, hmk]
  have hmem : FreeGroup.mk (wordOf (tlLowTau p q hp hq hcop) ++ L ++
      FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)))
      ∈ Subgroup.closure (tlWinGen p q ((p : ℤ) * (q : ℤ))) := by
    refine Subgroup.subset_closure ⟨_, rfl, ?_, ?_⟩
    · -- the weight of the concatenation vanishes: `1 + 0 - 1 = 0`
      rw [decor_lsig_append, decor_lsig_append, lsig_invRev, hlsigT, hlsig]
      ring
    · -- the walk of the concatenation stays in the band
      intro e he
      rw [decor_append] at he
      rcases List.mem_append.mp he with he₁ | he₂
      · rw [decor_append] at he₁
        rcases List.mem_append.mp he₁ with he₃ | he₄
        · -- the prefix `wordOf τ`
          exact winE_mono (tlW p q) le_rfl le_rfl (tlLowTau_walk p q hp hq hcop e he₃)
        · -- the middle `L`, shifted up by one: `[1, m+1] ⊆ [0, p*q]`
          rw [hlsigT] at he₄
          exact winE_mono (tlW p q) (by norm_num) hm
            (decor_winE_shift (tlW p q) 0 1 0 m L hwalk e he₄)
      · -- the suffix `invRev (wordOf τ)`, read back from level `1`
        rw [decor_lsig_append, hlsig, add_zero] at he₂
        rw [decor_invRev (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop))] at he₂
        obtain ⟨e', he'', hfe⟩ := List.mem_map.mp he₂
        have he' : e' ∈ decor (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop)) :=
          List.mem_reverse.mp he''
        rw [← hfe]
        exact winE_mono (tlW p q) le_rfl le_rfl (tlLowTau_walk p q hp hq hcop e' he')
  rw [← tlWin_eq_closure_tlWinGen] at hmem
  rwa [hmkW] at hmem

theorem tlWin_map_conj_le_tlH (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    {m : ℤ} (hm : m + 1 ≤ (p : ℤ) * (q : ℤ)) :
    (Work.OROneRel.tlWin p q m).map (MulAut.conj (Work.OROneRel.tlLowTau p q hp hq hcop)) ≤
      Work.OROneRel.tlH p q Wt := by
  have hmap : (tlWin p q m).map (MulAut.conj (tlLowTau p q hp hq hcop))
      ≤ tlWin p q ((p : ℤ) * (q : ℤ)) := by
    rw [tlWin_eq_closure_tlWinGen, Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    show tlLowTau p q hp hq hcop * z * (tlLowTau p q hp hq hcop)⁻¹
      ∈ tlWin p q ((p : ℤ) * (q : ℤ))
    exact tlWinGen_conj_mem_tlWin p q hp hq hcop hm hz
  rwa [tlWin_pq_eq_tlH p q hp hq hcop Wt hW0 hcoh hwin htree] at hmap

end Work.OROneRel
