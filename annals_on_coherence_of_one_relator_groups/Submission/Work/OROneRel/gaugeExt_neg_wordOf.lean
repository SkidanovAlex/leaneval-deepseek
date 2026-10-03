import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gaugeExtWalkDefs
import Submission.Work.OROneRel.gauge_band_last_not

/-!
# Below the band the global gauge is literally the chain word

`Work.OROneRel.gaugeExt p q hq Wt` extends a band gauge `Wt` of the two-letter level graph
(`c = tlW p q`, `a ↦ q`, `b ↦ -p`) to all of `ℤ` by the two `a`-chains `gPosL` (above the band
`[0, pq]`) and `gNegL` (below it); see `Submission/Work/OROneRel/globalGauge.lean`.

The global gauge is *defined* as the class of the explicit chain word (`gaugeExt i =
FreeGroup.mk (gaugeExtL i)`), so a priori `wordOf (gaugeExt i)` is only the *reduction* of the chain
word `gaugeExtL i` and may be shorter than it.  The point of this file is that below the band
nothing is ever cancelled:

  `wordOf (gaugeExt i) = gNegL p q hq Wt i`  for `i < 0`,

together with the companion last-letter fact `(gNegL i).getLast? = some (0, false)` (the last letter
of the lower chain is the backwards `a`).

The reduction of the chain word is the identity exactly when the chain word is reduced.  The lower
chain is

  `gNegL i = wordOf (Wt r) ++ [a⁻¹, a⁻¹, …, a⁻¹]`,   `r = i + kq ∈ [0, q)`,  `k = (-i + q - 1) / q`,

built by the recursion `gNegL i = gNegL (i + q) ++ [a⁻¹]`; the only possible cancellation is at the
junction of `wordOf (Wt r)` with the first `a⁻¹`, i.e. it happens iff `wordOf (Wt r)` ends with `a`.
This is excluded by the hypothesis `htree`: the decorated walk of `Wt r` runs through the tree of
the window `[0, pq]`, so all its edges have non-negative source level, while the edge of a final `a`
would be `(0, r - q)` with `r < q`; this is the first half of
`Submission/Work/OROneRel/gauge_band_last_not.lean` (`gauge_band_last_not`).

With `FreeGroup.IsReduced.reduce_eq` and `wordOf_gaugeExt_reduce`
(`Submission/Work/OROneRel/gaugeExtWalkDefs.lean`) this gives the first conjunct; the second is the
definitional unfolding `gNegL_eq`.
-/

namespace Work.OROneRel

noncomputable section

/-! ## Auxiliary list facts -/

/-- If the last letter of a list is not `a`, then no member of `getLast?` is `a`. -/
private theorem mem_getLast?_ne {L : List (Fin 2 × Bool)} {a : Fin 2 × Bool}
    (h : L.getLast? ≠ some ((0 : Fin 2), true)) (ha : a ∈ L.getLast?) :
    a ≠ ((0 : Fin 2), true) := by
  intro heq
  rw [Option.mem_def, heq] at ha
  exact h ha

/-- **Appending a backwards `a` to a reduced word whose last letter is not `a` keeps it reduced.**
The only junction of the concatenation is between the last letter of `L` and `a⁻¹`; these do not
cancel because the last letter of `L` is not `a`. -/
private theorem isReduced_append_neg {L : List (Fin 2 × Bool)} (h : FreeGroup.IsReduced L)
    (hlast : L.getLast? ≠ some ((0 : Fin 2), true)) :
    FreeGroup.IsReduced (L ++ [((0 : Fin 2), false)]) := by
  rw [FreeGroup.IsReduced, List.isChain_append]
  refine ⟨h, FreeGroup.IsReduced.singleton, ?_⟩
  intro a ha b hb hab
  rw [List.head?_singleton, Option.mem_some_iff] at hb
  subst hb
  have hane := mem_getLast?_ne hlast ha
  cases hc : a.2
  · rfl
  · exfalso
    apply hane
    obtain ⟨x, y⟩ := a
    simp_all

/-- The reduced word of an element of the free group is reduced. -/
private theorem wordOf_isReduced (u : FreeGroup (Fin 2)) : FreeGroup.IsReduced (wordOf u) := by
  rw [wordOf_eq_toWord_inst]
  exact FreeGroup.isReduced_toWord

/-- **The last letter of the lower chain is the backwards `a`.**  Immediate from the recursion
equation `gNegL_eq`. -/
private theorem gNegL_getLast {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} (i : ℤ) :
    (gNegL p q hq Wt i).getLast? = some ((0 : Fin 2), false) := by
  rw [gNegL_eq i, List.getLast?_concat]

/-! ## The lower chain is reduced -/

/-- **The lower chain word of the global gauge is reduced**, for every level `i < 0`.

Strong induction on the number `(-i).toNat` of steps of the recursion `gNegL i = gNegL (i + q) ++
[a⁻¹]`: a backwards `a` appends to a reduced word (the induction hypothesis) or to the band word
`wordOf (Wt (i + q))` at the exit level `i + q ∈ [0, q)` (reduced by `FreeGroup.isReduced_toWord`),
and in the exit case the last letter of the band word is not `a` by `gauge_band_last_not`. -/
private theorem gNegL_isReduced {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ npq p q →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 (npq p q)) :
    ∀ i : ℤ, i < 0 → FreeGroup.IsReduced (gNegL p q hq Wt i) := by
  have key : ∀ n : ℕ, ∀ i : ℤ, (-i).toNat ≤ n → i < 0 →
      FreeGroup.IsReduced (gNegL p q hq Wt i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin hi
      have hqle : (q : ℤ) ≤ npq p q := q_le_npq (p := p) (q := q) hp
      rw [gNegL_eq i]
      by_cases hsq : 0 ≤ i + (q : ℤ)
      · -- the chain has come back into the band at the level `i + q ∈ [0, q)`
        rw [if_pos hsq]
        refine isReduced_append_neg (wordOf_isReduced (Wt (i + (q : ℤ)))) ?_
        exact (gauge_band_last_not (p := p) (q := q) hcoh htree hsq (by omega)).1 (by omega)
      · -- the chain takes one more step
        rw [if_neg hsq]
        have hlt : (-(i + (q : ℤ))).toNat < n := by
          have h2 : 0 < -i := by omega
          have hstep : (-(i + (q : ℤ))).toNat < (-i).toNat := by
            rw [Int.toNat_lt_toNat h2]
            omega
          omega
        have hrec := ih ((-(i + (q : ℤ))).toNat) hlt (i + (q : ℤ)) le_rfl (by omega)
        refine isReduced_append_neg hrec ?_
        rw [gNegL_getLast]
        simp
  exact fun i hi => key (-i).toNat i le_rfl hi

theorem gaugeExt_neg_wordOf {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    {i : ℤ} (hi : i < 0) :
    Work.OROneRel.wordOf (Work.OROneRel.gaugeExt p q hq Wt i) = Work.OROneRel.gNegL p q hq Wt i ∧
    (Work.OROneRel.gNegL p q hq Wt i).getLast? = some ((0 : Fin 2), false) := by
  have hred := gNegL_isReduced (p := p) (q := q) (hq := hq) (Wt := Wt) hp hcoh htree i hi
  refine ⟨?_, gNegL_getLast (p := p) (q := q) (hq := hq) (Wt := Wt) i⟩
  -- below the band the explicit chain word *is* `gNegL`, and it is reduced
  rw [wordOf_gaugeExt_reduce p q hq Wt i, gaugeExtL,
    dif_neg (by rintro ⟨h1, -⟩; omega), dif_pos hi]
  exact FreeGroup.IsReduced.reduce_eq hred

end

end Work.OROneRel
