import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs

/-!
# Extending a band gauge to all of `ℤ`

Let `c = tlW p q` (`a ↦ q`, `b ↦ -p`) be the weight of the two-letter level graph and let
`Wt : ℤ → FreeGroup (Fin 2)` be a gauge of the *band* `[0, pq]`: `Wt 0 = 1`,
`cohom c (Wt i) = ofAdd i` for `i ∈ [0,pq]`, and the walk of `Wt i` runs through edges of the band
whose loop class vanishes (`htree`).

The target `Work.OROneRel.bandGaugeExtend` extends such a `Wt` to a function `Wt'` on *all* of `ℤ`
which keeps the band data: `Wt'` still has weight `ofAdd i` at every level, its band words still
walk through the tree of the window, and the loop classes of the edges of the window `[0,pq]` are
unchanged.

The extension used here is the crudest possible one: keep `Wt` on the band and put `τ ^ i` outside
it, where `τ` is the given element with `cohom c τ = ofAdd 1` (whose existence is exactly what makes
the weight condition satisfiable above the band).  Every condition only ever inspects `Wt'` at the
levels `e.2` and `e.2 + c e.1` of an edge `e` of the window (which both lie in the band) -- the
"outside" values are used for nothing but the global weight identity, which is why `τ ^ i` is
enough.
-/

namespace Work.OROneRel

noncomputable section

/-- **The extension of a band gauge by `τ`**: the band values of `Wt` inside `[0,pq]`, and `τ ^ i`
outside it. -/
noncomputable def bandExt (p q : ℕ) (τ : FreeGroup (Fin 2)) (Wt : ℤ → FreeGroup (Fin 2)) :
    ℤ → FreeGroup (Fin 2) :=
  fun i => if 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ) then Wt i else τ ^ i

/-- On the band, `bandExt` is the original gauge. -/
theorem bandExt_of_band {p q : ℕ} {τ : FreeGroup (Fin 2)} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (h1 : 0 ≤ i) (h2 : i ≤ (p : ℤ) * (q : ℤ)) : bandExt p q τ Wt i = Wt i := by
  simp only [bandExt]
  rw [if_pos ⟨h1, h2⟩]

/-- The extension has the prescribed weights outside the band, where it is `τ ^ i`. -/
theorem cohom_tau_zpow {p q : ℕ} {τ : FreeGroup (Fin 2)}
    (hτ : cohom (tlW p q) τ = Multiplicative.ofAdd 1) (i : ℤ) :
    cohom (tlW p q) (τ ^ i) = Multiplicative.ofAdd i := by
  rw [map_zpow, hτ, ← ofAdd_zsmul]
  simp

/-- **On the window, the extension computes the same loop classes as the band gauge.**  Indeed, the
loop class of the edge `e = (x,i)` only involves the gauge at the two band levels `i` and
`i + c x`. -/
theorem coverClassAt_bandExt_of_winE {p q : ℕ} {τ : FreeGroup (Fin 2)}
    {Wt : ℤ → FreeGroup (Fin 2)} {e : Fin 2 × ℤ}
    (he : e ∈ winE (tlW p q) 0 ((p:ℤ)*(q:ℤ))) :
    coverClassAt (bandExt p q τ Wt) (tlW p q) e = coverClassAt Wt (tlW p q) e := by
  obtain ⟨h1, h2, h3, h4⟩ := he
  rw [coverClassAt, coverClassAt, gaugeMap_of, gaugeMap_of]
  congr 1
  · rw [bandExt_of_band h1 h2]
  · rw [bandExt_of_band h3 h4]

end

theorem bandGaugeExtend (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {τ : FreeGroup (Fin 2)}
    {Wt : ℤ → FreeGroup (Fin 2)}
    (hτ : Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1)
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    ∃ Wt' : ℤ → FreeGroup (Fin 2),
      Wt' 0 = 1 ∧
      (∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt' i) = Multiplicative.ofAdd i) ∧
      (∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
        ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt' i)),
          Work.OROneRel.coverEdge e ∈
            Work.OROneRel.winTree Wt' (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∀ e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)),
        Work.OROneRel.coverClassAt Wt' (Work.OROneRel.tlW p q) e =
          Work.OROneRel.coverClassAt Wt (Work.OROneRel.tlW p q) e) := by
  refine ⟨bandExt p q τ Wt, ?_, ?_, ?_, ?_⟩
  · -- the level `0` lies in the band, so the extension takes the value `Wt 0`
    have h0 : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
      have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      nlinarith
    rw [bandExt_of_band (le_rfl : (0 : ℤ) ≤ 0) h0, hW0]
  · -- the weight: the band values by `hcoh`, the outside values by `hτ`
    intro i
    by_cases h : 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ)
    · rw [bandExt_of_band h.1 h.2]
      exact hcoh i h.1 h.2
    · rw [show bandExt p q τ Wt i = τ ^ i from by
        simp only [bandExt]
        exact if_neg h]
      exact cohom_tau_zpow hτ i
  · -- the walk of a band word: the edges are the ones of `htree` (the words agree on the band) and
    -- the loop classes are the ones of `Wt` (only band levels are involved)
    intro i h1 h2 e he
    rw [bandExt_of_band h1 h2] at he
    have hmem := htree i h1 h2 e he
    rw [mem_winTree] at hmem ⊢
    exact ⟨hmem.1, by rw [coverClassAt_bandExt_of_winE hmem.1]; exact hmem.2⟩
  · -- the loop classes on the window are unchanged
    intro e he
    exact coverClassAt_bandExt_of_winE he

end Work.OROneRel
