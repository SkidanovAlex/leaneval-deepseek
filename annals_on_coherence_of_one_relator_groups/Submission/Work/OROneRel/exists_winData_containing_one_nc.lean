-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The window data with the level `1` in the window and the window minimal

`Work.OROneRel.NC.exists_winWindowData` produces, for a relator `u` all of whose letters have non-zero
exponent sum, a surjective weight `c` killing `u` (`cohom c u = 1`), a window `[lo,hi]` of levels, a
deck element `τ` and a gauge `Wt`.

This file provides `Work.OROneRel.NC.exists_winData_containing_one`, the version of the customer's
statement in which

* the level `1` is *contained* in the window: `lo ≤ 1` and `1 ≤ hi`, and
* the window is *minimal*: the walk of `u` cannot be translated by any non-zero amount to fit
  inside the window (`hone`).

Since `cohom c u = 1` the walk of `u` is *closed*, and the walk stays in the window; hence
`0 ∈ [lo,hi]`, so `lo ≤ 1` is for free.  The only possible obstruction is `hi = 0`: the window then
lies entirely below the level `1`.

In that case the data is *reflected* in the level line.  Put `c' = -c` (so the level `i` of the
`c`-cover becomes the level `-i` of the `c'`-cover) and `Wt' i = Wt (-i)`.  Then, with
`lo' = -hi = 0` and `hi' = -lo ≥ 1`:

* an edge `(x,j)` of the `c'`-cover is in the window `[lo',hi']` exactly when the edge `(x,-j)` is in
  the window `[lo,hi]` (`mem_winE_neg`),
* the loop class of `(x,j)` under the gauge `Wt'` is the loop class of `(x,-j)` under the gauge `Wt`
  (`coverClassAt_neg`), whence the same statement for the tree `winTree` (`mem_winTree_neg`),
* the decorated word of a word `L` for the reflected weight is the level-negation of the decorated
  word for `c` (`decor_neg`),
* `cohom c' = (cohom c)⁻¹` as a homomorphism (`cohom_neg`), so `cohom c'` still kills `u`,
* the minimality `hone` of the window is reflected into the minimality of the reflected window, with
  the shift `k` replaced by `-k` (`hone_neg`).

Every required conjunct is then transported along these identities.  The helpers are local to this
file.
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.exists_winWindowData_nc
import Submission.Work.OROneRel.band_of_winE_decor

namespace Work.OROneRel.NC

universe u

variable {α : Type u}

/-! ## Reflecting the level line -/

/-- The weight of a word with respect to the negated weight function is the negative of its weight. -/
private theorem lsig_neg (c : α → ℤ) (L : List (α × Bool)) :
    lsig (fun x => -c x) L = -lsig c L := by
  induction L with
  | nil => rw [lsig_nil', lsig_nil', neg_zero]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [lsig_cons', lsig_cons', ih]
      simp only [linc, Bool.false_eq_true, if_false]
      ring
    · rw [lsig_cons', lsig_cons', ih]
      simp only [linc, if_true]
      ring

/-- **The cohomology of the negated weight is the inverse.** -/
private theorem cohom_neg (c : α → ℤ) (w : FreeGroup α) :
    cohom (fun x : α => -c x) w = (cohom c w)⁻¹ := by
  have h1 := cohom_mk (fun x : α => -c x) (wordOf w)
  rw [mk_wordOf] at h1
  have h2 := cohom_mk c (wordOf w)
  rw [mk_wordOf] at h2
  rw [h1, h2, lsig_neg, ofAdd_neg]

/-- **The decorated word of the reflected weight** is the level-negation of the decorated word. -/
private theorem decor_neg (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    decor (fun x => -c x) i L = (decor c (-i) L).map (fun p => ((p.1.1, -p.1.2), p.2)) := by
  induction L generalizing i with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · have h1 : decor (fun x : α => -c x) i ((a, false) :: L)
          = ((a, i + c a), false) :: decor (fun x : α => -c x) (i + c a) L := by
        show ((a, i - (-c a)), false) :: decor (fun x : α => -c x) (i - (-c a)) L
            = ((a, i + c a), false) :: decor (fun x : α => -c x) (i + c a) L
        congr 1
        · ring_nf
        · ring_nf
      rw [h1, show decor c (-i) ((a, false) :: L)
          = ((a, -i - c a), false) :: decor c (-i - c a) L from rfl,
        List.map_cons, ih (i + c a), show -i - c a = -(i + c a) from by ring]
      simp
    · have h1 : decor (fun x : α => -c x) i ((a, true) :: L)
          = ((a, i), true) :: decor (fun x : α => -c x) (i - c a) L := by
        show ((a, i), true) :: decor (fun x : α => -c x) (i + (-c a)) L
            = ((a, i), true) :: decor (fun x : α => -c x) (i - c a) L
        rfl
      rw [h1, show decor c (-i) ((a, true) :: L)
          = ((a, -i), true) :: decor c (-i + c a) L from rfl,
        List.map_cons, ih (i - c a), show -i + c a = -(i - c a) from by ring]
      simp

/-- **The loop class of a reflected edge.**  The class of the edge `(x,j)` of the `(-c)`-cover under
the gauge `Wt (-·)` is the class of the edge `(x,-j)` of the `c`-cover under the gauge `Wt`. -/
private theorem coverClassAt_neg (c : α → ℤ) (W : ℤ → FreeGroup α) (x : α) (j : ℤ) :
    coverClassAt (fun i => W (-i)) (fun x : α => -c x) (x, j) = coverClassAt W c (x, -j) := by
  simp only [coverClassAt, gaugeMap_of]
  rw [show -(j + -c x) = -j + c x from by ring]

/-- **The reflected window.**  The edge `(x,j)` of the `(-c)`-cover lies in the window `[-hi,-lo]`
exactly when the edge `(x,-j)` lies in the window `[lo,hi]`. -/
private theorem mem_winE_neg (c : α → ℤ) (lo hi : ℤ) (x : α) (j : ℤ) :
    (x, j) ∈ winE (fun x : α => -c x) (-hi) (-lo) ↔ (x, -j) ∈ winE c lo hi := by
  simp only [mem_winE]
  constructor <;> intro h <;> obtain ⟨h1, h2, h3, h4⟩ := h <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **The reflected tree.**  The edge `(x,j)` of the `(-c)`-cover is a tree edge of the window
`[-hi,-lo]` for the gauge `Wt (-·)` exactly when the edge `(x,-j)` is a tree edge of the window
`[lo,hi]` for the gauge `Wt`. -/
private theorem mem_winTree_neg (c : α → ℤ) (lo hi : ℤ) (W : ℤ → FreeGroup α) (x : α) (j : ℤ) :
    (x, j) ∈ winTree (fun i => W (-i)) (fun x : α => -c x) (-hi) (-lo) ↔
      (x, -j) ∈ winTree W c lo hi := by
  simp only [mem_winTree, mem_winE_neg c lo hi x j, coverClassAt_neg c W x j]

/-- **The reflection of the minimality of the window.**  If no non-zero translation of the walk of
`L` fits into `[lo,hi]`, then no non-zero translation of the reflected walk fits into the reflected
window `[-hi,-lo]`; the shift `k` corresponds to `-k`. -/
private theorem hone_neg (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool))
    (h : ∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor c 0 L,
      lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
        p.1.2 + c p.1.1 + k ≤ hi)) :
    ∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor (fun x => -c x) 0 L,
      -hi ≤ p.1.2 + k ∧ -hi ≤ p.1.2 + -c p.1.1 + k ∧ p.1.2 + k ≤ -lo ∧
        p.1.2 + -c p.1.1 + k ≤ -lo) := by
  intro k hk hforall
  refine h (-k) (neg_ne_zero.mpr hk) ?_
  intro q hq
  have hqmap : ((q.1.1, -q.1.2), q.2) ∈ decor (fun x : α => -c x) 0 L := by
    rw [show decor (fun x : α => -c x) 0 L
        = (decor c 0 L).map (fun p => ((p.1.1, -p.1.2), p.2)) from by
      rw [decor_neg, neg_zero]]
    exact List.mem_map_of_mem hq
  have hh := hforall _ hqmap
  obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
  simp only [] at hh1 hh2 hh3 hh4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## The window data containing the level `1` -/

theorem exists_winData_containing_one {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (c : α → ℤ) (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      Work.OROneRel.cohom c u = 1 ∧ Wt 0 = 1 ∧
      (∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      lo ≤ 1 ∧ 1 ≤ hi ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
            lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
              p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi) ∧
      (∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) := by
  classical
  obtain ⟨c, τ, lo, hi, Wt, hsurj, hcu, -, hW0, hcoh, hlt, hwinE, hone, htree, hcov, hlast⟩ :=
    exists_winWindowData u hu hn hbad
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hne : wordOf u ≠ [] := by
    intro hw
    exact hu1 (by rw [← mk_wordOf u, hw]; rfl)
  -- the walk of `u` starts at the level `0`, which therefore lies in the window
  have h0 : lo ≤ 0 ∧ 0 ≤ hi :=
    (band_of_winE_decor c lo hi (wordOf u) hne hwinE).zero
  by_cases hhi : 1 ≤ hi
  · -- the window already contains the level `1`
    exact ⟨c, lo, hi, Wt, hcu, hW0, hcoh, by omega, hhi, hwinE, hone, htree, hcov, hlast⟩
  · -- the window lies below the level `1`: reflect it in the level line
    push Not at hhi
    refine ⟨fun x : α => -c x, -hi, -lo, fun i => Wt (-i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the reflected weight still kills `u`
      rw [cohom_neg, hcu]; rfl
    · -- the reflected gauge starts at the identity
      show Wt (-(0 : ℤ)) = 1
      rw [neg_zero]; exact hW0
    · -- the reflected gauge has the prescribed levels
      intro i
      rw [cohom_neg, hcoh (-i)]
      simp
    · -- `-hi ≤ 1`
      omega
    · -- `1 ≤ -lo`
      omega
    · -- the walk of `u` lies in the reflected window
      intro p hp
      rw [show decor (fun x : α => -c x) 0 (wordOf u)
          = (decor c 0 (wordOf u)).map (fun p => ((p.1.1, -p.1.2), p.2)) from by
        rw [decor_neg, neg_zero]] at hp
      obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hp
      subst hqeq
      refine (mem_winE_neg c lo hi q.1.1 (-q.1.2)).mpr ?_
      simpa [coverEdge] using hwinE q hq
    · -- the minimality of the reflected window
      exact hone_neg c lo hi (wordOf u) hone
    · -- the gauge of the reflected window spans the reflected window
      intro i hi1 hi2 q hq
      rw [show decor (fun x : α => -c x) 0 (wordOf (Wt (-i)))
          = (decor c 0 (wordOf (Wt (-i)))).map (fun p => ((p.1.1, -p.1.2), p.2)) from by
        rw [decor_neg, neg_zero]] at hq
      obtain ⟨q', hq', hqeq⟩ := List.mem_map.mp hq
      subst hqeq
      have h1 : lo ≤ -i := by omega
      have h2 : -i ≤ hi := by omega
      have hq'' := htree (-i) h1 h2 q' hq'
      change (q'.1.1, -q'.1.2) ∈
        winTree (fun i => Wt (-i)) (fun x : α => -c x) (-hi) (-lo)
      rw [mem_winTree_neg c lo hi Wt q'.1.1 (-q'.1.2)]
      simpa [coverEdge] using hq''
    · -- every generator has a reflected window edge
      intro x
      obtain ⟨j, hj⟩ := hcov x
      exact ⟨-j, (mem_winE_neg c lo hi x (-j)).mpr (by simpa using hj)⟩
    · -- some traversal of the walk is a reflected tree edge
      obtain ⟨q, hq, hpt⟩ := hlast
      refine ⟨(fun p => ((p.1.1, -p.1.2), p.2)) q, ?_, ?_⟩
      · rw [show decor (fun x : α => -c x) 0 (wordOf u)
            = (decor c 0 (wordOf u)).map (fun p => ((p.1.1, -p.1.2), p.2)) from by
          rw [decor_neg, neg_zero]]
        exact List.mem_map_of_mem hq
      · change (q.1.1, -q.1.2) ∈
          winTree (fun i => Wt (-i)) (fun x : α => -c x) (-hi) (-lo)
        rw [mem_winTree_neg c lo hi Wt q.1.1 (-q.1.2)]
        simpa [coverEdge] using hpt

end Work.OROneRel.NC
