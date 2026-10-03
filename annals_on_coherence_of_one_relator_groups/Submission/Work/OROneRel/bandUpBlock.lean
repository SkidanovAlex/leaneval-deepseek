import Mathlib
import Submission.Work.OROneRel.bandUpBlockDict
import Submission.Work.OROneRel.band_halves_inter
import Submission.Work.OROneRel.tlWin_deckClimb
import Submission.Work.OROneRel.exists_short_deck_with_deck_mem
import Submission.Work.OROneRel.tlWin_succ_of_walk_le
import Submission.Work.OROneRel.hnnConjMap_injective_tlWin_bottom
import Submission.Work.OROneRel.tlWin_pq_eq_tlH
import Submission.Work.OROneRel.winE_mono
import Submission.Work.OROneRel.bandUpBlockHk_of_hnnConjMap_injective

/-!
# The up-block lemma of the two-letter band (the corrected, two-guard form)

## The target

With `tlPle c = ⟨tlHk k : k ≤ c⟩` the target `Work.OROneRel.bandUpBlock` says: for a `±1` level walk
`t : Fin n → ℤ` with `t 0 = t (n-1) = b` and `t i ≥ b`, letters `y i ∈ tlHk (t i)`, the *peak* guard
`y i ∉ tlAk (t i - 1)` (when the level before and after `i` are both `t i - 1`) and the *valley*
guard `y i ∉ tlAk (t i)` (both neighbours one level up), the product `∏ y i` is **not** in
`tlPle (b-1)`.

## The `(INT)` squeeze (proved here, without any unfinished input)

`Work.OROneRel.band_halves_inter` (**INT**: `tlPle c ⊓ tlPge (c+1) = tlAk c`, proved in this
workspace) gives immediately:

* `prod_mem_tlPge_of_levels`: a product of letters at levels `≥ b` lies in `tlPge b`;
* `prod_mem_tlHk_of_mem_tlPle_sub_one`: **if it also lies in `tlPle (b-1)`, then it lies in the band
  vertex `tlHk b`** — because `tlPle (b-1) ⊓ tlPge b = tlAk (b-1) ⊆ tlHk b`.

Hence the target is *equivalent*, given `(INT)`, both to the strictly stronger statement

> **(♠)** `Work.OROneRel.bandUpBlockHk`: under the same hypotheses with `n ≥ 2`, `∏ y i ∉ tlHk b`.

(`(♠) ⟹ target`: if the target's conclusion failed then, by the two lemmas above, `∏ y ∈ tlHk b`;
the case `n = 1` is the base case `singleLetter_not_mem_tlPle_band` proved below from `(INT)`.)
and — by `(INT)` and the dictionary of `Submission/Work/OROneRel/bandUpBlockDict.lean` — to the
"pinch-free" statement

> `∏ y ∉ tlPle (b-1)  ⟺  w ∉ hnnEdgeA tlH τ`,  `w = h₀ τ^{ε₁} h₁ ⋯ h_{n-1}`,

where `h i = τ^(-t i)·y i·τ^(t i) ∈ tlH` and `ε i = t i - t (i-1)` (the letters of the product
telescope as in `Work.OROneRel.prod_conj_telescope`).

## The crux is available: the target is *proved* here

The crux of the two-letter band,

  `Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop))`,

is now a *theorem* — obtained through the **short-deck route** that the fleet completed after the
older statement `Work.OROneRel.band_hnnConjMap_injective` (`Submission/Work/OROneRel/
band_hnnConjMap_injective.lean`, still an unfinished stub) was written:

* `exists_short_deck_with_deck_mem`: there is `σ` of weight `1` whose walk lies in the *short* window
  `[0, p+q-1]` and with `tlLowTau * σ⁻¹ ∈ tlWin p q (p*q)` (a *walk* statement: it never inspects the
  opaque `tlLowTau = (twoLetterLowTauBound …).choose` beyond its interface);
* `tlWin_succ_of_walk_le`: for such a `σ` the window climb
  `tlWin (m+1) = tlWin m ⊔ σ·tlWin m·σ⁻¹` holds on `[p+q-1, p*q]` (for the opaque `tlLowTau` itself
  this recursion is *false*, so the deck change is essential: `NOTES_tlWin_succ_lemma.md`);
* `hnnConjMap_injective_tlWin_bottom`: the bottom window `[0, p+q-1]` is a cycle, so its HNN
  extension is two-generated, hence injective;
* `tlWin_pq_eq_tlH`: `tlWin p q (p*q) = tlH p q Wt`;
* `band_hnnConjMap_injective_of_shortDeck`: the climb plus the deck change give the crux.

`tlH_hnnConjMap_injective` below re-derives the crux from those five inputs, in this file.

The chain `crux ⟹ (♠) ⟹ target` is:

* **(♠) from the crux**: `Work.OROneRel.bandUpBlockHk_of_hnnConjMap_injective`
  (`Submission/Work/OROneRel/bandUpBlockHk_of_hnnConjMap_injective.lean`, proved), wrapped here as
  `bandUpBlockHk_of_crux`.  It transports the walk to the HNN word
  `h 0 * τ^{δ 1} * h 1 * ⋯ * h (n-1)` of `Fin (n-1)` letters
  (`h j = τ^{-t j} y j τ^{t j}` for `j ≤ n-2`, the *packing trick*: this way no guard is needed at
  the last letter), shows it is `NoPinch` (the two guards are exactly the no-pinch conditions —
  `not_mem_hnnEdgeA_of_not_mem_tlAk_sub_one`, `not_mem_hnnEdgeB_of_not_mem_tlAk` of
  `bandUpBlockDict`), and that its product is `τ^{-b} (∏ y) τ^{b} · (h (n-1))⁻¹ ∈ tlH` whenever
  `∏ y ∈ tlHk b`; Britton (`Work.OROneRel.britton_hnnConjMap_injective`) then forces the list to be
  empty, contradicting `n ≥ 2`.
* **the target from (♠)**: `bandUpBlock_of_hk` below (the `(INT)` squeeze plus the `n = 1` base case).

## The import obstruction, and the `BubCrux` copy set

The two halves of the two-letter band development are **mutually exclusive in one Lean
environment**, because of a *single* duplicated declaration name: `Work.OROneRel.mem_tlHk_iff` is
declared both in `Submission/Work/OROneRel/tlBandDescent.lean` (the "descent" half, which is where
`blkPrev`/`blkNext` — the indices of the statement above — live) and in
`Submission/Work/OROneRel/band_hnnConjMap_injective.lean` (the "climb" half, which is where `tlWin`
and the short-deck chain live).  Lean refuses to import both, and no file can contain a proof of
`bandUpBlock` (whose *statement* needs `blkPrev` and whose *proof* needs the crux) until one of the
two copies is renamed or one of the two original files is de-duplicated.

This file resolves the obstruction without touching any other agent's file: the modules of the
short-deck chain (22 files, including a copy of `band_hnnConjMap_injective` with the clashing lemma
renamed to `mem_tlHk_iff_bub` and the two unfinished stub theorems dropped) are copied verbatim into
`Submission/Work/BubCrux/`, and this file imports the copies.  Consequently

* `bandUpBlock` is stated exactly as requested (with `tlBandDescent`'s `blkPrev`/`blkNext`, since
  `bandUpBlockDict` imports `upBlockDefs`), and it is proved with no unfinished input;
* and any file that can import `tlBandDescent` (in particular
  `band_cosetGraph_isTree.lean` and the other descent files) can import this module too — the copies
  declare only names of the climb half, none of which the descent half declares.

**Recommended de-duplication.**  The copy set exists only because of the duplicate `mem_tlHk_iff`.
If the owner of `tlBandDescent.lean` (or of `band_hnnConjMap_injective.lean`) renames their copy
(the consumers of each are inside their own half), then `Submission/Work/BubCrux/` can be deleted
and the five `import Submission.Work.BubCrux.*` lines above pointed back at
`Submission.Work.OROneRel.*`.
-/

namespace Work.OROneRel

universe u

/-! ## Elementary subgroup bookkeeping -/

/-- An element of `tlHk k` with `k ≤ c` lies in the lower half at level `c`. -/
theorem mem_tlPle_of_mem_tlHk' (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) {c k : ℤ} (h : k ≤ c) {x : FreeGroup (Fin 2)}
    (hx : x ∈ tlHk p q hp hq hcop Wt k) : x ∈ tlPle p q hp hq hcop Wt c :=
  tlHk_le_tlPle p q hp hq hcop Wt (k := k) (c := c) h hx

/-- An element of `tlHk k` with `c ≤ k` lies in the upper half at level `c`. -/
theorem mem_tlPge_of_mem_tlHk' (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) {c k : ℤ} (h : c ≤ k) {x : FreeGroup (Fin 2)}
    (hx : x ∈ tlHk p q hp hq hcop Wt k) : x ∈ tlPge p q hp hq hcop Wt c :=
  tlHk_le_tlPge p q hp hq hcop Wt (k := k) (c := c) h hx

/-- A product of a `Fin`-indexed family lying in a subgroup lies in the subgroup. -/
theorem prod_ofFn_mem' {G : Type*} [Group G] {H : Subgroup G} {n : ℕ} {f : Fin n → G}
    (h : ∀ i, f i ∈ H) : (List.ofFn f).prod ∈ H :=
  Subgroup.list_prod_mem H (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact h i)

/-! ## The `(INT)` squeeze -/

/-- **A product of letters at levels `≥ b` lies in the upper half at level `b`.** -/
theorem prod_mem_tlPge_of_levels (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) {b : ℤ} {n : ℕ} {t : Fin n → ℤ} {y : Fin n → FreeGroup (Fin 2)}
    (hge : ∀ i, b ≤ t i) (hy : ∀ i, y i ∈ tlHk p q hp hq hcop Wt (t i)) :
    (List.ofFn y).prod ∈ tlPge p q hp hq hcop Wt b :=
  prod_ofFn_mem' (fun i => mem_tlPge_of_mem_tlHk' p q hp hq hcop Wt (hge i) (hy i))

/-- **The `(INT)` squeeze.**  If the product of a family of letters at levels `≥ b` lies in the
lower half `tlPle (b-1)`, then it lies in the *band vertex at level `b`*.

This is `(INT)` (`Work.OROneRel.band_halves_inter`) at `c = b-1`:
`tlPle (b-1) ⊓ tlPge b = tlAk (b-1) = tlHk (b-1) ⊓ tlHk b ⊆ tlHk b`. -/
theorem prod_mem_tlHk_of_mem_tlPle_sub_one (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    {b : ℤ} {n : ℕ} {t : Fin n → ℤ} {y : Fin n → FreeGroup (Fin 2)}
    (hge : ∀ i, b ≤ t i) (hy : ∀ i, y i ∈ tlHk p q hp hq hcop Wt (t i))
    (hmem : (List.ofFn y).prod ∈ tlPle p q hp hq hcop Wt (b - 1)) :
    (List.ofFn y).prod ∈ tlHk p q hp hq hcop Wt b := by
  have hge' : (List.ofFn y).prod ∈ tlPge p q hp hq hcop Wt b :=
    prod_mem_tlPge_of_levels p q hp hq hcop Wt hge hy
  have hINT := band_halves_inter p q hp hq hcop Wt hW0 hcoh hwin htree (b - 1)
  have hgate : (List.ofFn y).prod ∈ tlAk p q hp hq hcop Wt (b - 1) := by
    rw [← hINT]
    exact ⟨hmem, by rwa [show b - 1 + 1 = b from by ring]⟩
  have h := tlAk_le_tlHk_right p q hp hq hcop Wt (b - 1) hgate
  rwa [show b - 1 + 1 = b from by ring] at h

/-! ## The base case `n = 1` -/

/-- **The base case.**  A single letter at level `b` outside the gate `tlAk (b-1)` is outside
`tlPle (b-1)`.  This is `(INT)` at `c = b-1` alone. -/
theorem singleLetter_not_mem_tlPle_band (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (b : ℤ) (y : FreeGroup (Fin 2)) (hy : y ∈ tlHk p q hp hq hcop Wt b)
    (hpeak : y ∉ tlAk p q hp hq hcop Wt (b - 1)) :
    y ∉ tlPle p q hp hq hcop Wt (b - 1) := by
  intro hmem
  have hge : y ∈ tlPge p q hp hq hcop Wt b :=
    mem_tlPge_of_mem_tlHk' p q hp hq hcop Wt le_rfl hy
  have hINT := band_halves_inter p q hp hq hcop Wt hW0 hcoh hwin htree (b - 1)
  refine hpeak ?_
  rw [← hINT]
  exact ⟨hmem, by rwa [show b - 1 + 1 = b from by ring]⟩

/-! ## The target, reduced to `(♠)` -/

/-- **The reduction.**  Given the band-vertex form `(♠)` of the up-block lemma `(hHK)`, the target
`bandUpBlock` follows: if the product lay in `tlPle (b-1)` then, by the `(INT)` squeeze, it would lie
in `tlHk b`, contradicting `(♠)`; the case `n = 1` is the base case `singleLetter_not_mem_tlPle_band`
proved above from `(INT)`. -/
theorem bandUpBlock_of_hk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hHK : ∀ (b : ℤ) {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2)),
      t ⟨0, by omega⟩ = b → t ⟨n - 1, by omega⟩ = b → (∀ i, b ≤ t i) →
      (∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
        t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1) →
      (∀ i, y i ∈ Work.OROneRel.tlHk p q hp hq hcop Wt (t i)) →
      (∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i - 1 →
        Work.OROneRel.blkNext b t i = t i - 1 →
        y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i - 1)) →
      (∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i + 1 →
        Work.OROneRel.blkNext b t i = t i + 1 →
        y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i)) →
      (List.ofFn y).prod ∉ Work.OROneRel.tlHk p q hp hq hcop Wt b)
    (b : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2))
    (hbase : t ⟨0, hn⟩ = b) (hlast : t ⟨n - 1, by omega⟩ = b)
    (hge : ∀ i, b ≤ t i)
    (hstep : ∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
      t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1)
    (hy : ∀ i, y i ∈ Work.OROneRel.tlHk p q hp hq hcop Wt (t i))
    (hpeak : ∀ i : Fin n, Work.OROneRel.blkPrev b hn t i = t i - 1 →
      Work.OROneRel.blkNext b t i = t i - 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i - 1))
    (hvalley : ∀ i : Fin n, Work.OROneRel.blkPrev b hn t i = t i + 1 →
      Work.OROneRel.blkNext b t i = t i + 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i)) :
    (List.ofFn y).prod ∉ Work.OROneRel.tlPle p q hp hq hcop Wt (b - 1) := by
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · -- ## the base case `n = 1`
    subst hn1
    have hprod : (List.ofFn y).prod = y ⟨0, hn⟩ := by
      rw [List.ofFn_succ (n := 0)]
      simp
    rw [hprod]
    refine singleLetter_not_mem_tlPle_band p q hp hq hcop Wt hW0 hcoh hwin htree b _ ?_ ?_
    · rw [← hbase]
      exact hy ⟨0, hn⟩
    · intro hmem
      have h1 : Work.OROneRel.blkPrev b hn t ⟨0, hn⟩ = t ⟨0, hn⟩ - 1 := by
        rw [Work.OROneRel.blkPrev_zero, hbase]
      have h2 : Work.OROneRel.blkNext b t ⟨0, hn⟩ = t ⟨0, hn⟩ - 1 := by
        rw [Work.OROneRel.blkNext, hbase]
        simp
      have h3 := hpeak ⟨0, hn⟩ h1 h2
      rw [hbase] at h3
      exact h3 hmem
  · -- ## the inductive case `n ≥ 2`: reduce to `(♠)` via the `(INT)` squeeze
    intro hmem
    have hk := prod_mem_tlHk_of_mem_tlPle_sub_one p q hp hq hcop Wt hW0 hcoh hwin htree hge hy hmem
    exact hHK b (by omega) t y hbase hlast hge hstep hy
      (fun i h1 h2 => hpeak i h1 h2) (fun i h1 h2 => hvalley i h1 h2) hk

/-! ## The crux of the two-letter band, by the short-deck route -/

/-- **The `F₂`-level crux of the two-letter band.**  The comparison map of the pair
`(tlH p q Wt, tlLowTau p q)` is injective.

This is the statement that the older file `Submission/Work/OROneRel/band_hnnConjMap_injective.lean`
still carries as an unfinished target; it is proved here from the completed short-deck route (in the
fork-free copies of `Submission/Work/BubCrux/`, see the module docstring), so that nothing in this
file depends on that unfinished target:

* `exists_short_deck_with_deck_mem` provides `σ` of weight one whose walk lies in the short window
  `[0, p+q-1]` and with `tlLowTau * σ⁻¹ ∈ tlWin p q (p*q)`;
* `tlWin_succ_of_walk_le` gives the climb `tlWin (m+1) = tlWin m ⊔ σ·tlWin m·σ⁻¹` for
  `p+q-1 ≤ m`, `m+1 ≤ p*q` (from `σ`'s walk, transported into `winE 0 m`);
* `hnnConjMap_injective_tlWin_bottom` is the (cyclic) bottom case;
* `band_hnnConjMap_injective_of_shortDeck` assembles them, using the deck change
  `hnnConjMap_injective_iff_mul_left` to replace `tlLowTau` by `σ`. -/
theorem tlH_hnnConjMap_injective (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)) := by
  classical
  obtain ⟨σ, hσcoh, hσwalk, hdeck⟩ := exists_short_deck_with_deck_mem p q hp hq hcop
  refine band_hnnConjMap_injective_of_shortDeck p q hp hq (Wt := Wt) (σ := σ) ?_ ?_ hdeck ?_
  · -- the climb, with the walk hypothesis at every window from `p+q-1` up to `p*q`
    intro m hm1 hm2
    refine tlWin_succ_of_walk_le p q hp hq hcop hm1 hm2 hσcoh ?_
    intro e he
    exact winE_mono (tlW p q) le_rfl hm1 (hσwalk e he)
  · exact hnnConjMap_injective_tlWin_bottom p q hp hq hcop hσcoh
  · exact tlWin_pq_eq_tlH p q hp hq hcop Wt hW0 hcoh hwin htree

/-! ## `(♠)` from the crux, with the injectivity hypothesis supplied explicitly -/

/-- The up-block lemma in the band-vertex form `(♠)`, with the crux hypothesis (injectivity of the
comparison map of the pair `(tlH, tlLowTau)`) passed as an explicit argument.  This is
`Work.OROneRel.bandUpBlockHk_of_hnnConjMap_injective` with its hypothesis front-loaded, so that it
can be fed to `bandUpBlock_of_hk` by partial application. -/
theorem bandUpBlockHk_of_crux (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hInj : Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)))
    (b : ℤ) {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2))
    (hbase : t ⟨0, by omega⟩ = b) (hlast : t ⟨n - 1, by omega⟩ = b)
    (hge : ∀ i, b ≤ t i)
    (hstep : ∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
      t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1)
    (hy : ∀ i, y i ∈ Work.OROneRel.tlHk p q hp hq hcop Wt (t i))
    (hpeak : ∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i - 1 →
      Work.OROneRel.blkNext b t i = t i - 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i - 1))
    (hvalley : ∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i + 1 →
      Work.OROneRel.blkNext b t i = t i + 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i)) :
    (List.ofFn y).prod ∉ Work.OROneRel.tlHk p q hp hq hcop Wt b :=
  bandUpBlockHk_of_hnnConjMap_injective p q hp hq hcop Wt hW0 hcoh hwin htree hInj
    b hn t y hbase hlast hge hstep hy hpeak hvalley

/-! ## The target -/

theorem bandUpBlock (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (b : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2))
    (hbase : t ⟨0, hn⟩ = b) (hlast : t ⟨n - 1, by omega⟩ = b)
    (hge : ∀ i, b ≤ t i)
    (hstep : ∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
      t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1)
    (hy : ∀ i, y i ∈ Work.OROneRel.tlHk p q hp hq hcop Wt (t i))
    (hpeak : ∀ i : Fin n, Work.OROneRel.blkPrev b hn t i = t i - 1 →
      Work.OROneRel.blkNext b t i = t i - 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i - 1))
    (hvalley : ∀ i : Fin n, Work.OROneRel.blkPrev b hn t i = t i + 1 →
      Work.OROneRel.blkNext b t i = t i + 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i)) :
    (List.ofFn y).prod ∉ Work.OROneRel.tlPle p q hp hq hcop Wt (b - 1) :=
  bandUpBlock_of_hk p q hp hq hcop Wt hW0 hcoh hwin htree
    (bandUpBlockHk_of_crux p q hp hq hcop Wt hW0 hcoh hwin htree
      (tlH_hnnConjMap_injective p q hp hq hcop Wt hW0 hcoh hwin htree))
    b hn t y hbase hlast hge hstep hy hpeak hvalley

end Work.OROneRel
