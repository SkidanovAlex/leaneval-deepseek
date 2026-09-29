-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Resample/chunksOfWordT.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.pbApplyDefs
import Submission.Work.Resample.PBChunk.buildFramePB
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.buildDefs
import Submission.Work.Resample.PBChunk.chunksProof
import Submission.Work.Resample.PBChunk.readBits_ev
import Submission.Work.Resample.PBChunk.buildCounterFrame
import Submission.Work.Resample.PBChunk.walkFrame
import Submission.Work.Resample.PBChunk.chunksArith
/-!
# `Work.Resample.ChunksOfWord`: the chunking word

`ChunksOfWord` (see `Submission/Work/Resample/pbApplyDefs.lean`) asks for a word that cuts the list
`ofList xs` below an integer `int m` into consecutive chunks of length `m` (`1 ≤ m`,
`m ∣ xs.length`).

The program used here is the chunksOf word of the Layout area
(`Submission/Work/Layout/chunksOfDefs.lean`):

* `readBitsProg` reads the bits of `int m` onto the scratch stack `sBits` (most significant first,
  above a `gMark` sentinel);
* `buildCounterProg` builds the unary counter `gPend^m ++ [gSent]` on `sM`;
* `walkProg` moves the elements of `ofList xs` onto the element stack `sT` (in reverse order);
* the `nil` terminator left by `walkProg` on stack 0 is dropped;
* `buildProg` rebuilds the chunk list `ofList (chunks.map ofList)` on stack 0, one chunk at a time;
* finally the `gSent` sentinel of `sT` is dropped and the counter on `sM` is drained.

`Work.Resample.PBChunk.mainProg` is *not* used: `fullProg` forgets to drop the `nil` terminator that
`walkProg` leaves on stack 0, which would leave stack 0 as `(ofList chunks).enc ++ nil :: A0`
instead of `(ofList chunks).enc ++ A0`; the version below inserts `.pop 0 rE` before `buildProg`.

The proof composes the raw phase lemmas of the Layout area (`readBits_ev`, `buildCounterFrame`,
`walkFrame`, `buildFramePB`, `drainTo_ev`) and converts the result into a `WordR` triple.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH
open Work.Layout

/-- Cost constant of the chunking word. -/
def CK : ℕ := 100000

/-- Body of the chunking word, after the integer `int m` has been read off stack 0. -/
def chunksBody : Cmd :=
  seqs [Work.Resample.PBChunk.buildCounterProg, Work.Resample.PBChunk.walkProg, .pop 0 Work.Resample.PBChunk.rE,
    Work.Resample.PBChunk.buildProg, .pop Work.Resample.PBChunk.sT Work.Resample.PBChunk.rE,
    Work.Resample.PBChunk.drainToProg Work.Resample.PBChunk.sM Work.Layout.gSent]

/-- The chunking word: read the bits of `int m`, then dispatch on whether the list is empty
(the empty branch only has to drop the bits from `sBits`). -/
def chunksMain : Cmd :=
  seqs [Work.Resample.PBChunk.readBitsProg, .peek 0 Work.Resample.PBChunk.rE,
    .ite Work.Resample.PBChunk.rE Glyph.cons chunksBody Work.Resample.PBChunk.emptyProg]

/-! ## Pure list and size facts -/

/-- The `elemOrder` of the consecutive `m`-chunks of `xs` is the reversal of `xs`. -/
theorem elemOrder_drop_take (m : ℕ) (xs : List Val) (hdvd : m ∣ xs.length) :
    elemOrder ((List.range (xs.length / m)).map fun i => (xs.drop (i * m)).take m) = xs.reverse := by
  rw [Work.Resample.PBChunk.elemOrder_range_map]
  congr 1
  simpa only [Work.Resample.PBChunk.chunkAt] using Work.Resample.PBChunk.flatMap_range_chunkAt_eq xs hdvd

/-- The element stack sequence delivered by `sT` for the consecutive chunks of `xs`. -/
theorem elemOrder_enc_drop_take (m : ℕ) (xs : List Val) (hdvd : m ∣ xs.length) :
    ((elemOrder ((List.range (xs.length / m)).map fun i => (xs.drop (i * m)).take m)).map
        Val.enc).flatten = ((xs.map Val.enc).reverse).flatten := by
  rw [elemOrder_drop_take m xs hdvd, List.map_reverse]

/-- Every consecutive `m`-chunk of `xs` has length `m`. -/
theorem drop_take_length {m : ℕ} (hm : 1 ≤ m) {xs : List Val} (hdvd : m ∣ xs.length) :
    ∀ c ∈ (List.range (xs.length / m)).map (fun i => (xs.drop (i * m)).take m), c.length = m := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' : i < xs.length / m := List.mem_range.mp hi
  simpa only [Work.Resample.PBChunk.chunkAt] using Work.Resample.PBChunk.chunk_length hm hdvd i hi'

/-- A nonempty list whose length is divisible by `m ≥ 1` has at least `m` elements. -/
theorem le_vsz_ofList_of_dvd {m : ℕ} (hm : 1 ≤ m) {xs : List Val} (hne : xs ≠ [])
    (hdvd : m ∣ xs.length) : m ≤ vsz (ofList xs) := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  exact le_trans (Nat.le_of_dvd hpos hdvd) (Work.Resample.PBChunk.length_le_vsz_ofList xs)

/-- The number of chunks is at most the size of the list. -/
theorem div_le_vsz_ofList (m : ℕ) (xs : List Val) : xs.length / m ≤ vsz (ofList xs) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · have h1 : xs.length / m ≤ (xs.length / m) * m := Nat.le_mul_of_pos_right _ h
    have h2 : (xs.length / m) * m ≤ xs.length := Nat.div_mul_le_self _ _
    have h3 := Work.Resample.PBChunk.length_le_vsz_ofList xs
    omega

/-- `List.map ofList` after another `List.map`, in the shape of the `ChunksOfWord` statement. -/
theorem ofList_map_map {α : Type} (l : List α) (f : α → List Val) :
    List.map ofList (List.map f l) = List.map (fun i => ofList (f i)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

/-! ## The raw evaluation of the chunking word -/

/-- The chunking word maps `int m :: ofList xs :: A` to `ofList chunks :: A`, restoring every
other stack. -/
theorem chunksMain_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {m : ℕ}
    {xs : List Val} {A : List Glyph} (hm : 1 ≤ m) (hdvd : m ∣ xs.length)
    (h0 : X 0 = (Val.int (m : ℤ)).enc ++ ((ofList xs).enc ++ A)) :
    ∃ s' n, Ev main chunksMain ⟨g, X⟩ s' n ∧
      n ≤ CK * (vsz (ofList xs) + (xs.length / m + 1) * isz (m : ℤ) + 1) ∧
      s'.stk 0 = (ofList (((List.range (xs.length / m)).map
        fun i => (xs.drop (i * m)).take m).map ofList)).enc ++ A ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, hev₁, hn₁, hs₁₀, hs₁b, hfr₁⟩ :=
    Work.Resample.PBChunk.readBits_ev (main := main) (g := g) (X := X) (m := m)
      (A := (ofList xs).enc ++ A) (B := X Work.Resample.PBChunk.sBits) h0 rfl
  rcases xs with _ | ⟨y, ys⟩
  · -- ## the list is empty: just drop the bits of `m` from `sBits`
    obtain ⟨s₂, hev₂, hs₂₀, hs₂r, hs₂f, -⟩ :=
      Work.Resample.PBChunk.step_peek (main := main) (k := 0) (r := Work.Resample.PBChunk.rE) (h := Glyph.nil) (L := A)
        (g := s₁.reg) (X := s₁.stk) (by rw [hs₁₀]; rfl)
    have hs₂b : s₂.stk Work.Resample.PBChunk.sBits = (Work.Resample.PBChunk.bitsG m.bits).reverse ++
        Work.Layout.gMark :: X Work.Resample.PBChunk.sBits := by
      rw [hs₂f Work.Resample.PBChunk.sBits (by decide), hs₁b]
    obtain ⟨s₃, n₃, hev₃, hn₃, hs₃b, hfr₃⟩ :=
      Work.Resample.PBChunk.drainTo_ev (main := main) (k := Work.Resample.PBChunk.sBits) (κ := Work.Layout.gMark)
        (G := (Work.Resample.PBChunk.bitsG m.bits).reverse) (B := X Work.Resample.PBChunk.sBits)
        (g := s₂.reg) (X := s₂.stk)
        (by rw [← Work.Resample.PBChunk.bitsG_reverse]; exact Work.Resample.PBChunk.gMark_notMem_bitsG m.bits.reverse)
        hs₂b
    have hite : Ev main (.ite Work.Resample.PBChunk.rE Glyph.cons chunksBody Work.Resample.PBChunk.emptyProg) s₂ s₃
        (n₃ + 1) := Ev.iteF (by rw [hs₂r]; decide) hev₃
    have hmain : Ev main chunksMain ⟨g, X⟩ s₃ (n₁ + (1 + (n₃ + 1))) := by
      unfold chunksMain
      have h₁ : Ev main (.seq (.peek 0 Work.Resample.PBChunk.rE)
          (.ite Work.Resample.PBChunk.rE Glyph.cons chunksBody Work.Resample.PBChunk.emptyProg)) s₁ s₃
          (1 + (n₃ + 1)) := Ev.seq' hev₂ hite (by omega)
      exact Ev.seq' hev₁ h₁ (by omega)
    refine ⟨s₃, n₁ + (1 + (n₃ + 1)), hmain, ?_, ?_, ?_⟩
    · -- cost
      have h3 : n₃ ≤ 6 * (m.bits.length + 1) + 4 := by
        refine le_trans hn₃ ?_
        rw [List.length_reverse, Work.Resample.PBChunk.bitsG_length]
      have hI : isz (m : ℤ) = m.bits.length + 2 := Work.Resample.PBChunk.isz_eq_bits_length m
      have hvs : vsz (ofList ([] : List Val)) = 1 := rfl
      have hz : (([] : List Val).length) / m = 0 := by simp
      rw [hvs, hz]
      simp only [CK]
      omega
    · -- stack 0
      rw [hfr₃ 0 (by decide), hs₂₀] <;> simp [ofList, Val.enc]
    · -- frame
      intro j hj
      by_cases hb : j = Work.Resample.PBChunk.sBits
      · rw [hb, hs₃b]
      · rw [hfr₃ j (by omega), hs₂f j (by omega), hfr₁ j hj hb]
  · -- ## the list is `y :: ys`
    have hs₁₀' : s₁.stk 0 = Glyph.cons :: (y.enc ++ (ofList ys).enc ++ A) := by
      rw [hs₁₀, Work.Resample.PBChunk.enc_ofList_cons, List.cons_append, List.append_assoc]
    obtain ⟨s₂, hev₂, hs₂₀, hs₂r, hs₂f, -⟩ :=
      Work.Resample.PBChunk.step_peek (main := main) (k := 0) (r := Work.Resample.PBChunk.rE) (h := Glyph.cons)
        (L := y.enc ++ (ofList ys).enc ++ A) (g := s₁.reg) (X := s₁.stk) hs₁₀'
    -- stack bookkeeping of the phases
    have hs₂b : s₂.stk Work.Resample.PBChunk.sBits = (Work.Resample.PBChunk.bitsG m.bits).reverse ++
        Work.Layout.gMark :: X Work.Resample.PBChunk.sBits := by
      rw [hs₂f Work.Resample.PBChunk.sBits (by decide), hs₁b]
    -- (a) build the unary counter on `sM`
    obtain ⟨s₃, n₃, hev₃, hn₃, hs₃M, hs₃b, hs₃T2, hfr₃⟩ :=
      Work.Resample.PBChunk.buildCounterFrame (main := main) (g := s₂.reg) (X := s₂.stk)
        (L := m.bits.reverse) (B6 := X Work.Resample.PBChunk.sBits) (M0 := X Work.Resample.PBChunk.sM)
        (by rw [hs₂b, ← Work.Resample.PBChunk.bitsG_reverse]) (by rw [hs₂f Work.Resample.PBChunk.sM (by decide),
          hfr₁ Work.Resample.PBChunk.sM (by decide) (by decide)])
    have hs₃₀ : s₃.stk 0 = Glyph.cons :: (y.enc ++ (ofList ys).enc ++ A) := by
      rw [hfr₃ 0 (by decide) (by decide) (by decide), hs₂₀]
    have hs₃T : s₃.stk Work.Resample.PBChunk.sT = X Work.Resample.PBChunk.sT := by
      rw [hfr₃ Work.Resample.PBChunk.sT (by decide) (by decide) (by decide),
        hs₂f Work.Resample.PBChunk.sT (by decide), hfr₁ Work.Resample.PBChunk.sT (by decide) (by decide)]
    have hs₃M' : s₃.stk Work.Resample.PBChunk.sM =
        List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: X Work.Resample.PBChunk.sM := by
      rw [hs₃M, Work.Resample.PBChunk.valBits_bits_reverse]
    have hs₃W : s₃.stk Work.Resample.PBChunk.sW = X Work.Resample.PBChunk.sW := by
      rw [hfr₃ Work.Resample.PBChunk.sW (by decide) (by decide) (by decide),
        hs₂f Work.Resample.PBChunk.sW (by decide), hfr₁ Work.Resample.PBChunk.sW (by decide) (by decide)]
    have hs₃B : s₃.stk Work.Resample.PBChunk.sB = X Work.Resample.PBChunk.sB := by
      rw [hfr₃ Work.Resample.PBChunk.sB (by decide) (by decide) (by decide),
        hs₂f Work.Resample.PBChunk.sB (by decide), hfr₁ Work.Resample.PBChunk.sB (by decide) (by decide)]
    have hs₃C : s₃.stk Work.Resample.PBChunk.sC = X Work.Resample.PBChunk.sC := by
      rw [hfr₃ Work.Resample.PBChunk.sC (by decide) (by decide) (by decide),
        hs₂f Work.Resample.PBChunk.sC (by decide), hfr₁ Work.Resample.PBChunk.sC (by decide) (by decide)]
    have hs₃T2' : s₃.stk Work.Resample.PBChunk.sT2 = X Work.Resample.PBChunk.sT2 := by
      rw [hs₃T2, hs₂f Work.Resample.PBChunk.sT2 (by decide),
        hfr₁ Work.Resample.PBChunk.sT2 (by decide) (by decide)]
    have hs₃b' : s₃.stk Work.Resample.PBChunk.sBits = X Work.Resample.PBChunk.sBits := by
      rw [hs₃b]
    -- (b) walk the elements onto `sT`
    obtain ⟨s₄, n₄, hev₄, hn₄, hs₄₀, hs₄T, hs₄B, hs₄C, hfr₄⟩ :=
      Work.Resample.PBChunk.walkFrame (main := main) (g := s₃.reg) (X := s₃.stk) (ys := y :: ys)
        (A := A) (T0 := X Work.Resample.PBChunk.sT) hs₃₀ hs₃T
    have hs₄M : s₄.stk Work.Resample.PBChunk.sM =
        List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: X Work.Resample.PBChunk.sM := by
      rw [hfr₄ Work.Resample.PBChunk.sM (by decide) (by decide) (by decide) (by decide), hs₃M']
    have hs₄W : s₄.stk Work.Resample.PBChunk.sW = X Work.Resample.PBChunk.sW := by
      rw [hfr₄ Work.Resample.PBChunk.sW (by decide) (by decide) (by decide) (by decide), hs₃W]
    have hs₄b : s₄.stk Work.Resample.PBChunk.sBits = X Work.Resample.PBChunk.sBits := by
      rw [hfr₄ Work.Resample.PBChunk.sBits (by decide) (by decide) (by decide) (by decide), hs₃b']
    have hs₄T2 : s₄.stk Work.Resample.PBChunk.sT2 = X Work.Resample.PBChunk.sT2 := by
      rw [hfr₄ Work.Resample.PBChunk.sT2 (by decide) (by decide) (by decide) (by decide), hs₃T2']
    -- (c) drop the `nil` terminator of the walked list
    obtain ⟨s₅, hev₅, hs₅₀, -, hs₅f, -⟩ :=
      Work.Resample.PBChunk.step_pop (main := main) (k := 0) (r := Work.Resample.PBChunk.rE) (h := Glyph.nil) (L := A)
        (g := s₄.reg) (X := s₄.stk) hs₄₀
    have hs₅T : s₅.stk Work.Resample.PBChunk.sT = ((y :: ys).map Val.enc).reverse.flatten ++
        Work.Layout.gSent :: X Work.Resample.PBChunk.sT := by
      rw [hs₅f Work.Resample.PBChunk.sT (by decide), hs₄T]
    -- (d) build the chunk list
    obtain ⟨s₆, n₆, hev₆, hn₆, hs₆₀, hs₆T, hs₆M, hs₆W, hs₆B, hs₆C, hs₆T2, hfr₆⟩ :=
      buildFramePB (main := main) (g := s₅.reg) (X := s₅.stk)
        (ch := (List.range ((y :: ys).length / m)).map fun i => ((y :: ys).drop (i * m)).take m)
        (m := m) (A0 := A) (T0 := X Work.Resample.PBChunk.sT) (M0 := X Work.Resample.PBChunk.sM)
        (W0 := X Work.Resample.PBChunk.sW) hm
        (drop_take_length hm hdvd)
        (by rw [hs₅T, elemOrder_enc_drop_take m (y :: ys) hdvd])
        (by rw [hs₅f Work.Resample.PBChunk.sM (by decide), hs₄M])
        (by rw [hs₅f Work.Resample.PBChunk.sW (by decide), hs₄W])
        (by rw [hs₅₀])
    -- (e) drop the `gSent` sentinel of `sT`
    obtain ⟨s₇, hev₇, hs₇T, -, hs₇f, -⟩ :=
      Work.Resample.PBChunk.step_pop (main := main) (k := Work.Resample.PBChunk.sT) (r := Work.Resample.PBChunk.rE)
        (h := Work.Layout.gSent) (L := X Work.Resample.PBChunk.sT) (g := s₆.reg) (X := s₆.stk) hs₆T
    -- (f) drain the unary counter
    obtain ⟨s₈, n₈, hev₈, hn₈, hs₈M, hfr₈⟩ :=
      Work.Resample.PBChunk.drainTo_ev (main := main) (k := Work.Resample.PBChunk.sM) (κ := Work.Layout.gSent)
        (G := List.replicate m Work.Layout.gPend) (B := X Work.Resample.PBChunk.sM)
        (g := s₇.reg) (X := s₇.stk) (Work.Resample.PBChunk.gSent_notMem_replicate m)
        (by rw [hs₇f Work.Resample.PBChunk.sM (by decide), hs₆M])
    -- composition
    have e78 : Ev main (.seq (.pop Work.Resample.PBChunk.sT Work.Resample.PBChunk.rE)
        (Work.Resample.PBChunk.drainToProg Work.Resample.PBChunk.sM Work.Layout.gSent)) ⟨s₆.reg, s₆.stk⟩ s₈
        (1 + n₈) := Ev.seq' hev₇ hev₈ (by omega)
    have e678 : Ev main (.seq Work.Resample.PBChunk.buildProg (.seq (.pop Work.Resample.PBChunk.sT Work.Resample.PBChunk.rE)
        (Work.Resample.PBChunk.drainToProg Work.Resample.PBChunk.sM Work.Layout.gSent))) ⟨s₅.reg, s₅.stk⟩ s₈
        (n₆ + (1 + n₈)) := Ev.seq' hev₆ e78 (by omega)
    have e5678 : Ev main (.seq (.pop 0 Work.Resample.PBChunk.rE) (.seq Work.Resample.PBChunk.buildProg
        (.seq (.pop Work.Resample.PBChunk.sT Work.Resample.PBChunk.rE)
          (Work.Resample.PBChunk.drainToProg Work.Resample.PBChunk.sM Work.Layout.gSent)))) ⟨s₄.reg, s₄.stk⟩ s₈
        (1 + (n₆ + (1 + n₈))) := Ev.seq' hev₅ e678 (by omega)
    have e45678 : Ev main (.seq Work.Resample.PBChunk.walkProg (.seq (.pop 0 Work.Resample.PBChunk.rE)
        (.seq Work.Resample.PBChunk.buildProg (.seq (.pop Work.Resample.PBChunk.sT Work.Resample.PBChunk.rE)
          (Work.Resample.PBChunk.drainToProg Work.Resample.PBChunk.sM Work.Layout.gSent))))) ⟨s₃.reg, s₃.stk⟩ s₈
        (n₄ + (1 + (n₆ + (1 + n₈)))) := Ev.seq' hev₄ e5678 (by omega)
    have hbody : Ev main chunksBody ⟨s₂.reg, s₂.stk⟩ s₈
        (n₃ + (n₄ + (1 + (n₆ + (1 + n₈))))) := by
      unfold chunksBody
      exact Ev.seq' hev₃ e45678 (by omega)
    have hite : Ev main (.ite Work.Resample.PBChunk.rE Glyph.cons chunksBody Work.Resample.PBChunk.emptyProg) s₂ s₈
        (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1) := Ev.iteT hs₂r hbody
    have hmain : Ev main chunksMain ⟨g, X⟩ s₈
        (n₁ + (1 + (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1))) := by
      unfold chunksMain
      have h₁ : Ev main (.seq (.peek 0 Work.Resample.PBChunk.rE)
          (.ite Work.Resample.PBChunk.rE Glyph.cons chunksBody Work.Resample.PBChunk.emptyProg)) s₁ s₈
          (1 + (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1)) := Ev.seq' hev₂ hite (by omega)
      exact Ev.seq' hev₁ h₁ (by omega)
    refine ⟨s₈, _, hmain, ?_, ?_, ?_⟩
    · -- cost
      have hQ : (y :: ys).length / m ≤ vsz (ofList (y :: ys)) := div_le_vsz_ofList m (y :: ys)
      have hMle : m ≤ vsz (ofList (y :: ys)) := le_vsz_ofList_of_dvd hm (by simp) hdvd
      have hI : isz (m : ℤ) = m.bits.length + 2 := Work.Resample.PBChunk.isz_eq_bits_length m
      have h1 : 1 ≤ isz (m : ℤ) := by omega
      have h6 : vsz (ofList (((List.range ((y :: ys).length / m)).map
          fun i => ((y :: ys).drop (i * m)).take m).map ofList))
          = vsz (ofList (y :: ys)) + 2 * ((y :: ys).length / m) := by
        simpa only [Work.Resample.PBChunk.chunkAt] using Work.Resample.PBChunk.vsz_chunks (y :: ys) m hm hdvd
      have hchs : (((List.range ((y :: ys).length / m)).map
          fun i => ((y :: ys).drop (i * m)).take m).length) = (y :: ys).length / m := by simp
      have h3 : n₃ ≤ 100 * (m + m.bits.length + 1) := by
        refine le_trans hn₃ ?_
        rw [Work.Resample.PBChunk.valBits_bits_reverse, List.length_reverse]
      have h6' : n₆ ≤ 100 * (vsz (ofList (y :: ys)) + 3 * ((y :: ys).length / m) + 1) := by
        rw [h6, hchs] at hn₆
        omega
      have h8 : n₈ ≤ 6 * (m + 1) + 4 := by
        refine le_trans hn₈ ?_
        simp
      have htarget : CK * (vsz (ofList (y :: ys)) + ((y :: ys).length / m + 1) * isz (m : ℤ) + 1)
          = CK * vsz (ofList (y :: ys)) + CK * (((y :: ys).length / m) * isz (m : ℤ))
            + CK * isz (m : ℤ) + CK := by
        ring
      rw [htarget]
      simp only [CK]
      have hQI : (y :: ys).length / m ≤ ((y :: ys).length / m) * isz (m : ℤ) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h300 : 300 * ((y :: ys).length / m)
          ≤ 100000 * (((y :: ys).length / m) * isz (m : ℤ)) :=
        le_trans (Nat.mul_le_mul_left 300 hQI) (Nat.mul_le_mul_right _ (by norm_num))
      omega
    · -- stack 0
      rw [hfr₈ 0 (by decide), hs₇f 0 (by decide), hs₆₀]
    · -- frame
      intro j hj
      by_cases hM : j = Work.Resample.PBChunk.sM
      · rw [hM, hs₈M]
      · rw [hfr₈ j hM]
        by_cases hT : j = Work.Resample.PBChunk.sT
        · rw [hT, hs₇T]
        · rw [hs₇f j hT]
          by_cases hB : j = Work.Resample.PBChunk.sB
          · rw [hB, hs₆B, hs₅f Work.Resample.PBChunk.sB (by decide), hs₄B, hs₃B]
          · by_cases hC : j = Work.Resample.PBChunk.sC
            · rw [hC, hs₆C, hs₅f Work.Resample.PBChunk.sC (by decide), hs₄C, hs₃C]
            · by_cases hW : j = Work.Resample.PBChunk.sW
              · rw [hW, hs₆W]
              · rw [hfr₆ j hj hT hM hW hB hC, hs₅f j hj]
                by_cases hT2 : j = Work.Resample.PBChunk.sT2
                · rw [hT2, hs₄T2]
                · by_cases hb : j = Work.Resample.PBChunk.sBits
                  · rw [hb, hs₄b]
                  · rw [hfr₄ j hj hT hB hC, hfr₃ j hM hb hT2, hs₂f j hj, hfr₁ j hj hb]

end Work.Resample.PBChunk
namespace Work.Resample.PBChunk
open HvdH
open Work.Layout

/-- **`Work.Resample.ChunksOfWord`**: the chunking word. -/
theorem chunksOfWordPB : Work.Resample.ChunksOfWord := by
  refine ⟨chunksMain, CK, ?_⟩
  intro main m xs hm hdvd
  intro vs hpre s R hs0
  obtain ⟨rest, hvs⟩ := hpre
  subst hvs
  have h0 : s.stk 0 = (Val.int (m : ℤ)).enc ++ ((ofList xs).enc ++ (encs rest ++ R)) := by
    rw [hs0]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  obtain ⟨s', n, hev, hn, hs'0, hfr⟩ :=
    chunksMain_ev (main := main) (g := s.reg) (X := s.stk) (m := m) (xs := xs)
      (A := encs rest ++ R) hm hdvd h0
  obtain ⟨n₀, hevE, hn₀⟩ := hev
  refine ⟨ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m))
      :: rest, s', n₀, ⟨rest, rfl, rfl⟩, hevE, le_trans hn₀ hn, ?_, hfr⟩
  rw [hs'0, ofList_map_map]
  simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]

end Work.Resample.PBChunk