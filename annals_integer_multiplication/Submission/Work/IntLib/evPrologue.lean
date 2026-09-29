import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.urRebuildK32
import Submission.Work.Layout.Base
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.evMainEvStkEq

/-!
# `IntLib` / `evPrologue`: the setup phase of the `evalPoly` word

`evPrologue` is the *prologue* of the `evalPoly` word of Harvey–van der Hoeven §2.1: given the
public `evStk` conventions, it produces a program which, from a state whose stack 0 carries the
digit chain `intList hs` followed by the height `int b` and the caller's data `Y 0`, reaches the
canonical initial state `⟨·, evStk hs b 0 [] [] Y⟩` of the main loop (`evMainLoop`), keeping every
other stack at `Y`.

The word is assembled from the two given gadgets `chainProg` (which peels the whole chain off
stack 0, reversing it onto `aL`) and `readProg` (which peels `int b` off stack 0, reversing it onto
`aR`), together with the library gadgets `UR.urProg` (binary-to-unary rebuild of `b` on `aCB`) and
`Shift.{clearRgn, clearAll, drain}`.  The constant `200` is deliberately generous: every stage of
the prologue is linear in `pbT hs b = Σ|h| + len·(b+2) + isz b + 100`, so the whole cost fits
`200·(KCM+KR+1)·pbT hs b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Preliminary material -/

/-- The flag register of the `Shift` region procedures (distinct from `rX`). -/
def rFl : Reg := (2 : Fin 16)

theorem rFl_ne_rX : rFl ≠ rX := by decide

/-- The nine stacks whose frame markers the prologue pushes. -/
def evLs : List Stk := [aR, aB, aCB, aL, aW, aO, aA, a2, aCW]

/-- Membership test in `evLs` in the form used below. -/
theorem notMem_evLs {k : Stk} (h1 : k ≠ aR) (h2 : k ≠ aB) (h3 : k ≠ aCB) (h4 : k ≠ aL)
    (h5 : k ≠ aW) (h6 : k ≠ aO) (h7 : k ≠ aA) (h8 : k ≠ a2) (h9 : k ≠ aCW) : k ∉ evLs := by
  intro hmem
  have h := hmem
  dsimp only [evLs] at h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 rfl
  · exact h2 rfl
  · exact h3 rfl
  · exact h4 rfl
  · exact h5 rfl
  · exact h6 rfl
  · exact h7 rfl
  · exact h8 rfl
  · exact h9 rfl

theorem upd_aO_apply {X : Stk → List Glyph} {v : List Glyph} {k : Stk} (hk : k ≠ aO) :
    (Function.update X aO v) k = X k := Function.update_of_ne hk v X

theorem upd_aCW_apply {X : Stk → List Glyph} {v : List Glyph} {k : Stk} (hk : k ≠ aCW) :
    (Function.update X aCW v) k = X k := Function.update_of_ne hk v X

/-- `.set r c` followed by `.push k r`: push the glyph `c` on stack `k`. -/
def spPush (r : Reg) (c : Glyph) (k : Stk) : Cmd := seqs [.set r c, .push k r]

theorem spPush_ev (main : Cmd) (r : Reg) (c : Glyph) (k : Stk) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    ∃ g', Ev main (spPush r c k) ⟨g, X⟩ ⟨g', Function.update X k (c :: X k)⟩ 2 := by
  have h1 : Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 := ev_set' main r c g X
  have h2 : Ev main (.push k r) ⟨Function.update g r c, X⟩
      ⟨Function.update g r c, Function.update X k (c :: X k)⟩ 1 := by
    simpa using ev_push' main k r (Function.update g r c) X
  refine ⟨Function.update g r c, ?_⟩
  show Ev main (seqs [.set r c, .push k r]) ⟨g, X⟩
    ⟨Function.update g r c, Function.update X k (c :: X k)⟩ 2
  exact Ev.seq' h1 h2 (by omega)

/-- Push the frame marker of every stack of `L` onto that stack. -/
def markAllX : List Stk → (Stk → List Glyph) → Stk → List Glyph
  | [], X => X
  | k :: L, X => markAllX L (Function.update X k (Shift.gmk k :: X k))

theorem markAllX_notMem : ∀ (L : List Stk) (X : Stk → List Glyph) (j : Stk),
    j ∉ L → markAllX L X j = X j := by
  intro L
  induction L with
  | nil => intro X j _; rfl
  | cons k L ih =>
      intro X j hj
      show markAllX L (Function.update X k (Shift.gmk k :: X k)) j = X j
      rw [ih (Function.update X k (Shift.gmk k :: X k)) j
        (fun h => hj (List.mem_cons_of_mem k h))]
      exact Function.update_of_ne
        (fun h : j = k => hj (by rw [← h]; exact List.mem_cons_self ..)) _ _

theorem markAllX_mem : ∀ (L : List Stk) (X : Stk → List Glyph) (j : Stk), L.Nodup → j ∈ L →
    markAllX L X j = Shift.gmk j :: X j := by
  intro L
  induction L with
  | nil => intro X j _ hj; exact (List.not_mem_nil hj).elim
  | cons k L ih =>
      intro X j hnd hj
      rcases List.mem_cons.mp hj with hjk | hj'
      · rw [hjk]
        show markAllX L (Function.update X k (Shift.gmk k :: X k)) k = Shift.gmk k :: X k
        rw [markAllX_notMem L (Function.update X k (Shift.gmk k :: X k)) k
            (List.nodup_cons.mp hnd).1,
          Function.update_self]
      · show markAllX L (Function.update X k (Shift.gmk k :: X k)) j = _
        rw [ih (Function.update X k (Shift.gmk k :: X k)) j (List.nodup_cons.mp hnd).2 hj']
        congr 1
        exact Function.update_of_ne
          (fun h : j = k => (List.nodup_cons.mp hnd).1 (by rw [← h]; exact hj')) _ _

/-- The marker-pushing phase: every stack of `L` gets its marker `gmk k` pushed on top. -/
theorem keysEv (main : Cmd) (r : Reg) (L : List Stk) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ g', Ev main (seqs (L.map (fun k => spPush r (Shift.gmk k) k))) ⟨g, X⟩ ⟨g', markAllX L X⟩
      (2 * L.length + 1) := by
  induction L generalizing g X with
  | nil => exact ⟨g, ev_skip main ⟨g, X⟩⟩
  | cons k L ih =>
      obtain ⟨g1, h1⟩ := spPush_ev main r (Shift.gmk k) k g X
      obtain ⟨g2, h2⟩ := ih g1 (Function.update X k (Shift.gmk k :: X k))
      refine ⟨g2, ?_⟩
      have h := Ev.seqs_cons (cs := L.map (fun k => spPush r (Shift.gmk k) k)) h1 h2
      have hcost : 2 + (2 * L.length + 1) ≤ 2 * (k :: L).length + 1 := by
        simp only [List.length_cons]; omega
      exact h.mono hcost

/-- Reversal of the canonical encoding of `int N` — see `enc_int_eq`. -/
theorem enc_int_eq (N : ℕ) :
    Val.enc (.int (N : ℤ)) = Glyph.pos :: (N.bits.map Glyph.bit ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int]
  have hsign : (if (N : ℤ) < 0 then Glyph.neg else Glyph.pos) = Glyph.pos := by
    have h : ¬ ((N : ℤ) < 0) := by omega
    simp only [h, ↓reduceIte]
  rw [hsign, Work.IntLib.encodeNat_eq_bits]
  rfl

theorem enc_int_rev (N : ℕ) :
    (Val.enc (.int (N : ℤ))).reverse =
      Glyph.iend :: (N.bits.reverse.map Glyph.bit ++ [Glyph.pos]) := by
  rw [enc_int_eq]
  rw [List.reverse_cons, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [← List.map_reverse]
  rfl

theorem noMark_rev {l : List Glyph} (h : Shift.NoMark l) : Shift.NoMark l.reverse :=
  fun g hg k => h g (List.mem_reverse.mp hg) k

/-- The size of a `cons`-node. -/
theorem vsz_cons_loc (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (a.enc ++ b.enc).length + 1 = a.enc.length + b.enc.length + 1
  rw [List.length_append]

theorem vsz_ofList_loc : ∀ (vs : List Val), vsz (ofList vs) = (vs.map vsz).sum + vs.length + 1 := by
  intro vs
  induction vs with
  | nil => rfl
  | cons a t ih =>
      rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, vsz_cons_loc, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem vsz_intNat_loc (h : ℕ) : vsz (Val.int (h : ℤ)) = h.size + 2 := by
  have h2 : (Val.int (h : ℤ)).enc.length = isz (h : ℤ) := Work.IntLib.vsz_int _
  show (Val.int (h : ℤ)).enc.length = h.size + 2
  rw [h2, Work.IntLib.isz_eq]
  first | rfl | simp

/-- The exact size of the encoding of a chain of naturals. -/
theorem vsz_intList_loc : ∀ (hs : List ℕ),
    vsz (intList hs) = (hs.map fun h => h.size).sum + 3 * hs.length + 1 := by
  intro hs
  induction hs with
  | nil => rfl
  | cons h t ih =>
      rw [show intList (h :: t) = Val.cons (Val.int (h : ℤ)) (intList t) from rfl,
        vsz_cons_loc, ih, vsz_intNat_loc]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- The size parameter of the prologue: `Σ|h| + len·(b+2) + isz b + 100`. -/
def pbT (hs : List ℕ) (b : ℕ) : ℕ :=
  (hs.map fun h => h.size).sum + hs.length * (b + 2) + isz (b : ℤ) + 100

/-- The elementary size estimates which make every stage of the prologue linear in `pbT hs b`. -/
theorem evBudgetLoc (hs : List ℕ) (b : ℕ) (hne : hs ≠ []) :
    vsz (intList hs) ≤ 2 * pbT hs b ∧
    (hs.map fun h => h.size).sum + hs.length + 1 ≤ pbT hs b ∧
    isz (b : ℤ) ≤ pbT hs b ∧
    b.size + b + 1 ≤ 2 * pbT hs b ∧
    1 ≤ pbT hs b := by
  have hm1 : 1 ≤ hs.length := by
    cases hs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hmul : 2 * hs.length ≤ hs.length * (b + 2) := by
    have h2 : 2 ≤ b + 2 := by omega
    calc 2 * hs.length = hs.length * 2 := by ring
      _ ≤ hs.length * (b + 2) := Nat.mul_le_mul_left hs.length h2
  have hm2 : hs.length + 1 ≤ hs.length * (b + 2) := by
    have h4 : 4 * hs.length ≤ 2 * (hs.length * (b + 2)) := by
      have h := Nat.mul_le_mul_left 2 hmul
      calc 4 * hs.length = 2 * (2 * hs.length) := by ring
        _ ≤ 2 * (hs.length * (b + 2)) := h
    omega
  have h2m : hs.length + 1 ≤ 2 * hs.length := by omega
  have hb2sz : b.size ≤ isz (b : ℤ) := by
    show b.size ≤ b.size + 2
    omega
  have hb2m : b + 1 ≤ hs.length * (b + 2) := by
    have h := Nat.le_mul_of_pos_right (b + 2) hm1
    rw [Nat.mul_comm] at h
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vsz_intList_loc hs]
    dsimp only [pbT]
    nlinarith [hmul, hm1, Nat.zero_le ((hs.map fun h => h.size).sum), Nat.zero_le (isz (b : ℤ))]
  · dsimp only [pbT]
    omega
  · dsimp only [pbT]
    omega
  · dsimp only [pbT]
    omega
  · dsimp only [pbT]
    omega

/-- The program of the prologue. -/
def evMkP (r : Reg) : Cmd := seqs (evLs.map (fun k => spPush r (Shift.gmk k) k))

def evProg (chainProg readProg : Cmd) : Cmd :=
  .seq (evMkP rX)
    (.seq chainProg
      (.seq readProg
        (.seq (UR.urProg aR aB aCB aT)
          (.seq (Shift.clearRgn aB (Shift.gmk aB) rX rFl)
            (.seq (Shift.clearAll aR rX rFl)
              (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
                (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW))))))))

theorem evPrologue (chainProg readProg : HvdH.Cmd) (KCM KR : ℕ)
    (hchain : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
      (hs : List ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (HvdH.intList hs) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main chainProg ⟨g, X⟩ s' n ∧
        n ≤ KCM * ((hs.map fun h => h.size).sum + hs.length + 1) ∧
        s'.stk 0 = rest ∧
        s'.stk Work.IntLib.aL = (HvdH.Val.enc (HvdH.intList hs)).reverse ++ X Work.IntLib.aL ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.aL → s'.stk j = X j))
    (hread : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
      (h : ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main readProg ⟨g, X⟩ s' n ∧
        n ≤ KR * (h.size + 2) ∧ s'.stk 0 = rest ∧
        s'.stk Work.IntLib.aR = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X Work.IntLib.aR ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.aR → s'.stk j = X j)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (b : ℕ) (hs : List ℕ) (hne : hs ≠ [])
      (Y : HvdH.Stk → List HvdH.Glyph),
      X 0 = HvdH.Val.enc (HvdH.intList hs) ++ HvdH.Val.enc (.int (b : ℤ)) ++ Y 0 →
      (∀ k : HvdH.Stk, k ≠ 0 → X k = Y k) →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (KCM + KR + 1) * ((hs.map fun h => h.size).sum + hs.length * (b + 2)
          + HvdH.isz (b : ℤ) + 100) ∧
        s' = ⟨s'.reg, Work.IntLib.evStk hs b 0 [] [] Y⟩ := by
  refine ⟨evProg chainProg readProg, 200, ?_⟩
  intro main g X b hs hne Y hX0 hXY
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := evBudgetLoc hs b hne
  -- ### 1. the frame markers
  obtain ⟨g1, he1⟩ := keysEv main rX evLs g X
  let X1 : Stk → List Glyph := markAllX evLs X
  have hLnd : evLs.Nodup := by dsimp only [evLs]; decide
  have hX1mem : ∀ k : Stk, k ∈ evLs → X1 k = Shift.gmk k :: X k := by
    intro k hk
    exact markAllX_mem evLs X k hLnd hk
  have hX1not : ∀ k : Stk, k ∉ evLs → X1 k = X k := by
    intro k hk
    exact markAllX_notMem evLs X k hk
  have hX1_0 : X1 0 = Val.enc (intList hs) ++ (Val.enc (.int (b : ℤ)) ++ Y 0) := by
    have h0 : X1 0 = X 0 := hX1not 0 (by dsimp only [evLs]; decide)
    rw [h0, hX0]
    exact List.append_assoc _ _ _
  have hcost1 : 2 * evLs.length + 1 ≤ 19 := by dsimp only [evLs]; decide
  have hE1 : Ev main (evMkP rX) ⟨g, X⟩ ⟨g1, X1⟩ 19 := he1.mono hcost1
  -- ### 2. the chain reader
  obtain ⟨s2, n2, he2, hn2, h2_0, h2_L, h2_oth⟩ :=
    hchain main g1 X1 hs (Val.enc (.int (b : ℤ)) ++ Y 0) hX1_0
  have hE2 : Ev main chainProg ⟨g1, X1⟩ s2 (KCM * pbT hs b) :=
    he2.mono (le_trans hn2 (Nat.mul_le_mul_left KCM hb2))
  have h2_aL : s2.stk aL = (Val.enc (intList hs)).reverse ++ Shift.gmk aL :: Y aL := by
    rw [h2_L, hX1mem aL (by dsimp only [evLs]; decide), hXY aL (by decide)]
  -- ### 3. the digit reader
  obtain ⟨s3, n3, he3, hn3, h3_0, h3_R, h3_oth⟩ :=
    hread main s2.reg s2.stk b (Y 0) h2_0
  have hE3 : Ev main readProg ⟨s2.reg, s2.stk⟩ s3 (KR * pbT hs b) :=
    he3.mono (le_trans hn3 (Nat.mul_le_mul_left KR hb3))
  have h3_aR : s3.stk aR = (Val.enc (.int (b : ℤ))).reverse ++ Shift.gmk aR :: Y aR := by
    have h : s2.stk aR = Shift.gmk aR :: Y aR := by
      rw [h2_oth aR (by decide) (by decide), hX1mem aR (by dsimp only [evLs]; decide),
        hXY aR (by decide)]
    rw [h3_R, h]
  have h3_aB : s3.stk aB = Shift.gmk aB :: Y aB := by
    rw [h3_oth aB (by decide) (by decide), h2_oth aB (by decide) (by decide),
      hX1mem aB (by dsimp only [evLs]; decide), hXY aB (by decide)]
  have h3_aCB : s3.stk aCB = Shift.gmk aCB :: Y aCB := by
    rw [h3_oth aCB (by decide) (by decide), h2_oth aCB (by decide) (by decide),
      hX1mem aCB (by dsimp only [evLs]; decide), hXY aCB (by decide)]
  have h3_aT : s3.stk aT = Y aT := by
    rw [h3_oth aT (by decide) (by decide), h2_oth aT (by decide) (by decide),
      hX1not aT (by dsimp only [evLs]; decide), hXY aT (by decide)]
  -- ### 4. rebuild the unary counter `Unary b` on `aCB`
  have h3_aR' : s3.stk aR =
      (Glyph.iend :: (b.bits.reverse.map Glyph.bit ++ [Glyph.pos])) ++
        Shift.gmk aR :: Y aR := by
    rw [h3_aR, enc_int_rev b]
  obtain ⟨s4, n4, he4, hn4, h4_aR, h4_aB, h4_aCB, h4_aT, h4_oth⟩ :=
    urRebuildK32 main aR aB aCB aT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s3.reg s3.stk b.bits (Y aR) (Shift.gmk aB :: Y aB)
      (Shift.gmk aCB :: Y aCB) (Y aT) h3_aR' h3_aB h3_aCB h3_aT
  have h4_aR' : s4.stk aR = Shift.gmk aR :: Y aR := h4_aR
  have h4_aB' : s4.stk aB = Val.enc (.int (b : ℤ)) ++ Shift.gmk aB :: Y aB := by
    rw [h4_aB, ← enc_int_eq b]
  have h4_aCB' : s4.stk aCB = Unary b (Shift.gmk aCB :: Y aCB) := by
    rw [h4_aCB, ofBits_bits]
  have hE4 : Ev main (UR.urProg aR aB aCB aT) ⟨s3.reg, s3.stk⟩ s4 (64 * pbT hs b) := by
    have h4 : n4 ≤ 32 * (b.size + b + 1) := by
      have hob : ofBits b.bits = b := by
        first | exact ofBits_bits b | exact (ofBits_bits b).symm
      have hlen : b.bits.length = b.size := by
        first | exact Nat.size_eq_bits_len b | exact (Nat.size_eq_bits_len b).symm
      have h := hn4
      rw [hob, hlen] at h
      exact h
    have hcost : 32 * (b.size + b + 1) ≤ 64 * pbT hs b := by
      calc 32 * (b.size + b + 1) ≤ 32 * (2 * pbT hs b) := Nat.mul_le_mul_left 32 hb4
        _ = 64 * pbT hs b := by ring
    exact he4.mono (le_trans h4 hcost)
  -- ### 5. drop the rebuilt value from `aB`
  have hG4 : ∀ h ∈ Val.enc (.int (b : ℤ)), h ≠ Shift.gmk aB :=
    fun h hh => noMark_enc (.int (b : ℤ)) h hh aB
  obtain ⟨s5, n5, he5, hn5, _, h5_aB, h5_oth⟩ :=
    Shift.clearRgn_ev main aB (Shift.gmk aB) rX rFl (Val.enc (.int (b : ℤ))) (Y aB)
      s4.reg s4.stk hG4 h4_aB'
  have hE5 : Ev main (Shift.clearRgn aB (Shift.gmk aB) rX rFl) ⟨s4.reg, s4.stk⟩ s5
      (12 * pbT hs b) := by
    have hlen : (Val.enc (.int (b : ℤ))).length = isz (b : ℤ) := Work.IntLib.vsz_int _
    have hle' : n5 ≤ 5 * (isz (b : ℤ) + 1) + 2 := by
      rw [hlen] at hn5
      exact hn5
    exact ⟨n5, he5, by omega⟩
  -- ### 6. remove the marker from `aR`
  have h5_aR : s5.stk aR = Shift.gmk aR :: Y aR := by
    rw [h5_oth aR (by decide), h4_aR']
  obtain ⟨s6, n6, he6, hn6, h6_aR, h6_oth⟩ :=
    Shift.clearAll_ev (main := main) aR rX rFl ([] : List Glyph) (Y aR) s5.reg s5.stk
      (by simp) h5_aR
  have hE6 : Ev main (Shift.clearAll aR rX rFl) ⟨s5.reg, s5.stk⟩ s6 (9 * pbT hs b) := by
    refine ⟨n6, he6, ?_⟩
    have h6 : n6 ≤ 9 := hn6
    omega
  -- ### 7. move the chain back onto stack 0
  have h6_aL : s6.stk aL = (Val.enc (intList hs)).reverse ++ Shift.gmk aL :: Y aL := by
    rw [h6_oth aL (by decide), h5_oth aL (by decide),
      h4_oth aL (by decide) (by decide) (by decide) (by decide),
      h3_oth aL (by decide) (by decide), h2_aL]
  have h6_0 : s6.stk 0 = Y 0 := by
    rw [h6_oth 0 (by decide), h5_oth 0 (by decide),
      h4_oth 0 (by decide) (by decide) (by decide) (by decide), h3_0]
  have hG6 : ∀ h ∈ (Val.enc (intList hs)).reverse, h ≠ Shift.gmk aL :=
    fun h hh => noMark_rev (noMark_enc (intList hs)) h hh aL
  obtain ⟨s7, n7, he7, hn7, _, h7_aL, h7_0, h7_oth⟩ :=
    Shift.drain_ev main aL 0 (Shift.gmk aL) rX rFl (by decide) rFl_ne_rX
      (Val.enc (intList hs)).reverse (Y aL) (Y 0) s6.reg s6.stk hG6 h6_aL h6_0
  have h7_0' : s7.stk 0 = Val.enc (intList hs) ++ Y 0 := by
    rw [h7_0, List.reverse_reverse]
  have hE7 : Ev main (Shift.drain aL 0 (Shift.gmk aL) rX rFl) ⟨s6.reg, s6.stk⟩ s7
      (17 * pbT hs b) := by
    have hvl : (Val.enc (intList hs)).reverse.length = vsz (intList hs) := by
      show (Val.enc (intList hs)).reverse.length = (Val.enc (intList hs)).length
      rw [List.length_reverse]
    have hle' : n7 ≤ 5 * (vsz (intList hs) + 1) + 2 := by
      rw [hvl] at hn7
      exact hn7
    exact ⟨n7, he7, by omega⟩
  -- ### 8. `pos` on `aO` and `gEnd` on `aCW`
  obtain ⟨g8, he8⟩ := spPush_ev main rX Glyph.pos aO s7.reg s7.stk
  let X8 : Stk → List Glyph := Function.update s7.stk aO (Glyph.pos :: s7.stk aO)
  obtain ⟨g9, he9⟩ := spPush_ev main rX gEnd aCW g8 X8
  let X9 : Stk → List Glyph := Function.update X8 aCW (gEnd :: X8 aCW)
  have hE8 : Ev main (spPush rX Glyph.pos aO) ⟨s7.reg, s7.stk⟩ ⟨g8, X8⟩ 2 := he8
  have hE9 : Ev main (spPush rX gEnd aCW) ⟨g8, X8⟩ ⟨g9, X9⟩ 2 := he9
  -- ### 9. compose the eight stages
  have hR1 : Ev main (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW))
      ⟨s7.reg, s7.stk⟩ ⟨g9, X9⟩ (2 + 2) := Ev.seq' hE8 hE9 (by omega)
  have hR2 : Ev main (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
      (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW)))
      ⟨s6.reg, s6.stk⟩ ⟨g9, X9⟩ (17 * pbT hs b + (2 + 2)) := Ev.seq' hE7 hR1 (by omega)
  have hR3 : Ev main (.seq (Shift.clearAll aR rX rFl)
      (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
        (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW))))
      ⟨s5.reg, s5.stk⟩ ⟨g9, X9⟩ (9 * pbT hs b + (17 * pbT hs b + (2 + 2))) :=
    Ev.seq' hE6 hR2 (by omega)
  have hR4 : Ev main (.seq (Shift.clearRgn aB (Shift.gmk aB) rX rFl)
      (.seq (Shift.clearAll aR rX rFl)
        (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
          (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW)))))
      ⟨s4.reg, s4.stk⟩ ⟨g9, X9⟩
      (12 * pbT hs b + (9 * pbT hs b + (17 * pbT hs b + (2 + 2)))) :=
    Ev.seq' hE5 hR3 (by omega)
  have hR5 : Ev main (.seq (UR.urProg aR aB aCB aT)
      (.seq (Shift.clearRgn aB (Shift.gmk aB) rX rFl)
        (.seq (Shift.clearAll aR rX rFl)
          (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
            (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW))))))
      ⟨s3.reg, s3.stk⟩ ⟨g9, X9⟩
      (64 * pbT hs b + (12 * pbT hs b + (9 * pbT hs b + (17 * pbT hs b + (2 + 2))))) :=
    Ev.seq' hE4 hR4 (by omega)
  have hR6 : Ev main (.seq readProg
      (.seq (UR.urProg aR aB aCB aT)
        (.seq (Shift.clearRgn aB (Shift.gmk aB) rX rFl)
          (.seq (Shift.clearAll aR rX rFl)
            (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
              (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW)))))))
      ⟨s2.reg, s2.stk⟩ ⟨g9, X9⟩
      (KR * pbT hs b + (64 * pbT hs b + (12 * pbT hs b + (9 * pbT hs b +
        (17 * pbT hs b + (2 + 2)))))) :=
    Ev.seq' hE3 hR5 (by omega)
  have hR7 : Ev main (.seq chainProg
      (.seq readProg
        (.seq (UR.urProg aR aB aCB aT)
          (.seq (Shift.clearRgn aB (Shift.gmk aB) rX rFl)
            (.seq (Shift.clearAll aR rX rFl)
              (.seq (Shift.drain aL 0 (Shift.gmk aL) rX rFl)
                (.seq (spPush rX Glyph.pos aO) (spPush rX gEnd aCW))))))))
      ⟨g1, X1⟩ ⟨g9, X9⟩
      (KCM * pbT hs b + (KR * pbT hs b + (64 * pbT hs b + (12 * pbT hs b +
        (9 * pbT hs b + (17 * pbT hs b + (2 + 2))))))) :=
    Ev.seq' hE2 hR6 (by omega)
  have hfinal : Ev main (evProg chainProg readProg) ⟨g, X⟩ ⟨g9, X9⟩
      (19 + (KCM * pbT hs b + (KR * pbT hs b + (64 * pbT hs b + (12 * pbT hs b +
        (9 * pbT hs b + (17 * pbT hs b + (2 + 2)))))))) :=
    Ev.seq' hE1 hR7 (by omega)
  -- ### 10. the budget
  have hsum : 19 + (KCM * pbT hs b + (KR * pbT hs b + (64 * pbT hs b + (12 * pbT hs b +
      (9 * pbT hs b + (17 * pbT hs b + (2 + 2))))))) ≤ 200 * (KCM + KR + 1) * pbT hs b := by
    have h23 : 23 ≤ 23 * pbT hs b := by
      calc 23 = 23 * 1 := by ring
        _ ≤ 23 * pbT hs b := Nat.mul_le_mul_left 23 hb5
    have hcoef : KCM + KR + 125 ≤ 200 * (KCM + KR + 1) := by omega
    calc 19 + (KCM * pbT hs b + (KR * pbT hs b + (64 * pbT hs b + (12 * pbT hs b +
          (9 * pbT hs b + (17 * pbT hs b + (2 + 2)))))))
        = KCM * pbT hs b + KR * pbT hs b + 102 * pbT hs b + 23 := by ring
      _ ≤ KCM * pbT hs b + KR * pbT hs b + 125 * pbT hs b := by omega
      _ = (KCM + KR + 125) * pbT hs b := by ring
      _ ≤ 200 * (KCM + KR + 1) * pbT hs b := Nat.mul_le_mul_right _ hcoef
  -- ### 11. the final state is the canonical `evStk` state
  have hwalkL : ∀ k : Stk, k ≠ aO → k ≠ aCW → k ≠ aC → k ≠ aL → k ≠ aR → k ≠ aB → k ≠ aCB →
      k ≠ aT → X9 k = X1 k := by
    intro k h1 h2 h3 h4 h5 h6 h7 h8
    calc X9 k = s7.stk k := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply h2, upd_aO_apply h1]
      _ = s6.stk k := h7_oth k h4 h3
      _ = s5.stk k := h6_oth k h5
      _ = s4.stk k := h5_oth k h6
      _ = s3.stk k := h4_oth k h5 h6 h7 h8
      _ = s2.stk k := h3_oth k h3 h5
      _ = X1 k := h2_oth k h3 h4
  have h9_aW : X9 aW = Shift.gmk aW :: Y aW := by
    calc X9 aW = X1 aW := hwalkL aW (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      _ = Shift.gmk aW :: X aW := hX1mem aW (by dsimp only [evLs]; decide)
      _ = Shift.gmk aW :: Y aW := by rw [hXY aW (by decide)]
  have h9_aA : X9 aA = Shift.gmk aA :: Y aA := by
    calc X9 aA = X1 aA := hwalkL aA (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      _ = Shift.gmk aA :: X aA := hX1mem aA (by dsimp only [evLs]; decide)
      _ = Shift.gmk aA :: Y aA := by rw [hXY aA (by decide)]
  have h9_a2 : X9 a2 = Shift.gmk a2 :: Y a2 := by
    calc X9 a2 = X1 a2 := hwalkL a2 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      _ = Shift.gmk a2 :: X a2 := hX1mem a2 (by dsimp only [evLs]; decide)
      _ = Shift.gmk a2 :: Y a2 := by rw [hXY a2 (by decide)]
  have h7_aO : s7.stk aO = Shift.gmk aO :: Y aO := by
    calc s7.stk aO = s6.stk aO := h7_oth aO (by decide) (by decide)
      _ = s5.stk aO := h6_oth aO (by decide)
      _ = s4.stk aO := h5_oth aO (by decide)
      _ = s3.stk aO := h4_oth aO (by decide) (by decide) (by decide) (by decide)
      _ = s2.stk aO := h3_oth aO (by decide) (by decide)
      _ = X1 aO := h2_oth aO (by decide) (by decide)
      _ = Shift.gmk aO :: X aO := hX1mem aO (by dsimp only [evLs]; decide)
      _ = Shift.gmk aO :: Y aO := by rw [hXY aO (by decide)]
  have h7_aCW : s7.stk aCW = Shift.gmk aCW :: Y aCW := by
    calc s7.stk aCW = s6.stk aCW := h7_oth aCW (by decide) (by decide)
      _ = s5.stk aCW := h6_oth aCW (by decide)
      _ = s4.stk aCW := h5_oth aCW (by decide)
      _ = s3.stk aCW := h4_oth aCW (by decide) (by decide) (by decide) (by decide)
      _ = s2.stk aCW := h3_oth aCW (by decide) (by decide)
      _ = X1 aCW := h2_oth aCW (by decide) (by decide)
      _ = Shift.gmk aCW :: X aCW := hX1mem aCW (by dsimp only [evLs]; decide)
      _ = Shift.gmk aCW :: Y aCW := by rw [hXY aCW (by decide)]
  have h7_aB : s7.stk aB = Shift.gmk aB :: Y aB := by
    rw [h7_oth aB (by decide) (by decide), h6_oth aB (by decide), h5_aB]
  have h9_aC : X9 aC = Val.enc (intList (hs.drop 0)) ++ Y aC := by
    have hd : hs.drop 0 = hs := by first | rfl | simp
    rw [hd]
    show X9 0 = Val.enc (intList hs) ++ Y 0
    calc X9 0 = s7.stk 0 := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply (by decide : (0 : Stk) ≠ aCW),
            upd_aO_apply (by decide : (0 : Stk) ≠ aO)]
      _ = Val.enc (intList hs) ++ Y 0 := h7_0'
  have h9_aO : X9 aO = [].reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
    calc X9 aO = Glyph.pos :: s7.stk aO := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply (by decide : aO ≠ aCW), Shift.upStk_same]
      _ = Glyph.pos :: (Shift.gmk aO :: Y aO) := by rw [h7_aO]
      _ = [].reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
            first | rfl | simp
  have hX8aCW : X8 aCW = s7.stk aCW := by
    show (Function.update s7.stk aO (Glyph.pos :: s7.stk aO)) aCW = s7.stk aCW
    exact Function.update_of_ne (by decide : aCW ≠ aO) _ _
  have h9_aCW : X9 aCW = Unary 0 (Shift.gmk aCW :: Y aCW) := by
    have h1 : X9 aCW = gEnd :: X8 aCW := by
      show (Function.update X8 aCW (gEnd :: X8 aCW)) aCW = gEnd :: X8 aCW
      exact Shift.upStk_same aCW (gEnd :: X8 aCW)
    calc X9 aCW = gEnd :: X8 aCW := h1
      _ = gEnd :: s7.stk aCW := congrArg (fun l => gEnd :: l) hX8aCW
      _ = gEnd :: (Shift.gmk aCW :: Y aCW) := congrArg (fun l => gEnd :: l) h7_aCW
      _ = Unary 0 (Shift.gmk aCW :: Y aCW) := by first | rfl | simp [Unary]
  have h9_aCB : X9 aCB = Unary b (Shift.gmk aCB :: Y aCB) := by
    calc X9 aCB = s7.stk aCB := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply (by decide : aCB ≠ aCW), upd_aO_apply (by decide : aCB ≠ aO)]
      _ = Unary b (Shift.gmk aCB :: Y aCB) := by
          rw [h7_oth aCB (by decide) (by decide), h6_oth aCB (by decide),
            h5_oth aCB (by decide), h4_aCB']
  have h9_aB : X9 aB = Shift.gmk aB :: Y aB := by
    calc X9 aB = s7.stk aB := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply (by decide : aB ≠ aCW), upd_aO_apply (by decide : aB ≠ aO)]
      _ = Shift.gmk aB :: Y aB := h7_aB
  have h9_aL : X9 aL = Shift.gmk aL :: Y aL := by
    calc X9 aL = s7.stk aL := by
          dsimp only [X9, X8]
          rw [upd_aCW_apply (by decide : aL ≠ aCW), upd_aO_apply (by decide : aL ≠ aO)]
      _ = Shift.gmk aL :: Y aL := h7_aL
  have h9_oth : ∀ k : Stk, k ∉ ({aC, aW, aO, aCW, aCB, aA, aB, a2, aL} : Finset Stk) →
      X9 k = Y k := by
    intro k hk
    obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := not_mem_evStk_set hk
    by_cases hR : k = aR
    · rw [hR]
      calc X9 aR = s7.stk aR := by
            dsimp only [X9, X8]
            rw [upd_aCW_apply (by decide : aR ≠ aCW), upd_aO_apply (by decide : aR ≠ aO)]
        _ = s6.stk aR := h7_oth aR (by decide) (by decide)
        _ = Y aR := h6_aR
    · by_cases hT : k = aT
      · rw [hT]
        calc X9 aT = s7.stk aT := by
              dsimp only [X9, X8]
              rw [upd_aCW_apply (by decide : aT ≠ aCW), upd_aO_apply (by decide : aT ≠ aO)]
          _ = s6.stk aT := h7_oth aT (by decide) (by decide)
          _ = s5.stk aT := h6_oth aT (by decide)
          _ = s4.stk aT := h5_oth aT (by decide)
          _ = Y aT := h4_aT
      · have hkL : k ∉ evLs :=
          notMem_evLs hR hk7 hk5 hk9 hk2 hk3 hk6 hk8 hk4
        calc X9 k = X1 k := hwalkL k hk3 hk4 hk1 hk9 hR hk7 hk5 hT
          _ = X k := hX1not k hkL
          _ = Y k := hXY k hk1
  have hX9eq : X9 = evStk hs b 0 [] [] Y := by
    rw [evMainEvStkEq]
    exact ⟨h9_aC, h9_aW, h9_aO, h9_aCW, h9_aCB, h9_aA, h9_aB, h9_a2, h9_aL, h9_oth⟩
  -- ### 12. conclusion
  refine ⟨⟨g9, evStk hs b 0 [] [] Y⟩, 200 * (KCM + KR + 1) * pbT hs b, ?_, ?_, ?_⟩
  · have h := hfinal.mono hsum
    rw [hX9eq] at h
    exact h
  · show 200 * (KCM + KR + 1) * pbT hs b ≤ 200 * (KCM + KR + 1) * pbT hs b
    exact le_rfl
  · rfl

end Work.IntLib
