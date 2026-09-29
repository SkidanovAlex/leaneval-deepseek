import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.chunksOfDefs
import Submission.Work.Layout.chunksArith
import Submission.Work.Layout.chunksProof
import Submission.Work.Layout.readBits_ev
import Submission.Work.Layout.walk_ev
import Submission.Work.Layout.walkFrame
import Submission.Work.Layout.buildCounterFrame
import Submission.Work.Layout.buildFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Work.Layout

open HvdH

/-- The `i`-th entry of `(List.range c).map f`, when `i < c`. -/
theorem getD_map_range {f : ℕ → List Val} {c : ℕ} :
    ∀ i < c, ((List.range c).map f).getD i [] = f i := by
  intro i hi
  have hmem : i ∈ List.range c := List.mem_range.mpr hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hmem)]
  simp

/-- `ofList` commutes with `List.map` into the fused form used by the statement. -/
theorem map_ofList_map {α : Type} (l : List α) (f : α → List Val) :
    List.map ofList (List.map f l) = List.map (fun i => ofList (f i)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

/-- **`LayoutLib.chunksOf`**: cut `ofList xs` into consecutive chunks of length `m` (`1 ≤ m`,
`m ∣ xs.length`).  Build a unary counter of `m` markers (`m ≤ xs.length` unless `xs = []`) and move `m`
elements at a time to a scratch stack, rebuilding each chunk with `cons` and consing it onto the
accumulated list of chunks. -/
theorem chunksOfWord : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (m : ℕ) (xs : List Val), 1 ≤ m → m ∣ xs.length →
    WordR main p (fun vs => ∃ rest, vs = .int m :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int m :: ofList xs :: rest ∧
      out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m)) :: rest)
    (fun _ => K * (vsz (ofList xs) + (xs.length / m + 1) * isz m + 1)) := by
  refine ⟨mainProg, 1000, ?_⟩
  intro main m xs hm hdvd
  rw [WordR]
  intro vs hvs s R hs0
  obtain ⟨rest, rfl⟩ := hvs
  set A : List Glyph := encs rest ++ R with hA
  have h0 : s.stk 0 = (Val.int (m : ℤ)).enc ++ ((ofList xs).enc ++ A) := by
    rw [hs0]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc, hA]
  obtain ⟨s₁, n₁, hev₁, hb₁, hs₁_0, hs₁_b, hs₁_fr⟩ :=
    readBits_ev (main := main) (g := s.reg) (X := s.stk) (m := m)
      (A := (ofList xs).enc ++ A) (B := s.stk sBits) h0 rfl
  cases xs with
  | nil =>
      have hhead : s₁.stk 0 = Glyph.nil :: A := by
        rw [hs₁_0]
        simp only [ofList, List.foldr_nil, Val.enc, List.singleton_append]
      obtain ⟨s₂, hev₂, hs₂_0, hs₂_r, hs₂_fr, -⟩ :=
        step_peek (main := main) (k := 0) (r := rE) (g := s₁.reg) (X := s₁.stk)
          (h := Glyph.nil) (L := A) hhead
      have hs₂_b : s₂.stk sBits = (bitsG m.bits).reverse ++ gMark :: s.stk sBits := by
        rw [hs₂_fr sBits (by decide : sBits ≠ 0), hs₁_b]
      have hnot : gMark ∉ (bitsG m.bits).reverse :=
        fun h => gMark_notMem_bitsG m.bits (List.mem_reverse.mp h)
      obtain ⟨s₃, n₃, hev₃, hb₃, hs₃_b, hs₃_fr⟩ :=
        drainTo_ev (main := main) (k := sBits) (κ := gMark) (G := (bitsG m.bits).reverse)
          (B := s.stk sBits) (g := s₂.reg) (X := s₂.stk) hnot hs₂_b
      have hcond : ¬ (s₂.reg rE = Glyph.cons) := by rw [hs₂_r]; decide
      have hite : Ev main (.ite rE Glyph.cons fullProg emptyProg) s₂ s₃ (n₃ + 1) :=
        Ev.iteF hcond hev₃
      have hseq : Ev main (seqs [.peek 0 rE, .ite rE Glyph.cons fullProg emptyProg]) s₁ s₃
          (1 + (n₃ + 1)) := Ev.seq' hev₂ hite (by omega)
      have hmain : Ev main mainProg s s₃ (n₁ + (1 + (n₃ + 1))) := by
        unfold mainProg
        exact Ev.seq' hev₁ hseq (by omega)
      have hcost : n₁ + (1 + (n₃ + 1)) ≤
          1000 * (vsz (ofList ([] : List Val)) + ((([] : List Val).length) / m + 1) * isz (m : ℤ) + 1) := by
        have h1 : n₁ ≤ 8 * (m.bits.length + 2) + 10 := by
          have h := hb₁
          rw [isz_eq_bits_length] at h
          exact h
        have h3 : n₃ ≤ 6 * (m.bits.length + 1) + 4 := by
          have h := hb₃
          rw [List.length_reverse, bitsG_length] at h
          omega
        have hv : vsz (ofList ([] : List Val)) = 1 := by simp [vsz, ofList, Val.enc]
        rw [hv, isz_eq_bits_length]
        simp only [List.length_nil, Nat.zero_div]
        omega
      obtain ⟨n₀, heval, hle₀⟩ := hmain
      refine ⟨ofList ([] : List Val) :: rest, s₃, n₀, ⟨rest, rfl, ?_⟩, heval, ?_, ?_, ?_⟩
      · simp
      · exact le_trans hle₀ hcost
      · have hs₃_0 : s₃.stk 0 = Glyph.nil :: A :=
          by rw [hs₃_fr 0 (by decide : (0 : Stk) ≠ sBits), hs₂_0]
        rw [hs₃_0, hA]
        simp only [encs, List.map_cons, List.flatten_cons, ofList, List.foldr_nil, Val.enc,
          List.singleton_append, List.cons_append, List.nil_append]
      · intro k hk
        by_cases hb : k = sBits
        · subst hb; rw [hs₃_b]
        · rw [hs₃_fr k (by omega), hs₂_fr k (by omega), hs₁_fr k hk hb]
  | cons y ys =>
      have hhead : s₁.stk 0 = Glyph.cons :: (y.enc ++ (ofList ys).enc ++ A) := by
        rw [hs₁_0, enc_ofList_cons, List.cons_append]
      obtain ⟨s₂, hev₂, hs₂_0, hs₂_r, hs₂_fr, -⟩ :=
        step_peek (main := main) (k := 0) (r := rE) (g := s₁.reg) (X := s₁.stk)
          (h := Glyph.cons) (L := y.enc ++ (ofList ys).enc ++ A) hhead
      have hcond : s₂.reg rE = Glyph.cons := hs₂_r
      have h6₂ : s₂.stk sBits = bitsG m.bits.reverse ++ gMark :: s.stk sBits := by
        rw [hs₂_fr sBits (by decide : sBits ≠ 0), hs₁_b, bitsG_reverse]
      have hM₂ : s₂.stk sM = s.stk sM := by
        rw [hs₂_fr sM (by decide : sM ≠ 0),
            hs₁_fr sM (by decide : sM ≠ 0) (by decide : sM ≠ sBits)]
      obtain ⟨s₃, n₃, hev₃, hb₃, hs₃M, hs₃b, hs₃T2, hs₃fr⟩ :=
        buildCounterFrame (main := main) (g := s₂.reg) (X := s₂.stk) (L := m.bits.reverse)
          (B6 := s.stk sBits) (M0 := s.stk sM) h6₂ hM₂
      have hM₃ : s₃.stk sM = List.replicate m gPend ++ gSent :: s.stk sM := by
        rw [hs₃M, valBits_bits_reverse]
      have h0₃ : s₃.stk 0 = Glyph.cons :: (y.enc ++ (ofList ys).enc ++ A) := by
        rw [hs₃fr 0 (by decide : (0 : Stk) ≠ sM) (by decide : (0 : Stk) ≠ sBits)
              (by decide : (0 : Stk) ≠ sT2), hs₂_0]
      have hT₃ : s₃.stk sT = s.stk sT := by
        rw [hs₃fr sT (by decide : sT ≠ sM) (by decide : sT ≠ sBits) (by decide : sT ≠ sT2),
            hs₂_fr sT (by decide : sT ≠ 0),
            hs₁_fr sT (by decide : sT ≠ 0) (by decide : sT ≠ sBits)]
      obtain ⟨s₄, n₄, hev₄, hb₄, hs₄_0, hs₄T, hs₄B, hs₄C, hs₄fr⟩ :=
        walkFrame (main := main) (g := s₃.reg) (X := s₃.stk) (ys := y :: ys) (A := A)
          (T0 := s.stk sT)
          (by rw [h0₃, enc_ofList_cons, List.cons_append]) hT₃
      obtain ⟨s₅, hev₅, hs₅_0, hs₅_r, hs₅_fr, -⟩ :=
        step_pop (main := main) (k := 0) (r := rE) (g := s₄.reg) (X := s₄.stk)
          (h := Glyph.nil) (L := A) hs₄_0
      set ch : List (List Val) := (List.range ((y :: ys).length / m)).map
        (fun i => ((y :: ys).drop (i * m)).take m) with hch
      have heo : elemOrder ch = (y :: ys).reverse := by
        rw [hch, elemOrder_range_map]
        congr 1
        simpa only [chunkAt] using flatMap_range_chunkAt_eq (y :: ys) hdvd
      have hs₅T : s₅.stk sT = ((elemOrder ch).map Val.enc).flatten ++ gSent :: s.stk sT := by
        rw [hs₅_fr sT (by decide : sT ≠ 0), hs₄T, heo, List.map_reverse]
      have hs₅M : s₅.stk sM = List.replicate m gPend ++ gSent :: s.stk sM := by
        rw [hs₅_fr sM (by decide : sM ≠ 0),
            hs₄fr sM (by decide : sM ≠ 0) (by decide : sM ≠ sT) (by decide : sM ≠ sB)
              (by decide : sM ≠ sC), hM₃]
      have hs₅W : s₅.stk sW = s.stk sW := by
        rw [hs₅_fr sW (by decide : sW ≠ 0),
            hs₄fr sW (by decide : sW ≠ 0) (by decide : sW ≠ sT) (by decide : sW ≠ sB)
              (by decide : sW ≠ sC),
            hs₃fr sW (by decide : sW ≠ sM) (by decide : sW ≠ sBits) (by decide : sW ≠ sT2),
            hs₂_fr sW (by decide : sW ≠ 0),
            hs₁_fr sW (by decide : sW ≠ 0) (by decide : sW ≠ sBits)]
      have hs₅B : s₅.stk sB = s.stk sB := by
        rw [hs₅_fr sB (by decide : sB ≠ 0), hs₄B,
            hs₃fr sB (by decide : sB ≠ sM) (by decide : sB ≠ sBits) (by decide : sB ≠ sT2),
            hs₂_fr sB (by decide : sB ≠ 0),
            hs₁_fr sB (by decide : sB ≠ 0) (by decide : sB ≠ sBits)]
      have hs₅C : s₅.stk sC = s.stk sC := by
        rw [hs₅_fr sC (by decide : sC ≠ 0), hs₄C,
            hs₃fr sC (by decide : sC ≠ sM) (by decide : sC ≠ sBits) (by decide : sC ≠ sT2),
            hs₂_fr sC (by decide : sC ≠ 0),
            hs₁_fr sC (by decide : sC ≠ 0) (by decide : sC ≠ sBits)]
      have hs₅b : s₅.stk sBits = s.stk sBits := by
        rw [hs₅_fr sBits (by decide : sBits ≠ 0),
            hs₄fr sBits (by decide : sBits ≠ 0) (by decide : sBits ≠ sT) (by decide : sBits ≠ sB)
              (by decide : sBits ≠ sC), hs₃b]
      have hs₅T2 : s₅.stk sT2 = s.stk sT2 := by
        rw [hs₅_fr sT2 (by decide : sT2 ≠ 0),
            hs₄fr sT2 (by decide : sT2 ≠ 0) (by decide : sT2 ≠ sT) (by decide : sT2 ≠ sB)
              (by decide : sT2 ≠ sC),
            hs₃T2, hs₂_fr sT2 (by decide : sT2 ≠ 0),
            hs₁_fr sT2 (by decide : sT2 ≠ 0) (by decide : sT2 ≠ sBits)]
      have hlen : ∀ i, i < ch.length → (ch.getD i []).length = m := by
        intro i hi
        have hi' : i < (y :: ys).length / m := by
          have h := hi; rw [hch] at h; simpa using h
        have hget : ch.getD i [] = ((y :: ys).drop (i * m)).take m := by
          rw [hch]
          exact getD_map_range (f := fun i => ((y :: ys).drop (i * m)).take m)
            (c := (y :: ys).length / m) i hi'
        rw [hget]
        exact chunk_length hm hdvd i hi'
      obtain ⟨s₆, n₆, hev₆, hb₆, hs₆_0, hs₆T, hs₆M, hs₆W, hs₆B, hs₆C, hs₆T2, hs₆fr⟩ :=
        buildFrame (main := main) (g := s₅.reg) (X := s₅.stk) (ch := ch) (m := m) (A0 := A)
          (T0 := s.stk sT) (M0 := s.stk sM) (W0 := s.stk sW) hm hlen hs₅T hs₅M hs₅W hs₅_0
      obtain ⟨s₇, hev₇, hs₇T, hs₇_r, hs₇_fr, -⟩ :=
        step_pop (main := main) (k := sT) (r := rE) (g := s₆.reg) (X := s₆.stk)
          (h := gSent) (L := s.stk sT) hs₆T
      have hM₇ : s₇.stk sM = List.replicate m gPend ++ gSent :: s.stk sM := by
        rw [hs₇_fr sM (by decide : sM ≠ sT), hs₆M]
      obtain ⟨s₈, n₈, hev₈, hb₈, hs₈M, hs₈_fr⟩ :=
        drainTo_ev (main := main) (k := sM) (κ := gSent) (G := List.replicate m gPend)
          (B := s.stk sM) (g := s₇.reg) (X := s₇.stk) (gSent_notMem_replicate m) hM₇
      have h67 : Ev main (seqs [.pop sT rE, drainToProg sM gSent]) s₆ s₈ (1 + n₈) :=
        Ev.seq' hev₇ hev₈ (by omega)
      have h567 : Ev main (seqs [buildProg, .pop sT rE, drainToProg sM gSent]) s₅ s₈
          (n₆ + (1 + n₈)) := Ev.seq' hev₆ h67 (by omega)
      have h4567 : Ev main (seqs [.pop 0 rE, buildProg, .pop sT rE, drainToProg sM gSent]) s₄ s₈
          (1 + (n₆ + (1 + n₈))) := Ev.seq' hev₅ h567 (by omega)
      have h34567 : Ev main (seqs [walkProg, .pop 0 rE, buildProg, .pop sT rE,
          drainToProg sM gSent]) s₃ s₈ (n₄ + (1 + (n₆ + (1 + n₈)))) :=
        Ev.seq' hev₄ h4567 (by omega)
      have hfull : Ev main fullProg s₂ s₈ (n₃ + (n₄ + (1 + (n₆ + (1 + n₈))))) := by
        unfold fullProg
        exact Ev.seq' hev₃ h34567 (by omega)
      have hite : Ev main (.ite rE Glyph.cons fullProg emptyProg) s₂ s₈
          (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1) := Ev.iteT hcond hfull
      have hseq : Ev main (seqs [.peek 0 rE, .ite rE Glyph.cons fullProg emptyProg]) s₁ s₈
          (1 + (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1)) := Ev.seq' hev₂ hite (by omega)
      have hmain : Ev main mainProg s s₈
          (n₁ + (1 + (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1))) := by
        unfold mainProg
        exact Ev.seq' hev₁ hseq (by omega)
      have hchlen : ch.length = (y :: ys).length / m := by rw [hch]; simp
      have hvsz : vsz (ofList (ch.map ofList)) = vsz (ofList (y :: ys)) + 2 * ((y :: ys).length / m) := by
        simpa [hch] using vsz_chunks (y :: ys) m hm hdvd
      have hcost : n₁ + (1 + (n₃ + (n₄ + (1 + (n₆ + (1 + n₈)))) + 1)) ≤
          1000 * (vsz (ofList (y :: ys)) + ((y :: ys).length / m + 1) * isz (m : ℤ) + 1) := by
        have hI : isz (m : ℤ) = m.bits.length + 2 := isz_eq_bits_length m
        have hmV : m ≤ vsz (ofList (y :: ys)) := by
          have h1 : m ≤ (y :: ys).length := Nat.le_of_dvd (List.length_pos_iff.mpr (by simp)) hdvd
          exact le_trans h1 (length_le_vsz_ofList (y :: ys))
        have hLmV : (y :: ys).length / m ≤ vsz (ofList (y :: ys)) :=
          le_trans (Nat.div_le_self _ _) (length_le_vsz_ofList (y :: ys))
        have h1 : n₁ ≤ 8 * (m.bits.length + 2) + 10 := by
          have h := hb₁; rw [hI] at h; exact h
        have h3 : n₃ ≤ 100 * (m + m.bits.length + 1) := by
          have h := hb₃
          rw [valBits_bits_reverse, List.length_reverse] at h
          exact h
        have h4 : n₄ ≤ 40 * (vsz (ofList (y :: ys)) + 1) := hb₄
        have h6 : n₆ ≤ 100 * (vsz (ofList (y :: ys)) + 3 * ((y :: ys).length / m) + 1) := by
          have h := hb₆
          rw [hvsz, hchlen] at h
          omega
        have h8 : n₈ ≤ 6 * (m + 1) + 4 := by
          have h := hb₈; rw [List.length_replicate] at h; exact h
        have hQI : (y :: ys).length / m ≤ ((y :: ys).length / m) * isz (m : ℤ) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have htarget : 1000 * (vsz (ofList (y :: ys)) + ((y :: ys).length / m + 1) * isz (m : ℤ) + 1)
            = 1000 * vsz (ofList (y :: ys)) + 1000 * (((y :: ys).length / m) * isz (m : ℤ))
              + 1000 * isz (m : ℤ) + 1000 := by ring
        rw [htarget]
        omega
      obtain ⟨n₀, heval, hle₀⟩ := hmain
      have h80 : s₈.stk 0 = (ofList (ch.map ofList)).enc ++ A := by
        rw [hs₈_fr 0 (by decide : (0 : Stk) ≠ sM), hs₇_fr 0 (by decide : (0 : Stk) ≠ sT), hs₆_0]
      refine ⟨ofList (ch.map ofList) :: rest, s₈, n₀, ⟨rest, rfl, ?_⟩, heval, ?_, ?_, ?_⟩
      · simpa only [hch, map_ofList_map]
      · exact le_trans hle₀ hcost
      · rw [h80, hA]
        simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
      · intro k hk0
        by_cases hT : k = sT
        · subst hT; rw [hs₈_fr sT (by decide : sT ≠ sM), hs₇T]
        by_cases hM : k = sM
        · subst hM; exact hs₈M
        by_cases hW : k = sW
        · subst hW
          rw [hs₈_fr sW (by decide : sW ≠ sM), hs₇_fr sW (by decide : sW ≠ sT), hs₆W]
        by_cases hB : k = sB
        · subst hB
          rw [hs₈_fr sB (by decide : sB ≠ sM), hs₇_fr sB (by decide : sB ≠ sT), hs₆B, hs₅B]
        by_cases hC : k = sC
        · subst hC
          rw [hs₈_fr sC (by decide : sC ≠ sM), hs₇_fr sC (by decide : sC ≠ sT), hs₆C, hs₅C]
        by_cases hb : k = sBits
        · subst hb
          rw [hs₈_fr sBits (by decide : sBits ≠ sM), hs₇_fr sBits (by decide : sBits ≠ sT),
            hs₆fr sBits (by decide : sBits ≠ 0) (by decide : sBits ≠ sT) (by decide : sBits ≠ sM)
              (by decide : sBits ≠ sW) (by decide : sBits ≠ sB) (by decide : sBits ≠ sC), hs₅b]
        by_cases hT2 : k = sT2
        · subst hT2
          rw [hs₈_fr sT2 (by decide : sT2 ≠ sM), hs₇_fr sT2 (by decide : sT2 ≠ sT),
            hs₆fr sT2 (by decide : sT2 ≠ 0) (by decide : sT2 ≠ sT) (by decide : sT2 ≠ sM)
              (by decide : sT2 ≠ sW) (by decide : sT2 ≠ sB) (by decide : sT2 ≠ sC), hs₅T2]
        · rw [hs₈_fr k hM, hs₇_fr k hT,
            hs₆fr k hk0 hT hM hW hB hC, hs₅_fr k hk0,
            hs₄fr k hk0 hT hB hC, hs₃fr k hM hb hT2, hs₂_fr k hk0, hs₁_fr k hk0 hb]

end Work.Layout
