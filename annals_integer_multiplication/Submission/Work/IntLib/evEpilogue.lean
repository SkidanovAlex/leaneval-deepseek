import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.evEmitDefs

/-!
# `IntLib` / `evEpilogue`: the last phase of the `evalPoly` word

At the end of the main loop (`evMainLoop`) the state is `evStk hs b hs.length W' LO' Y`: the input
chain has been consumed (stack `aC = 0` holds only the terminating `nil`), the finalised low bits
`LO'` sit on `aO` below their sign, the window `W'` sits on `aW`, and the unary counters `aCB`
(with `b` units) and `aCW` are spent.  `evVal hs b hs.length W' LO'` says
`ofBits LO' + 2^|LO'| * ofBits W' = evalChunks hs b`.

The emit word (`Submission/Work/IntLib/evEmit.lean`) turns such a state into the encoding of
`V = ofBits LO' + 2^|LO'| * ofBits W'` on stack 0, provided

* every stack other than `0`, `aW`, `aO`, `aV`, `aCB`, `aCW` carries its frame marker
  `Shift.gmk k` above the tail `Y k`,
* the regions above the markers of `aV`, `aCB`, `aCW` contain no marker of that stack,
* stack 0 is exactly `Y 0`.

So the epilogue only has to

* pop the terminating `nil` off stack 0, and
* re-push the frame markers of the seven stacks `aV, 9, 10, 12, 13, 14, 15` that the `evalPoly`
  word leaves bare,

and then call the emit word with `V := evalChunks hs b`, `Vr := []`, `Rcb := Unary b []` and
`Rcw := Unary 0 []`.  Its cost is `1 + (2*7+1) + KE * (|LO'| + |W'| + |Rcb| + |Rcw| + 24)`, and
`|LO'| + |W'| + (b+1) + 1 + 24 ≤ |W'| + |LO'| + (|hs|+1)*(b+1) + isz b + 40`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Toolkit -/

/-- The stacks whose frame markers the epilogue re-pushes before calling the emit word. -/
def evEpiL : List Stk := [aV, 9, 10, 12, 13, 14, 15]

theorem evEpiL_nodup : evEpiL.Nodup := by decide

theorem evEpiL_length : evEpiL.length = 7 := by decide

/-- `Unary n (e :: rest) = Unary n [] ++ e :: rest`. -/
theorem Unary_cons_append (n : ℕ) (e : Glyph) (rest : List Glyph) :
    Unary n (e :: rest) = Unary n [] ++ e :: rest := by
  show List.replicate n gTok ++ gEnd :: (e :: rest)
      = (List.replicate n gTok ++ gEnd :: ([] : List Glyph)) ++ e :: rest
  rw [List.append_assoc]
  rfl

theorem Unary_zero_nil : Unary 0 ([] : List Glyph) = [gEnd] := rfl

/-- `Unary b []` has length `b + 1`. -/
theorem Unary_nil_length (b : ℕ) : (Unary b ([] : List Glyph)).length = b + 1 := by
  simp [Unary]

theorem Unary_zero_nil_length : (Unary 0 ([] : List Glyph)).length = 1 := by
  simp [Unary]

/-- `Val.enc` of the empty list of naturals is the single glyph `nil`. -/
theorem enc_intList_nil_el : Val.enc (intList ([] : List ℕ)) = [Glyph.nil] := rfl

/-- An element of a unary counter is a unit, the end marker, or lies below the counter. -/
theorem mem_Unary {n : ℕ} {rest : List Glyph} {h : Glyph} (hh : h ∈ Unary n rest) :
    h = gTok ∨ h = gEnd ∨ h ∈ rest := by
  rw [Unary_eq_append] at hh
  rcases List.mem_append.mp hh with h1 | h1
  · exact Or.inl (List.eq_of_mem_replicate h1)
  · rcases List.mem_cons.mp h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)

/-- `aV` is not one of the stacks touched by the `evalPoly` word. -/
theorem evStk_aV (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aV = Y aV :=
  evStk_other hs b j W LO Y (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The stacks of `evEpiL` are not among those whose content `evStk` describes. -/
theorem evEpiL_notUsed : ∀ k : Stk, k ∈ evEpiL → k ≠ aC ∧ k ≠ aW ∧ k ≠ aO ∧ k ≠ aCW ∧
    k ≠ aCB ∧ k ≠ aA ∧ k ≠ aB ∧ k ≠ a2 ∧ k ≠ aL := by decide

/-- On the stacks of `evEpiL` the `evalPoly` state function is the identity, so the epilogue finds
the bare tails there. -/
theorem evStk_mem_evEpiL (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph)
    {k : Stk} (hk : k ∈ evEpiL) : evStk hs b j W LO Y k = Y k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := evEpiL_notUsed k hk
  exact evStk_other hs b j W LO Y h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- Every stack satisfying the hypotheses of the emit word is either one of the four stacks whose
`evStk` value is `gmk k :: Y k`, or one of the seven stacks of `evEpiL`. -/
theorem stk_cover : ∀ k : Stk, k ≠ 0 → k ≠ aW → k ≠ aO → k ≠ aV → k ≠ aCB → k ≠ aCW →
    k = aA ∨ k = aB ∨ k = a2 ∨ k = aL ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by
  decide

/-- Pushing the frame markers of a list of stacks. -/
theorem ev_pushMarkersAux (main : Cmd) (r : Reg) (L : List Stk) :
    L.Nodup → ∀ s : State, ∃ (s' : State) (n : ℕ),
      Ev main (Work.Layout.seqs (L.map (fun k => Work.IntLib.pushConst k (Shift.gmk k) r)))
        s s' n ∧
      n ≤ 2 * L.length + 1 ∧
      (∀ k ∈ L, s'.stk k = Shift.gmk k :: s.stk k) ∧
      (∀ j : Stk, j ∉ L → s'.stk j = s.stk j) := by
  induction L with
  | nil =>
      intro _ s
      refine ⟨s, 1, ?_, by simp, by simp, by simp⟩
      exact Ev.seqs_nil
  | cons k ks ih =>
      intro hL s
      obtain ⟨hkL, hks⟩ := List.nodup_cons.mp hL
      obtain ⟨s₁, n₁, hE₁, hn₁, hk₁, hoth₁⟩ := ev_pushConst main k (Shift.gmk k) r s
      obtain ⟨s₂, n₂, hE₂, hn₂, hk₂, hoth₂⟩ := ih hks s₁
      refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons]
        exact Ev.seqs_cons hE₁ hE₂
      · simp only [List.length_cons]
        omega
      · intro k' hk'
        rcases List.mem_cons.mp hk' with h' | hk'
        · rw [h', hoth₂ k hkL]
          exact hk₁
        · rw [hk₂ k' hk', hoth₁ k' (fun h => hkL (h ▸ hk'))]
      · intro j hj
        rw [hoth₂ j (fun h => hj (List.mem_cons_of_mem k h)),
          hoth₁ j (fun h => hj (by rw [h]; exact List.mem_cons_self))]

/-- `2 ≤ isz b`. -/
theorem two_le_isz_nat (b : ℕ) : 2 ≤ HvdH.isz (b : ℤ) := by
  simp only [HvdH.isz, Int.natAbs_natCast]
  omega

/-- The cost arithmetic of the epilogue: the pop, the seven marker pushes and the emit budget fit
into the claimed bound. -/
theorem evEpilogue_bound (KE LOlen Wlen b hslen n₂ nₑ : ℕ)
    (h₂ : n₂ ≤ 15)
    (hₑ : nₑ ≤ KE * (LOlen + Wlen + 0 + (b + 1) + 1 + 24))
    (hiz : 2 ≤ HvdH.isz (b : ℤ)) :
    1 + (n₂ + nₑ) ≤ (KE + 40) *
      (Wlen + LOlen + (hslen + 1) * (b + 1) + HvdH.isz (b : ℤ) + 40) := by
  set inner := LOlen + Wlen + 0 + (b + 1) + 1 + 24 with hinner
  set T := Wlen + LOlen + (hslen + 1) * (b + 1) + HvdH.isz (b : ℤ) + 40 with hT
  have hC : b + 1 ≤ (hslen + 1) * (b + 1) := Nat.le_mul_of_pos_left (b + 1) (Nat.succ_pos hslen)
  have hinner_le : inner ≤ T := by
    rw [hinner, hT]
    omega
  have hKe : KE * inner ≤ KE * T := Nat.mul_le_mul_left KE hinner_le
  have hT1 : 1 ≤ T := by
    rw [hT]
    omega
  have h40 : 16 ≤ 40 * T := by
    have h := Nat.mul_le_mul_left 40 hT1
    omega
  have hn : 1 + (n₂ + nₑ) ≤ 16 + KE * inner := by omega
  have hbig : 16 + KE * inner ≤ 40 * T + KE * T := by omega
  have hsplit : 40 * T + KE * T = (KE + 40) * T :=
    (Nat.add_comm (KE * T) (40 * T)).symm.trans (Nat.add_mul KE 40 T).symm
  exact le_trans hn (le_trans hbig hsplit.le)

theorem evEpilogue (emitProg : HvdH.Cmd) (KE : ℕ)
    (hem : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
      (W LO : List Bool) (V : ℕ) (Vr Rcb Rcw : List HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph),
      X Work.IntLib.aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Y Work.IntLib.aW →
      X Work.IntLib.aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Y Work.IntLib.aO →
      X Work.IntLib.aV = Vr ++ Work.IntLib.Shift.gmk Work.IntLib.aV :: Y Work.IntLib.aV →
      X Work.IntLib.aCB = Rcb ++ Work.IntLib.Shift.gmk Work.IntLib.aCB :: Y Work.IntLib.aCB →
      X Work.IntLib.aCW = Rcw ++ Work.IntLib.Shift.gmk Work.IntLib.aCW :: Y Work.IntLib.aCW →
      (∀ h ∈ Vr, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aV) →
      (∀ h ∈ Rcb, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aCB) →
      (∀ h ∈ Rcw, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aCW) →
      X 0 = Y 0 →
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.aW → k ≠ Work.IntLib.aO → k ≠ Work.IntLib.aV →
        k ≠ Work.IntLib.aCB → k ≠ Work.IntLib.aCW → X k = Work.IntLib.Shift.gmk k :: Y k) →
      Work.IntLib.ofBits LO + 2 ^ LO.length * Work.IntLib.ofBits W = V →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main emitProg ⟨g, X⟩ s' n ∧
        n ≤ KE * (LO.length + W.length + Vr.length + Rcb.length + Rcw.length + 24) ∧
        s'.stk 0 = HvdH.Val.enc (.int (V : ℤ)) ++ Y 0 ∧
        (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = Y j)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (W' LO' : List Bool) (b : ℕ) (hs : List ℕ) (Y : HvdH.Stk → List HvdH.Glyph),
      Work.IntLib.evVal hs b hs.length W' LO' →
      ∃ (s' : HvdH.State) (n : ℕ),
        Work.Layout.Ev main prog ⟨g, Work.IntLib.evStk hs b hs.length W' LO' Y⟩ s' n ∧
        n ≤ K * (KE + 40) * (W'.length + LO'.length + (hs.length + 1) * (b + 1)
          + HvdH.isz (b : ℤ) + 40) ∧
        s'.stk 0 = HvdH.Val.enc (.int (HvdH.evalChunks hs b : ℤ)) ++ Y 0 ∧
        (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = Y j) := by
  refine ⟨Cmd.seq (.pop aC rX) (Cmd.seq
      (Work.Layout.seqs (evEpiL.map (fun k => Work.IntLib.pushConst k (Shift.gmk k) rX)))
      emitProg), 1, ?_⟩
  intro main g W' LO' b hs Y hval
  obtain ⟨-, -, harith⟩ := hval
  -- ## step 1: pop the terminating `nil` off stack 0
  obtain ⟨S₁, n₁, hE₁, hn₁, hS₁k, hS₁o⟩ :=
    ev_popHead main aC rX (⟨g, evStk hs b hs.length W' LO' Y⟩ : State)
  have hS₁ev : ∀ j : Stk, j ≠ aC → S₁.stk j = evStk hs b hs.length W' LO' Y j := by
    intro j hj
    rw [hS₁o j hj]
  have hS₁0 : S₁.stk 0 = Y 0 := by
    have h : S₁.stk aC = (Val.enc (intList (hs.drop hs.length)) ++ Y aC).tail := by
      simpa only [Work.Layout.stk_mk, evStk_aC] using hS₁k
    have hdrop : hs.drop hs.length = [] := List.drop_eq_nil_of_le le_rfl
    rw [hdrop, enc_intList_nil_el] at h
    simpa [Work.IntLib.aC] using h
  -- ## step 2: re-push the frame markers of `evEpiL`
  obtain ⟨S₂, n₂, hE₂, hn₂, hS₂in, hS₂out⟩ := ev_pushMarkersAux main rX evEpiL evEpiL_nodup S₁
  have hS₂ev : ∀ j : Stk, j ∉ evEpiL → j ≠ aC →
      S₂.stk j = evStk hs b hs.length W' LO' Y j := by
    intro j hj hj0
    rw [hS₂out j hj, hS₁ev j hj0]
  have hS₂0 : S₂.stk 0 = Y 0 := by
    rw [hS₂out 0 (by decide), hS₁0]
  -- ## step 3: the hypotheses of the emit word
  have hW₂ : S₂.stk aW = W'.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [hS₂ev aW (by decide) (by decide), evStk_aW]
  have hO₂ : S₂.stk aO = LO'.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
    rw [hS₂ev aO (by decide) (by decide), evStk_aO]
  have hV₂ : S₂.stk aV = Shift.gmk aV :: Y aV := by
    rw [hS₂in aV (by decide), hS₁ev aV (by decide), evStk_aV]
  have hCB₂ : S₂.stk aCB = Unary b [] ++ Shift.gmk aCB :: Y aCB := by
    rw [hS₂ev aCB (by decide) (by decide), evStk_aCB, Unary_cons_append]
  have hCW₂ : S₂.stk aCW = Unary 0 [] ++ Shift.gmk aCW :: Y aCW := by
    rw [hS₂ev aCW (by decide) (by decide), evStk_aCW, Unary_cons_append]
  have hmarkV : ∀ h ∈ ([] : List Glyph), h ≠ Shift.gmk aV := by simp
  have hmarkCB : ∀ h ∈ Unary b [], h ≠ Shift.gmk aCB := by
    intro h hh
    rcases mem_Unary hh with h' | h'
    · rw [h']; decide
    · rcases h' with h' | h'
      · rw [h']; decide
      · simp at h'
  have hmarkCW : ∀ h ∈ Unary 0 [], h ≠ Shift.gmk aCW := by
    intro h hh
    rw [Unary_zero_nil] at hh
    rw [List.mem_singleton.mp hh]
    decide
  have hoth₂ : ∀ k : Stk, k ≠ 0 → k ≠ aW → k ≠ aO → k ≠ aV → k ≠ aCB → k ≠ aCW →
      S₂.stk k = Shift.gmk k :: Y k := by
    intro k hk0 hkW hkO hkV hkCB hkCW
    rcases stk_cover k hk0 hkW hkO hkV hkCB hkCW with h | h | h | h | h | h | h | h | h | h
    · rw [h, hS₂ev aA (by decide) (by decide), evStk_aA]
    · rw [h, hS₂ev aB (by decide) (by decide), evStk_aB]
    · rw [h, hS₂ev a2 (by decide) (by decide), evStk_a2]
    · rw [h, hS₂ev aL (by decide) (by decide), evStk_aL]
    · have hs9 : S₂.stk 9 = Shift.gmk 9 :: S₁.stk 9 := hS₂in 9 (by decide)
      have he9 : S₁.stk 9 = Y 9 := by
        rw [hS₁ev 9 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs9, he9]
    · have hs10 : S₂.stk 10 = Shift.gmk 10 :: S₁.stk 10 := hS₂in 10 (by decide)
      have he10 : S₁.stk 10 = Y 10 := by
        rw [hS₁ev 10 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs10, he10]
    · have hs12 : S₂.stk 12 = Shift.gmk 12 :: S₁.stk 12 := hS₂in 12 (by decide)
      have he12 : S₁.stk 12 = Y 12 := by
        rw [hS₁ev 12 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs12, he12]
    · have hs13 : S₂.stk 13 = Shift.gmk 13 :: S₁.stk 13 := hS₂in 13 (by decide)
      have he13 : S₁.stk 13 = Y 13 := by
        rw [hS₁ev 13 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs13, he13]
    · have hs14 : S₂.stk 14 = Shift.gmk 14 :: S₁.stk 14 := hS₂in 14 (by decide)
      have he14 : S₁.stk 14 = Y 14 := by
        rw [hS₁ev 14 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs14, he14]
    · have hs15 : S₂.stk 15 = Shift.gmk 15 :: S₁.stk 15 := hS₂in 15 (by decide)
      have he15 : S₁.stk 15 = Y 15 := by
        rw [hS₁ev 15 (by decide)]
        exact evStk_mem_evEpiL hs b hs.length W' LO' Y (by decide)
      rw [h, hs15, he15]
  -- ## step 4: the emit word
  have harith' : ofBits LO' + 2 ^ LO'.length * ofBits W' = evalChunks hs b := by
    rw [harith, List.take_length]
  obtain ⟨s', n₃, hE₃, hn₃, hs'0, hs'oth⟩ :=
    hem main S₂.reg S₂.stk W' LO' (evalChunks hs b)
      ([] : List Glyph) (Unary b []) (Unary 0 []) Y
      hW₂ hO₂ hV₂ hCB₂ hCW₂ hmarkV hmarkCB hmarkCW hS₂0 hoth₂ harith'
  have hE₃' : Ev main emitProg S₂ s' n₃ := hE₃
  -- ## assembling the result
  refine ⟨s', 1 + (n₂ + n₃), ?_, ?_, hs'0, hs'oth⟩
  · refine (Ev.seq hE₁ (Ev.seq hE₂ hE₃')).mono ?_
    omega
  · have hn₂' : n₂ ≤ 15 := by
      rw [evEpiL_length] at hn₂
      omega
    have hn₃' : n₃ ≤ KE * (LO'.length + W'.length + 0 + (b + 1) + 1 + 24) := by
      rw [List.length_nil, Unary_nil_length, Unary_zero_nil_length] at hn₃
      exact hn₃
    rw [Nat.one_mul]
    exact evEpilogue_bound KE LO'.length W'.length b hs.length n₂ n₃ hn₂' hn₃'
      (two_le_isz_nat b)

end Work.IntLib
