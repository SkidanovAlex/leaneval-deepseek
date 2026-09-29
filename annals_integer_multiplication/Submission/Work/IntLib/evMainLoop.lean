import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.chunksAPI
import Submission.Work.IntLib.evChainDefs
import Submission.Work.IntLib.evMainValStep
import Submission.Work.IntLib.evMainBodyTail
import Submission.Work.IntLib.evMainEvStkEq

/-!
# `IntLib` / `evMainLoop`: the main loop of the `evalPoly` word

`evBody` consumes one `cons` cell of the chain `intList hs` on stack `aC = 0` (reading the digit
with the gadget `readG`, refilling the working counter with `copyG` and doing the carry-add with
`addG`) and appends `b` finalised bits to `aO`, keeping the invariant `evVal hs b j W LO`.

`evMainLoop` runs this loop over the whole chain, given the gadget specifications `hread`, `hcopy`,
`hadd`, with the cost bound `(10*KR + 10*KC + 40*KA + 50) * (Σ|h| + length*(b+2) + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Composition of `seqs` -/

/-- Concatenation of `seqs` programs, at the `Ev` level. -/
theorem evMain_seqs_append {main : Cmd} : ∀ (l₁ l₂ : List Cmd) (s t u : State) (C₁ C₂ : ℕ),
    Ev main (seqs l₁) s t C₁ → Ev main (seqs l₂) t u C₂ → Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ s t u C₁ C₂ h₁ h₂
      obtain ⟨n, he, -⟩ := h₁
      cases he
      exact h₂.mono (by omega)
  | cons c cs ih =>
      intro l₂ s t u C₁ C₂ h₁ h₂
      cases cs with
      | nil =>
        cases l₂ with
        | nil =>
          obtain ⟨n, he, -⟩ := h₂
          cases he
          exact h₁.mono (by omega)
        | cons d ds => exact Ev.seq h₁ h₂
      | cons d ds =>
        obtain ⟨n₁, e₁, hl₁⟩ := h₁
        rw [show seqs (c :: d :: ds) = .seq c (seqs (d :: ds)) from rfl] at e₁
        cases e₁ with
        | seq e e' =>
          have hrec : Ev main (seqs ((d :: ds) ++ l₂)) _ u (_ + C₂) :=
            ih l₂ _ _ u _ C₂ ⟨_, e', le_rfl⟩ h₂
          exact (Ev.seq ⟨_, e, le_rfl⟩ hrec).mono (by omega)

/-- `Ev` for a list of commands, with an exact budget. -/
theorem evMain_seqs_append' {main : Cmd} {l₁ l₂ : List Cmd} {s t u : State} {C₁ C₂ : ℕ}
    (h₁ : Ev main (seqs l₁) s t C₁) (h₂ : Ev main (seqs l₂) t u C₂) :
    Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) :=
  evMain_seqs_append l₁ l₂ s t u C₁ C₂ h₁ h₂

/-! ## Cost bookkeeping -/

/-- The budget for one iteration of the `evalPoly` main loop (body plus the loop test). -/
def evBodyCost (KR KC KA b h : ℕ) : ℕ :=
  6 + KR * (h.size + 2) + KC * (b + 1) + KA * (4 * b + h.size + 2)

/-- The total budget for a list of remaining digits. -/
def evBudget (b : ℕ) (l : List ℕ) : ℕ :=
  (l.map (fun h => h.size)).sum + l.length * (b + 2)

/-- The constant of the final cost bound. -/
def evK (KR KC KA : ℕ) : ℕ := 10 * KR + 10 * KC + 40 * KA + 50

theorem evBudget_cons (b h : ℕ) (t : List ℕ) :
    evBudget b (h :: t) = h.size + b + 2 + evBudget b t := by
  simp only [evBudget, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
  ring

theorem evBudget_nil (b : ℕ) : evBudget b [] = 0 := by simp [evBudget]

/-- One loop iteration (body cost plus the loop test) fits in the per-digit share of the budget. -/
theorem evMain_stepCost_le (h b KR KC KA : ℕ) (hb : 1 ≤ b) :
    evBodyCost KR KC KA b h + 1 ≤ evK KR KC KA * (h.size + b + 2) := by
  have h1 : h.size + 2 ≤ 10 * (h.size + b + 2) := by omega
  have h2 : b + 1 ≤ 10 * (h.size + b + 2) := by omega
  have h4 : 4 * b + h.size + 2 ≤ 40 * (h.size + b + 2) := by omega
  have h5 : (7 : ℕ) ≤ 50 * (h.size + b + 2) := by nlinarith
  simp only [evBodyCost, evK]
  nlinarith [Nat.mul_le_mul_right (KR) h1, Nat.mul_le_mul_right (KC) h2,
    Nat.mul_le_mul_right (KA) h4]

/-- The initial `set` instruction and the final loop test are absorbed by the `+1` of the bound. -/
theorem evMain_topCost_le (A KR KC KA : ℕ) :
    2 + evK KR KC KA * A ≤ evK KR KC KA * (A + 1) := by
  have h : 2 ≤ evK KR KC KA := by simp only [evK]; omega
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## Small helpers for the stack function -/

theorem upd_aC_apply {X : Stk → List Glyph} {v : List Glyph} {k : Stk} (hk : k ≠ aC) :
    (Function.update X aC v) k = X k := Function.update_of_ne hk v X

/-- The nine stacks of the `evalPoly` word are pairwise distinct. -/
theorem evNine_not {k : Stk}
    (h : k ∉ ({aC, aW, aO, aCW, aCB, aA, aB, a2, aL} : Finset Stk)) :
    k ≠ aC ∧ k ≠ aW ∧ k ≠ aO ∧ k ≠ aCW ∧ k ≠ aCB ∧ k ≠ aA ∧ k ≠ aB ∧ k ≠ a2 ∧
      k ≠ aL := by
  simpa using h

/-! ## The gadget specifications -/

/-- The three gadget specifications used by the `evalPoly` main loop (as in `HvdH.IntLib`):
`readG` reads one integer off stack 0 and prepends its reversed encoding to `aA`, `copyG` refills the
working counter `aCW` from the master counter `aCB`, and `addG` performs one carry-add step. -/
structure EvGadgets (main : Cmd) (readG copyG addG : Cmd) (KR KC KA b : ℕ) : Prop where
  read : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (rest : List Glyph),
      X 0 = Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : State) (n : ℕ), Ev main readG ⟨g, X⟩ s' n ∧ n ≤ KR * (h.size + 2) ∧
        s'.stk 0 = rest ∧ s'.stk aA = (Val.enc (.int (h : ℤ))).reverse ++ X aA ∧
        (∀ j : Stk, j ≠ 0 → j ≠ aA → s'.stk j = X j)
  copy : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (m : ℕ) (Ca Cb : List Glyph),
      X aCB = Unary m Ca → X aCW = gEnd :: Cb →
      ∃ (s' : State) (n : ℕ), Ev main copyG ⟨g, X⟩ s' n ∧ n ≤ KC * (m + 1) ∧
        s'.stk aCB = Unary m Ca ∧ s'.stk aCW = Unary m Cb ∧
        (∀ k : Stk, k ≠ aCB → k ≠ aCW → s'.stk k = X k)
  add : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (W LO : List Bool)
      (Ws Os Cs Bs A2s As : List Glyph),
      X aA = (Val.enc (.int (h : ℤ))).reverse ++ Shift.gmk aA :: As →
      X aW = W.map Glyph.bit ++ Shift.gmk aW :: Ws →
      X aO = LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os →
      X aCW = Unary b (Shift.gmk aCW :: Cs) →
      X aB = Shift.gmk aB :: Bs →
      X a2 = Shift.gmk a2 :: A2s →
      ∃ (s' : State) (n : ℕ), Ev main addG ⟨g, X⟩ s' n ∧
        n ≤ KA * (b + W.length + h.size + 1) ∧
        s'.stk aA = Shift.gmk aA :: As ∧
        (∃ W' : List Bool, s'.stk aW = W'.map Glyph.bit ++ Shift.gmk aW :: Ws ∧
          ofBits W' = (ofBits W + h) / 2 ^ b ∧
          W'.length ≤ max W.length (h.size + 1) + 1 ∧
          (1 ≤ b → W.length ≤ 3 * b + 1 → h.size ≤ 3 * b → W'.length ≤ 3 * b + 1)) ∧
        (∃ LO' : List Bool, s'.stk aO = LO'.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os ∧
          LO'.length = LO.length + b ∧
          ofBits LO' = ofBits LO + 2 ^ LO.length * ((ofBits W + h) % 2 ^ b)) ∧
        s'.stk aCW = Unary 0 (Shift.gmk aCW :: Cs) ∧
        s'.stk aB = Shift.gmk aB :: Bs ∧
        s'.stk a2 = Shift.gmk a2 :: A2s ∧
        (∀ j : Stk, j ≠ aA → j ≠ aW → j ≠ aO →
          j ≠ aCW → j ≠ aB → j ≠ a2 → s'.stk j = X j)

/-! ## One iteration of the main loop -/

theorem evBody_ev (main readG copyG addG : Cmd) (KR KC KA b : ℕ)
    (G : EvGadgets main readG copyG addG KR KC KA b) (hb : 1 ≤ b)
    (hs : List ℕ) (j h : ℕ) (tl : List ℕ) (W LO : List Bool) (Y : Stk → List Glyph)
    (g : Reg → Glyph)
    (hd : hs.drop j = h :: tl) (hh : h < 2 ^ (3 * b)) (hval : evVal hs b j W LO) :
    ∃ (W' LO' : List Bool) (s' : State),
      Ev main (evBody readG copyG addG) ⟨g, evStk hs b j W LO Y⟩ s' (evBodyCost KR KC KA b h) ∧
      s'.stk = evStk hs b (j + 1) W' LO' Y ∧
      s'.reg rLp = (if tl = [] then fStop else fGo) ∧
      evVal hs b (j + 1) W' LO' := by
  have hWlen : W.length ≤ 3 * b + 1 := hval.2.1
  have hsz : h.size ≤ 3 * b := Nat.size_le.mpr hh
  have hdrop1 : hs.drop (j + 1) = tl := by rw [← List.tail_drop, hd]; rfl
  have h0C : (evStk hs b j W LO Y) aC =
      Glyph.cons :: (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC) := by
    have hd' : Val.enc (intList (hs.drop j)) =
        Glyph.cons :: (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl)) := by
      rw [hd, enc_intList_cons]
    rw [evStk_aC, hd', List.cons_append]
  -- ### 1. `pop`: the digit `h` becomes the top value of stack 0
  have hpop : Ev main (.pop aC rX) ⟨g, evStk hs b j W LO Y⟩
      ⟨Function.update g rX Glyph.cons,
        Function.update (evStk hs b j W LO Y) aC
          (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)⟩ 1 := by
    have ht : ((evStk hs b j W LO Y) aC).tail =
        Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC := by rw [h0C]; rfl
    have hhead : ((evStk hs b j W LO Y) aC).headD Glyph.eos = Glyph.cons := by
      rw [h0C]; rfl
    have hp := ev_pop' main aC rX g (evStk hs b j W LO Y)
    rw [ht, hhead] at hp
    exact hp
  have hX1 : (Function.update (evStk hs b j W LO Y) aC
        (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)) 0
      = Val.enc (.int (h : ℤ)) ++ (Val.enc (intList tl) ++ Y aC) := by
    have h1 : (Function.update (evStk hs b j W LO Y) aC
        (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)) 0
        = Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC :=
      Function.update_self aC _ _
    rw [h1, List.append_assoc]
  -- ### 2. `readG`
  obtain ⟨s2, n2, h2ev, h2le, h2s0, h2sA, h2fr⟩ :=
    G.read (Function.update g rX Glyph.cons)
      (Function.update (evStk hs b j W LO Y) aC
        (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)) h
      (Val.enc (intList tl) ++ Y aC) hX1
  have hs2A : s2.stk aA = (Val.enc (.int (h : ℤ))).reverse ++ Shift.gmk aA :: Y aA := by
    rw [h2sA, upd_aC_apply (by decide : aA ≠ aC), evStk_aA]
  have hs2W : s2.stk aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [h2fr aW (by decide) (by decide), upd_aC_apply (by decide : aW ≠ aC), evStk_aW]
  have hs2O : s2.stk aO =
      LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
    rw [h2fr aO (by decide) (by decide), upd_aC_apply (by decide : aO ≠ aC), evStk_aO]
  have hs2CB : s2.stk aCB = Unary b (Shift.gmk aCB :: Y aCB) := by
    rw [h2fr aCB (by decide) (by decide), upd_aC_apply (by decide : aCB ≠ aC), evStk_aCB]
  have hs2CW : s2.stk aCW = gEnd :: (Shift.gmk aCW :: Y aCW) := by
    rw [h2fr aCW (by decide) (by decide), upd_aC_apply (by decide : aCW ≠ aC), evStk_aCW,
      Unary_zero]
  have hs2B : s2.stk aB = Shift.gmk aB :: Y aB := by
    rw [h2fr aB (by decide) (by decide), upd_aC_apply (by decide : aB ≠ aC), evStk_aB]
  have hs22 : s2.stk a2 = Shift.gmk a2 :: Y a2 := by
    rw [h2fr a2 (by decide) (by decide), upd_aC_apply (by decide : a2 ≠ aC), evStk_a2]
  -- ### 3. `copyG`: refill the working counter
  obtain ⟨s3, n3, h3ev, h3le, h3CB, h3CW, h3fr⟩ :=
    G.copy s2.reg s2.stk
      b (Shift.gmk aCB :: Y aCB) (Shift.gmk aCW :: Y aCW) hs2CB hs2CW
  have hs3A : s3.stk aA = (Val.enc (.int (h : ℤ))).reverse ++ Shift.gmk aA :: Y aA := by
    rw [h3fr aA (by decide) (by decide)]; exact hs2A
  have hs3W : s3.stk aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [h3fr aW (by decide) (by decide)]; exact hs2W
  have hs3O : s3.stk aO =
      LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
    rw [h3fr aO (by decide) (by decide)]; exact hs2O
  have hs3B : s3.stk aB = Shift.gmk aB :: Y aB := by
    rw [h3fr aB (by decide) (by decide)]; exact hs2B
  have hs32 : s3.stk a2 = Shift.gmk a2 :: Y a2 := by
    rw [h3fr a2 (by decide) (by decide)]; exact hs22
  -- ### 4. `addG`: the carry-add step
  obtain ⟨s4, n4, h4ev, h4le, h4A, ⟨W', h4W, h4Wval, h4Wlen, h4Wlen3⟩,
      ⟨LO', h4O, h4Olen, h4Oval⟩, h4CW, h4B, h42, h4fr⟩ :=
    G.add s3.reg s3.stk
      h W LO (Y aW) (Y aO) (Y aCW) (Y aB) (Y a2) (Y aA)
      hs3A hs3W hs3O h3CW hs3B hs32
  have hs40 : s4.stk 0 = Val.enc (intList tl) ++ Y aC := by
    rw [h4fr 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h3fr 0 (by decide) (by decide), h2s0]
  have hs4CB : s4.stk aCB = Unary b (Shift.gmk aCB :: Y aCB) := by
    rw [h4fr aCB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h3CB
  have hs4L : s4.stk aL = Shift.gmk aL :: Y aL := by
    rw [h4fr aL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h3fr aL (by decide) (by decide),
      h2fr aL (by decide) (by decide), upd_aC_apply (by decide : aL ≠ aC), evStk_aL]
  have hval' : evVal hs b (j + 1) W' LO' :=
    evMainValStep hd hval h4Olen h4Oval h4Wval (h4Wlen3 hb hWlen hsz)
  -- ### 5. the loop test (peek + ite)
  obtain ⟨s5, n5, h5ev, h5le, h5stk, h5reg⟩ :=
    evMainBodyTail main s4.reg s4.stk tl (Y aC) hs40
  -- ### 6. the final state is again an `evStk` state
  have hstk : s5.stk = evStk hs b (j + 1) W' LO' Y := by
    rw [evMainEvStkEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h5stk, hdrop1]; exact hs40
    · rw [h5stk]; exact h4W
    · rw [h5stk]; exact h4O
    · rw [h5stk]; exact h4CW
    · rw [h5stk]; exact hs4CB
    · rw [h5stk]; exact h4A
    · rw [h5stk]; exact h4B
    · rw [h5stk]; exact h42
    · rw [h5stk]; exact hs4L
    · intro k hk
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := evNine_not hk
      rw [h5stk, h4fr k e6 e2 e3 e4 e7 e8, h3fr k e5 e4, h2fr k e1 e6,
        upd_aC_apply e1]
      exact evStk_other hs b j W LO Y e1 e2 e3 e4 e5 e6 e7 e8 e9
  -- ### 7. cost
  have hn4' : n4 ≤ KA * (4 * b + h.size + 2) :=
    le_trans h4le (Nat.mul_le_mul_left KA (by omega))
  have hcost : (((1 : ℕ) + n2) + n3 + n4) + n5 ≤ evBodyCost KR KC KA b h := by
    have h1 : ((1 : ℕ) + n2) + n3 ≤ 1 + KR * (h.size + 2) + KC * (b + 1) := by omega
    have h2 : ((1 : ℕ) + n2) + n3 + n4 ≤
        1 + KR * (h.size + 2) + KC * (b + 1) + KA * (4 * b + h.size + 2) := by omega
    simp only [evBodyCost]
    omega
  -- ### 8. compose the pieces
  refine ⟨W', LO', s5, ?_, hstk, h5reg, hval'⟩
  have hapop : Ev main (seqs [.pop aC rX]) ⟨g, evStk hs b j W LO Y⟩
      ⟨Function.update g rX Glyph.cons,
        Function.update (evStk hs b j W LO Y) aC
          (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)⟩ 1 := hpop
  have haread : Ev main (seqs [readG]) ⟨Function.update g rX Glyph.cons,
        Function.update (evStk hs b j W LO Y) aC
          (Val.enc (.int (h : ℤ)) ++ Val.enc (intList tl) ++ Y aC)⟩ s2 n2 := h2ev
  have hacopy : Ev main (seqs [copyG]) s2 s3 n3 := h3ev
  have haadd : Ev main (seqs [addG]) s3 s4 n4 := h4ev
  have hatail : Ev main (seqs [.peek aC rY,
      .ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop)]) s4 s5 n5 := h5ev
  have e1 := evMain_seqs_append' hapop haread
  have e2 := evMain_seqs_append' e1 hacopy
  have e3 := evMain_seqs_append' e2 haadd
  have e4 := evMain_seqs_append' e3 hatail
  exact e4.mono hcost

/-! ## The main loop -/

theorem evLoop_ev (main readG copyG addG : Cmd) (KR KC KA b : ℕ)
    (G : EvGadgets main readG copyG addG KR KC KA b) (hb : 1 ≤ b)
    (hs : List ℕ) (hh : ∀ h ∈ hs, h < 2 ^ (3 * b)) :
    ∀ (l : List ℕ) (j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) (g : Reg → Glyph),
      hs.drop j = l → j + l.length = hs.length → (∀ h ∈ l, h < 2 ^ (3 * b)) →
      evVal hs b j W LO → g rLp = (if l = [] then fStop else fGo) →
      ∃ (W' LO' : List Bool) (s' : State) (C : ℕ),
        Ev main (.loop rLp fGo (evBody readG copyG addG)) ⟨g, evStk hs b j W LO Y⟩ s' C ∧
        C ≤ 1 + evK KR KC KA * evBudget b l ∧
        s'.stk = evStk hs b hs.length W' LO' Y ∧ evVal hs b hs.length W' LO' := by
  intro l
  induction l with
  | nil =>
      intro j W LO Y g hd hjl hhl hval hg
      have hj : j = hs.length := by simpa using hjl
      subst hj
      have hgf : g rLp = fStop := by simpa using hg
      refine ⟨W, LO, ⟨g, evStk hs b hs.length W LO Y⟩, 1, ?_, ?_, rfl, hval⟩
      · have hne : g rLp ≠ fGo := by rw [hgf]; exact fun h => fGo_ne_fStop h.symm
        exact Ev.loopF hne
      · rw [evBudget_nil]; omega
  | cons h t ih =>
      intro j W LO Y g hd hjl hhl hval hg
      have hhlt : h < 2 ^ (3 * b) := hhl h (List.mem_cons_self ..)
      have htl : ∀ x ∈ t, x < 2 ^ (3 * b) := fun x hx => hhl x (List.mem_cons_of_mem h hx)
      have hgf : g rLp = fGo := by rw [hg, if_neg (by simp)]
      obtain ⟨W', LO', s2, h2ev, h2stk, h2reg, h2val⟩ :=
        evBody_ev main readG copyG addG KR KC KA b G hb hs j h t W LO Y g hd hhlt hval
      have hd1 : hs.drop (j + 1) = t := by rw [← List.tail_drop, hd]; rfl
      have hjl1 : (j + 1) + t.length = hs.length := by
        have hlen : (hs.drop j).length = hs.length - j := List.length_drop
        rw [hd] at hlen
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨W'', LO'', s3, C3, h3ev, h3le, h3stk, h3val⟩ :=
        ih (j + 1) W' LO' Y s2.reg hd1 hjl1 htl h2val h2reg
      have hs2eq : s2 = ⟨s2.reg, evStk hs b (j + 1) W' LO' Y⟩ := by rw [← h2stk]
      rw [← hs2eq] at h3ev
      have hstep : evBodyCost KR KC KA b h + 1 ≤ evK KR KC KA * (h.size + b + 2) := by
        simpa only [evBodyCost, evK] using evMain_stepCost_le h b KR KC KA hb
      have hCloop : evBodyCost KR KC KA b h + C3 + 1 ≤
          1 + evK KR KC KA * evBudget b (h :: t) := by
        rw [evBudget_cons, Nat.mul_add]
        nlinarith [h3le, hstep]
      refine ⟨W'', LO'', s3, evBodyCost KR KC KA b h + C3 + 1,
        Ev.loopT hgf h2ev h3ev, hCloop, h3stk, h3val⟩

theorem evMainLoop (main : HvdH.Cmd) (readG copyG addG : HvdH.Cmd) (KR KC KA : ℕ)
    (b : ℕ) (hb : 1 ≤ b) (hs : List ℕ) (hne : hs ≠ []) (hh : ∀ h ∈ hs, h < 2 ^ (3 * b))
    (hread : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (h : ℕ)
      (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main readG ⟨g, X⟩ s' n ∧
        n ≤ KR * (h.size + 2) ∧ s'.stk 0 = rest ∧
        s'.stk Work.IntLib.aA = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X Work.IntLib.aA ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.aA → s'.stk j = X j))
    (hcopy : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (m : ℕ)
      (Ca Cb : List HvdH.Glyph),
      X Work.IntLib.aCB = Work.IntLib.Unary m Ca → X Work.IntLib.aCW = Work.IntLib.gEnd :: Cb →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main copyG ⟨g, X⟩ s' n ∧ n ≤ KC * (m + 1) ∧
        s'.stk Work.IntLib.aCB = Work.IntLib.Unary m Ca ∧
        s'.stk Work.IntLib.aCW = Work.IntLib.Unary m Cb ∧
        (∀ k : HvdH.Stk, k ≠ Work.IntLib.aCB → k ≠ Work.IntLib.aCW → s'.stk k = X k))
    (hadd : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (h : ℕ)
      (W LO : List Bool) (Ws Os Cs Bs A2s As : List HvdH.Glyph),
      X Work.IntLib.aA = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ Work.IntLib.Shift.gmk Work.IntLib.aA :: As →
      X Work.IntLib.aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Ws →
      X Work.IntLib.aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Os →
      X Work.IntLib.aCW = Work.IntLib.Unary b (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) →
      X Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs →
      X Work.IntLib.a2 = Work.IntLib.Shift.gmk Work.IntLib.a2 :: A2s →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main addG ⟨g, X⟩ s' n ∧
        n ≤ KA * (b + W.length + h.size + 1) ∧
        s'.stk Work.IntLib.aA = Work.IntLib.Shift.gmk Work.IntLib.aA :: As ∧
        (∃ W' : List Bool, s'.stk Work.IntLib.aW = W'.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Ws ∧
          Work.IntLib.ofBits W' = (Work.IntLib.ofBits W + h) / 2 ^ b ∧
          W'.length ≤ max W.length (h.size + 1) + 1 ∧
          (1 ≤ b → W.length ≤ 3 * b + 1 → h.size ≤ 3 * b → W'.length ≤ 3 * b + 1)) ∧
        (∃ LO' : List Bool, s'.stk Work.IntLib.aO = LO'.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Os ∧
          LO'.length = LO.length + b ∧
          Work.IntLib.ofBits LO' = Work.IntLib.ofBits LO + 2 ^ LO.length * ((Work.IntLib.ofBits W + h) % 2 ^ b)) ∧
        s'.stk Work.IntLib.aCW = Work.IntLib.Unary 0 (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) ∧
        s'.stk Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs ∧
        s'.stk Work.IntLib.a2 = Work.IntLib.Shift.gmk Work.IntLib.a2 :: A2s ∧
        (∀ j : HvdH.Stk, j ≠ Work.IntLib.aA → j ≠ Work.IntLib.aW → j ≠ Work.IntLib.aO →
          j ≠ Work.IntLib.aCW → j ≠ Work.IntLib.aB → j ≠ Work.IntLib.a2 → s'.stk j = X j))
    (Y : HvdH.Stk → List HvdH.Glyph) (W LO : List Bool) (g : HvdH.Reg → HvdH.Glyph)
    (h0 : Work.IntLib.evVal hs b 0 W LO) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main (Work.IntLib.evLoopP readG copyG addG) ⟨g, Work.IntLib.evStk hs b 0 W LO Y⟩ s' n ∧
      n ≤ (10 * KR + 10 * KC + 40 * KA + 50) * ((hs.map fun h => h.size).sum + hs.length * (b + 2) + 1) ∧
      ∃ (W' LO' : List Bool), s' = ⟨s'.reg, Work.IntLib.evStk hs b hs.length W' LO' Y⟩ ∧
        Work.IntLib.evVal hs b hs.length W' LO' := by
  have G : EvGadgets main readG copyG addG KR KC KA b := ⟨hread, hcopy, hadd⟩
  have hset : Ev main (.set rLp fGo) ⟨g, evStk hs b 0 W LO Y⟩
      ⟨Function.update g rLp fGo, evStk hs b 0 W LO Y⟩ 1 :=
    ev_set' main rLp fGo g (evStk hs b 0 W LO Y)
  obtain ⟨W', LO', s1, C, hloop, hC, hstk, hval'⟩ :=
    evLoop_ev main readG copyG addG KR KC KA b G hb hs hh hs 0 W LO Y
      (Function.update g rLp fGo) (by simp) (by simp) hh h0
      (by rw [if_neg hne]; exact Function.update_self rLp fGo g)
  refine ⟨s1, 1 + C, ?_, ?_, W', LO', ?_, hval'⟩
  · exact Ev.seqs_cons hset hloop
  · have h3 : evK KR KC KA * (evBudget b hs + 1)
        = evK KR KC KA * evBudget b hs + evK KR KC KA := by
      rw [Nat.mul_add, Nat.mul_one]
    have := evMain_topCost_le (evBudget b hs) KR KC KA
    show 1 + C ≤ evK KR KC KA * (evBudget b hs + 1)
    rw [h3]
    omega
  · rw [← hstk]

end Work.IntLib
